import os
import asyncio
import logging
import sys
import io
import json
import random
from dataclasses import dataclass
from typing import List, Optional, Dict, Set, Tuple
from datetime import datetime, timedelta, timezone
from telethon import TelegramClient, events, Button
from telethon.sessions import StringSession
from telethon.tl.types import UpdateMessageReactions
from telethon.errors import (
    ChatWriteForbiddenError, UserBannedInChannelError,
    AuthKeyError, SessionExpiredError,
    FloodWaitError
)
import aiohttp as _aiohttp
from aiohttp import web
from fpdf import FPDF
from fpdf.enums import XPos, YPos

from config import (
    API_ID, API_HASH, BOT_TOKEN, ADMIN_ID,
    PREDICTION_CHANNEL_ID, PREDICTION_CHANNEL_ID2,
    DISTRIBUTION_CHANNEL_ID  as _DIST_CH_INIT,
    COMPTEUR2_CHANNEL_ID     as _C2_CH_INIT,
    PREDICTION_CHANNEL_ID3   as _C3_CH_INIT,
    PREDICTION_CHANNEL_ID4   as _C4_CH_INIT,
    PORT, RENDER_EXTERNAL_URL,
    ALL_SUITS, SUIT_DISPLAY, API_SILENCE_ALERT_MINUTES,
    PREDICTION_DF_DEFAULT,
    B_INCREMENT_DEFAULT,
    COMPTEUR8_THRESHOLD, COMPTEUR8_DATA_FILE,
)
import db as db
from api_utils import get_latest_results
from parole import get_parole

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger(__name__)

if not API_ID or API_ID == 0:
    logger.error("API_ID manquant")
    exit(1)
if not API_HASH:
    logger.error("API_HASH manquant")
    exit(1)
if not BOT_TOKEN:
    logger.error("BOT_TOKEN manquant")
    exit(1)

# ============================================================================
# VARIABLES GLOBALES
# ============================================================================

pending_predictions: Dict[int, dict] = {}
canal_pred_msg_ids: Dict[int, int] = {}   # {telegram_msg_id → game_number} — suivi réactions canal
notified_reactions: Set[tuple] = set()    # {(msg_id, user_id, emoji)} déjà notifiés
current_game_number = 0
last_prediction_time: Optional[datetime] = None
prediction_channel_ok = False
client = None
suit_block_until: Dict[str, datetime] = {}

# Suivi santé API 1xBet
last_api_success_time: Optional[datetime] = None
api_silence_alerted: bool = False  # évite de spammer l'admin

# Suivi formation : stocke la dernière meilleure formation ("f1", "f2", "f3", None)
_last_formation_best: Optional[str] = None

# Dernier exemple concret de formation déclenché (pour message canal horaire)
_last_formation_example: Optional[Dict] = None
# {
#   'original_game': int,          # jeu N prédit
#   'original_suit': str,          # costume prédit (normalisé)
#   'card_position': str,          # '1ère', '2ème', '3ème'
#   'recommended_suit': str,       # costume recommandé pour N+1
#   'next_game': int,              # jeu N+1 à vérifier
# }

# Formation follow-up : {game_to_check: {recommended_suit, canal_msg_id, original_game, ...}}
formation_follow_ups: Dict[int, dict] = {}

# Compteur de prédictions résolues — rapport formation auto tous les 10
_resolved_predictions_count: int = 0
FORMATION_AUTO_EVERY = 10   # envoyer le rapport tous les N prédictions résolues

# Historique API des jeux
game_history: Dict[int, dict] = {}

# Cache live : stocke TOUS les jeux (en cours + terminés) tels que retournés par l'API.
# Mis à jour à chaque poll ; sert de filet de sécurité pour les rattrapages.
# Nettoyé automatiquement après vérification ou quand le cache dépasse 200 entrées.
game_result_cache: Dict[int, dict] = {}

processed_games: Set[int] = set()  # Jeux déjà comptabilisés (compteur2, compteur4)
prediction_checked_games: Set[int] = set()  # Jeux dont les prédictions ont été vérifiées
recently_predicted: Set[int] = set()  # Anti-doublon : game_numbers déjà envoyés (jamais re-sendés)

# Proposition de stratégie en attente de confirmation ("Oui")
pending_strategy_proposal: Dict = {}   # {name, changes, description, expires}
auto_strategy_revert:    Dict = {}   # anciens paramètres avant auto-application (pour Annuler)

# Proposition horaire auto en attente de confirmation admin
hourly_pending_auto: Optional[Dict] = None   # {best_auto, msg_id, heure, timestamp}

# Dernier résultat de simulation silencieuse (cmd_strategie → /raison2)
last_strategy_simulation: Dict = {}    # stocke les combos + scores + recommandation

# ============================================================================
# 216 COMPTEURS SILENCIEUX INDÉPENDANTS (C13 + C2 propre à chaque combo)
# 3 miroirs × 6 wx × 6 B × 2 df_sim = 216
# ============================================================================
GLOBAL_COMBOS = [
    {'num': 1, 'name': 'Joker Alpha (P1)',     'mirror': {'♦':'♥','♥':'♦','♣':'♠','♠':'♣'}, 'disp': '♦️↔️❤️ / ♣️↔️♠️'},
    {'num': 2, 'name': 'Kouamé Standard (P2)', 'mirror': {'♦':'♣','♣':'♦','♥':'♠','♠':'♥'}, 'disp': '♦️↔️♣️ / ❤️↔️♠️'},
    {'num': 3, 'name': 'Kouamé Delta (P3)',    'mirror': {'♦':'♠','♠':'♦','♥':'♣','♣':'♥'}, 'disp': '♦️↔️♠️ / ❤️↔️♣️'},
]
GLOBAL_COMBOS_BY_NUM: Dict[int, Dict] = {c['num']: c for c in GLOBAL_COMBOS}
# clé: (combo_num, wx, b, df_sim) → état du tracker
silent_combo_states: Dict = {}

# Compteur2 - Gestion des costumes manquants
compteur2_trackers: Dict[str, 'Compteur2Tracker'] = {}
compteur2_seuil_B = 3                        # B défini par l'admin (référence de base)
compteur2_seuil_B_per_suit: Dict[str, int] = {s: 3 for s in ('♠', '♥', '♦', '♣')}  # B dynamique par costume (démarre au B admin)
compteur2_active = True

# Événements PERDU — pour PDF analyse horaire
perdu_events: List[Dict] = []
perdu_pdf_msg_id: Optional[int] = None

# Bilan automatique vers le canal de prédiction
bilan_interval_hours: int = 4   # Actif par défaut — toutes les 4h pile (00h, 04h, 08h, 12h, 16h, 20h)
bilan_task: Optional[asyncio.Task] = None
bilan_1440_sent: bool = False  # Évite le double envoi au jeu #1440

# Concours par costume — mémoire du cycle précédent
concours_last_winner: Optional[str] = None   # suit du vainqueur du dernier cycle
concours_last_pct:    float          = 0.0   # taux de réussite du dernier vainqueur

# Heures favorables automatique vers le canal
heures_favorables_active: bool = True  # Annonce toutes les 3h pile
heures_fav_countdown_msg_id: Optional[int] = None       # ID du message compte à rebours en cours
heures_fav_countdown_task: Optional[asyncio.Task] = None  # Task de mise à jour du countdown
countdown_panel_counter: int = 0                          # Numéro incrémental du panneau envoyé
c4_favorable_event_count: int = 0                         # Compteur C4 → fenêtre favorable (2 = déclenchement)

comparaison_nb_jours: int = 3          # Nombre de jours à comparer (modifiable par admin)

# Compteur1 - Gestion des costumes présents consécutifs
compteur1_trackers: Dict[str, 'Compteur1Tracker'] = {}
compteur1_history: List[Dict] = []
MIN_CONSECUTIVE_FOR_STATS = 3

# Gestion des écarts entre prédictions
MIN_GAP_BETWEEN_PREDICTIONS = 4
last_prediction_number_sent = 0

# Historiques
finalized_messages_history: List[Dict] = []
MAX_HISTORY_SIZE = 50
prediction_history: List[Dict] = []

# File d'attente de prédictions
prediction_queue: List[Dict] = []
PREDICTION_SEND_AHEAD = 2   # gardé pour compatibilité /queue affichage
PREDICTION_DF = PREDICTION_DF_DEFAULT  # df: quand jeu N finit → prédit N+df

# Offsets de prédiction C2 (modifiables par admin)
B_LOSS_INCREMENT: int = B_INCREMENT_DEFAULT  # incrément du B après un PERDU

# Tâches d'animation en cours (original_game → asyncio.Task)
animation_tasks: Dict[int, asyncio.Task] = {}

# Canaux secondaires (initialisés depuis config.py — modifiables via /canaux)
DISTRIBUTION_CHANNEL_ID = _DIST_CH_INIT
COMPTEUR2_CHANNEL_ID    = _C2_CH_INIT
# Canal 3 & 4 — canaux additionnels recevant prédictions + résultats (None = désactivé)
PREDICTION_CHANNEL_ID3  = _C3_CH_INIT
PREDICTION_CHANNEL_ID4  = _C4_CH_INIT

# Compteur 11 — Perdu hier → prédit demain
compteur11_perdu_hier:   List[Dict] = []   # [{game_number, suit, date}] prédictions perdues HIER
compteur11_perdu_today:  List[Dict] = []   # [{game_number, suit, date}] prédictions perdues AUJOURD'HUI
compteur11_triggered:    set = set()        # Jeux déjà déclenchés ce cycle (évite doublons)
COMPTEUR11_FILE = 'compteur11_data.json'

# ============================================================================
# SYSTÈME COMPTEUR13 — CONSÉCUTIFS + MIROIR
# Compteur13 compte les apparitions CONSÉCUTIVES du même costume.
# Quand le streak atteint le seuil wx :
#   → Calcule le miroir de X selon COMPTEUR13_MIRROR
#   → Consulte C2 : le miroir a-t-il atteint le seuil B (manque bloqué) ?
#       OUI → bloque la prédiction RÉELLE (attente prochain signal C13)
#       NON → prédit le miroir au jeu suivant (df)
# RÈGLE C2 :
#   - Prédictions RÉELLES  : C2[miroir] ≥ B  → prédiction bloquée
#   - 216 trackers SILENCIEUX : même règle — chaque tracker a son propre C2
#   - /raison / /raison2 : affichage des résultats, pas de filtre C2
# Paires miroir par défaut (P1) : ♦↔♥  |  ♣↔♠
# ============================================================================
COMPTEUR13_THRESHOLD: int = 5              # Seuil wx (modifiable par admin)
COMPTEUR13_SKIP:      int = 0              # 0=normal · 1=sauter 1 jeu avant de prédire (N+df+1)
compteur13_active: bool   = True
compteur13_trackers: Dict[str, int] = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
compteur13_start:    Dict[str, int] = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
COMPTEUR13_MIRROR: Dict[str, str]   = {
    '♦': '♥', '♥': '♦',
    '♣': '♠', '♠': '♣',
}

# ============================================================================
# SYSTÈME DE RESTRICTION HORAIRE
# ============================================================================

# Liste de fenêtres (start_hour, end_hour) pendant lesquelles les prédictions sont AUTORISÉES
# Si la liste est vide: pas de restriction
PREDICTION_HOURS: List[Tuple[int, int]] = []

def is_prediction_time_allowed() -> bool:
    """Retourne True si les prédictions sont autorisées à l'heure actuelle."""
    if not PREDICTION_HOURS:
        return True
    now = datetime.now()
    current_min = now.hour * 60 + now.minute
    for (start_h, end_h) in PREDICTION_HOURS:
        start_min = start_h * 60
        end_min = end_h * 60
        if start_min == end_min:
            return True  # Fenêtre nulle = toujours autorisé
        if start_min < end_min:
            if start_min <= current_min < end_min:
                return True
        else:
            # Fenêtre qui passe minuit (ex: 23-0 ou 18-17)
            if current_min >= start_min or current_min < end_min:
                return True
    return False

def format_hours_config() -> str:
    if not PREDICTION_HOURS:
        return "✅ Aucune restriction (prédictions 24h/24)"
    lines = []
    for i, (s, e) in enumerate(PREDICTION_HOURS, 1):
        lines.append(f"  {i}. {s:02d}h00 → {e:02d}h00")
    return "\n".join(lines)

# ============================================================================
# SYSTÈME COMPTEUR4 - ÉCARTS DE 10+
# ============================================================================

COMPTEUR4_THRESHOLD = 10  # Seuil d'absences consécutives
COMPTEUR4_DATA_FILE  = 'compteur4_data.json'  # Persistant entre resets (comme C7)
compteur4_trackers: Dict[str, int] = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
compteur4_events: List[Dict] = []  # Événements terminés persistants
compteur4_pdf_msg_id: Optional[int] = None  # ID du message PDF envoyé à l'admin

# État courant de la série d'absences (pour suivre debut_game, comme C7)
compteur4_current: Dict[str, dict] = {
    suit: {'count': 0, 'start_game': None, 'start_time': None, 'alerted': False}
    for suit in ('♠', '♥', '♦', '♣')
}

# ============================================================================
# SYSTÈME COMPTEUR5 - PRÉSENCES CONSÉCUTIVES DE 10+
# ============================================================================
COMPTEUR5_THRESHOLD = 10  # Seuil de présences consécutives
compteur5_trackers: Dict[str, int] = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
compteur5_events: List[Dict] = []  # Événements enregistrés
compteur5_pdf_msg_id: Optional[int] = None  # ID du message PDF envoyé à l'admin

# ============================================================================
# SYSTÈME COMPTEUR7 — SÉRIES CONSÉCUTIVES (MIN 5) — PERSISTANT ENTRE RESETS
# ============================================================================
COMPTEUR7_THRESHOLD = 5                          # Seuil minimum de présences consécutives
COMPTEUR7_DATA_FILE  = 'compteur7_data.json'      # Fichier persistant (survit aux resets)
HOURLY_DATA_FILE     = 'hourly_suit_data.json'   # Données horaires pour /comparaison
PENDING_PRED_FILE    = 'pending_predictions.json' # Prédictions en cours (survit aux redémarrages)

# État courant : pour chaque costume, série en cours
compteur7_current: Dict[str, dict] = {
    suit: {'count': 0, 'start_game': None, 'start_time': None}
    for suit in ('♠', '♥', '♦', '♣')
}
compteur7_completed: List[Dict] = []             # Séries terminées (≥ seuil), persistantes
compteur7_pdf_msg_id: Optional[int] = None       # ID du dernier PDF envoyé à l'admin

# ============================================================================
# SYSTÈME COMPTEUR8 — ABSENCES CONSÉCUTIVES — MIROIR DU COMPTEUR7
# Compteur7 : compte les PRÉSENCES consécutives (seuil ≥5)
# Compteur8 : compte les ABSENCES  consécutives (alerte ≥5, série ≥10)
# ============================================================================
compteur8_current: Dict[str, dict] = {
    suit: {'count': 0, 'start_game': None, 'start_time': None}
    for suit in ('♠', '♥', '♦', '♣')
}
compteur8_completed: List[Dict] = []   # Séries ≥ COMPTEUR8_THRESHOLD terminées (persistantes)
compteur8_pdf_msg_id: Optional[int] = None

# ── C8 PRÉDICTION — quand l'absence atteint le seuil, C8 prédit le manque ──
COMPTEUR8_PRED_SEUIL: int = 8   # Seuil d'absences consécutives → prédiction du manque
                                 # Indépendant de COMPTEUR8_THRESHOLD (qui gère les séries)

# ── FILTRE PRÉSENCE CONSÉCUTIVE — éviter de prédire un costume trop présent ──
PRES_BLOCK_SEUIL: int = 8       # Si un costume est présent ≥N fois de suite → bloqué

# ============================================================================
# SYSTÈME COMPTEUR14 — FRÉQUENCE ABSOLUE DES COSTUMES (cycle de 1440 jeux)
# Compte combien de fois chaque costume est apparu dans la main du joueur.
# Cycle : 1 à 1440 jeux. À la fin du cycle → rapport envoyé à l'admin → reset.
# ============================================================================
COMPTEUR14_CYCLE_SIZE: int = 1440          # Nombre de jeux par cycle
compteur14_counts: Dict[str, int] = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
compteur14_cycle_games: int       = 0      # Jeux joués dans le cycle courant
compteur14_cycle_start: int       = 0      # Numéro du 1er jeu du cycle courant

# Données horaires cumulées pour /comparaison (heure→costume→nb)
hourly_suit_data:  Dict[int, Dict[str, int]] = {h: {'♠': 0, '♥': 0, '♦': 0, '♣': 0} for h in range(24)}
hourly_game_count: Dict[int, int]            = {h: 0 for h in range(24)}

# ============================================================================

pending_input: dict = {}                     # {user_id: {'action': str, 'chat_id': int}} — saisie valeur via bouton

def generate_compteur4_pdf(events_list: List[Dict]) -> bytes:
    """Génère un PDF avec le tableau des écarts Compteur4 (format série comme C7)."""
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors = {
        '♠': (30, 30, 30),
        '♥': (180, 0, 0),
        '♦': (0, 80, 180),
        '♣': (0, 120, 0),
    }

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(120, 30, 0)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Absences Consecutives Compteur 4', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Seuil: {COMPTEUR4_THRESHOLD} absences consecutives | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | '
        f'Total: {len(events_list)} serie(s) | PERSISTANT', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    col_widths = [32, 22, 22, 32, 32, 26]
    headers    = ['Date', 'Heure', 'Costume', 'Debut', 'Fin', 'Nb fois']

    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(120, 30, 0)
    pdf.set_text_color(255, 255, 255)
    for header, width in zip(headers, col_widths):
        pdf.cell(width, 9, header, border=1, fill=True, align='C')
    pdf.ln()

    pdf.set_font('Helvetica', '', 11)
    alt = False
    for ev in events_list:
        suit      = ev.get('suit', '')
        r, g, b   = suit_colors.get(suit, (0, 0, 0))
        date_str  = ev['end_time'].strftime('%d/%m/%Y')
        time_str  = ev['end_time'].strftime('%Hh%M')
        suit_name = suit_names_map.get(suit, suit)
        start_str = f"#{ev['start_game']}"
        end_str   = f"#{ev['end_game']}"
        count_str = f"{ev['count']}x"

        bg = (255, 240, 235) if alt else (255, 255, 255)
        pdf.set_fill_color(*bg)
        pdf.set_text_color(0, 0, 0)

        pdf.cell(col_widths[0], 9, date_str, border=1, fill=alt, align='C')
        pdf.cell(col_widths[1], 9, time_str, border=1, fill=alt, align='C')

        pdf.set_text_color(r, g, b)
        pdf.set_font('Helvetica', 'B', 11)
        pdf.cell(col_widths[2], 9, suit_name, border=1, fill=alt, align='C')
        pdf.set_font('Helvetica', '', 11)
        pdf.set_text_color(0, 0, 0)

        pdf.cell(col_widths[3], 9, start_str, border=1, fill=alt, align='C')
        pdf.cell(col_widths[4], 9, end_str,   border=1, fill=alt, align='C')

        pdf.set_text_color(r, g, b)
        pdf.set_font('Helvetica', 'B', 12)
        pdf.cell(col_widths[5], 9, count_str, border=1, fill=alt, align='C')
        pdf.set_font('Helvetica', '', 11)
        pdf.set_text_color(0, 0, 0)

        pdf.ln()
        alt = not alt

    if not events_list:
        pdf.set_text_color(150, 150, 150)
        pdf.cell(0, 8, 'Aucune serie d absence enregistree', border=1, align='C')
        pdf.ln()

    pdf.ln(8)
    pdf.set_font('Helvetica', 'B', 12)
    pdf.set_fill_color(120, 30, 0)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 10, 'Resume par costume', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
    pdf.ln(3)
    from collections import Counter
    suit_counts = Counter(ev.get('suit', '') for ev in events_list)
    for suit in ['♠', '♥', '♦', '♣']:
        r, g, b = suit_colors.get(suit, (0, 0, 0))
        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_text_color(r, g, b)
        name = suit_names_map.get(suit, suit)
        cnt  = suit_counts.get(suit, 0)
        pdf.cell(0, 8, f'  {name} : {cnt} serie(s) de {COMPTEUR4_THRESHOLD}+ absences', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.ln(5)
    pdf.set_font('Helvetica', 'I', 9)
    pdf.set_text_color(130, 130, 130)
    pdf.cell(0, 6,
        'BACCARAT AI - PERSISTANT - Reset #1440 ne supprime PAS ce fichier - '
        f'{datetime.now().strftime("%d/%m/%Y %H:%M")}', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    return bytes(pdf.output())

async def send_compteur4_threshold_alert(suit: str, game_number: int, start_game: int):
    """Envoie une alerte immédiate à l'admin quand le seuil de 10 absences est atteint (série en cours)."""
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    suit_emoji_map = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
    suit_names_map = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
    try:
        admin_entity = await client.get_entity(ADMIN_ID)
        now   = datetime.now()
        emoji = suit_emoji_map.get(suit, suit)
        name  = suit_names_map.get(suit, suit)
        msg = (
            "🚨 **COMPTEUR 4 — SEUIL ATTEINT**\n\n"
            f"{now.strftime('%d/%m/%Y')} à {now.strftime('%Hh%M')} "
            f"{emoji} **{COMPTEUR4_THRESHOLD} fois absent** — numéro **{start_game}_{game_number}**\n\n"
            f"_{name} absent depuis le jeu #{start_game}. La série continue…_"
        )
        await client.send_message(admin_entity, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur4_threshold_alert: {e}")


async def send_compteur4_series_alert(series: Dict):
    """Envoie la notification finale quand une série d'absences Compteur4 se termine."""
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    suit_emoji_map = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
    suit_names_map = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
    try:
        admin_entity = await client.get_entity(ADMIN_ID)
        suit     = series['suit']
        emoji    = suit_emoji_map.get(suit, suit)
        name     = suit_names_map.get(suit, suit)
        end_time = series['end_time']
        msg = (
            "🔴 **COMPTEUR 4 — SÉRIE TERMINÉE**\n\n"
            f"{end_time.strftime('%d/%m/%Y')} à {end_time.strftime('%Hh%M')} "
            f"{emoji} **{series['count']} fois** du numéro "
            f"**{series['start_game']}_{series['end_game']}**\n\n"
            f"_{name} absent {series['count']} fois consécutives._\n\n"
            "📄 PDF mis à jour ci-dessous."
        )
        await client.send_message(admin_entity, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur4_series_alert: {e}")


async def send_compteur4_pdf():
    """Génère et envoie (ou remplace) le PDF Compteur4 à l'admin."""
    global compteur4_pdf_msg_id

    if not ADMIN_ID or ADMIN_ID == 0:
        logger.warning("⚠️ ADMIN_ID non configuré, PDF non envoyé")
        return

    try:
        pdf_bytes = generate_compteur4_pdf(compteur4_events)
        pdf_buffer = io.BytesIO(pdf_bytes)
        pdf_buffer.name = "compteur4_ecarts.pdf"

        admin_entity = await client.get_entity(ADMIN_ID)

        # Supprimer l'ancien message PDF si il existe
        if compteur4_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [compteur4_pdf_msg_id])
                logger.info(f"🗑️ Ancien PDF supprimé (msg {compteur4_pdf_msg_id})")
            except Exception as e:
                logger.warning(f"⚠️ Impossible de supprimer ancien PDF: {e}")
            compteur4_pdf_msg_id = None

        caption = (
            "🔴 **COMPTEUR4 — PDF mis à jour**\n\n"
            f"Total séries d'absences enregistrées : **{len(compteur4_events)}**\n"
            f"Seuil : **≥ {COMPTEUR4_THRESHOLD}** absences consécutives\n"
            "⚠️ Ce PDF persiste entre tous les resets\n"
            f"Mis à jour : {datetime.now().strftime('%d/%m/%Y %Hh%M')}"
        )

        sent = await client.send_file(
            admin_entity,
            pdf_buffer,
            caption=caption,
            parse_mode='markdown',
            attributes=[],
            file_name="compteur4_absences.pdf"
        )
        compteur4_pdf_msg_id = sent.id
        logger.info(f"✅ PDF Compteur4 envoyé à l'admin (msg {compteur4_pdf_msg_id})")

    except Exception as e:
        logger.error(f"❌ Erreur envoi PDF: {e}")
        import traceback
        logger.error(traceback.format_exc())

# ============================================================================
# COMPTEUR5 — PRÉSENCES CONSÉCUTIVES
# ============================================================================

def generate_compteur5_pdf(events_list: List[Dict]) -> bytes:
    """Génère un PDF avec le tableau des présences consécutives Compteur5."""
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors = {
        '♠': (30, 30, 30),
        '♥': (180, 0, 0),
        '♦': (0, 80, 180),
        '♣': (0, 120, 0),
    }

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(0, 100, 50)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Presences Consecutives Compteur 5', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Seuil: {COMPTEUR5_THRESHOLD} presences consecutives | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | '
        f'Total: {len(events_list)} evenement(s)', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    col_widths = [38, 22, 32, 42, 56]
    headers    = ['Date', 'Heure', 'Numero jeu', 'Costume present', 'Autres cartes']

    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(0, 100, 50)
    pdf.set_text_color(255, 255, 255)
    for header, width in zip(headers, col_widths):
        pdf.cell(width, 9, header, border=1, fill=True, align='C')
    pdf.ln()

    pdf.set_font('Helvetica', '', 11)
    alt = False
    for ev in events_list:
        present_suit = ev.get('suit', '')
        r, g, b = suit_colors.get(present_suit, (0, 0, 0))

        date_str  = ev['datetime'].strftime('%d/%m/%Y')
        time_str  = ev['datetime'].strftime('%Hh%M')
        game_str  = str(ev['game_number'])
        suit_name = suit_names_map.get(present_suit, present_suit)
        others    = ' | '.join(
            suit_names_map.get(s, s)
            for s in ev.get('player_suits', [])
            if s != present_suit
        ) or '-'

        pdf.set_fill_color(*(240, 255, 240) if alt else (255, 255, 255))
        pdf.set_text_color(0, 0, 0)
        pdf.cell(col_widths[0], 9, date_str, border=1, fill=alt, align='C')
        pdf.cell(col_widths[1], 9, time_str, border=1, fill=alt, align='C')
        pdf.cell(col_widths[2], 9, game_str, border=1, fill=alt, align='C')

        pdf.set_text_color(r, g, b)
        pdf.set_font('Helvetica', 'B', 11)
        pdf.cell(col_widths[3], 9, suit_name, border=1, fill=alt, align='C')
        pdf.set_font('Helvetica', '', 11)
        pdf.set_text_color(80, 80, 80)
        pdf.cell(col_widths[4], 9, others, border=1, fill=alt, align='C')
        pdf.ln()
        alt = not alt

    if not events_list:
        pdf.set_text_color(150, 150, 150)
        pdf.cell(0, 8, 'Aucune presence consecutive enregistree', border=1, align='C')
        pdf.ln()

    # Résumé par costume
    pdf.ln(8)
    pdf.set_font('Helvetica', 'B', 12)
    pdf.set_fill_color(0, 100, 50)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 10, 'Resume par costume', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
    pdf.ln(3)
    from collections import Counter as _Counter
    suit_counts = _Counter(ev.get('suit', '') for ev in events_list)
    for suit in ['♠', '♥', '♦', '♣']:
        r, g, b = suit_colors.get(suit, (0, 0, 0))
        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_text_color(r, g, b)
        name = suit_names_map.get(suit, suit)
        cnt  = suit_counts.get(suit, 0)
        pdf.cell(0, 8, f'  {name} : {cnt} fois le seuil de {COMPTEUR5_THRESHOLD} atteint', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.ln(5)
    pdf.set_font('Helvetica', 'I', 9)
    pdf.set_text_color(130, 130, 130)
    pdf.cell(0, 6, f'BACCARAT AI - CONFIDENTIEL - {datetime.now().strftime("%d/%m/%Y %H:%M")}', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    return bytes(pdf.output())


async def send_compteur5_alert(triggered_suits: List[str], game_number: int):
    """Envoie une notification texte immédiate à l'admin quand le seuil C5 est atteint."""
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    suit_emoji_map = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
    suit_names_map = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
    try:
        admin_entity = await client.get_entity(ADMIN_ID)
        now = datetime.now()
        lines = ["✅ **COMPTEUR 5 — PRÉSENT 10 FOIS**", ""]
        for suit in triggered_suits:
            emoji = suit_emoji_map.get(suit, suit)
            lines.append(
                f"Le {now.strftime('%d/%m/%Y')} A {now.strftime('%Hh%M')} "
                f"{emoji} Numéro {game_number}"
            )
        lines += [
            "",
            f"_{suit_names_map.get(triggered_suits[0], triggered_suits[0])} "
            f"présent **{COMPTEUR5_THRESHOLD} fois consécutives**._",
            "",
            "📄 PDF mis à jour ci-dessous."
        ]
        await client.send_message(admin_entity, "\n".join(lines), parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur5_alert: {e}")


async def send_compteur5_pdf():
    """Génère et envoie (ou remplace) le PDF Compteur5 à l'admin."""
    global compteur5_pdf_msg_id
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        pdf_bytes = generate_compteur5_pdf(compteur5_events)
        pdf_buffer = io.BytesIO(pdf_bytes)
        pdf_buffer.name = "compteur5_presences.pdf"
        admin_entity = await client.get_entity(ADMIN_ID)

        if compteur5_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [compteur5_pdf_msg_id])
            except Exception as e:
                logger.debug(f"Suppression ancien PDF C5 ignorée: {e}")
            compteur5_pdf_msg_id = None

        caption = (
            "✅ **COMPTEUR5 — PDF mis à jour**\n\n"
            f"Total présences consécutives enregistrées : **{len(compteur5_events)}**\n"
            f"Seuil actuel : **{COMPTEUR5_THRESHOLD}** présences consécutives\n"
            f"Mis à jour : {datetime.now().strftime('%d/%m/%Y %Hh%M')}"
        )
        sent = await client.send_file(
            admin_entity, pdf_buffer,
            caption=caption, parse_mode='markdown',
            attributes=[], file_name="compteur5_presences.pdf"
        )
        compteur5_pdf_msg_id = sent.id
        logger.info("✅ PDF Compteur5 envoyé à l'admin")
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur5_pdf: {e}")
        import traceback; logger.error(traceback.format_exc())


# ============================================================================
# PDF PERDU + ANALYSE HORAIRE + ANALYSE CROISÉE PAR DATE
# ============================================================================

def _group_hours_into_ranges(sorted_hours: List[int]) -> List[Tuple[int, int]]:
    """Regroupe une liste d'heures triées en plages consécutives."""
    if not sorted_hours:
        return []
    ranges = []
    start = end = sorted_hours[0]
    for h in sorted_hours[1:]:
        if h == end + 1:
            end = h
        else:
            ranges.append((start, end))
            start = end = h
    ranges.append((start, end))
    return ranges


def _analyse_perdu_dates(events: List[Dict]) -> Dict:
    """
    Analyse croisée des pertes par date ET par heure.
    Retourne un dict avec :
      - by_date         : {date_str: [hours]}
      - by_day_of_week  : {weekday_name: count}
      - hour_freq       : {hour: nb_dates_differentes_où_cette_heure_est_mauvaise}
      - danger_hours    : heures mauvaises sur >= 2 dates différentes
      - safe_hours      : plages horaires recommandées (sans danger)
      - recommendation  : texte de recommandation final
      - dates_analysees : liste des dates impliquées
    """
    from collections import defaultdict, Counter

    if not events:
        return {
            'by_date': {}, 'by_day_of_week': {}, 'hour_freq': {},
            'danger_hours': [], 'safe_hours': [], 'recommendation': '',
            'dates_analysees': []
        }

    # Regrouper par date
    by_date: Dict[str, List[int]] = defaultdict(list)
    by_day_of_week: Counter = Counter()
    for ev in events:
        d = ev['time'].strftime('%d/%m/%Y')
        h = ev['time'].hour
        by_date[d].append(h)
        by_day_of_week[DAYS_FR[ev['time'].weekday()]] += 1

    dates_analysees = sorted(by_date.keys())

    # Pour chaque heure, compter sur combien de dates distinctes elle apparaît
    hour_date_set: Dict[int, set] = defaultdict(set)
    for d, hours in by_date.items():
        for h in hours:
            hour_date_set[h].add(d)

    hour_freq = {h: len(dates) for h, dates in hour_date_set.items()}
    nb_dates = len(by_date)

    # Heures dangereuses : présentes sur >= 2 dates OU >= 50% des dates
    danger_hours = sorted([
        h for h, cnt in hour_freq.items()
        if cnt >= 2 or (nb_dates >= 2 and cnt / nb_dates >= 0.5)
    ])

    # Heures sûres = toutes les heures de 0 à 23 sauf les dangereuses
    danger_set = set(danger_hours)
    safe_all = [h for h in range(24) if h not in danger_set]
    safe_ranges = _group_hours_into_ranges(safe_all)

    # Construire la recommandation texte
    if danger_hours:
        danger_ranges = _group_hours_into_ranges(danger_hours)
        danger_labels = []
        for s, e in danger_ranges:
            nb = max(hour_freq.get(h, 0) for h in range(s, e + 1))
            label = f"{s:02d}h-{e+1:02d}h ({nb} date(s))" if s != e else f"{s:02d}h-{s+1:02d}h ({nb} date(s))"
            danger_labels.append(label)

        if safe_ranges:
            safe_labels = [
                f"{s:02d}h00 - {e+1:02d}h00" if s != e else f"{s:02d}h00 - {s+1:02d}h00"
                for s, e in safe_ranges
            ]
            rec = (
                f"D'apres mes analyses sur {nb_dates} date(s) ({', '.join(dates_analysees)}), "
                f"les plages a risque sont : {', '.join(danger_labels)}. "
                "Je vous conseille de programmer les predictions uniquement sur : "
                f"{' | '.join(safe_labels)}."
            )
        else:
            rec = (
                f"D'apres mes analyses sur {nb_dates} date(s) ({', '.join(dates_analysees)}), "
                "des pertes ont ete detectees a presque toutes les heures. "
                "Aucune plage vraiment sure n'a pu etre identifiee. "
                "Reduisez la frequence des predictions."
            )
    else:
        rec = (
            f"Analyse sur {nb_dates} date(s) : aucun pattern horaire repetitif detecte. "
            "Les pertes sont bien distribuees sur la journee — pas de plage a eviter en particulier."
        )

    return {
        'by_date': dict(by_date),
        'by_day_of_week': dict(by_day_of_week),
        'hour_freq': hour_freq,
        'danger_hours': danger_hours,
        'safe_ranges': safe_ranges,
        'recommendation': rec,
        'dates_analysees': dates_analysees,
    }


def _build_admin_notification(events: List[Dict], date_analysis: Dict) -> str:
    """Génère le message texte de notification admin avec recommandation horaire."""
    total = len(events)
    if total == 0:
        return "📊 Aucune perte enregistrée pour le moment."

    nb_dates = len(date_analysis['dates_analysees'])
    danger_hours = date_analysis['danger_hours']
    safe_ranges = date_analysis.get('safe_ranges', [])

    lines = [
        "⚠️ **ANALYSE DES PERTES — RECOMMANDATION HORAIRE**",
        "",
        f"📅 Dates analysées ({nb_dates}) : {', '.join(date_analysis['dates_analysees'])}",
        f"📉 Total pertes : **{total}**",
        "",
    ]

    if danger_hours:
        danger_ranges = _group_hours_into_ranges(danger_hours)
        lines.append("🔴 **Plages à risque élevé (répétitives sur plusieurs dates) :**")
        for s, e in danger_ranges:
            nb = max(date_analysis['hour_freq'].get(h, 0) for h in range(s, e + 1))
            label = f"{s:02d}h00–{e+1:02d}h00" if s != e else f"{s:02d}h00–{s+1:02d}h00"
            lines.append(f"  • {label} → pertes détectées sur {nb} date(s)")
        lines.append("")

    if safe_ranges:
        lines.append("✅ **Plages recommandées (faibles risques) :**")
        for s, e in safe_ranges:
            label = f"{s:02d}h00 → {e+1:02d}h00" if s != e else f"{s:02d}h00 → {s+1:02d}h00"
            lines.append(f"  • {label}")
        lines.append("")
        safe_labels = [
            f"{s:02d}h-{e+1:02d}h" if s != e else f"{s:02d}h-{s+1:02d}h"
            for s, e in safe_ranges
        ]
        lines.append(
            "💡 **Conseil** : La plupart des heures analysées ne sont pas favorables. "
            "Je vous conseille de programmer vos prédictions en définissant "
            f"**{' | '.join(safe_labels)}** d'après mes analyses des dates : "
            f"{', '.join(date_analysis['dates_analysees'])}."
        )
    else:
        lines.append("⚠️ Aucune plage sûre identifiable — réduisez la fréquence des prédictions.")

    lines.append("")
    lines.append("_📄 Voir le PDF ci-dessous pour l'analyse complète par date._")
    return "\n".join(lines)


def generate_perdu_pdf(events: List[Dict]) -> bytes:
    """Génère le PDF des pertes avec analyse horaire, analyse croisée par date et recommandation."""
    date_analysis = _analyse_perdu_dates(events)
    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    suit_names = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}

    def section_header(title: str, r: int, g: int, b: int):
        pdf.ln(8)
        pdf.set_font('Helvetica', 'B', 12)
        pdf.set_fill_color(r, g, b)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(0, 10, title, new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
        pdf.ln(3)
        pdf.set_text_color(0, 0, 0)

    # ── Titre principal ──────────────────────────────────────────────────────
    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(139, 0, 0)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Analyse Complete des Pertes', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)
    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | '
        f'Total: {len(events)} perte(s) | '
        f'Dates analysees: {len(date_analysis["dates_analysees"])}', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    # ── Tableau historique des pertes ────────────────────────────────────────
    section_header('Historique des Pertes', 50, 50, 50)
    col_w = [32, 22, 24, 26, 14, 14, 58]
    hdrs = ['Date', 'Heure', 'Jeu #', 'Costume', 'Ratt.', 'B avant', 'B apres']
    pdf.set_font('Helvetica', 'B', 10)
    pdf.set_fill_color(50, 50, 50)
    pdf.set_text_color(255, 255, 255)
    for h, w in zip(hdrs, col_w):
        pdf.cell(w, 9, h, border=1, fill=True, align='C')
    pdf.ln()
    pdf.set_font('Helvetica', '', 10)
    alt = False
    for ev in events:
        pdf.set_fill_color(*(245, 230, 230) if alt else (255, 255, 255))
        pdf.set_text_color(0, 0, 0)
        row = [
            ev['time'].strftime('%d/%m/%Y'),
            ev['time'].strftime('%H:%M'),
            str(ev['game']),
            suit_names.get(ev['suit'], ev['suit']),
            f"R{ev['rattrapage']}",
            str(ev['b_before']),
            str(ev['b_after'])
        ]
        for d, w in zip(row, col_w):
            pdf.cell(w, 8, d, border=1, fill=alt, align='C')
        pdf.ln()
        alt = not alt
    if not events:
        pdf.set_text_color(150, 150, 150)
        pdf.cell(0, 8, 'Aucune perte enregistree', border=1, align='C')
        pdf.ln()

    # ── Analyse par date ─────────────────────────────────────────────────────
    section_header('Comparaison des Pertes par Date', 20, 80, 160)
    if date_analysis['by_date']:
        col_date = 50
        col_hours = 100
        col_nb = 40
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_fill_color(20, 80, 160)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(col_date, 9, 'Date', border=1, fill=True, align='C')
        pdf.cell(col_hours, 9, 'Heures de perte', border=1, fill=True, align='C')
        pdf.cell(col_nb, 9, 'Nb pertes', border=1, fill=True, align='C')
        pdf.ln()
        pdf.set_font('Helvetica', '', 10)
        alt = False
        for date_str in date_analysis['dates_analysees']:
            hours = sorted(date_analysis['by_date'][date_str])
            hours_label = ', '.join(f'{h:02d}h' for h in hours)
            pdf.set_fill_color(*(220, 235, 255) if alt else (255, 255, 255))
            pdf.set_text_color(0, 0, 0)
            pdf.cell(col_date, 8, date_str, border=1, fill=alt, align='C')
            pdf.cell(col_hours, 8, hours_label, border=1, fill=alt, align='C')
            pdf.cell(col_nb, 8, str(len(hours)), border=1, fill=alt, align='C')
            pdf.ln()
            alt = not alt
    else:
        pdf.set_text_color(150, 150, 150)
        pdf.set_font('Helvetica', '', 10)
        pdf.cell(0, 8, 'Pas encore assez de donnees par date.', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── Analyse par heure (fréquence cross-dates) ────────────────────────────
    section_header('Frequence des Heures de Perte (toutes dates confondues)', 100, 50, 0)
    if date_analysis['hour_freq']:
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_fill_color(100, 50, 0)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(40, 9, 'Heure', border=1, fill=True, align='C')
        pdf.cell(60, 9, 'Nb dates concernees', border=1, fill=True, align='C')
        pdf.cell(90, 9, 'Niveau de risque', border=1, fill=True, align='C')
        pdf.ln()
        pdf.set_font('Helvetica', '', 10)
        nb_dates_total = len(date_analysis['dates_analysees'])
        for hour in sorted(date_analysis['hour_freq'].keys()):
            cnt = date_analysis['hour_freq'][hour]
            pct = cnt / nb_dates_total * 100 if nb_dates_total else 0
            if hour in date_analysis['danger_hours']:
                risk = 'RISQUE ELEVE'
                pdf.set_text_color(180, 0, 0)
                pdf.set_fill_color(255, 220, 220)
                do_fill = True
            else:
                risk = 'Acceptable'
                pdf.set_text_color(0, 0, 0)
                pdf.set_fill_color(255, 255, 255)
                do_fill = False
            pdf.cell(40, 8, f'{hour:02d}h00', border=1, fill=do_fill, align='C')
            pdf.cell(60, 8, f'{cnt}/{nb_dates_total} ({pct:.0f}%)', border=1, fill=do_fill, align='C')
            pdf.cell(90, 8, risk, border=1, fill=do_fill, align='C')
            pdf.ln()
            pdf.set_text_color(0, 0, 0)
    else:
        pdf.set_text_color(150, 150, 150)
        pdf.set_font('Helvetica', '', 10)
        pdf.cell(0, 8, 'Aucune donnee disponible.', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── Analyse par jour de la semaine ───────────────────────────────────────
    section_header('Pertes par Jour de la Semaine', 80, 0, 120)
    if date_analysis['by_day_of_week']:
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_fill_color(80, 0, 120)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(80, 9, 'Jour', border=1, fill=True, align='C')
        pdf.cell(60, 9, 'Nb pertes', border=1, fill=True, align='C')
        pdf.ln()
        pdf.set_font('Helvetica', '', 10)
        pdf.set_text_color(0, 0, 0)
        for day, cnt in sorted(date_analysis['by_day_of_week'].items(),
                               key=lambda x: -x[1]):
            pdf.cell(80, 8, day, border=1, align='C')
            pdf.cell(60, 8, str(cnt), border=1, align='C')
            pdf.ln()
    else:
        pdf.set_text_color(150, 150, 150)
        pdf.set_font('Helvetica', '', 10)
        pdf.cell(0, 8, 'Aucune donnee disponible.', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── Seuils B par costume ─────────────────────────────────────────────────
    section_header('Seuils B actuels par Costume', 70, 70, 70)
    pdf.set_font('Helvetica', '', 11)
    pdf.set_text_color(0, 0, 0)
    for suit in ['♠', '♥', '♦', '♣']:
        b_val = compteur2_seuil_B_per_suit.get(suit, compteur2_seuil_B)
        pdf.cell(0, 8, f'  {suit_names.get(suit, suit)}: B = {b_val}', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── Recommandation finale ────────────────────────────────────────────────
    section_header('RECOMMANDATION - Plages Horaires Conseilees', 0, 100, 0)
    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(0, 0, 0)
    if date_analysis['danger_hours']:
        danger_ranges = _group_hours_into_ranges(date_analysis['danger_hours'])
        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_text_color(180, 0, 0)
        pdf.cell(0, 8, '  Plages a EVITER :', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.set_font('Helvetica', '', 10)
        for s, e in danger_ranges:
            nb = max(date_analysis['hour_freq'].get(h, 0) for h in range(s, e + 1))
            label = f'{s:02d}h00 - {e+1:02d}h00' if s != e else f'{s:02d}h00 - {s+1:02d}h00'
            pdf.cell(0, 8, f'    X  {label}  (pertes sur {nb} date(s))', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.ln(3)

    if date_analysis.get('safe_ranges'):
        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_text_color(0, 120, 0)
        pdf.cell(0, 8, '  Plages RECOMMANDEES :', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.set_font('Helvetica', '', 10)
        for s, e in date_analysis['safe_ranges']:
            label = f'{s:02d}h00 - {e+1:02d}h00' if s != e else f'{s:02d}h00 - {s+1:02d}h00'
            pdf.cell(0, 8, f'    OK  {label}', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.ln(4)

    pdf.set_font('Helvetica', 'I', 10)
    pdf.set_text_color(50, 50, 50)
    rec_clean = date_analysis['recommendation'].replace('\u2019', "'").replace('—', '-').replace('–', '-').replace('…', '...')
    pdf.multi_cell(0, 7, f'  Synthese : {rec_clean}')

    # ── Pied de page ─────────────────────────────────────────────────────────
    pdf.ln(5)
    pdf.set_font('Helvetica', 'I', 9)
    pdf.set_text_color(150, 150, 150)
    pdf.cell(0, 6, "Ce PDF est envoye uniquement a l'administrateur - CONFIDENTIEL", new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    return bytes(pdf.output())


async def send_perdu_pdf():
    """Envoie la notification texte + le PDF de comparaison à l'admin."""
    global perdu_pdf_msg_id
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        date_analysis = _analyse_perdu_dates(perdu_events)
        notif_text = _build_admin_notification(perdu_events, date_analysis)

        pdf_bytes = generate_perdu_pdf(perdu_events)
        buf = io.BytesIO(pdf_bytes)
        buf.name = "perdu_analyse_complete.pdf"

        admin_entity = await client.get_entity(ADMIN_ID)

        # Supprimer l'ancien PDF s'il existe
        if perdu_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [perdu_pdf_msg_id])
            except Exception as e:
                logger.debug(f"Suppression ancien PDF Perdus ignorée: {e}")
            perdu_pdf_msg_id = None

        # 1. Envoyer la notification texte en premier
        await client.send_message(admin_entity, notif_text, parse_mode='markdown')

        # 2. Envoyer le PDF de comparaison
        caption = (
            "📊 **ANALYSE COMPLÈTE DES PERTES**\n\n"
            f"Total pertes: **{len(perdu_events)}**\n"
            f"Dates analysées: **{len(date_analysis['dates_analysees'])}**\n"
            f"Mis à jour: {datetime.now().strftime('%d/%m/%Y %H:%M')}\n\n"
            "_Comparaison croisée heures × dates incluse._"
        )
        sent = await client.send_file(
            admin_entity, buf,
            caption=caption,
            parse_mode='markdown',
            file_name="perdu_analyse_complete.pdf"
        )
        perdu_pdf_msg_id = sent.id
        logger.info("✅ Notification + PDF comparaison envoyés à l'admin")
    except Exception as e:
        logger.error(f"❌ Erreur send_perdu_pdf: {e}")

# ============================================================================
# BILAN AUTOMATIQUE
# ============================================================================

def _number_to_big(n: int) -> str:
    """Convertit un nombre en gros chiffres unicode."""
    digit_map = {'0':'0️⃣','1':'1️⃣','2':'2️⃣','3':'3️⃣','4':'4️⃣',
                 '5':'5️⃣','6':'6️⃣','7':'7️⃣','8':'8️⃣','9':'9️⃣'}
    return ''.join(digit_map.get(c, c) for c in str(n))


def get_bilan_text() -> str:
    """Génère le texte du bilan des prédictions avec taux de réussite."""
    counts = {'r0': 0, 'r1': 0, 'r2': 0, 'r3': 0, 'perdu': 0}
    for pred in prediction_history:
        st = pred.get('status', '')
        rl = pred.get('rattrapage_level', 0)
        if 'gagne' in st:
            key = f'r{rl}' if rl <= 3 else 'r3'
            counts[key] += 1
        elif st == 'perdu':
            counts['perdu'] += 1

    total = sum(counts.values())
    if total == 0:
        return "📊 **BILAN** — Aucune prédiction finalisée pour le moment."

    total_gagnes = counts['r0'] + counts['r1'] + counts['r2'] + counts['r3']
    taux_reussite = total_gagnes / total * 100
    taux_perdu = counts['perdu'] / total * 100

    def pct(n): return f"{n/total*100:.1f}%"

    now = datetime.now().strftime('%d/%m/%Y %H:%M')
    total_big = _number_to_big(total)
    lines = [
        "╔══════════════════════════════╗",
        "║  📊 TOTAL PRÉDICTIONS        ║",
        f"║       {total_big}",
        "╚══════════════════════════════╝",
        "",
        "📈 **BILAN DES PRÉDICTIONS**",
        f"🕒 {now}",
        "━" * 30,
        f"✅0️⃣ GAGNÉ DIRECT : **{counts['r0']}** ({pct(counts['r0'])})",
        f"✅1️⃣ GAGNÉ R1     : **{counts['r1']}** ({pct(counts['r1'])})",
        f"✅2️⃣ GAGNÉ R2     : **{counts['r2']}** ({pct(counts['r2'])})",
        f"✅3️⃣ GAGNÉ R3     : **{counts['r3']}** ({pct(counts['r3'])})",
        "━" * 30,
        f"❌ PERDU          : **{counts['perdu']}** ({pct(counts['perdu'])})",
        "━" * 30,
        f"🏆 Taux de réussite : **{taux_reussite:.1f}%** ({total_gagnes} gagnées)",
        f"💔 Taux de perte   : **{taux_perdu:.1f}%** ({counts['perdu']} perdues)",
    ]
    return "\n".join(lines)

SUIT_NAMES_FR = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
SUIT_EMOJI    = {'♠': '♠️', '♥': '♥️', '♦': '♦️', '♣': '♣️'}
SUIT_ICON     = {'♠': '🗡️', '♥': '💖', '♦': '💎', '♣': '🍀'}

SUIT_WINNER_PHRASES = {
    '♠': (
        "🗡️ Tranchant. Implacable. Souverain.\n"
        "Pique n'a laissé aucun répit à ses rivaux —\n"
        "chaque prédiction tombait comme un verdict définitif.\n"
        "La lame la plus affûtée du cycle règne en maître absolu !"
    ),
    '♥': (
        "💖 Passionné. Généreux. Flamboyant.\n"
        "Cœur a porté le groupe sur ses épaules tout au long du cycle.\n"
        "Chaque prédiction était un cadeau offert à nos membres.\n"
        "Une performance de feu — digne des plus grands champions !"
    ),
    '♦': (
        "💎 Pur. Précis. Étincelant.\n"
        "Carreau a brillé comme seuls les vrais diamants savent le faire.\n"
        "Une précision cristalline, prédiction après prédiction, sans faille.\n"
        "Ce cycle lui appartenait depuis le premier jeu !"
    ),
    '♣': (
        "🍀 Solide. Chanceux. Imparable.\n"
        "Trèfle a transformé la chance en art pur ce cycle.\n"
        "Chaque prédiction portait la marque des très grands.\n"
        "La porte-bonheur du groupe règne enfin — et c'est mérité !"
    ),
}

SUIT_ENCOURAGE = {
    '♠': {
        1: "🗡️ **PIQUE — CHAMPION ABSOLU !** La lame a tout taillé. La couronne est portée fièrement. Garde ce tranchant au prochain cycle ! 👑",
        2: "🗡️ **PIQUE — PODIUM MÉRITÉ !** Tu n'es qu'à une lame du titre. Affûte encore et le premier rang est à toi. 💪",
        3: "🗡️ **PIQUE — CYCLE EN RETRAIT.** La lame n'est pas brisée — elle se retrempait. Reviens plus mordant au prochain tour ! 🔥",
        4: "🗡️ **PIQUE — DERNIÈRE PLACE.** Les grandes lames se retrempent dans l'adversité. Ta revanche arrive ! ⚡",
    },
    '♥': {
        1: "💖 **CŒUR — MAGNIFIQUE !** Tu as tout donné avec passion et générosité. Le sommet t'appartient. Continue à brûler ! 👑",
        2: "💖 **CŒUR — 2ÈME MARCHE !** Déjà un exploit ! La première place t'attend au prochain cycle. Ne lâche rien ! 💪",
        3: "💖 **CŒUR — TU PEUX MIEUX !** Mets-y toute ta flamme et le prochain cycle sera le tien. 🔥",
        4: "💖 **CŒUR — PAS UN GRAND CYCLE.** Mais les champions de feu rebondissent toujours avec éclat ! ⚡",
    },
    '♦': {
        1: "💎 **CARREAU — ÉTINCELANT !** Ce cycle t'appartient entièrement. Continue à briller de mille feux. 👑",
        2: "💎 **CARREAU — TRÈS PROCHE !** À quelques éclats du diamant suprême. Encore un effort et le titre est à toi. 💪",
        3: "💎 **CARREAU — QUELQUES ÉCLATS PERDUS.** Mais un diamant reste diamant. Retrouve ta brillance ! 🔥",
        4: "💎 **CARREAU — EN BAS ?** Les vrais diamants se forment sous pression. Ton heure viendra ! ⚡",
    },
    '♣': {
        1: "🍀 **TRÈFLE — LA CHANCE SOURIT AUX AUDACIEUX !** Tu as tout renversé ce cycle. Champion incontestable ! 👑",
        2: "🍀 **TRÈFLE — EXCELLENTE PERF !** À deux doigts du titre. La chance est encore avec toi — saisis-la ! 💪",
        3: "🍀 **TRÈFLE — BONNE PERF.** Tu visais plus haut, et tu le sais. Le prochain cycle sera le bon ! 🔥",
        4: "🍀 **TRÈFLE — DERNIER CE CYCLE.** Mais le trèfle porte bonheur — ta revanche spectaculaire est en route ! ⚡",
    },
}

RANK_MEDALS = ['🥇', '🥈', '🥉', '4️⃣']
RANK_LABELS = ['1er', '2ème', '3ème', '4ème']

_SEP  = "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
_DBL  = "══════════════════════════════════"

def _bar(pct: float, width: int = 10) -> str:
    filled = max(0, min(width, round(pct / 100 * width)))
    return '█' * filled + '░' * (width - filled)

def _suit_stats_block(suit: str, s: dict, rank: int) -> list:
    em   = SUIT_EMOJI[suit]
    icon = SUIT_ICON[suit]
    name = SUIT_NAMES_FR[suit]
    r0, r1, r2, r3 = s['r0'], s['r1'], s['r2'], s['r3']
    lost  = s['losses']
    total = s['total']
    wins  = r0 + r1 + r2 + r3
    pct   = (wins / total * 100) if total > 0 else 0.0
    medal = RANK_MEDALS[rank - 1]
    bar   = _bar(pct)
    return [
        f"{medal} {em} {icon} **{name.upper()}**",
        "┌─ Victoires ──────────────────────┐",
        f"│  ✅ Direct : {r0:<5}  🔄 R1 : {r1:<5} │",
        f"│  🔄 R2     : {r2:<5}  🔄 R3 : {r3:<5} │",
        f"│  ❌ Perdus : {lost:<5}  📦 Total: {total:<4}│",
        f"│  🎯 {bar} **{pct:>5.1f}%**      │",
        "└──────────────────────────────────┘",
    ]


def get_concours_par_costume_text() -> tuple:
    """
    Calcule et formate le palmarès du concours de prédictions par costume.
    Retourne (msg1, msg2) — deux messages Telegram séparés.
      msg1 : Intro cinématique + Stats détaillées par costume
      msg2 : Révélation champion + Classement + Comparaison + Encouragements + Signature
    """
    global concours_last_winner, concours_last_pct

    # ── 1. Calculer les stats par costume ────────────────────────────────────
    stats = {
        s: {'r0': 0, 'r1': 0, 'r2': 0, 'r3': 0,
            'wins': 0, 'losses': 0, 'total': 0, 'pct': 0.0}
        for s in ALL_SUITS
    }
    for pred in prediction_history:
        suit = pred.get('suit', '')
        if suit not in stats:
            continue
        st = pred.get('status', '')
        rl = pred.get('rattrapage_level', 0)
        if 'gagne' in st:
            key = f'r{min(rl, 3)}'
            stats[suit][key]     += 1
            stats[suit]['wins']  += 1
            stats[suit]['total'] += 1
        elif st == 'perdu':
            stats[suit]['losses'] += 1
            stats[suit]['total']  += 1

    for suit in stats:
        t = stats[suit]['total']
        stats[suit]['pct'] = (stats[suit]['wins'] / t * 100) if t > 0 else 0.0

    ranked = sorted(
        ALL_SUITS,
        key=lambda s: (stats[s]['pct'], stats[s]['total']),
        reverse=True
    )

    winner      = ranked[0]
    winner_name = SUIT_NAMES_FR[winner]
    winner_em   = SUIT_EMOJI[winner]
    winner_icon = SUIT_ICON[winner]
    winner_pct  = stats[winner]['pct']
    winner_wins = stats[winner]['wins']
    winner_tot  = stats[winner]['total']
    winner_bar  = _bar(winner_pct, 12)

    now = datetime.now().strftime('%d/%m/%Y — %H:%M')

    # ════════════════════════════════════════
    # MESSAGE 1 — Intro + Stats
    # ════════════════════════════════════════
    lines = [
        "🎴✨ **BACCARAT AI** ✨🎴",
        _SEP,
        "🏁 **FIN DE CYCLE — 1 440 JEUX**",
        f"📅 {now}",
        _SEP,
        "",
        "⚡ **LE VERDICT EST TOMBÉ !** ⚡",
        "1 440 jeux. 4 costumes. 1 seul champion.",
        "Les chiffres ne mentent pas — découvrez",
        "le palmarès complet de ce cycle !",
        "",
        _SEP,
        "📊 **STATISTIQUES DÉTAILLÉES — PAR COSTUME**",
        _SEP,
        "",
    ]
    for i, suit in enumerate(ranked):
        lines += _suit_stats_block(suit, stats[suit], i + 1)
        lines.append("")

    # ════════════════════════════════════════
    # MESSAGE 2 — Champion + Classement + Suite
    # ════════════════════════════════════════
    lines2 = []

    # ── Révélation dramatique du champion ──────────────────────────────────
    lines2 += [
        "🚨🏆 **RÉVÉLATION DU CHAMPION** 🏆🚨",
        _SEP,
        "",
        f"   {winner_em} {winner_icon}",
        f"🥇 **{winner_name.upper()}**",
        "   règne sur ce cycle !",
        "",
        "📊 Taux de réussite",
        f"   {winner_bar} **{winner_pct:.1f}%**",
    ]
    if winner_tot > 0:
        lines2.append(f"   ✅ {winner_wins} gagnées / {winner_tot} prédictions")
    lines2 += ["", ""]
    for phrase_line in SUIT_WINNER_PHRASES[winner].split('\n'):
        lines2.append(f"  {phrase_line}")
    lines2 += [
        "",
        "💰 **4 000 000 FCFA** attribués",
        "   par Kouamé Sossou ! 🙌",
        "",
        _SEP,
    ]

    # ── Classement final ────────────────────────────────────────────────────
    lines2 += [
        "🏆 **CLASSEMENT FINAL DU CYCLE**",
        _SEP,
    ]
    for i, suit in enumerate(ranked):
        em   = SUIT_EMOJI[suit]
        icon = SUIT_ICON[suit]
        name = SUIT_NAMES_FR[suit]
        s    = stats[suit]
        bar  = _bar(s['pct'], 8)
        lines2.append(
            f"{RANK_MEDALS[i]}  {em}{icon} **{name:<8}**  {bar} {s['pct']:>5.1f}%  ({s['total']} pred.)"
        )
    lines2 += ["", _SEP]

    # ── Comparaison cycle précédent ─────────────────────────────────────────
    lines2 += ["📈 **VS CYCLE PRÉCÉDENT**", ""]
    if concours_last_winner and concours_last_winner in SUIT_NAMES_FR:
        prev      = concours_last_winner
        prev_em   = SUIT_EMOJI[prev]
        prev_icon = SUIT_ICON[prev]
        prev_name = SUIT_NAMES_FR[prev]
        prev_pct  = concours_last_pct
        if prev == winner:
            lines2 += [
                f"🔁 {winner_em}{winner_icon} **{winner_name.upper()} CONFIRME SA DOMINATION !**",
                f"Déjà champion au cycle précédent ({prev_pct:.1f}%),",
                f"il récidive avec **{winner_pct:.1f}%** — une constance redoutable !",
                "Les rivaux devront se surpasser pour le détrôner.",
            ]
        else:
            diff  = winner_pct - prev_pct
            trend = "montée en puissance SPECTACULAIRE !" if diff > 10 else \
                    "belle progression !" if diff > 0 else \
                    "résultat serré mais verdict sans appel !"
            lines2 += [
                f"Cycle précédent : {prev_em}{prev_icon} **{prev_name.upper()}** menait avec **{prev_pct:.1f}%**",
                "",
                f"Mais ce cycle, {winner_em}{winner_icon} **{winner_name.upper()}** a frappé fort",
                f"avec **{winner_pct:.1f}%** — {trend}",
                "",
                f"👉 {prev_em} {prev_name} cède sa couronne ce cycle.",
                "   La revanche est-elle pour le prochain ? 🔥",
            ]
    else:
        lines2 += [
            "🆕 **Premier concours enregistré !**",
            "Les résultats seront comparés au prochain cycle.",
            "📌 Rendez-vous dans 1 440 jeux !",
        ]
    lines2 += ["", _SEP]

    # ── Un mot pour chaque costume ──────────────────────────────────────────
    lines2 += ["💬 **UN MOT POUR CHAQUE COSTUME**", ""]
    for i, suit in enumerate(ranked):
        lines2.append(SUIT_ENCOURAGE[suit][i + 1])
        lines2.append("")

    # ── Signature ───────────────────────────────────────────────────────────
    lines2 += [
        _SEP,
        "✍️ **BACCARAT AI** — par Kouamé Sossou",
        "🚀 Nouveau cycle lancé — En avant ! ♠️♦️♥️♣️",
        _SEP,
    ]

    return "\n".join(lines), "\n".join(lines2)


async def bilan_loop():
    """Envoie le bilan toutes les 4h à heure alignée : 00h, 04h, 08h, 12h, 16h, 20h."""
    global bilan_interval_hours
    interval = 4
    while True:
        try:
            now = datetime.now()
            # Heure alignée : prochain multiple de 4h
            hours_since_last  = now.hour % interval
            hours_until_next  = interval - hours_since_last
            seconds_until_next = hours_until_next * 3600 - (now.minute * 60 + now.second)
            if seconds_until_next <= 0:
                seconds_until_next += interval * 3600
            await asyncio.sleep(seconds_until_next)

            if bilan_interval_hours == 0:
                continue

            heure = datetime.now().strftime('%H:%M')
            txt   = get_bilan_text()

            # Chat privé admin uniquement
            if ADMIN_ID and ADMIN_ID != 0:
                try:
                    admin_entity = await client.get_entity(ADMIN_ID)
                    await client.send_message(admin_entity, txt, parse_mode='markdown')
                    logger.info(f"📊 Bilan 4h envoyé à l'admin ({heure})")
                except Exception as admin_err:
                    logger.error(f"❌ Bilan admin: {admin_err}")
        except Exception as e:
            logger.error(f"❌ Erreur bilan_loop: {e}")
            await asyncio.sleep(60)


ROLLING_WINDOW = 30   # nombre de dernières prédictions pour le score glissant
MIN_ROLLING    = 1    # minimum pour être éligible (1 prédiction suffit)


def _rolling_score(state: dict, window: int = ROLLING_WINDOW):
    """Score glissant : wins - losses sur les <window> dernières prédictions."""
    hist = state.get('pred_history', [])
    recent = hist[-window:] if len(hist) >= window else hist
    if len(recent) < MIN_ROLLING:
        return None, 0, 0, len(recent)
    wins   = sum(1 for h in recent if h.get('win'))
    losses = len(recent) - wins
    return wins - losses, wins, losses, len(recent)


async def auto_strategy_hourly_loop():
    """
    Toutes les heures pile (01:00, 02:00, … 24:00) :
    1. Évalue les 216 trackers sur la fenêtre de l'heure écoulée
    2. Envoie la proposition à l'admin avec boutons ✅/❌
    3. Remet les 216 stocks à zéro immédiatement (nouveau départ)
    4. Stocke la proposition en DB pour l'historique
    La stratégie n'est appliquée qu'après confirmation admin.
    """
    while True:
        try:
            now = datetime.now()
            seconds_until_next_hour = (60 - now.minute) * 60 - now.second
            if seconds_until_next_hour <= 0:
                seconds_until_next_hour += 3600
            await asyncio.sleep(seconds_until_next_hour)

            heure = datetime.now().strftime('%H:%M')

            best_key        = None
            best_score      = None
            best_wins       = 0
            best_losses_cap = 0
            best_recent_cap = 0
            best_val        = None
            best_per_mirror = {}   # pour affichage uniquement

            fallback_key      = None   # meilleur avec le moins de pertes
            fallback_min_loss = float('inf')
            fallback_max_wins = 0
            fallback_score    = None
            fallback_wins_cap = 0
            fallback_loss_cap = 0
            fallback_recent_cap = 0

            for key, state in silent_combo_states.items():
                combo_num, wx, b, df_sim = key
                score, wins, losses, recent = _rolling_score(state)
                if score is None:
                    continue   # moins de MIN_ROLLING prédictions

                # ── Sélection principale : UNIQUEMENT les combos sans aucune perte ──
                if losses == 0:
                    if best_key is None or wins > best_wins or (
                            wins == best_wins and score > (best_score or 0)):
                        best_key        = key
                        best_score      = score
                        best_wins       = wins
                        best_losses_cap = losses
                        best_recent_cap = recent

                # ── Fallback : min pertes puis max victoires ──────────────────
                if losses < fallback_min_loss or (
                        losses == fallback_min_loss and wins > fallback_max_wins):
                    fallback_key      = key
                    fallback_min_loss = losses
                    fallback_max_wins = wins
                    fallback_score    = score
                    fallback_wins_cap = wins
                    fallback_loss_cap = losses
                    fallback_recent_cap = recent

                # ── Classement par miroir pour la notification (tous combos) ──
                prev = best_per_mirror.get(combo_num)
                if prev is None or score > prev[0] or (score == prev[0] and wins > prev[1]):
                    best_per_mirror[combo_num] = (score, wins, losses, recent, key, state)

            # Toujours remettre les stocks à zéro à l'heure pile, même sans données
            total_preds_before = sum(
                s.get('total', 0) for s in silent_combo_states.values()
            )
            reset_silent_combo_states()
            logger.info(
                f"🔄 [{heure}] Stocks silencieux remis à zéro "
                f"({total_preds_before} prédictions de l'heure écoulée effacées)"
            )

            # ── Sélection finale : zéro-perte ou, à défaut, meilleur ratio ──
            if best_key is None and fallback_key is not None:
                # Aucun combo sans perte → on utilise le fallback
                best_key        = fallback_key
                best_score      = fallback_score
                best_wins       = fallback_wins_cap
                best_losses_cap = fallback_loss_cap
                best_recent_cap = fallback_recent_cap
                is_fallback     = True
            else:
                is_fallback = False

            if best_key is None:
                # Vraiment aucune donnée suffisante
                _with_data = sum(
                    1 for st in silent_combo_states.values()
                    if st.get('total', 0) >= MIN_ROLLING
                )
                logger.info(
                    f"🕐 [{heure}] Données insuffisantes ({_with_data} combos avec données)"
                )
                if ADMIN_ID:
                    try:
                        await client.send_message(
                            ADMIN_ID,
                            f"🕐 **{heure}** — Évaluation horaire terminée\n\n"
                            f"📊 Prédictions silencieuses cette heure : **{total_preds_before}**\n"
                            "ℹ️ Aucun combo n'a encore reçu de prédiction — "
                            "accumulation en cours.\n"
                            "_Les stocks repartent à zéro._"
                        )
                    except Exception:
                        pass
                continue

            combo_num, wx, b, df_sim = best_key
            combo = GLOBAL_COMBOS_BY_NUM.get(combo_num)
            if not combo:
                logger.warning(f"🕐 [{heure}] Auto-stratégie horaire : combo_num={combo_num} introuvable")
                continue

            # Utiliser les valeurs capturées AVANT le reset (pred_history est vide après)
            r_score  = best_score
            r_wins   = best_wins
            r_losses = best_losses_cap
            r_recent = best_recent_cap

            best_auto = {
                'combo_num':    combo_num,
                'mirror':       combo['mirror'],
                'disp':         combo['disp'],
                'name':         combo['name'],
                'wx':           wx,
                'b':            b,
                'df_sim':       df_sim,
                'score':        r_score,
                'wins':         r_wins,
                'losses':       r_losses,
                'total':        r_recent,
                'mirror_ranks': best_per_mirror,
                'is_fallback':  is_fallback,
            }

            logger.info(
                f"🕐 [{heure}] Proposition horaire (rolling {ROLLING_WINDOW}) "
                f"→ {combo['name']} wx={wx} B={b} trigger+{df_sim} | "
                f"score={r_score:+d} (✅{r_wins} ❌{r_losses} / {r_recent} pred.)"
            )

            if best_auto.get('is_fallback', False):
                # Fallback (a des pertes) → proposition manuelle ✅/❌ à l'admin
                await propose_hourly_strategy(best_auto, heure)
            else:
                # 0 perte → application automatique immédiate, admin reçoit ❌ Annuler
                await apply_best_strategy_auto(best_auto)

            # ── Message de formation simple au canal (toutes les heures pile) ──
            asyncio.ensure_future(_send_formation_simple_to_canal(heure))

        except Exception as e:
            logger.error(f"❌ auto_strategy_hourly_loop: {e}")
            await asyncio.sleep(60)


def reset_silent_combo_states():
    """
    Remet à zéro les wins/losses/total/pred_history des 216 trackers silencieux.
    Les compteurs actifs (c13, c13_start, c2, pending) sont conservés.
    Appelée chaque heure pile après l'évaluation.
    """
    for state in silent_combo_states.values():
        state['wins']         = 0
        state['losses']       = 0
        state['total']        = 0
        state['pred_history'] = []


async def _save_strategy_history_entry(entry: dict):
    """Ajoute une entrée à l'historique strategy_history en DB (max 100 entrées)."""
    try:
        history = await db.db_load_kv('strategy_history') or []
        if not isinstance(history, list):
            history = []
        history.append(entry)
        if len(history) > 100:
            history = history[-100:]
        await db.db_save_kv('strategy_history', history)
    except Exception as e:
        logger.error(f"❌ _save_strategy_history_entry: {e}")


async def propose_hourly_strategy(best_auto: dict, heure: str):
    """
    Envoie la proposition de stratégie horaire à l'admin avec boutons ✅/❌.
    Stocke la proposition en DB (historique).
    Ne modifie PAS les paramètres actifs — attend la confirmation admin.
    """
    global hourly_pending_auto
    if not ADMIN_ID:
        return

    mirror_ranks = best_auto.get('mirror_ranks', {})
    medals  = ['🥇', '🥈', '🥉']
    sorted_ranks = sorted(
        mirror_ranks.items(),
        key=lambda x: (x[1][0], x[1][1]),
        reverse=True,
    )

    # Ligne de détail par miroir (avec tous les params)
    detail_lines = []
    for rank_idx, (cnum, (sc, w, l, rc, best_k, _)) in enumerate(sorted_ranks):
        cname  = GLOBAL_COMBOS_BY_NUM.get(cnum, {}).get('name', f'P{cnum}')
        medal  = medals[rank_idx] if rank_idx < len(medals) else '  '
        b_num, wx_num, b_b, df_num = best_k
        detail_lines.append(
            f"  {medal} **{cname}**\n"
            f"       P={cnum} | wx={wx_num} | B={b_b} | df+{df_num} | "
            f"Score **{sc:+d}** (✅{w} ❌{l} / {rc} pred.)"
        )

    new_df_sim  = best_auto.get('df_sim', 1)
    is_fallback = best_auto.get('is_fallback', False)

    if is_fallback:
        quality_line = (
            "⚠️ _Aucun combo sans perte cette heure — meilleur ratio disponible "
            f"(❌{best_auto['losses']} perte(s) sur {best_auto['total']} pred.)._"
        )
        badge = "🥈 Meilleur ratio disponible"
    else:
        quality_line = "✅ _Combo sans aucune perte cette heure._"
        badge        = "🏆 Meilleure configuration (0 perte)"

    lines = [
        "╔══════════════════════════════════╗",
        f"║  🕐 PROPOSITION HORAIRE — {heure}  ║",
        "╚══════════════════════════════════╝",
        "",
        "📊 **Classement des 3 miroirs (heure écoulée) :**",
    ] + detail_lines + [
        "",
        f"**{badge} :**",
        f"  Miroir : **{best_auto['name']}** ({best_auto['disp']})",
        f"  wx C13 : **{best_auto['wx']}** consécutives",
        f"  B  C2  : **{best_auto['b']}** absences",
        f"  df     : **trigger+{new_df_sim}**",
        f"  Score  : **{best_auto['score']:+d}** pts (✅{best_auto['wins']} ❌{best_auto['losses']} / {best_auto['total']} pred.)",
        "",
        quality_line,
        "⚠️ _Les stocks silencieux ont été remis à zéro. Nouveau départ._",
        "",
        "👇 Confirme pour appliquer cette stratégie maintenant :",
    ]

    try:
        msg = await client.send_message(
            ADMIN_ID,
            "\n".join(lines),
            buttons=[
                [Button.inline("✅ Confirmer", b"confirm_hourly"),
                 Button.inline("❌ Ignorer",   b"ignore_hourly")],
            ],
            parse_mode='markdown',
        )
        hourly_pending_auto = {
            'best_auto':  best_auto,
            'msg_id':     msg.id,
            'heure':      heure,
            'timestamp':  datetime.now().isoformat(),
        }
        logger.info(f"📨 Proposition horaire envoyée à l'admin (msg_id={msg.id})")
    except Exception as e:
        logger.error(f"❌ propose_hourly_strategy — envoi: {e}")
        hourly_pending_auto = {
            'best_auto':  best_auto,
            'msg_id':     None,
            'heure':      heure,
            'timestamp':  datetime.now().isoformat(),
        }

    entry = {
        'heure':     heure,
        'timestamp': datetime.now().isoformat(),
        'params': {
            'nom':      best_auto['name'],
            'miroir':   best_auto['disp'],
            'combo_num': best_auto['combo_num'],
            'wx':       best_auto['wx'],
            'b':        best_auto['b'],
            'df_sim':   best_auto['df_sim'],
            'score':    best_auto['score'],
            'wins':     best_auto['wins'],
            'losses':   best_auto['losses'],
            'total':    best_auto['total'],
        },
        'decision': 'en_attente',
    }
    db.db_schedule(_save_strategy_history_entry(entry))


# ─────────────────────────────────────────────────────────────────────────────
# SYSTÈME HEURES FAVORABLES — Basé sur Compteur4 (2 déclenchements → fenêtre)
# ─────────────────────────────────────────────────────────────────────────────

def is_c14_balanced(threshold_pct: float = 0.20) -> bool:
    """
    Retourne True si la distribution C14 est équilibrée entre les 4 costumes.
    Équilibré = (max - min) < threshold_pct × moyenne globale.
    Si oui → fenêtre favorable de 30 min ; sinon → 3 heures.
    """
    counts = list(compteur14_counts.values())
    total  = sum(counts)
    if total == 0:
        return False
    avg = total / len(counts)
    return (max(counts) - min(counts)) < threshold_pct * avg


async def trigger_favorable_window_from_c4():
    """
    Déclenchée après 2 événements C4 (seuil atteint 2 fois, peu importe l'heure).
    - C14 équilibré → fenêtre de 30 min
    - C14 non équilibré → fenêtre de 3 heures
    Annonce texte au canal + panneau countdown + notification admin.
    """
    global heures_fav_countdown_msg_id, heures_fav_countdown_task, countdown_panel_counter

    if not heures_favorables_active or not PREDICTION_CHANNEL_ID:
        return
    try:
        canal_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not canal_entity:
            return

        now     = datetime.now()
        now_min = now.hour * 60 + now.minute

        balanced       = is_c14_balanced()
        window_minutes = 30 if balanced else 180

        start_h        = (now.hour + 1) % 24
        end_total_min  = (start_h * 60 + window_minutes) % (24 * 60)
        end_h          = end_total_min // 60
        end_min_part   = end_total_min % 60

        interval_str = (
            f"{start_h:02d}h00 → {end_h:02d}h{end_min_part:02d}"
            if end_min_part else
            f"{start_h:02d}h00 → {end_h:02d}h00"
        )
        duree_str  = "30 min" if balanced else "3 heures"
        raison_str = "C14 équilibré — distribution constante" if balanced else "2 déclenchements C4 détectés"

        start_minute  = start_h * 60
        minutes_left  = (start_minute - now_min) % (24 * 60)
        total_minutes = window_minutes

        # ── Annonce texte ─────────────────────────────────────────────────────
        annonce = (
            "⏰ **HEURE FAVORABLE DÉTECTÉE**\n\n"
            f"🟢 Créneau : **{interval_str}** _(Côte d'Ivoire)_\n"
            f"⏳ Durée : **{duree_str}**\n"
            f"📊 Raison : {raison_str}\n\n"
            "_En Dieu nous comptons, Sossou Kouamé prediction 🔥_"
        )
        await client.send_message(canal_entity, annonce, parse_mode='markdown')
        logger.info(f"⏰ Heure favorable annoncée : {interval_str} ({duree_str})")

        # ── Panneau countdown ─────────────────────────────────────────────────
        if heures_fav_countdown_task and not heures_fav_countdown_task.done():
            heures_fav_countdown_task.cancel()
            heures_fav_countdown_msg_id = None

        panel = _build_countdown_panel(interval_str, minutes_left, total_minutes, False)
        sent  = await client.send_message(canal_entity, panel, parse_mode='markdown')
        heures_fav_countdown_msg_id = sent.id
        countdown_panel_counter += 1

        await db.db_save_countdown_panel(
            countdown_panel_counter, interval_str, start_h, end_h, minutes_left
        )
        await _save_active_panel(
            countdown_panel_counter, interval_str,
            start_h, end_h, start_minute, total_minutes, sent.id
        )
        heures_fav_countdown_task = asyncio.create_task(
            _heures_fav_countdown_runner(
                sent.id, canal_entity, interval_str, start_minute, total_minutes
            )
        )
        logger.info(f"🟦 Panneau #{countdown_panel_counter} envoyé : {interval_str} dans {minutes_left}min")

        # ── Notification admin ────────────────────────────────────────────────
        if ADMIN_ID and ADMIN_ID != 0:
            try:
                admin_entity = await client.get_entity(ADMIN_ID)
                await client.send_message(
                    admin_entity,
                    (
                        "⏰ **Heure favorable déclenchée (C4×2)**\n"
                        f"Créneau : **{interval_str}** | Durée : {duree_str}\n"
                        f"Raison : {raison_str}\n"
                        f"C14 : {dict(compteur14_counts)} ({compteur14_cycle_games} jeux)"
                    ),
                    parse_mode='markdown'
                )
            except Exception as adm_e:
                logger.error(f"❌ Admin heure favorable: {adm_e}")

    except Exception as e:
        logger.error(f"❌ trigger_favorable_window_from_c4: {e}")


# ── Compte à rebours heures favorables ──────────────────────────────────────

def _build_countdown_panel(interval_str: str, minutes_left: int,
                            total_minutes: int, blink_state: bool = False) -> str:
    """
    Génère le panneau visuel bleu de compte à rebours pour le canal.
    Coins colorés selon la fraction de temps ÉCOULÉ :
      0–25%  → 🟦 bleu (aucun coin coloré)
      25–50% → 🟢 vert
      50–75% → 🟡 jaune
      75%+   → 🔴 rouge
    'blink_state' alterne l'affichage pour simuler le clignotement.
    """
    elapsed_frac = 1.0 - (minutes_left / total_minutes) if total_minutes > 0 else 1.0

    if elapsed_frac < 0.25:
        corner = "🟦"
    elif elapsed_frac < 0.50:
        corner = "🟢" if not blink_state else "⬜"
    elif elapsed_frac < 0.75:
        corner = "🟡" if not blink_state else "⬜"
    else:
        corner = "🔴" if not blink_state else "⬜"

    h, m = divmod(minutes_left, 60)
    if h > 0 and m > 0:
        temps = f"{h}h {m:02d}min"
    elif h > 0:
        temps = f"{h}h"
    else:
        temps = f"{m}min"

    panel = (
        f"{corner}🟦🟦🟦🟦🟦🟦🟦🟦🟦🟦🟦🟦{corner}\n"
        "🟦                              🟦\n"
        "🟦   ⏰ **HEURE FAVORABLE**   🟦\n"
        f"🟦   🕐 _{interval_str}_   🟦\n"
        "🟦   🇨🇮 _(heure Côte d'Ivoire)_   🟦\n"
        f"🟦   ⏳ Dans **{temps}**   🟦\n"
        "🟦                              🟦\n"
        f"{corner}🟦🟦🟦🟦🟦🟦🟦🟦🟦🟦🟦🟦{corner}\n"
        "\n_En Dieu nous comptons, Sossou Kouamé prediction 🔥_"
    )
    return panel


async def _save_active_panel(panel_number: int, interval_str: str,
                              start_h: int, end_h: int,
                              start_minute: int, total_minutes: int, msg_id: int):
    """Persiste l'état du panneau countdown actif en DB (kv_store)."""
    data = {
        'active':        True,
        'panel_number':  panel_number,
        'interval_str':  interval_str,
        'start_h':       start_h,
        'end_h':         end_h,
        'start_minute':  start_minute,
        'total_minutes': total_minutes,
        'msg_id':        msg_id,
    }
    await db.db_save_kv('active_panel', data)


async def _clear_active_panel():
    """Marque le panneau actif comme terminé en DB."""
    await db.db_save_kv('active_panel', {'active': False})


async def _heures_fav_countdown_runner(msg_id: int, canal_entity,
                                        interval_str: str,
                                        start_minute: int, total_minutes: int):
    """
    Tâche de fond : met à jour le panneau de compte à rebours toutes les 10 min.
    - Supprime le message quand l'heure favorable commence.
    - Supprime aussi si 8h max ont été atteintes.
    """
    global heures_fav_countdown_msg_id, heures_fav_countdown_task
    CHECK_INTERVAL = 10 * 60     # mise à jour toutes les 10 min
    MAX_AGE        = 8 * 60 * 60 # 8 heures maximum
    blink_state    = False
    start_time     = datetime.now()

    while True:
        await asyncio.sleep(CHECK_INTERVAL)
        try:
            now = datetime.now()
            now_min   = now.hour * 60 + now.minute
            remaining = (start_minute - now_min) % (24 * 60)
            elapsed_sec = (now - start_time).total_seconds()

            # Supprimer si heure arrivée ou 8h max écoulées
            if remaining <= 0 or elapsed_sec >= MAX_AGE:
                try:
                    await client.delete_messages(canal_entity, [msg_id])
                    logger.info("🟦 Countdown heure favorable supprimé (arrivé ou expiré)")
                except Exception:
                    pass
                heures_fav_countdown_msg_id = None
                heures_fav_countdown_task   = None
                await _clear_active_panel()
                break

            blink_state = not blink_state
            panel = _build_countdown_panel(interval_str, remaining, total_minutes, blink_state)
            ok = await safe_edit_message(canal_entity, msg_id, panel,
                                         label=f"countdown {interval_str}", max_retries=3)
            if ok:
                logger.debug(f"🟦 Countdown mis à jour : {remaining}min restantes")
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.debug(f"⚠️ Countdown update: {e}")
            break

    heures_fav_countdown_task = None


async def restore_countdown_panel_if_needed():
    """
    Au démarrage : reprend un panneau countdown actif depuis la DB si encore valide.
    Le panneau a été créé par trigger_favorable_window_from_c4.
    Si expiré ou absent → rien. Le prochain C4×2 déclenchera un nouveau panneau.
    """
    global heures_fav_countdown_msg_id, heures_fav_countdown_task, countdown_panel_counter
    try:
        if not heures_favorables_active or not PREDICTION_CHANNEL_ID:
            return

        canal_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not canal_entity:
            return

        now     = datetime.now()
        now_min = now.hour * 60 + now.minute

        saved_panel = await db.db_load_kv('active_panel')
        if not saved_panel or not saved_panel.get('active'):
            logger.info("🟦 Restauration panneau : aucun panneau actif en DB")
            return

        start_minute  = saved_panel['start_minute']
        total_minutes = saved_panel['total_minutes']
        interval_str  = saved_panel['interval_str']
        panel_number  = saved_panel['panel_number']
        stored_msg_id = saved_panel.get('msg_id')
        remaining     = (start_minute - now_min) % (24 * 60)

        if remaining <= 0:
            await _clear_active_panel()
            logger.info("🟦 Panneau DB expiré — nettoyage effectué")
            return

        panel = _build_countdown_panel(interval_str, remaining, total_minutes, False)
        msg_id_to_use = None

        if stored_msg_id:
            ok = await safe_edit_message(
                canal_entity, stored_msg_id, panel,
                label=f"reprise panneau #{panel_number}", max_retries=3
            )
            if ok:
                msg_id_to_use = stored_msg_id
                logger.info(f"🟦 Panneau #{panel_number} repris (édité) : {interval_str} — {remaining}min")

        if msg_id_to_use is None:
            sent = await client.send_message(canal_entity, panel, parse_mode='markdown')
            msg_id_to_use = sent.id
            logger.info(f"🟦 Panneau #{panel_number} repris (nouveau message) : {interval_str} — {remaining}min")

        heures_fav_countdown_msg_id = msg_id_to_use
        await _save_active_panel(
            panel_number, interval_str,
            saved_panel.get('start_h', 0), saved_panel.get('end_h', 0),
            start_minute, total_minutes, msg_id_to_use
        )
        heures_fav_countdown_task = asyncio.create_task(
            _heures_fav_countdown_runner(
                msg_id_to_use, canal_entity, interval_str, start_minute, total_minutes
            )
        )
    except Exception as e:
        logger.error(f"❌ restore_countdown_panel_if_needed: {e}")


def update_compteur4(game_number: int, player_suits: Set[str], player_cards_raw: list) -> tuple:
    """
    Met à jour Compteur4 — logique série complète (comme Compteur7 pour les absences).
    - Quand un costume est absent, la série monte.
    - À l'atteinte du seuil, une alerte immédiate est envoyée (série toujours en cours).
    - Quand le costume réapparaît et que la série était >= seuil, la série est enregistrée.
    Retourne : (threshold_alerts, completed_series)
      - threshold_alerts : liste de suits ayant JUSTE atteint le seuil (alerte immédiate)
      - completed_series : liste de dicts de séries terminées (enregistrer dans PDF)
    """
    global compteur4_trackers, compteur4_current, compteur4_events

    threshold_alerts  = []
    completed_series  = []
    now = datetime.now()

    for suit in ALL_SUITS:
        cur = compteur4_current[suit]
        if suit in player_suits:
            # Costume présent → fin de série d'absence si série >= seuil
            if cur['count'] >= COMPTEUR4_THRESHOLD:
                series = {
                    'suit':       suit,
                    'count':      cur['count'],
                    'start_game': cur['start_game'],
                    'end_game':   game_number - 1,
                    'start_time': cur['start_time'],
                    'end_time':   now,
                }
                compteur4_events.append(series)
                completed_series.append(series)
                save_compteur4_data()
                logger.info(
                    f"🔴 C4: {suit} série d'absence terminée "
                    f"{series['count']}x (#{series['start_game']}→#{series['end_game']})"
                )
            # Reset
            cur['count']      = 0
            cur['start_game'] = None
            cur['start_time'] = None
            cur['alerted']    = False
            compteur4_trackers[suit] = 0
        else:
            # Costume absent → incrémenter la série
            if cur['count'] == 0:
                cur['start_game'] = game_number
                cur['start_time'] = now
            cur['count'] += 1
            compteur4_trackers[suit] = cur['count']

            # Alerte immédiate quand on atteint exactement le seuil
            if cur['count'] == COMPTEUR4_THRESHOLD and not cur['alerted']:
                cur['alerted'] = True
                threshold_alerts.append(suit)
                logger.info(f"🚨 C4: {suit} absent {COMPTEUR4_THRESHOLD} fois! (série continue…)")

    return threshold_alerts, completed_series


def update_compteur5(game_number: int, player_suits: Set[str], player_cards_raw: list) -> List[str]:
    """Met à jour Compteur5 (présences consécutives). Retourne les costumes ayant atteint le seuil."""
    global compteur5_trackers, compteur5_events
    triggered = []
    for suit in ALL_SUITS:
        if suit in player_suits:
            compteur5_trackers[suit] += 1
            if compteur5_trackers[suit] == COMPTEUR5_THRESHOLD:
                ev = {
                    'datetime': datetime.now(),
                    'game_number': game_number,
                    'suit': suit,
                    'player_suits': list(player_suits),
                }
                compteur5_events.append(ev)
                triggered.append(suit)
                logger.info(f"✅ Compteur5: {suit} présent {COMPTEUR5_THRESHOLD} fois! (jeu #{game_number})")
        else:
            compteur5_trackers[suit] = 0
    return triggered

# ============================================================================
# COMPTEUR4 — PERSISTANCE (séries d'absences — survit aux resets)
# ============================================================================

async def load_compteur4_data():
    """Charge les séries d'absences Compteur4 depuis PostgreSQL (fallback JSON)."""
    global compteur4_events
    try:
        raw = await db.db_load_kv('compteur4')
        from_json = False
        if raw is None and os.path.exists(COMPTEUR4_DATA_FILE):
            with open(COMPTEUR4_DATA_FILE, 'r', encoding='utf-8') as f:
                raw = json.load(f)
            from_json = True
        if raw:
            compteur4_events = []
            for item in raw:
                item['start_time'] = datetime.fromisoformat(item['start_time'])
                item['end_time']   = datetime.fromisoformat(item['end_time'])
                compteur4_events.append(item)
            logger.info(f"📂 C4: {len(compteur4_events)} séries chargées")
            if from_json:
                save_compteur4_data()
                logger.info("📂 C4: migration JSON → PostgreSQL effectuée")
    except Exception as e:
        logger.error(f"❌ Chargement C4 échoué: {e}")
        compteur4_events = []


def save_compteur4_data():
    """Sauvegarde les séries d'absences Compteur4 dans PostgreSQL."""
    try:
        data = []
        for item in compteur4_events:
            row = dict(item)
            row['start_time'] = item['start_time'].isoformat()
            row['end_time']   = item['end_time'].isoformat()
            data.append(row)
        db.db_schedule(db.db_save_kv('compteur4', data))
    except Exception as e:
        logger.error(f"❌ Sauvegarde C4 échouée: {e}")


# ============================================================================
# COMPTEUR7 — SÉRIES CONSÉCUTIVES PERSISTANTES
# ============================================================================

async def load_compteur7_data():
    """Charge les séries Compteur7 depuis PostgreSQL (fallback JSON)."""
    global compteur7_completed
    try:
        raw = await db.db_load_kv('compteur7')
        from_json = False
        if raw is None and os.path.exists(COMPTEUR7_DATA_FILE):
            with open(COMPTEUR7_DATA_FILE, 'r', encoding='utf-8') as f:
                raw = json.load(f)
            from_json = True
        compteur7_completed = []
        if raw:
            for item in raw:
                item['start_time'] = datetime.fromisoformat(item['start_time'])
                item['end_time']   = datetime.fromisoformat(item['end_time'])
                compteur7_completed.append(item)
            logger.info(f"📂 C7: {len(compteur7_completed)} séries chargées")
            if from_json:
                save_compteur7_data()
                logger.info("📂 C7: migration JSON → PostgreSQL effectuée")
    except Exception as e:
        logger.error(f"❌ Chargement C7 échoué: {e}")
        compteur7_completed = []


def save_compteur7_data():
    """Sauvegarde les séries Compteur7 dans PostgreSQL."""
    try:
        data = []
        for item in compteur7_completed:
            row = dict(item)
            row['start_time'] = item['start_time'].isoformat()
            row['end_time']   = item['end_time'].isoformat()
            data.append(row)
        db.db_schedule(db.db_save_kv('compteur7', data))
    except Exception as e:
        logger.error(f"❌ Sauvegarde C7 échouée: {e}")


async def load_hourly_data():
    """Charge les données horaires depuis PostgreSQL (fallback JSON)."""
    global hourly_suit_data, hourly_game_count
    try:
        saved = await db.db_load_hourly()
        if saved is None and os.path.exists(HOURLY_DATA_FILE):
            with open(HOURLY_DATA_FILE, 'r', encoding='utf-8') as f:
                saved = json.load(f)
        if saved:
            for h_str, suits in saved.get('suits', {}).items():
                h = int(h_str)
                if 0 <= h <= 23:
                    for suit, cnt in suits.items():
                        if suit in hourly_suit_data[h]:
                            hourly_suit_data[h][suit] = cnt
            for h_str, cnt in saved.get('totals', {}).items():
                h = int(h_str)
                if 0 <= h <= 23:
                    hourly_game_count[h] = cnt
            logger.info("📂 Données horaires chargées")
    except Exception as e:
        logger.error(f"❌ Chargement données horaires: {e}")


def save_hourly_data():
    """Sauvegarde les données horaires dans PostgreSQL."""
    try:
        db.db_schedule(db.db_save_hourly(hourly_suit_data, hourly_game_count))
    except Exception as e:
        logger.error(f"❌ Sauvegarde données horaires: {e}")


def update_compteur7(game_number: int, player_suits: Set[str]) -> List[Dict]:
    """Met à jour Compteur7. Retourne les séries terminées (≥ seuil) dans ce jeu."""
    global compteur7_current, compteur7_completed
    newly_completed = []
    now = datetime.now()

    for suit in ALL_SUITS:
        current = compteur7_current[suit]
        if suit in player_suits:
            # Costume présent → incrémenter
            if current['count'] == 0:
                current['start_game'] = game_number
                current['start_time'] = now
            current['count'] += 1
        else:
            # Costume absent → vérifier si série terminée
            if current['count'] >= COMPTEUR7_THRESHOLD:
                series = {
                    'suit':       suit,
                    'count':      current['count'],
                    'start_game': current['start_game'],
                    'end_game':   game_number - 1,
                    'start_time': current['start_time'],
                    'end_time':   now,
                }
                compteur7_completed.append(series)
                newly_completed.append(series)
                save_compteur7_data()
                logger.info(
                    f"📊 C7: {suit} série terminée "
                    f"{series['count']}x (#{series['start_game']}→#{series['end_game']})"
                )
            # Reset le compteur
            current['count']      = 0
            current['start_game'] = None
            current['start_time'] = None

    return newly_completed


# ============================================================================
# SYSTÈME COMPTEUR8 — ABSENCES CONSÉCUTIVES (MIROIR COMPTEUR7)
# ============================================================================

def save_compteur8_data():
    """Sauvegarde les séries Compteur8 dans PostgreSQL."""
    try:
        data = {
            'completed': [
                {
                    **s,
                    'start_time': s['start_time'].isoformat(),
                    'end_time':   s['end_time'].isoformat(),
                }
                for s in compteur8_completed
            ]
        }
        db.db_schedule(db.db_save_kv('compteur8', data))
    except Exception as e:
        logger.error(f"❌ Erreur save_compteur8: {e}")


async def load_compteur8_data():
    """Charge les séries Compteur8 depuis PostgreSQL (fallback JSON)."""
    global compteur8_completed
    try:
        data = await db.db_load_kv('compteur8')
        from_json = False
        if data is None and os.path.exists(COMPTEUR8_DATA_FILE):
            with open(COMPTEUR8_DATA_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            from_json = True
        if data:
            compteur8_completed = []
            for s in data.get('completed', []):
                s['start_time'] = datetime.fromisoformat(s['start_time'])
                s['end_time']   = datetime.fromisoformat(s['end_time'])
                compteur8_completed.append(s)
            logger.info(f"✅ C8 chargé: {len(compteur8_completed)} série(s)")
            if from_json:
                save_compteur8_data()
                logger.info("📂 C8: migration JSON → PostgreSQL effectuée")
    except Exception as e:
        logger.error(f"❌ Erreur load_compteur8: {e}")


# ============================================================================
# SYSTÈME COMPTEUR14 — FRÉQUENCE ABSOLUE (cycle 1440 jeux)
# ============================================================================

def save_compteur14_data():
    """Sauvegarde l'état courant du Compteur14 dans PostgreSQL."""
    try:
        db.db_schedule(db.db_save_kv('compteur14', {
            'counts':      compteur14_counts,
            'cycle_games': compteur14_cycle_games,
            'cycle_start': compteur14_cycle_start,
        }))
    except Exception as e:
        logger.error(f"❌ Erreur save_compteur14: {e}")


async def load_compteur14_data():
    """Charge l'état du Compteur14 depuis PostgreSQL."""
    global compteur14_counts, compteur14_cycle_games, compteur14_cycle_start
    try:
        data = await db.db_load_kv('compteur14')
        if data:
            compteur14_counts      = data.get('counts', {'♠': 0, '♥': 0, '♦': 0, '♣': 0})
            compteur14_cycle_games = data.get('cycle_games', 0)
            compteur14_cycle_start = data.get('cycle_start', 0)
            logger.info(
                f"✅ C14 chargé: {compteur14_cycle_games}/{COMPTEUR14_CYCLE_SIZE} jeux "
                f"dans le cycle courant | {compteur14_counts}"
            )
        else:
            logger.info("📊 C14: aucune donnée sauvegardée, démarrage à zéro")
    except Exception as e:
        logger.error(f"❌ Erreur load_compteur14: {e}")


async def send_compteur14_report(game_number: int, is_final: bool = True):
    """
    Envoie le rapport de cycle à l'admin.
    is_final=True  → fin de cycle 1440 jeux (avant reset automatique)
    is_final=False → rapport intermédiaire sur demande /compteur14
    """
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        suit_names    = {'♠': 'Pique ♠', '♥': 'Cœur ❤️', '♦': 'Carreau ♦️', '♣': 'Trèfle ♣️'}
        total_appear  = sum(compteur14_counts.values())
        total_safe    = total_appear or 1

        header = (
            f"📊 **COMPTEUR 14 — {'BILAN CYCLE COMPLET' if is_final else 'ÉTAT INTERMÉDIAIRE'}**\n"
            f"Jeux #{compteur14_cycle_start} → #{game_number} "
            f"({compteur14_cycle_games}/{COMPTEUR14_CYCLE_SIZE})\n\n"
            "**Apparitions par costume (main joueur) :**\n"
        )

        lines = []
        for suit in ALL_SUITS:
            name  = suit_names.get(suit, suit)
            count = compteur14_counts.get(suit, 0)
            pct   = count / total_safe * 100
            bar   = "█" * int(pct / 5) + "░" * (20 - int(pct / 5))
            lines.append(f"  {name}: **{count}x** ({pct:.1f}%) [{bar}]")

        footer = (
            f"\n**Total apparitions :** {total_appear}\n"
            f"**Jeux analysés :** {compteur14_cycle_games}"
        )
        if is_final:
            footer += "\n\n_Cycle terminé — compteur remis à zéro pour le prochain cycle._"

        msg = header + "\n".join(lines) + footer
        admin_entity = await client.get_entity(ADMIN_ID)
        await client.send_message(admin_entity, msg, parse_mode='markdown')
        logger.info(f"📊 C14 rapport envoyé à l'admin (jeu #{game_number}, final={is_final})")
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur14_report: {e}")


def update_compteur14(game_number: int, player_suits: set) -> bool:
    """
    Met à jour le Compteur14 avec les costumes du jeu en cours.
    Retourne True si le cycle de COMPTEUR14_CYCLE_SIZE jeux vient de se terminer.
    """
    global compteur14_counts, compteur14_cycle_games, compteur14_cycle_start

    if compteur14_cycle_games == 0:
        compteur14_cycle_start = game_number

    for suit in player_suits:
        if suit in compteur14_counts:
            compteur14_counts[suit] += 1

    compteur14_cycle_games += 1

    if compteur14_cycle_games % 50 == 0:
        save_compteur14_data()

    return compteur14_cycle_games >= COMPTEUR14_CYCLE_SIZE


def reset_compteur14():
    """Remet le Compteur14 à zéro après rapport ou sur demande admin."""
    global compteur14_counts, compteur14_cycle_games, compteur14_cycle_start
    compteur14_counts      = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
    compteur14_cycle_games = 0
    compteur14_cycle_start = 0
    save_compteur14_data()


def update_compteur8(game_number: int, player_suits: Set[str]) -> List[Dict]:
    """
    Met à jour Compteur8 (absences consécutives) — miroir exact du Compteur7.
    C7 : présent → streak++, absent → fin de série si ≥ seuil
    C8 : absent  → streak++, présent → fin de série si ≥ seuil
    Retourne les séries terminées (≥ COMPTEUR8_THRESHOLD) dans ce jeu.
    """
    global compteur8_current, compteur8_completed
    newly_completed = []
    now = datetime.now()

    for suit in ALL_SUITS:
        cur = compteur8_current[suit]
        if suit not in player_suits:
            # Costume absent → incrémenter le streak d'absence
            if cur['count'] == 0:
                cur['start_game'] = game_number
                cur['start_time'] = now
            cur['count'] += 1
        else:
            # Costume présent → streak d'absence terminé
            if cur['count'] >= COMPTEUR8_THRESHOLD:
                series = {
                    'suit':       suit,
                    'count':      cur['count'],
                    'start_game': cur['start_game'],
                    'end_game':   game_number - 1,
                    'start_time': cur['start_time'],
                    'end_time':   now,
                }
                compteur8_completed.append(series)
                newly_completed.append(series)
                save_compteur8_data()
                logger.info(
                    f"📊 C8: {suit} absence terminée "
                    f"{series['count']}x (#{series['start_game']}→#{series['end_game']})"
                )
            # Reset dans tous les cas (streak d'absence terminé)
            cur['count']      = 0
            cur['start_game'] = None
            cur['start_time'] = None

    return newly_completed


# ============================================================================
# SYSTÈME COMPTEUR13 — CONSÉCUTIFS + MIROIR VALIDÉ PAR C2
# ============================================================================

def update_compteur13(game_number: int, player_suits: Set[str]) -> List[Dict]:
    """
    Compteur13 — Consécutifs + Miroir.

    Pour chaque costume X qui atteint wx apparitions consécutives :
      1. Calcule miroir(X) selon COMPTEUR13_MIRROR actif.
      2. Consulte C2 (trackers globaux) : le miroir a-t-il atteint le seuil B ?
           OUI → bloque la prédiction réelle (c2_mirror_blocked=True)
           NON → prédit miroir(X) au jeu current + df
    Les 216 trackers silencieux ont leur propre C2 interne et appliquent
    la même règle de blocage indépendamment.
    """
    global compteur13_trackers, compteur13_start, COMPTEUR13_THRESHOLD, COMPTEUR13_SKIP

    triggers = []
    for suit in ALL_SUITS:
        if suit in player_suits:
            if compteur13_trackers[suit] == 0:
                compteur13_start[suit] = game_number
            compteur13_trackers[suit] += 1
            logger.debug(f"🎯 C13 {suit}: {compteur13_trackers[suit]} consécutif(s) (jeu #{game_number})")

            if compteur13_trackers[suit] >= COMPTEUR13_THRESHOLD:
                miroir      = COMPTEUR13_MIRROR[suit]  # costume prédit = miroir de X
                suit_pred   = miroir
                game_offset = PREDICTION_DF + COMPTEUR13_SKIP   # +1 si mode saut activé

                # Consulter C2 : le miroir est-il un manque bloqué (absent ≥ B fois) ?
                c2_miroir_tracker = compteur2_trackers.get(miroir)
                b_val_miroir      = compteur2_seuil_B_per_suit.get(miroir, compteur2_seuil_B)
                c2_mirror_blocked = (
                    c2_miroir_tracker is not None
                    and c2_miroir_tracker.check_threshold(b_val_miroir)
                )

                triggers.append({
                    'suit_consec':       suit,
                    'suit_pred':         suit_pred,
                    'suit_miroir':       miroir,
                    'game_start':        compteur13_start[suit],
                    'game_trigger':      game_number,
                    'count':             compteur13_trackers[suit],
                    'game_offset':       game_offset,
                    'c2_mirror_blocked': c2_mirror_blocked,
                    'b_val_miroir':      b_val_miroir,
                    'c2_absence_count':  c2_miroir_tracker.counter if c2_miroir_tracker else 0,
                })
                logger.info(
                    f"🎯 C13: {suit} {compteur13_trackers[suit]}x consécutif(s) "
                    f"→ miroir={miroir} | C2_absent={c2_miroir_tracker.counter if c2_miroir_tracker else 0}"
                    f"/B={b_val_miroir} | miroir_bloqué={c2_mirror_blocked}"
                )
                compteur13_trackers[suit] = 0
                compteur13_start[suit] = 0
        else:
            if compteur13_trackers[suit] > 0:
                logger.debug(f"🔄 C13 {suit}: reset (était {compteur13_trackers[suit]}x)")
            compteur13_trackers[suit] = 0
            compteur13_start[suit] = 0
    return triggers


# ============================================================================
# 216 TRACKERS SILENCIEUX INDÉPENDANTS
# ============================================================================

def init_silent_combo_states(saved_stats: Optional[Dict] = None):
    """
    Initialise (ou réinitialise) les 216 états de trackers indépendants.
    Chaque clé (combo_num, wx, b, df_sim) a son propre C13 + C2.
    saved_stats : dict chargé depuis la DB pour restaurer wins/losses/historique.
    """
    global silent_combo_states
    _WX = range(3, 9)
    _B  = range(3, 9)
    for c in GLOBAL_COMBOS:
        for wx in _WX:
            for b in _B:
                for df_sim in (1, 2):
                    key  = (c['num'], wx, b, df_sim)
                    skey = f"{c['num']}:{wx}:{b}:{df_sim}"
                    saved = (saved_stats or {}).get(skey, {})
                    silent_combo_states[key] = {
                        'c13':          {s: 0 for s in ALL_SUITS},
                        'c13_start':    {s: 0 for s in ALL_SUITS},
                        'c2':           {s: 0 for s in ALL_SUITS},
                        'pending':      [],
                        'wins':         saved.get('wins',   0),
                        'losses':       saved.get('losses', 0),
                        'total':        saved.get('total',  0),
                        'pred_history': list(saved.get('pred_history', [])),
                    }
    logger.info(f"🔢 216 trackers silencieux initialisés ({len(silent_combo_states)} entrées)")


def update_silent_combos(game_number: int, player_suits: Set[str]):
    """
    Met à jour les 216 trackers indépendants pour le jeu terminé.
    Appelé UNE fois par jeu (player_hand_complete).
    """
    for key, state in silent_combo_states.items():
        combo_num, wx, b, df_sim = key
        mirror = GLOBAL_COMBOS_BY_NUM[combo_num]['mirror']

        # ── 1. Résoudre les prédictions en attente (avec rattrapage R0→R1→R2) ─
        still_pending = []
        for pred in state['pending']:
            pg          = pred['pred_game']
            rattrapage  = pred.get('rattrapage', 0)
            if pg == game_number:
                won = pred['suit'] in player_suits
                if won:
                    # ✅ Victoire (peu importe le rattrapage)
                    state['wins']  += 1
                    state['total'] += 1
                    hist = {
                        'gn':      game_number,
                        'suit':    pred['suit'],
                        'trigger': pred['trigger'],
                        'win':     True,
                        'r':       rattrapage,
                        'df_sim':  df_sim,
                    }
                    state['pred_history'].append(hist)
                    if len(state['pred_history']) > 60:
                        state['pred_history'].pop(0)
                elif rattrapage < 2:
                    # ❌ Échec — passage au rattrapage suivant (R1 ou R2)
                    pred['pred_game']  = game_number + 1
                    pred['rattrapage'] = rattrapage + 1
                    still_pending.append(pred)
                else:
                    # ❌ Perdu définitivement (R2 épuisé)
                    state['losses'] += 1
                    state['total']  += 1
                    hist = {
                        'gn':      game_number,
                        'suit':    pred['suit'],
                        'trigger': pred['trigger'],
                        'win':     False,
                        'r':       2,
                        'df_sim':  df_sim,
                    }
                    state['pred_history'].append(hist)
                    if len(state['pred_history']) > 60:
                        state['pred_history'].pop(0)
            elif pg < game_number:
                # Jeu attendu sauté par l'API → perte immédiate
                state['losses'] += 1
                state['total']  += 1
                hist = {
                    'gn':      pg,
                    'suit':    pred['suit'],
                    'trigger': pred['trigger'],
                    'win':     False,
                    'r':       rattrapage,
                    'df_sim':  df_sim,
                }
                state['pred_history'].append(hist)
                if len(state['pred_history']) > 60:
                    state['pred_history'].pop(0)
            else:
                still_pending.append(pred)
        state['pending'] = still_pending

        # ── 2. Mettre à jour C2 (absences consécutives — propre à ce tracker) ──
        for suit in ALL_SUITS:
            if suit in player_suits:
                state['c2'][suit] = 0       # présent → reset absence
            else:
                state['c2'][suit] += 1      # absent → incrément

        # ── 3. Mettre à jour C13 et détecter déclenchement ──────────────────
        for suit in ALL_SUITS:
            if suit in player_suits:
                if state['c13'][suit] == 0:
                    state['c13_start'][suit] = game_number
                state['c13'][suit] += 1

                if state['c13'][suit] >= wx:
                    # Déclenchement C13 → vérifier C2 sur le miroir (bloqueur)
                    mirror_suit = mirror.get(suit, suit)
                    c2_abs      = state['c2'].get(mirror_suit, 0)
                    if c2_abs < b:
                        # C2 ne bloque pas → prédiction silencieuse
                        state['pending'].append({
                            'pred_game':  game_number + df_sim,
                            'suit':       mirror_suit,
                            'trigger':    game_number,
                            'rattrapage': 0,
                        })
                    # Reset C13 après déclenchement (qu'il soit bloqué ou non)
                    state['c13'][suit]       = 0
                    state['c13_start'][suit] = 0
            else:
                state['c13'][suit]       = 0
                state['c13_start'][suit] = 0


async def save_silent_combo_stats():
    """Persiste les wins/losses/pred_history des 216 trackers en DB."""
    global silent_combo_states
    if not silent_combo_states:
        return
    try:
        payload = {}
        for key, state in silent_combo_states.items():
            combo_num, wx, b, df_sim = key
            skey = f"{combo_num}:{wx}:{b}:{df_sim}"
            payload[skey] = {
                'wins':         state['wins'],
                'losses':       state['losses'],
                'total':        state['total'],
                'pred_history': state['pred_history'][-40:],  # 40 dernières
            }
        await db.db_save_kv('silent_combo_stats', payload)
        logger.debug("💾 216 trackers silencieux sauvegardés en DB")
    except Exception as e:
        logger.error(f"❌ save_silent_combo_stats: {e}")


async def load_silent_combo_stats():
    """Charge les stats des 216 trackers depuis la DB et initialise les états."""
    global silent_combo_states
    try:
        data = await db.db_load_kv('silent_combo_stats')
        saved = data if isinstance(data, dict) else {}
        init_silent_combo_states(saved_stats=saved)
        total_preds = sum(s['total'] for s in silent_combo_states.values())
        logger.info(f"📂 216 trackers silencieux chargés · {total_preds} prédictions totales")
    except Exception as e:
        logger.error(f"❌ load_silent_combo_stats: {e}")
        init_silent_combo_states()


async def send_compteur13_alert(trigger: Dict, current_game: int):
    """Envoie la prédiction C13 au canal (sans filtre C6)."""
    try:
        suit_consec   = trigger['suit_consec']
        suit_pred     = trigger['suit_pred']
        suit_miroir   = trigger['suit_miroir']
        game_start    = trigger['game_start']
        game_trigger  = trigger['game_trigger']
        count         = trigger['count']
        game_offset   = trigger.get('game_offset', PREDICTION_DF)
        consec_disp = SUIT_DISPLAY.get(suit_consec, suit_consec)
        miroir_disp = SUIT_DISPLAY.get(suit_miroir, suit_miroir)
        pred_game   = current_game + game_offset

        reason = (
            f"C13 : {consec_disp} apparu {count} fois de suite "
            f"(jeux #{game_start}→#{game_trigger}, seuil wx={COMPTEUR13_THRESHOLD}). "
            f"Miroir prédit : {miroir_disp} au jeu #{pred_game}. "
            "C2 vérifié (miroir non bloqué) → prédiction lancée."
        )

        c13_meta = {
            'suit_consec':  suit_consec,
            'suit_miroir':  suit_miroir,
            'game_offset':  game_offset,
            'count':        count,
        }
        added = add_to_prediction_queue(
            pred_game, suit_pred, 'compteur13', reason,
            trigger_game=game_trigger, skip_c6=True, meta=c13_meta
        )
        if added:
            logger.info(f"🎯 C13: prédiction #{pred_game} {suit_pred} en file")
            await send_prediction_multi_channel(pred_game, suit_pred, 'compteur13', skip_c6=True, meta=c13_meta)
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur13_alert: {e}")


# ============================================================================
def generate_compteur8_pdf() -> bytes:
    """Génère un PDF combiné : Compteur8 (absences ≥10) + Compteur7 (présences ≥5) + comparaison."""
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors    = {'♠': (30, 30, 30), '♥': (180, 0, 0), '♦': (0, 80, 180), '♣': (0, 120, 0)}

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)

    # ── PAGE 1 : COMPTEUR8 — ABSENCES ────────────────────────────────────────
    pdf.add_page()
    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(180, 0, 0)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Compteur 8 : Absences Consecutives', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Absences >= {COMPTEUR8_THRESHOLD}x consecutives | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | '
        f'Total: {len(compteur8_completed)} serie(s) | PERSISTANT', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    col_widths8 = [32, 22, 22, 32, 32, 26]
    headers8    = ['Costume', 'Date debut', 'Heure debut', 'Jeu debut', 'Jeu fin', 'Nb absents']

    pdf.set_font('Helvetica', 'B', 9)
    pdf.set_fill_color(220, 50, 50)
    pdf.set_text_color(255, 255, 255)
    for w, h in zip(col_widths8, headers8):
        pdf.cell(w, 8, h, border=1, align='C', fill=True)
    pdf.ln()

    if compteur8_completed:
        for i, s in enumerate(sorted(compteur8_completed, key=lambda x: x['start_time'])):
            suit = s['suit']
            color = suit_colors.get(suit, (0, 0, 0))
            pdf.set_fill_color(245, 245, 245) if i % 2 == 0 else pdf.set_fill_color(255, 255, 255)
            pdf.set_text_color(*color)
            pdf.set_font('Helvetica', 'B', 9)
            row = [
                suit_names_map.get(suit, suit),
                s['start_time'].strftime('%d/%m/%Y'),
                s['start_time'].strftime('%Hh%M'),
                f"#{s['start_game']}",
                f"#{s['end_game']}",
                str(s['count']),
            ]
            fills = [True] + [False] * (len(col_widths8) - 1)
            for w, cell, fl in zip(col_widths8, row, fills):
                pdf.cell(w, 7, cell, border=1, align='C', fill=fl)
            pdf.ln()
    else:
        pdf.set_text_color(150, 150, 150)
        pdf.set_font('Helvetica', 'I', 10)
        pdf.cell(0, 10, 'Aucune serie d absence >= 10 enregistree.', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    # ── PAGE 2 : COMPTEUR7 — PRÉSENCES ───────────────────────────────────────
    pdf.add_page()
    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(90, 0, 160)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Compteur 7 : Presences Consecutives', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Serie enregistree >= {COMPTEUR7_THRESHOLD}x | '
        f'Total: {len(compteur7_completed)} serie(s) | PERSISTANT', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    col_widths7 = [32, 22, 22, 32, 32, 26]
    headers7    = ['Costume', 'Date debut', 'Heure debut', 'Jeu debut', 'Jeu fin', 'Nb presents']

    pdf.set_font('Helvetica', 'B', 9)
    pdf.set_fill_color(90, 0, 160)
    pdf.set_text_color(255, 255, 255)
    for w, h in zip(col_widths7, headers7):
        pdf.cell(w, 8, h, border=1, align='C', fill=True)
    pdf.ln()

    if compteur7_completed:
        for i, s in enumerate(sorted(compteur7_completed, key=lambda x: x['start_time'])):
            suit = s['suit']
            color = suit_colors.get(suit, (0, 0, 0))
            pdf.set_fill_color(245, 245, 245) if i % 2 == 0 else pdf.set_fill_color(255, 255, 255)
            pdf.set_text_color(*color)
            pdf.set_font('Helvetica', 'B', 9)
            row = [
                suit_names_map.get(suit, suit),
                s['start_time'].strftime('%d/%m/%Y'),
                s['start_time'].strftime('%Hh%M'),
                f"#{s['start_game']}",
                f"#{s['end_game']}",
                str(s['count']),
            ]
            fills = [True] + [False] * (len(col_widths7) - 1)
            for w, cell, fl in zip(col_widths7, row, fills):
                pdf.cell(w, 7, cell, border=1, align='C', fill=fl)
            pdf.ln()
    else:
        pdf.set_text_color(150, 150, 150)
        pdf.set_font('Helvetica', 'I', 10)
        pdf.cell(0, 10, 'Aucune serie de presences >= 5 enregistree.', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    # ── PAGE 3 : TABLEAU COMPARATIF C8 vs C7 ─────────────────────────────────
    pdf.add_page()
    pdf.set_font('Helvetica', 'B', 14)
    pdf.set_fill_color(50, 50, 50)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'COMPARAISON : C8 (Absences) vs C7 (Presences)', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(6)

    cmp_headers = ['Costume', 'C8 series', 'C8 max abs.', 'C8 moy abs.', 'C7 series', 'C7 max pres.', 'C7 moy pres.']
    cmp_widths  = [26, 22, 26, 26, 22, 28, 28]
    pdf.set_font('Helvetica', 'B', 9)
    pdf.set_text_color(255, 255, 255)
    pdf.set_fill_color(70, 70, 70)
    for w, h in zip(cmp_widths, cmp_headers):
        pdf.cell(w, 8, h, border=1, align='C', fill=True)
    pdf.ln()

    pdf.set_font('Helvetica', '', 9)
    for idx, suit in enumerate(ALL_SUITS):
        c8_s = [s for s in compteur8_completed if s['suit'] == suit]
        c7_s = [s for s in compteur7_completed if s['suit'] == suit]
        c8_max = max((s['count'] for s in c8_s), default=0)
        c7_max = max((s['count'] for s in c7_s), default=0)
        c8_moy = round(sum(s['count'] for s in c8_s) / len(c8_s), 1) if c8_s else 0
        c7_moy = round(sum(s['count'] for s in c7_s) / len(c7_s), 1) if c7_s else 0
        color = suit_colors.get(suit, (0, 0, 0))
        pdf.set_text_color(*color)
        pdf.set_fill_color(245, 245, 245) if idx % 2 == 0 else pdf.set_fill_color(255, 255, 255)
        row = [
            suit_names_map.get(suit, suit),
            str(len(c8_s)), str(c8_max), str(c8_moy),
            str(len(c7_s)), str(c7_max), str(c7_moy),
        ]
        for w, cell in zip(cmp_widths, row):
            pdf.cell(w, 7, cell, border=1, align='C', fill=False)
        pdf.ln()

    pdf.ln(8)
    pdf.set_text_color(80, 80, 80)
    pdf.set_font('Helvetica', 'I', 8)
    pdf.cell(0, 5,
        f'C8 = absences >= {COMPTEUR8_THRESHOLD} consecutives | '
        f'C7 = presences >= {COMPTEUR7_THRESHOLD} consecutives | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")}', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )

    return bytes(pdf.output())


async def send_compteur8_series_alert(series: Dict):
    """
    Notifie l'admin quand une série d'absences ≥ COMPTEUR8_THRESHOLD se termine.
    Format identique à send_compteur7_alert mais pour les absences.
    """
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
        suit_emoji_map = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
        suit  = series['suit']
        emoji = suit_emoji_map.get(suit, suit)
        end_t = series['end_time']
        msg = (
            "📊 **COMPTEUR 8 — SÉRIE TERMINÉE**\n\n"
            f"{end_t.strftime('%d/%m/%Y')} à {end_t.strftime('%Hh%M')} "
            f"{emoji} **{series['count']} fois** du numéro "
            f"**{series['start_game']}_{series['end_game']}**\n\n"
            f"_{suit_names_map.get(suit, suit)} absent {series['count']} fois consécutives._\n\n"
            "📄 PDF mis à jour ci-dessous."
        )
        admin_entity = await client.get_entity(ADMIN_ID)
        await client.send_message(admin_entity, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur8_series_alert: {e}")


async def send_compteur8_pred_alert(
    suit: str,
    trigger_game: int,
    pred_game: int,
    reason: str,
    blocked_others: List[str],
):
    """
    C8 PRÉDICTION : envoie la prédiction du costume manquant au jeu suivant.
    C8 s'impose sur C2 et C13 — les prédictions bloquées sont listées dans la raison.
    """
    try:
        suit_disp = SUIT_DISPLAY.get(suit, suit)
        added = add_to_prediction_queue(
            pred_game, suit, 'compteur8_pred', reason,
            trigger_game=trigger_game, skip_c6=True
        )
        if added:
            logger.info(f"🔴 C8 PRED: #{pred_game} {suit} en file (trigger #{trigger_game})")
            await send_prediction_multi_channel(pred_game, suit, 'compteur8_pred', skip_c6=True)

        # Informer l'admin si C8 a bloqué d'autres compteurs
        if blocked_others and ADMIN_ID:
            try:
                blocked_str = ', '.join(blocked_others)
                admin_entity = await client.get_entity(ADMIN_ID)
                await client.send_message(
                    admin_entity,
                    f"🔴 **C8 IMPOSITION — Jeu #{trigger_game}**\n\n"
                    f"{suit_disp} absent **{COMPTEUR8_PRED_SEUIL}x** consécutivement → "
                    f"C8 prédit {suit_disp} au jeu **#{pred_game}**.\n\n"
                    f"⛔ Bloqué(s) : **{blocked_str}**\n"
                    f"_Raison : C8 a atteint le seuil {COMPTEUR8_PRED_SEUIL} et s'est imposé._",
                    parse_mode='markdown'
                )
            except Exception:
                pass
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur8_pred_alert: {e}")


async def send_compteur8_pdf():
    """Génère et envoie (ou remplace) le PDF comparatif Compteur8/Compteur7 à l'admin."""
    global compteur8_pdf_msg_id
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        pdf_bytes  = generate_compteur8_pdf()
        pdf_buffer = io.BytesIO(pdf_bytes)
        pdf_buffer.name = "compteur8_vs_compteur7.pdf"
        admin_entity = await client.get_entity(ADMIN_ID)

        if compteur8_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [compteur8_pdf_msg_id])
            except Exception:
                pass
            compteur8_pdf_msg_id = None

        caption = (
            "📊 **COMPTEUR8 vs COMPTEUR7 — PDF mis à jour**\n\n"
            f"C8 absences (≥{COMPTEUR8_THRESHOLD}x) : **{len(compteur8_completed)}** série(s)\n"
            f"C7 présences (≥{COMPTEUR7_THRESHOLD}x) : **{len(compteur7_completed)}** série(s)\n"
            "⚠️ Ce PDF persiste entre tous les resets\n"
            f"Mis à jour : {datetime.now().strftime('%d/%m/%Y %Hh%M')}"
        )
        sent = await client.send_file(
            admin_entity, pdf_buffer,
            caption=caption, parse_mode='markdown',
            attributes=[], file_name="compteur8_vs_compteur7.pdf"
        )
        compteur8_pdf_msg_id = sent.id
        logger.info("✅ PDF Compteur8/C7 envoyé à l'admin")
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur8_pdf: {e}")
        import traceback; logger.error(traceback.format_exc())


def generate_compteur8_only_pdf() -> bytes:
    """Génère un PDF uniquement Compteur8 — absences consécutives (sans C7)."""
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors    = {'♠': (30, 30, 30), '♥': (180, 0, 0), '♦': (0, 80, 180), '♣': (0, 120, 0)}

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(180, 0, 0)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Compteur 8 : Absences Consecutives', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Absences >= {COMPTEUR8_THRESHOLD}x consecutives | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | '
        f'Total: {len(compteur8_completed)} serie(s) | PERSISTANT', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    col_widths = [32, 22, 22, 32, 32, 26]
    headers    = ['Costume', 'Date debut', 'Heure debut', 'Jeu debut', 'Jeu fin', 'Nb absents']

    pdf.set_font('Helvetica', 'B', 9)
    pdf.set_fill_color(220, 50, 50)
    pdf.set_text_color(255, 255, 255)
    for w, h in zip(col_widths, headers):
        pdf.cell(w, 8, h, border=1, align='C', fill=True)
    pdf.ln()

    if compteur8_completed:
        for i, s in enumerate(sorted(compteur8_completed, key=lambda x: x['start_time'])):
            suit  = s['suit']
            color = suit_colors.get(suit, (0, 0, 0))
            pdf.set_fill_color(245, 245, 245) if i % 2 == 0 else pdf.set_fill_color(255, 255, 255)
            pdf.set_text_color(*color)
            pdf.set_font('Helvetica', 'B', 9)
            row = [
                suit_names_map.get(suit, suit),
                s['start_time'].strftime('%d/%m/%Y'),
                s['start_time'].strftime('%Hh%M'),
                f"#{s['start_game']}",
                f"#{s['end_game']}",
                str(s['count']),
            ]
            fills = [True] + [False] * (len(col_widths) - 1)
            for w, cell, fl in zip(col_widths, row, fills):
                pdf.cell(w, 7, cell, border=1, align='C', fill=fl)
            pdf.ln()
    else:
        pdf.set_text_color(150, 150, 150)
        pdf.set_font('Helvetica', 'I', 10)
        pdf.cell(0, 10, f'Aucune serie d absence >= {COMPTEUR8_THRESHOLD} enregistree.', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    return bytes(pdf.output())


async def send_compteur8_only_pdf():
    """Envoie uniquement le PDF Compteur8 (absences) à l'admin."""
    global compteur8_pdf_msg_id
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        pdf_bytes  = generate_compteur8_only_pdf()
        pdf_buffer = io.BytesIO(pdf_bytes)
        pdf_buffer.name = "compteur8_absences.pdf"
        admin_entity = await client.get_entity(ADMIN_ID)

        if compteur8_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [compteur8_pdf_msg_id])
            except Exception:
                pass
            compteur8_pdf_msg_id = None

        caption = (
            f"📊 **COMPTEUR8 — Absences ≥{COMPTEUR8_THRESHOLD}x**\n"
            f"Total : **{len(compteur8_completed)}** série(s)\n"
            f"Mis à jour : {datetime.now().strftime('%d/%m/%Y %Hh%M')}"
        )
        sent = await client.send_file(
            admin_entity, pdf_buffer,
            caption=caption, parse_mode='markdown',
            attributes=[], file_name="compteur8_absences.pdf"
        )
        compteur8_pdf_msg_id = sent.id
        logger.info("✅ PDF Compteur8 seul envoyé à l'admin")
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur8_only_pdf: {e}")


def generate_comparaison_c8_pdf(nb_jours: int) -> bytes:
    """Génère un PDF de comparaison C8 (absences) jour par jour — toutes les données préservées."""
    from datetime import timedelta, date as date_type
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors    = {'♠': (30, 30, 30), '♥': (180, 0, 0), '♦': (0, 80, 180), '♣': (0, 120, 0)}

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=12)
    pdf.add_page()

    pdf.set_font('Helvetica', 'B', 15)
    pdf.set_fill_color(180, 0, 0)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 11, f'COMPARAISON C8 — Absences sur {nb_jours} jours', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(3)
    pdf.set_font('Helvetica', '', 9)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 5, f'Absences >= {COMPTEUR8_THRESHOLD}x | Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | Toutes donnees preservees', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.ln(5)

    today = datetime.now().date()
    col_w = [28, 22, 20, 28, 28, 22]
    headers = ['Costume', 'Date debut', 'H. debut', 'Jeu debut', 'Jeu fin', 'Nb absents']

    for d in range(nb_jours):
        target     = today - timedelta(days=d)
        label      = f"Aujourd'hui ({target.strftime('%d/%m/%Y')})" if d == 0 else f"J-{d} — {target.strftime('%d/%m/%Y')}"
        day_series = sorted([s for s in compteur8_completed if s['end_time'].date() == target], key=lambda x: x['start_time'])

        # En-tête du jour
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_fill_color(220, 50, 50)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(0, 8, f'  {label}  —  {len(day_series)} serie(s)', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
        pdf.ln(1)

        if not day_series:
            pdf.set_font('Helvetica', 'I', 9)
            pdf.set_text_color(150, 150, 150)
            pdf.cell(0, 6, '  Aucune serie d absence enregistree ce jour.', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            pdf.ln(3)
            continue

        # En-têtes de colonnes
        pdf.set_font('Helvetica', 'B', 8)
        pdf.set_fill_color(240, 200, 200)
        pdf.set_text_color(60, 0, 0)
        for w, h in zip(col_w, headers):
            pdf.cell(w, 7, h, border=1, align='C', fill=True)
        pdf.ln()

        # Lignes de données — TOUTES, aucune limite
        pdf.set_font('Helvetica', '', 8)
        for i, s in enumerate(day_series):
            suit  = s['suit']
            color = suit_colors.get(suit, (0, 0, 0))
            pdf.set_text_color(*color)
            bg = (250, 245, 245) if i % 2 == 0 else (255, 255, 255)
            pdf.set_fill_color(*bg)
            row = [
                suit_names_map.get(suit, suit),
                s['start_time'].strftime('%d/%m/%Y'),
                s['start_time'].strftime('%Hh%M'),
                f"#{s['start_game']}",
                f"#{s['end_game']}",
                str(s['count']),
            ]
            for w, cell in zip(col_w, row):
                pdf.cell(w, 6, cell, border=1, align='C', fill=True)
            pdf.ln()

        # Résumé par costume pour ce jour
        pdf.ln(2)
        pdf.set_font('Helvetica', 'I', 8)
        pdf.set_text_color(80, 80, 80)
        for suit in ALL_SUITS:
            ss = [x for x in day_series if x['suit'] == suit]
            if ss:
                maxi = max(x['count'] for x in ss)
                moy  = round(sum(x['count'] for x in ss) / len(ss), 1)
                pdf.cell(0, 5, f"  {suit_names_map.get(suit, suit)}: {len(ss)} serie(s) | max={maxi} | moy={moy}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.ln(4)

    return bytes(pdf.output())


def generate_comparaison_c7_pdf(nb_jours: int) -> bytes:
    """Génère un PDF de comparaison C7 (présences) jour par jour — toutes les données préservées."""
    from datetime import timedelta
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors    = {'♠': (30, 30, 30), '♥': (180, 0, 0), '♦': (0, 80, 180), '♣': (0, 120, 0)}

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=12)
    pdf.add_page()

    pdf.set_font('Helvetica', 'B', 15)
    pdf.set_fill_color(90, 0, 160)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 11, f'COMPARAISON C7 — Presences sur {nb_jours} jours', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(3)
    pdf.set_font('Helvetica', '', 9)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 5, f'Presences >= {COMPTEUR7_THRESHOLD}x | Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | Toutes donnees preservees', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.ln(5)

    today = datetime.now().date()
    col_w = [28, 22, 20, 28, 28, 22]
    headers = ['Costume', 'Date debut', 'H. debut', 'Jeu debut', 'Jeu fin', 'Nb presents']

    for d in range(nb_jours):
        target     = today - timedelta(days=d)
        label      = f"Aujourd'hui ({target.strftime('%d/%m/%Y')})" if d == 0 else f"J-{d} — {target.strftime('%d/%m/%Y')}"
        day_series = sorted([s for s in compteur7_completed if s['end_time'].date() == target], key=lambda x: x['start_time'])

        # En-tête du jour
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_fill_color(90, 0, 160)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(0, 8, f'  {label}  —  {len(day_series)} serie(s)', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
        pdf.ln(1)

        if not day_series:
            pdf.set_font('Helvetica', 'I', 9)
            pdf.set_text_color(150, 150, 150)
            pdf.cell(0, 6, '  Aucune serie de presences enregistree ce jour.', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            pdf.ln(3)
            continue

        # En-têtes de colonnes
        pdf.set_font('Helvetica', 'B', 8)
        pdf.set_fill_color(220, 200, 240)
        pdf.set_text_color(60, 0, 100)
        for w, h in zip(col_w, headers):
            pdf.cell(w, 7, h, border=1, align='C', fill=True)
        pdf.ln()

        # Lignes de données — TOUTES, aucune limite
        pdf.set_font('Helvetica', '', 8)
        for i, s in enumerate(day_series):
            suit  = s['suit']
            color = suit_colors.get(suit, (0, 0, 0))
            pdf.set_text_color(*color)
            bg = (248, 245, 255) if i % 2 == 0 else (255, 255, 255)
            pdf.set_fill_color(*bg)
            row = [
                suit_names_map.get(suit, suit),
                s['start_time'].strftime('%d/%m/%Y'),
                s['start_time'].strftime('%Hh%M'),
                f"#{s['start_game']}",
                f"#{s['end_game']}",
                str(s['count']),
            ]
            for w, cell in zip(col_w, row):
                pdf.cell(w, 6, cell, border=1, align='C', fill=True)
            pdf.ln()

        # Résumé par costume pour ce jour
        pdf.ln(2)
        pdf.set_font('Helvetica', 'I', 8)
        pdf.set_text_color(80, 80, 80)
        for suit in ALL_SUITS:
            ss = [x for x in day_series if x['suit'] == suit]
            if ss:
                maxi = max(x['count'] for x in ss)
                moy  = round(sum(x['count'] for x in ss) / len(ss), 1)
                pdf.cell(0, 5, f"  {suit_names_map.get(suit, suit)}: {len(ss)} serie(s) | max={maxi} | moy={moy}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.ln(4)

    return bytes(pdf.output())


def update_hourly_data(player_suits: Set[str]):
    """Met à jour les compteurs horaires (pour /comparaison)."""
    h = datetime.now(timezone.utc).replace(tzinfo=None).hour  # UTC+0 = heure Côte d'Ivoire
    hourly_game_count[h] += 1
    for suit in player_suits:
        if suit in hourly_suit_data[h]:
            hourly_suit_data[h][suit] += 1
    # Sauvegarde toutes les 5 parties
    if hourly_game_count[h] % 5 == 0:
        save_hourly_data()


def generate_compteur7_pdf() -> bytes:
    """Génère un PDF avec le tableau des séries consécutives Compteur7."""
    suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors    = {'♠': (30, 30, 30), '♥': (180, 0, 0), '♦': (0, 80, 180), '♣': (0, 120, 0)}
    events_list    = compteur7_completed

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    # Titre
    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(90, 0, 160)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Series Consecutives Compteur 7', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(4)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6,
        f'Seuil minimum: {COMPTEUR7_THRESHOLD}x | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")} | '
        f'Total: {len(events_list)} serie(s) | PERSISTANT', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    col_widths = [32, 22, 22, 32, 32, 26]
    headers    = ['Date', 'Heure', 'Costume', 'Debut', 'Fin', 'Nb fois']

    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(90, 0, 160)
    pdf.set_text_color(255, 255, 255)
    for header, width in zip(headers, col_widths):
        pdf.cell(width, 9, header, border=1, fill=True, align='C')
    pdf.ln()

    pdf.set_font('Helvetica', '', 11)
    alt = False
    for ev in events_list:
        suit       = ev.get('suit', '')
        r, g, b    = suit_colors.get(suit, (0, 0, 0))
        date_str   = ev['end_time'].strftime('%d/%m/%Y')
        time_str   = ev['end_time'].strftime('%Hh%M')
        suit_name  = suit_names_map.get(suit, suit)
        start_str  = f"#{ev['start_game']}"
        end_str    = f"#{ev['end_game']}"
        count_str  = f"{ev['count']}x"

        bg = (245, 245, 245) if alt else (255, 255, 255)
        pdf.set_fill_color(*bg)
        pdf.set_text_color(0, 0, 0)

        pdf.cell(col_widths[0], 9, date_str, border=1, fill=alt, align='C')
        pdf.cell(col_widths[1], 9, time_str, border=1, fill=alt, align='C')

        pdf.set_text_color(r, g, b)
        pdf.set_font('Helvetica', 'B', 11)
        pdf.cell(col_widths[2], 9, suit_name, border=1, fill=alt, align='C')
        pdf.set_font('Helvetica', '', 11)
        pdf.set_text_color(0, 0, 0)

        pdf.cell(col_widths[3], 9, start_str, border=1, fill=alt, align='C')
        pdf.cell(col_widths[4], 9, end_str,   border=1, fill=alt, align='C')

        pdf.set_text_color(r, g, b)
        pdf.set_font('Helvetica', 'B', 12)
        pdf.cell(col_widths[5], 9, count_str, border=1, fill=alt, align='C')
        pdf.set_font('Helvetica', '', 11)
        pdf.set_text_color(0, 0, 0)

        pdf.ln()
        alt = not alt

    if not events_list:
        pdf.set_text_color(150, 150, 150)
        pdf.cell(0, 8, 'Aucune serie enregistree', border=1, align='C')
        pdf.ln()

    # Résumé par costume
    pdf.ln(8)
    pdf.set_font('Helvetica', 'B', 12)
    pdf.set_fill_color(90, 0, 160)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 10, 'Resume par costume', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
    pdf.ln(3)

    from collections import Counter as _Counter
    suit_counts = _Counter(ev.get('suit', '') for ev in events_list)
    for suit in ['♠', '♥', '♦', '♣']:
        r, g, b = suit_colors.get(suit, (0, 0, 0))
        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_text_color(r, g, b)
        name = suit_names_map.get(suit, suit)
        cnt  = suit_counts.get(suit, 0)
        pdf.cell(0, 8, f'  {name} : {cnt} serie(s) de {COMPTEUR7_THRESHOLD}+ consecutives', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.ln(5)
    pdf.set_font('Helvetica', 'I', 9)
    pdf.set_text_color(130, 130, 130)
    pdf.cell(0, 6,
        'BACCARAT AI - PERSISTANT - Reset #1440 ne supprime PAS ce fichier - '
        f'{datetime.now().strftime("%d/%m/%Y %H:%M")}', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    return bytes(pdf.output())


async def send_compteur7_alert(series: Dict):
    """Envoie une notification à l'admin quand une série Compteur7 se termine."""
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    suit_emoji_map = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
    suit_names_map = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
    try:
        admin_entity = await client.get_entity(ADMIN_ID)
        suit     = series['suit']
        emoji    = suit_emoji_map.get(suit, suit)
        end_time = series['end_time']
        msg = (
            "📊 **COMPTEUR 7 — SÉRIE TERMINÉE**\n\n"
            f"{end_time.strftime('%d/%m/%Y')} à {end_time.strftime('%Hh%M')} "
            f"{emoji} **{series['count']} fois** du numéro "
            f"**{series['start_game']}_{series['end_game']}**\n\n"
            f"_{suit_names_map.get(suit, suit)} présent {series['count']} fois consécutives._\n\n"
            "📄 PDF mis à jour ci-dessous."
        )
        await client.send_message(admin_entity, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur7_alert: {e}")


async def send_compteur7_pdf():
    """Génère et envoie (ou remplace) le PDF Compteur7 à l'admin."""
    global compteur7_pdf_msg_id
    if not ADMIN_ID or ADMIN_ID == 0:
        return
    try:
        pdf_bytes  = generate_compteur7_pdf()
        pdf_buffer = io.BytesIO(pdf_bytes)
        pdf_buffer.name = "compteur7_series.pdf"
        admin_entity = await client.get_entity(ADMIN_ID)

        if compteur7_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [compteur7_pdf_msg_id])
            except Exception:
                pass
            compteur7_pdf_msg_id = None

        caption = (
            "📊 **COMPTEUR7 — PDF mis à jour**\n\n"
            f"Total séries enregistrées : **{len(compteur7_completed)}**\n"
            f"Seuil : **≥ {COMPTEUR7_THRESHOLD}** présences consécutives\n"
            "⚠️ Ce PDF persiste entre tous les resets\n"
            f"Mis à jour : {datetime.now().strftime('%d/%m/%Y %Hh%M')}"
        )
        sent = await client.send_file(
            admin_entity, pdf_buffer,
            caption=caption, parse_mode='markdown',
            attributes=[], file_name="compteur7_series.pdf"
        )
        compteur7_pdf_msg_id = sent.id
        logger.info("✅ PDF Compteur7 envoyé à l'admin")
    except Exception as e:
        logger.error(f"❌ Erreur send_compteur7_pdf: {e}")
        import traceback; logger.error(traceback.format_exc())


# ============================================================================
# NORMALISATION DES COSTUMES
# ============================================================================

def normalize_suit(s: str) -> str:
    """Normalise un costume API vers le format interne ('♠', '♥', '♦', '♣')."""
    s = s.strip()
    s = s.replace('\ufe0f', '')  # Retirer le variation selector
    s = s.replace('❤', '♥')
    return s

def get_player_suits(player_cards: list) -> Set[str]:
    """Extrait les costumes normalisés des cartes joueur."""
    suits = set()
    for card in player_cards:
        raw = card.get('S', '')
        normalized = normalize_suit(raw)
        if normalized in ALL_SUITS:
            suits.add(normalized)
    return suits


def _is_player_hand_complete(player_cards: list) -> bool:
    """
    Retourne True quand le joueur a FINI de tirer ses cartes.
    Le banquier ne nous concerne pas — on traite dès que le joueur est terminé.

    Règles Baccara :
      - ≥ 3 cartes joueur  → a tiré la 3ème (main définitive)
      - 2 cartes, score 6-7 → reste (ne tirera pas de 3ème carte)
      - 2 cartes, score 8-9 → naturelle (tirage impossible)
      - 2 cartes, score 0-5 → le joueur VA tirer → on attend encore
      - < 2 cartes          → distribution en cours → on attend
    """
    n = len(player_cards)
    if n >= 3:
        return True  # 3ème carte déjà tirée → joueur définitivement terminé
    if n == 2:
        score = 0
        for c in player_cards:
            r = c.get('R', 0)
            try:
                r = int(r)
            except (TypeError, ValueError):
                r = 0
            # Valeur baccara : as=1, 2-9=face, 10/J/Q/K=0
            score += r if 1 <= r <= 9 else 0
        score %= 10
        # Score 6 ou 7 → joueur reste  |  8 ou 9 → naturelle
        return score >= 6
    return False  # moins de 2 cartes → distribution non terminée

# ============================================================================
# CLASSES TRACKERS
# ============================================================================

@dataclass
class Compteur2Tracker:
    """Tracker pour le compteur2 (costumes manquants)."""
    suit: str
    counter: int = 0
    last_increment_game: int = 0

    def get_display_name(self) -> str:
        return SUIT_DISPLAY.get(self.suit, self.suit)

    def increment(self, game_number: int):
        self.counter += 1
        self.last_increment_game = game_number
        logger.info(f"📊 Compteur2 {self.suit}: {self.counter} (jeu #{game_number})")

    def reset(self, game_number: int):
        if self.counter > 0:
            logger.info(f"🔄 Compteur2 {self.suit}: reset {self.counter}→0 (jeu #{game_number})")
        self.counter = 0
        self.last_increment_game = 0

    def check_threshold(self, seuil_B: int) -> bool:
        return self.counter >= seuil_B


@dataclass
class Compteur1Tracker:
    """Tracker pour le compteur1 (costumes présents consécutivement)."""
    suit: str
    counter: int = 0
    start_game: int = 0
    last_game: int = 0

    def get_display_name(self) -> str:
        return SUIT_DISPLAY.get(self.suit, self.suit)

    def increment(self, game_number: int):
        if self.counter == 0:
            self.start_game = game_number
        self.counter += 1
        self.last_game = game_number

    def reset(self, game_number: int):
        if self.counter >= MIN_CONSECUTIVE_FOR_STATS:
            save_compteur1_series(self.suit, self.counter, self.start_game, self.last_game)
        self.counter = 0
        self.start_game = 0
        self.last_game = 0

    def get_status(self) -> str:
        if self.counter == 0:
            return "0"
        return f"{self.counter} (depuis #{self.start_game})"

# ============================================================================
# FONCTIONS COMPTEUR1
# ============================================================================

def save_compteur1_series(suit: str, count: int, start_game: int, end_game: int):
    global compteur1_history
    entry = {
        'suit': suit,
        'count': count,
        'start_game': start_game,
        'end_game': end_game,
        'timestamp': datetime.now()
    }
    compteur1_history.insert(0, entry)
    if len(compteur1_history) > 100:
        compteur1_history = compteur1_history[:100]

def get_compteur1_record(suit: str) -> int:
    max_count = 0
    for entry in compteur1_history:
        if entry['suit'] == suit and entry['count'] > max_count:
            max_count = entry['count']
    return max_count

def update_compteur1(game_number: int, player_suits: Set[str]):
    global compteur1_trackers
    for suit in ALL_SUITS:
        tracker = compteur1_trackers[suit]
        if suit in player_suits:
            tracker.increment(game_number)
        else:
            tracker.reset(game_number)

# ============================================================================
# FONCTIONS D'HISTORIQUE
# ============================================================================

def add_to_history(game_number: int, player_suits: Set[str]):
    global finalized_messages_history
    entry = {
        'timestamp': datetime.now(),
        'game_number': game_number,
        'player_suits': list(player_suits),
        'predictions_verified': []
    }
    finalized_messages_history.insert(0, entry)
    if len(finalized_messages_history) > MAX_HISTORY_SIZE:
        finalized_messages_history = finalized_messages_history[:MAX_HISTORY_SIZE]

def add_prediction_to_history(game_number: int, suit: str, verification_games: List[int], prediction_type: str = 'standard', reason: str = '', meta: Optional[Dict] = None):
    global prediction_history
    entry = {
        'predicted_game': game_number,
        'suit': suit,
        'predicted_at': datetime.now(),
        'verification_games': verification_games,
        'status': 'en_cours',
        'verified_at': None,
        'verified_by_game': None,
        'rattrapage_level': 0,
        'type': prediction_type,
        'reason': reason,
        'meta': meta or {},
    }
    prediction_history.insert(0, entry)
    if len(prediction_history) > MAX_HISTORY_SIZE:
        prediction_history = prediction_history[:MAX_HISTORY_SIZE]
    db.db_schedule(db.db_add_prediction_history(entry))


def update_prediction_in_history(game_number: int, suit: str, verified_by_game: int, rattrapage_level: int, final_status: str):
    global prediction_history, _resolved_predictions_count
    for pred in prediction_history:
        if pred['predicted_game'] == game_number and pred['suit'] == suit:
            pred['status'] = final_status
            pred['verified_at'] = datetime.now()
            pred['verified_by_game'] = verified_by_game
            pred['rattrapage_level'] = rattrapage_level
            db.db_schedule(db.db_update_prediction_history(game_number, suit, final_status, rattrapage_level, verified_by_game))
            break

    # ── Rapport formation auto : tous les FORMATION_AUTO_EVERY prédictions résolues ──
    # On compte seulement les résultats définitifs (gagne ou perdu), pas les expirations API.
    if final_status.startswith('gagne') or final_status == 'perdu':
        _resolved_predictions_count += 1
        logger.info(f"📊 Prédictions résolues : {_resolved_predictions_count} (seuil auto-formation : {FORMATION_AUTO_EVERY})")
        if _resolved_predictions_count % FORMATION_AUTO_EVERY == 0:
            logger.info(f"📢 Seuil {FORMATION_AUTO_EVERY} atteint → envoi automatique du rapport formation au canal")
            asyncio.ensure_future(_send_formation_to_canal())

def save_pending_predictions():
    """Sauvegarde les prédictions en attente dans PostgreSQL."""
    db.db_schedule(db.db_save_all_pending(pending_predictions))

async def load_pending_predictions():
    """Charge les prédictions en attente depuis PostgreSQL."""
    global pending_predictions
    try:
        loaded = await db.db_load_pending()
        pending_predictions = loaded
        logger.info(f"📂 {len(pending_predictions)} prédiction(s) en attente chargée(s)")
    except Exception as e:
        logger.error(f"❌ load_pending_predictions: {e}")
        pending_predictions = {}

async def load_prediction_history():
    """Charge l'historique des prédictions depuis PostgreSQL."""
    global prediction_history
    try:
        loaded = await db.db_load_prediction_history(limit=200)
        prediction_history = loaded
        logger.info(f"📂 {len(prediction_history)} prédiction(s) chargées depuis l'historique")
    except Exception as e:
        logger.error(f"❌ load_prediction_history: {e}")
        prediction_history = []


# ============================================================================
# SIMULATION SILENCIEUSE — PERSISTANCE EN BASE (kv_store)
# ============================================================================

def _sim_to_json(sim: dict) -> dict:
    """Convertit last_strategy_simulation en dict JSON-sérialisable."""
    sm = sim.get('sim_matrix', {})
    # clés tuples (combo, wx, b, skip) → "combo:wx:b:skip"
    sm_str = {f"{k[0]}:{k[1]}:{k[2]}:{k[3]}": v for k, v in sm.items()}

    # pred_lists : clés (combo, wx, df_sim) → "combo:wx:df_sim"
    pl = sim.get('pred_lists', {})
    pl_str = {f"{k[0]}:{k[1]}:{k[2]}": v for k, v in pl.items()}

    # combo_scores — df1_best/df2_best sont des (tuple_key, dict) → sérialiser
    cs_raw = sim.get('combo_scores', {})
    cs_ser = {}
    for cnum, sc in cs_raw.items():
        if sc is None:
            cs_ser[str(cnum)] = None
        else:
            sc_copy = dict(sc)
            for field in ('df1_best', 'df2_best'):
                pair = sc_copy.get(field)
                if pair and pair[0] is not None:
                    sc_copy[field] = {'key': list(pair[0]), 'val': pair[1]}
                else:
                    sc_copy[field] = None
            cs_ser[str(cnum)] = sc_copy

    ts = sim.get('timestamp', datetime.now())
    return {
        'timestamp':          ts.isoformat() if hasattr(ts, 'isoformat') else str(ts),
        'sim_matrix_str':     sm_str,
        'pred_lists_str':     pl_str,
        'combo_scores_ser':   cs_ser,
        'best_combo_key':     list(sim['best_combo_key']) if sim.get('best_combo_key') else None,
        'best_combo_val':     sim.get('best_combo_val'),
        'recommended_num':    sim.get('recommended_num'),
        'recommended_reason': sim.get('recommended_reason', ''),
        'total_c13':          sim.get('total_c13', 0),
        'total_analysed':     sim.get('total_analysed', 0),
        'verdict':            sim.get('verdict', ''),
        'vd':                 sim.get('vd', ''),
        'r0c': sim.get('r0c', 0), 'r1c': sim.get('r1c', 0),
        'r2c': sim.get('r2c', 0), 'r3c': sim.get('r3c', 0),
        'pdc': sim.get('pdc', 0),
    }


def _json_to_sim(data: dict) -> dict:
    """Reconstruit last_strategy_simulation depuis un dict JSON chargé."""
    # sim_matrix : clés "combo:wx:b:skip" → tuples (int, int, int, int)
    sm_str = data.get('sim_matrix_str', {})
    sm = {}
    for k_str, v in sm_str.items():
        parts = k_str.split(':')
        k = (int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3]))
        sm[k] = v

    # pred_lists : clés "combo:wx:df_sim" → (combo, wx, df_sim)
    pl_str = data.get('pred_lists_str', {})
    pl = {}
    for k_str, v in pl_str.items():
        parts = k_str.split(':')
        k = (int(parts[0]), int(parts[1]), int(parts[2]))
        pl[k] = v

    # combo_scores : clés str → int, df1_best/df2_best reconvertis
    cs_ser = data.get('combo_scores_ser', {})
    cs = {}
    for cnum_str, sc in cs_ser.items():
        cnum = int(cnum_str)
        if sc is None:
            cs[cnum] = None
        else:
            sc_copy = dict(sc)
            for field in ('df1_best', 'df2_best'):
                pair_data = sc_copy.get(field)
                if pair_data and pair_data.get('key') is not None:
                    sc_copy[field] = (tuple(pair_data['key']), pair_data['val'])
                else:
                    sc_copy[field] = (None, None)
            cs[cnum] = sc_copy

    bck_raw = data.get('best_combo_key')
    return {
        'timestamp':          datetime.fromisoformat(data.get('timestamp', datetime.now().isoformat())),
        'combos':             GLOBAL_COMBOS,
        'combo_scores':       cs,
        'sim_matrix':         sm,
        'pred_lists':         pl,
        'best_combo_key':     tuple(bck_raw) if bck_raw else None,
        'best_combo_val':     data.get('best_combo_val'),
        'param_proposals':    data.get('param_proposals', []),
        'recommended_num':    data.get('recommended_num'),
        'recommended_reason': data.get('recommended_reason', ''),
        'total_c13':          data.get('total_c13', 0),
        'total_analysed':     data.get('total_analysed', 0),
        'verdict':            data.get('verdict', ''),
        'vd':                 data.get('vd', ''),
        'r0c': data.get('r0c', 0), 'r1c': data.get('r1c', 0),
        'r2c': data.get('r2c', 0), 'r3c': data.get('r3c', 0),
        'pdc': data.get('pdc', 0),
    }


async def save_strategy_simulation():
    """Persiste last_strategy_simulation en base (kv_store)."""
    global last_strategy_simulation
    if not last_strategy_simulation:
        return
    try:
        payload = _sim_to_json(last_strategy_simulation)
        await db.db_save_kv('strategy_simulation', payload)
        logger.info("💾 Simulation silencieuse sauvegardée en DB")
    except Exception as e:
        logger.error(f"❌ save_strategy_simulation: {e}")


async def load_strategy_simulation():
    """Charge la dernière simulation silencieuse depuis la DB."""
    global last_strategy_simulation
    try:
        data = await db.db_load_kv('strategy_simulation')
        if not data:
            logger.info("📂 Simulation silencieuse : aucune donnée en DB")
            return
        last_strategy_simulation = _json_to_sim(data)
        ts = last_strategy_simulation.get('timestamp', '')
        total_c13 = last_strategy_simulation.get('total_c13', 0)
        logger.info(
            "📂 Simulation silencieuse chargée depuis DB "
            f"({total_c13} prédictions C13 · {ts})"
        )
    except Exception as e:
        logger.error(f"❌ load_strategy_simulation: {e}")
        last_strategy_simulation = {}


# ============================================================================
# AUTO-STRATÉGIE — Application automatique + bouton Annuler
# ============================================================================

async def apply_best_strategy_auto(best_auto: dict):
    """
    Applique immédiatement la meilleure configuration trouvée par la simulation.
    Envoie une notification à l'admin avec un bouton [❌ Annuler].
    Si l'admin n'annule pas, la configuration reste active indéfiniment.
    """
    global COMPTEUR13_MIRROR, COMPTEUR13_THRESHOLD, COMPTEUR13_SKIP, PREDICTION_DF
    global compteur2_seuil_B, compteur2_seuil_B_per_suit, auto_strategy_revert

    if not best_auto or not ADMIN_ID:
        return

    new_df_sim = best_auto.get('df_sim', 1)
    # SKIP = df_sim - PREDICTION_DF  (ex: df_sim=1, PREDICTION_DF=1 → SKIP=0 = normal)
    #                                  (ex: df_sim=2, PREDICTION_DF=1 → SKIP=1)
    new_skip   = max(0, new_df_sim - PREDICTION_DF)

    # ── Vérifier si un changement réel est nécessaire ───────────────────────
    same_mirror = (best_auto['mirror'] == dict(COMPTEUR13_MIRROR))
    same_wx     = (best_auto['wx']  == COMPTEUR13_THRESHOLD)
    same_b      = (best_auto['b']   == compteur2_seuil_B)
    same_df     = (new_skip          == COMPTEUR13_SKIP)
    if same_mirror and same_wx and same_b and same_df:
        logger.info("ℹ️ Auto-stratégie : paramètres déjà optimaux, aucun changement.")
        return

    # ── Sauvegarder les paramètres actuels pour permettre l'annulation ───────
    prev_mirror_name = next(
        (c['name'] for c in GLOBAL_COMBOS if c['mirror'] == dict(COMPTEUR13_MIRROR)),
        "inconnu"
    )
    auto_strategy_revert = {
        'mirror':       dict(COMPTEUR13_MIRROR),
        'wx':           COMPTEUR13_THRESHOLD,
        'b':            compteur2_seuil_B,
        'df_sim':       COMPTEUR13_SKIP,   # save current SKIP as df_sim
        'b_per_suit':   dict(compteur2_seuil_B_per_suit),
        'name_prev':    prev_mirror_name,
        'msg_id':       None,
    }

    # ── Appliquer les nouveaux paramètres ────────────────────────────────────
    old_mirror_disp = next(
        (c['disp'] for c in GLOBAL_COMBOS if c['mirror'] == dict(COMPTEUR13_MIRROR)),
        str(dict(COMPTEUR13_MIRROR))
    )
    old_wx   = COMPTEUR13_THRESHOLD
    old_b    = compteur2_seuil_B
    old_df   = COMPTEUR13_SKIP

    COMPTEUR13_MIRROR.clear()
    COMPTEUR13_MIRROR.update(best_auto['mirror'])
    COMPTEUR13_THRESHOLD = best_auto['wx']
    COMPTEUR13_SKIP      = new_skip
    compteur2_seuil_B    = best_auto['b']
    for s in ALL_SUITS:
        compteur2_seuil_B_per_suit[s] = best_auto['b']

    logger.info(
        f"🤖 Auto-stratégie appliquée : {best_auto['name']} | "
        f"miroir={dict(COMPTEUR13_MIRROR)} | wx={COMPTEUR13_THRESHOLD} | "
        f"B={compteur2_seuil_B} | df+{new_df_sim}"
    )

    # ── Construire et envoyer la notification admin ───────────────────────────
    changes  = []
    if not same_mirror:
        changes.append(f"  🔄 Miroir : {old_mirror_disp} → **{best_auto['disp']}**")
    if not same_wx:
        changes.append(f"  📏 wx C13 : {old_wx} → **{best_auto['wx']}** consécutives")
    if not same_b:
        changes.append(f"  🎚 B  C2  : {old_b} → **{best_auto['b']}** absences")
    if not same_df:
        changes.append(f"  📐 df     : df+{old_df} → **df+{new_df_sim}**")

    # Classement des 3 miroirs (rolling window) — trié par score décroissant
    mirror_ranks = best_auto.get('mirror_ranks', {})
    rank_lines = []
    medals = ['🥇', '🥈', '🥉']
    sorted_ranks = sorted(mirror_ranks.items(), key=lambda x: (x[1][0], x[1][1]), reverse=True)
    for rank_idx, (cnum, (sc, w, l, rc, _, _)) in enumerate(sorted_ranks):
        cname = GLOBAL_COMBOS_BY_NUM.get(cnum, {}).get('name', f'P{cnum}')
        medal = medals[rank_idx] if rank_idx < len(medals) else '  '
        rank_lines.append(f"  {medal} {cname} : **{sc:+d}** (✅{w} ❌{l} / {rc})")

    lines = [
        "╔══════════════════════════════╗",
        "║  🤖 STRATÉGIE AUTO-APPLIQUÉE ║",
        "╚══════════════════════════════╝",
        f"**{best_auto['name']}** · trigger+{new_df_sim}",
        "",
    ] + changes + [
        "",
        f"📊 Score glissant ({ROLLING_WINDOW} pred.) : **{best_auto['score']:+d}** pts "
        f"(✅{best_auto['wins']} | ❌{best_auto['losses']} / {best_auto['total']})",
        "",
        "📈 **Classement des 3 miroirs :**",
    ] + rank_lines + [
        "",
        "Active immédiatement — **aucune action requise**.",
        "_Appuie sur Annuler pour revenir aux paramètres précédents._",
    ]

    try:
        msg = await client.send_message(
            ADMIN_ID,
            "\n".join(lines),
            buttons=[[Button.inline("❌ Annuler", b"cancel_auto_strat")]],
            parse_mode='markdown',
        )
        auto_strategy_revert['msg_id'] = msg.id
        logger.info(f"📨 Notification auto-stratégie envoyée à l'admin (msg_id={msg.id})")
    except Exception as e:
        logger.error(f"❌ Notification auto-stratégie : {e}")


# ============================================================================
# COMPTEUR 11 — PERDU HIER → PRÉDIT DEMAIN
# ============================================================================

async def load_compteur11():
    """
    Charge C11 depuis PostgreSQL (fallback JSON).
    Si la date sauvegardée est HIER  → les perdus deviennent compteur11_perdu_hier.
    Si la date sauvegardée est AUJOURD'HUI → les perdus deviennent compteur11_perdu_today.
    """
    global compteur11_perdu_hier, compteur11_perdu_today
    today     = datetime.now().date()
    yesterday = today - timedelta(days=1)
    try:
        data = await db.db_load_kv('compteur11')
        if data is None and os.path.exists(COMPTEUR11_FILE):
            with open(COMPTEUR11_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
        if not data:
            return
        saved_date_str = data.get('date', '')
        if not saved_date_str:
            return
        saved_date = datetime.strptime(saved_date_str, '%Y-%m-%d').date()
        perdus = data.get('perdus', [])
        if saved_date == yesterday:
            compteur11_perdu_hier  = perdus
            compteur11_perdu_today = []
            logger.info(f"📋 C11 chargé: {len(perdus)} perdus d'hier ({saved_date_str})")
        elif saved_date == today:
            compteur11_perdu_today = perdus
            compteur11_perdu_hier  = []
            logger.info(f"📋 C11 chargé: {len(perdus)} perdus d'aujourd'hui (reload intraday)")
        else:
            compteur11_perdu_hier  = []
            compteur11_perdu_today = []
    except Exception as e:
        logger.error(f"❌ Erreur load_compteur11: {e}")


def save_compteur11():
    """Sauvegarde les perdus du jour dans PostgreSQL."""
    try:
        data = {
            'date':   datetime.now().strftime('%Y-%m-%d'),
            'perdus': compteur11_perdu_today,
        }
        db.db_schedule(db.db_save_kv('compteur11', data))
    except Exception as e:
        logger.error(f"❌ Erreur save_compteur11: {e}")


def compteur11_add_perdu(game_number: int, suit: str):
    """Enregistre une prédiction perdue dans la liste du jour (et sauvegarde)."""
    global compteur11_perdu_today
    # Éviter les doublons
    for e in compteur11_perdu_today:
        if e['game_number'] == game_number and e['suit'] == suit:
            return
    compteur11_perdu_today.append({
        'game_number': game_number,
        'suit':        suit,
        'date':        datetime.now().strftime('%Y-%m-%d'),
    })
    save_compteur11()
    logger.info(f"📋 C11 enregistré: #{game_number} {suit} perdu aujourd'hui")


# ─────────────────────────────────────────────────────────────────────────────
# RUNTIME CONFIG — persistance complète en DB (survit aux redémarrages Render)
# ─────────────────────────────────────────────────────────────────────────────

async def save_runtime_config():
    """
    Sauvegarde TOUS les paramètres modifiables dynamiquement dans la DB.
    Appelé automatiquement toutes les 60s depuis keep_alive_task,
    et immédiatement après chaque commande admin qui modifie un paramètre clé.
    """
    cfg = {
        'PREDICTION_CHANNEL_ID3':      PREDICTION_CHANNEL_ID3,
        'PREDICTION_CHANNEL_ID4':      PREDICTION_CHANNEL_ID4,
        'DISTRIBUTION_CHANNEL_ID':     DISTRIBUTION_CHANNEL_ID,
        'COMPTEUR2_CHANNEL_ID':        COMPTEUR2_CHANNEL_ID,
        'MIN_GAP_BETWEEN_PREDICTIONS': MIN_GAP_BETWEEN_PREDICTIONS,
        'COMPTEUR4_THRESHOLD':         COMPTEUR4_THRESHOLD,
        'COMPTEUR7_THRESHOLD':         COMPTEUR7_THRESHOLD,
        'COMPTEUR8_THRESHOLD':         COMPTEUR8_THRESHOLD,
        'COMPTEUR13_THRESHOLD':        COMPTEUR13_THRESHOLD,
        'PREDICTION_HOURS':            PREDICTION_HOURS,
        'compteur2_seuil_B':           compteur2_seuil_B,
        'compteur2_seuil_B_per_suit':  compteur2_seuil_B_per_suit,
        'B_LOSS_INCREMENT':            B_LOSS_INCREMENT,
        'compteur2_active':            compteur2_active,
        'compteur13_active':           compteur13_active,
        'heures_favorables_active':    heures_favorables_active,
    }
    try:
        await db.db_save_kv('runtime_config', cfg)
        logger.debug("💾 Config runtime sauvegardée en DB")
    except Exception as e:
        logger.error(f"❌ Erreur save_runtime_config: {e}")


async def load_runtime_config():
    """
    Charge tous les paramètres runtime depuis la DB au démarrage.
    Les valeurs en DB écrasent les valeurs par défaut de config.py.
    Si aucune sauvegarde n'existe, les valeurs par défaut restent.
    """
    global PREDICTION_CHANNEL_ID3, PREDICTION_CHANNEL_ID4
    global DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID
    global MIN_GAP_BETWEEN_PREDICTIONS
    global COMPTEUR4_THRESHOLD, COMPTEUR7_THRESHOLD, COMPTEUR8_THRESHOLD, COMPTEUR13_THRESHOLD
    global PREDICTION_HOURS
    global compteur2_seuil_B, compteur2_seuil_B_per_suit
    global B_LOSS_INCREMENT
    global compteur2_active, compteur13_active, heures_favorables_active

    try:
        cfg = await db.db_load_kv('runtime_config')
    except Exception as e:
        logger.error(f"❌ Erreur load_runtime_config: {e}")
        return

    if not cfg:
        logger.info("⚙️ Config runtime : aucune sauvegarde en DB — valeurs par défaut utilisées")
        return

    def _get(key, default):
        val = cfg.get(key)
        return val if val is not None else default

    PREDICTION_CHANNEL_ID3      = _get('PREDICTION_CHANNEL_ID3',      PREDICTION_CHANNEL_ID3)
    PREDICTION_CHANNEL_ID4      = _get('PREDICTION_CHANNEL_ID4',      PREDICTION_CHANNEL_ID4)
    DISTRIBUTION_CHANNEL_ID     = _get('DISTRIBUTION_CHANNEL_ID',     DISTRIBUTION_CHANNEL_ID)
    COMPTEUR2_CHANNEL_ID        = _get('COMPTEUR2_CHANNEL_ID',        COMPTEUR2_CHANNEL_ID)
    MIN_GAP_BETWEEN_PREDICTIONS = _get('MIN_GAP_BETWEEN_PREDICTIONS', MIN_GAP_BETWEEN_PREDICTIONS)
    COMPTEUR4_THRESHOLD         = _get('COMPTEUR4_THRESHOLD',         COMPTEUR4_THRESHOLD)
    COMPTEUR7_THRESHOLD         = _get('COMPTEUR7_THRESHOLD',         COMPTEUR7_THRESHOLD)
    COMPTEUR8_THRESHOLD         = _get('COMPTEUR8_THRESHOLD',         COMPTEUR8_THRESHOLD)
    COMPTEUR13_THRESHOLD        = _get('COMPTEUR13_THRESHOLD',        COMPTEUR13_THRESHOLD)
    PREDICTION_HOURS            = _get('PREDICTION_HOURS',            PREDICTION_HOURS)
    compteur2_seuil_B           = _get('compteur2_seuil_B',           compteur2_seuil_B)
    compteur2_seuil_B_per_suit  = _get('compteur2_seuil_B_per_suit',  compteur2_seuil_B_per_suit)
    B_LOSS_INCREMENT            = _get('B_LOSS_INCREMENT',            B_LOSS_INCREMENT)
    compteur2_active            = _get('compteur2_active',            compteur2_active)
    compteur13_active           = _get('compteur13_active',           compteur13_active)
    heures_favorables_active    = _get('heures_favorables_active',    heures_favorables_active)

    logger.info(
        "⚙️ Config runtime restaurée depuis DB — "
        f"C3:{PREDICTION_CHANNEL_ID3} | C4:{PREDICTION_CHANNEL_ID4} | "
        f"Dist:{DISTRIBUTION_CHANNEL_ID} | C2ch:{COMPTEUR2_CHANNEL_ID} | "
        f"Écart:{MIN_GAP_BETWEEN_PREDICTIONS} | "
        f"C4seuil:{COMPTEUR4_THRESHOLD} | C7seuil:{COMPTEUR7_THRESHOLD} | "
        f"C13wx:{COMPTEUR13_THRESHOLD} | B:{compteur2_seuil_B} | "
        f"C2actif:{compteur2_active} | C13actif:{compteur13_active}"
    )


async def compteur11_fire(entry: Dict, current_game: int):
    """Lance une prédiction C11 dans le canal (perdu hier → prédit aujourd'hui).
    C11 est indépendant de C2 et C6 : il prédit directement le costume perdu hier,
    en respectant l'écart df (déclenchement à game_number_perdu - PREDICTION_DF).
    skip_c6=True : C6 ne filtre pas les prédictions C11.
    """
    global compteur11_triggered
    orig_game = entry['game_number']
    suit      = entry['suit']
    trigger_key = f"{orig_game}_{suit}"
    if trigger_key in compteur11_triggered:
        return
    compteur11_triggered.add(trigger_key)

    pred_num = orig_game  # Même numéro de jeu que hier
    reason   = (
        f"C11: jeu #{orig_game} {suit} perdu hier — retour probable aujourd'hui "
        f"(déclenché au jeu #{current_game}, écart df={PREDICTION_DF})."
    )
    added = add_to_prediction_queue(pred_num, suit, 'compteur11', reason)
    # C11 indépendant : skip_c6=True (C6 ne s'applique pas aux prédictions C11)
    success = await send_prediction_multi_channel(pred_num, suit, 'compteur11', skip_c6=True)
    if added:
        for e in list(prediction_queue):
            if e['game_number'] == pred_num and e['suit'] == suit and e.get('type') == 'compteur11':
                prediction_queue.remove(e)
                break
    if success:
        logger.info(f"🔄 C11 prédit: #{pred_num} {suit} (perdu hier #{orig_game}, df={PREDICTION_DF})")
    else:
        logger.warning(f"⚠️ C11: envoi #{pred_num} {suit} échoué")


# ============================================================================
# INITIALISATION
# ============================================================================

def initialize_trackers():
    global compteur2_trackers, compteur1_trackers, compteur4_trackers, compteur5_trackers
    global compteur13_trackers, compteur13_start
    for suit in ALL_SUITS:
        compteur2_trackers[suit] = Compteur2Tracker(suit=suit)
        compteur1_trackers[suit] = Compteur1Tracker(suit=suit)
        compteur4_trackers[suit] = 0
        compteur5_trackers[suit] = 0
        compteur13_trackers[suit] = 0
        compteur13_start[suit]    = 0
    logger.info("📊 Trackers initialisés (Compteur1, Compteur2, Compteur4, Compteur5, Compteur13)")

# ============================================================================
# UTILITAIRES CANAL
# ============================================================================

def normalize_channel_id(channel_id) -> int:
    if not channel_id:
        return None
    channel_str = str(channel_id)
    if channel_str.startswith('-100'):
        return int(channel_str)
    if channel_str.startswith('-'):
        return int(channel_str)
    return int(f"-100{channel_str}")

# Cache pour resolve_channel : évite de spammer l'API Telegram à chaque polling
_channel_cache: Dict[int, object] = {}          # entity_id → entity
_channel_cache_failed: Dict[int, datetime] = {} # entity_id → heure d'échec
_CHANNEL_CACHE_TTL   = 300   # Succès : re-résoudre après 5 min
_CHANNEL_CACHE_FAIL  = 60    # Échec  : ne pas réessayer avant 60s

async def resolve_channel(entity_id):
    if not entity_id:
        return None
    # Échec récent → ne pas réessayer
    fail_time = _channel_cache_failed.get(entity_id)
    if fail_time and (datetime.now() - fail_time).total_seconds() < _CHANNEL_CACHE_FAIL:
        return None
    # Cache valide
    cached = _channel_cache.get(entity_id)
    if cached is not None:
        return cached
    try:
        normalized_id = normalize_channel_id(entity_id)
        entity = await client.get_entity(normalized_id)
        _channel_cache[entity_id] = entity
        _channel_cache_failed.pop(entity_id, None)
        return entity
    except Exception as e:
        logger.error(f"❌ Impossible de résoudre le canal {entity_id}: {e}")
        _channel_cache_failed[entity_id] = datetime.now()
        _channel_cache.pop(entity_id, None)
        return None

def block_suit(suit: str, minutes: int = 5):
    suit_block_until[suit] = datetime.now() + timedelta(minutes=minutes)
    logger.info(f"🔒 {suit} bloqué {minutes}min")

# ============================================================================
# SYSTÈME D'ANIMATION (BARRE DE CHARGEMENT)
# ============================================================================

BAR_SIZE = 10          # Taille totale de la barre
ANIM_INTERVAL = 5.0    # Secondes entre chaque frame — 5s réduit les flood waits Telegram

# Amplitude max totale par rattrapage: R0=2, R1=4, R2=7, R3=10
BAR_MAX_BY_RATTRAPAGE = [2, 4, 7, 10]

# Couleur et taille INCREMENTAL par niveau (la partie mobile)
# R0→2 blocs, R1→2 blocs supplémentaires, R2→3, R3→3
LEVEL_COLORS = ['🟦', '🟩', '🟨', '🟥']
LEVEL_SIZES  = [2, 2, 3, 3]

def build_anim_bar(rattrapage: int, frame: int) -> str:
    """Construit la barre multicolore.
    - Niveaux passés : blocs figés dans leur couleur
    - Niveau actuel  : ping-pong dans sa couleur
    """
    R = min(rattrapage, 3)

    # Partie figée (niveaux précédents)
    frozen = ''
    frozen_count = 0
    for lvl in range(R):
        count = LEVEL_SIZES[lvl]
        frozen += LEVEL_COLORS[lvl] * count
        frozen_count += count

    # Partie mobile (niveau actuel) — ping-pong 0 → LEVEL_SIZES[R]
    cur_size = LEVEL_SIZES[R]
    period   = cur_size * 2
    pos      = frame % max(period, 1)
    moving_count = pos if pos <= cur_size else period - pos
    moving = LEVEL_COLORS[R] * moving_count

    # Cases vides
    used  = frozen_count + moving_count
    empty = '⬜' * max(0, BAR_SIZE - used)

    return frozen + moving + empty


async def safe_edit_message(entity, msg_id: int, text: str,
                             parse_mode: str = 'markdown',
                             max_retries: int = 4,
                             label: str = '') -> bool:
    """
    Édite un message Telegram avec retry automatique sur FloodWait.
    Retourne True si succès, False si échec définitif.
    """
    for attempt in range(max_retries):
        try:
            await client.edit_message(entity, msg_id, text, parse_mode=parse_mode)
            return True
        except FloodWaitError as fw:
            wait_sec = fw.seconds + 1
            logger.warning(f"⏳ FloodWait {wait_sec}s {label} (tentative {attempt + 1}/{max_retries})")
            await asyncio.sleep(wait_sec)
        except Exception as e:
            err = str(e).lower()
            if 'not modified' in err:
                return True  # Pas d'erreur réelle
            if 'message_id_invalid' in err or 'message to edit not found' in err:
                logger.warning(f"⚠️ Message introuvable (msg_id invalide ou supprimé) {label}: {e}")
                return False
            logger.error(f"❌ Erreur édition {label}: {e}")
            return False
    logger.error(f"❌ Échec édition après {max_retries} tentatives {label}")
    return False


async def _run_animation(original_game: int, check_game: int, start_frame: int = 0):
    """Boucle d'animation: barre multicolore dont la couleur change selon le rattrapage."""
    global pending_predictions, animation_tasks

    try:
        prediction_entity  = await resolve_channel(PREDICTION_CHANNEL_ID)
        prediction_entity2 = await resolve_channel(PREDICTION_CHANNEL_ID2) if PREDICTION_CHANNEL_ID2 else None
        prediction_entity3 = await resolve_channel(PREDICTION_CHANNEL_ID3) if PREDICTION_CHANNEL_ID3 else None
        prediction_entity4 = await resolve_channel(PREDICTION_CHANNEL_ID4) if PREDICTION_CHANNEL_ID4 else None
        if not prediction_entity:
            return

        frame = start_frame
        while True:
            pred = pending_predictions.get(original_game)
            if not pred or pred.get('status') != 'en_cours':
                break

            msg_id  = pred.get('message_id')
            msg_id2 = pred.get('channel2_message_id')
            msg_id3 = pred.get('channel3_message_id')
            msg_id4 = pred.get('channel4_message_id')
            if not msg_id:
                break

            suit = pred['suit']
            suit_display = SUIT_DISPLAY.get(suit, suit)
            rattrapage = pred.get('rattrapage', 0)

            bar = build_anim_bar(rattrapage, frame)

            level_labels = ['🟦 R0', '🟩 R1', '🟨 R2', '🟥 R3']
            level_label  = level_labels[min(rattrapage, 3)]
            dots = '.' * ((frame % 3) + 1)

            formation_suffix = pred.get('formation_suffix', '')
            msg = (
                f"🎰 **PRÉDICTION #{original_game}**\n"
                f"🎯 Couleur: {suit_display}\n\n"
                f"🔍 Vérification jeu **#{check_game}** — {level_label}\n"
                f"`{bar}`\n"
                f"⏳ _Analyse{dots}_"
                f"{formation_suffix}"
            )

            await safe_edit_message(
                prediction_entity, msg_id, msg,
                label=f"anim #{original_game}",
                max_retries=2
            )
            if prediction_entity2 and msg_id2:
                await safe_edit_message(
                    prediction_entity2, msg_id2, msg,
                    label=f"anim2 #{original_game}",
                    max_retries=2
                )
            if prediction_entity3 and msg_id3:
                await safe_edit_message(
                    prediction_entity3, msg_id3, msg,
                    label=f"anim3 #{original_game}",
                    max_retries=2
                )
            if prediction_entity4 and msg_id4:
                await safe_edit_message(
                    prediction_entity4, msg_id4, msg,
                    label=f"anim4 #{original_game}",
                    max_retries=2
                )

            frame += 1
            await asyncio.sleep(ANIM_INTERVAL)

    except asyncio.CancelledError:
        pass
    except Exception as e:
        logger.debug(f"🎬 Erreur animation #{original_game}: {e}")
    finally:
        animation_tasks.pop(original_game, None)


def start_animation(original_game: int, check_game: int, start_frame: int = 0):
    """Démarre (ou redémarre) l'animation pour une prédiction."""
    stop_animation(original_game)
    task = asyncio.create_task(_run_animation(original_game, check_game, start_frame))
    animation_tasks[original_game] = task
    logger.info(f"🎬 Animation démarrée #{original_game} → vérifie #{check_game} (frame={start_frame})")


def stop_animation(original_game: int):
    """Arrête l'animation d'une prédiction."""
    task = animation_tasks.pop(original_game, None)
    if task and not task.done():
        task.cancel()


def stop_all_animations():
    """Arrête toutes les animations en cours."""
    for game_num in list(animation_tasks.keys()):
        stop_animation(game_num)


# ============================================================================
# GESTION DES PRÉDICTIONS
# ============================================================================

def format_prediction_message(game_number: int, suit: str, status: str = 'en_cours',
                              current_check: int = None, verified_games: List[int] = None,
                              rattrapage: int = 0) -> str:
    suit_display = SUIT_DISPLAY.get(suit, suit)

    if status == 'en_cours':
        verif_parts = []
        for i in range(4):
            check_num = game_number + i
            if current_check == check_num:
                verif_parts.append(f"🔵#{check_num}")
            elif verified_games and check_num in verified_games:
                continue
            else:
                verif_parts.append(f"⬜#{check_num}")
        verif_line = " | ".join(verif_parts)
        return (
            f"🎰 PRÉDICTION #{game_number}\n"
            f"🎯 Couleur: {suit_display}\n"
            "📊 Statut: En cours ⏳\n"
            f"🔍 Vérification: {verif_line}"
        )

    elif status == 'gagne':
        num_emoji = ['0️⃣', '1️⃣', '2️⃣', '3️⃣']
        badge = num_emoji[rattrapage] if rattrapage < len(num_emoji) else f'{rattrapage}️⃣'
        return (
            f"🏆 **PRÉDICTION #{game_number}**\n\n"
            f"🎯 **Couleur:** {suit_display}\n"
            f"✅ **Statut:** ✅{badge} GAGNÉ"
        )

    elif status == 'perdu':
        return (
            f"💔 **PRÉDICTION #{game_number}**\n\n"
            f"🎯 **Couleur:** {suit_display}\n"
            "❌ **Statut:** PERDU 😭"
        )

    elif status == 'expirée_api':
        return (
            f"⚠️ **PRÉDICTION #{game_number}**\n\n"
            f"🎯 **Couleur:** {suit_display}\n"
            "🔌 **Statut:** EXPIRÉ — jeu sauté par l'API"
        )

    return ""

async def send_prediction_to_channel(channel_id: int, game_number: int, suit: str,
                                     prediction_type: str, is_secondary: bool = False) -> Optional[int]:
    try:
        if not is_secondary and suit in suit_block_until and datetime.now() < suit_block_until[suit]:
            logger.info(f"🔒 {suit} bloqué, prédiction annulée")
            return None
        if not channel_id:
            return None
        channel_entity = await resolve_channel(channel_id)
        if not channel_entity:
            logger.error(f"❌ Canal {channel_id} inaccessible")
            return None
        msg = format_prediction_message(game_number, suit, 'en_cours', game_number, [])
        sent = await client.send_message(channel_entity, msg, parse_mode='markdown')
        return sent.id
    except ChatWriteForbiddenError:
        logger.error(f"❌ Pas de permission dans {channel_id}")
        return None
    except UserBannedInChannelError:
        logger.error(f"❌ Bot banni de {channel_id}")
        return None
    except Exception as e:
        logger.error(f"❌ Erreur envoi à {channel_id}: {e}")
        return None

async def send_prediction_multi_channel(game_number: int, suit: str, prediction_type: str = 'standard', skip_c6: bool = False, meta: Optional[Dict] = None) -> bool:
    global last_prediction_time, last_prediction_number_sent, DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID

    # Vérification restriction horaire
    if not is_prediction_time_allowed():
        logger.info(f"⏰ Heure non autorisée, prédiction #{game_number} bloquée")
        return False

    success = False

    if PREDICTION_CHANNEL_ID:
        if game_number in pending_predictions:
            logger.warning(f"⚠️ #{game_number} déjà dans pending")
            return False

        # Anti-doublon : blocage si cette prédiction a déjà été envoyée (même après résolution)
        if game_number in recently_predicted:
            logger.warning(f"🚫 #{game_number} déjà prédit (recently_predicted) — doublon bloqué")
            return False

        old_last = last_prediction_number_sent
        last_prediction_number_sent = game_number

        # Chercher la raison et le meta dans la file d'attente
        queued_reason = ''
        queued_meta   = meta or {}
        for qp in prediction_queue:
            if qp['game_number'] == game_number and qp['suit'] == suit:
                queued_reason = qp.get('reason', '')
                queued_meta   = qp.get('meta', meta or {})
                break
        if not queued_reason:
            for qp in prediction_queue:
                if qp['game_number'] == game_number:
                    queued_reason = qp.get('reason', '')
                    if not queued_meta:
                        queued_meta = qp.get('meta', {})
                    break

        pending_predictions[game_number] = {
            'suit': suit,
            'message_id': None,
            'status': 'sending',
            'type': prediction_type,
            'sent_time': datetime.now(),
            'verification_games': [game_number, game_number + 1, game_number + 2],
            'verified_games': [],
            'found_at': None,
            'rattrapage': 0,
            'current_check': game_number,
            'reason': queued_reason
        }

        # ── Envoi simultané Canal1 + Canal2 + Canal3 (asyncio.gather) ───────────
        secondary_channel_id = None
        if prediction_type == 'distribution' and DISTRIBUTION_CHANNEL_ID:
            secondary_channel_id = DISTRIBUTION_CHANNEL_ID
        elif prediction_type == 'compteur2' and COMPTEUR2_CHANNEL_ID:
            secondary_channel_id = COMPTEUR2_CHANNEL_ID

        async def _noop(): return None

        tasks = [
            send_prediction_to_channel(PREDICTION_CHANNEL_ID,  game_number, suit, prediction_type, is_secondary=False),
            send_prediction_to_channel(PREDICTION_CHANNEL_ID2, game_number, suit, prediction_type, is_secondary=True) if PREDICTION_CHANNEL_ID2 else _noop(),
            send_prediction_to_channel(PREDICTION_CHANNEL_ID3, game_number, suit, prediction_type, is_secondary=True) if PREDICTION_CHANNEL_ID3 else _noop(),
            send_prediction_to_channel(PREDICTION_CHANNEL_ID4, game_number, suit, prediction_type, is_secondary=True) if PREDICTION_CHANNEL_ID4 else _noop(),
            send_prediction_to_channel(secondary_channel_id,   game_number, suit, prediction_type, is_secondary=True) if secondary_channel_id else _noop(),
        ]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        msg_id     = results[0] if not isinstance(results[0], Exception) else None
        ch2_msg_id = results[1] if not isinstance(results[1], Exception) else None
        ch3_msg_id = results[2] if not isinstance(results[2], Exception) else None
        ch4_msg_id = results[3] if not isinstance(results[3], Exception) else None
        sec_msg_id = results[4] if not isinstance(results[4], Exception) else None

        if ch2_msg_id:
            logger.info(f"✅ Canal2 #{game_number} {suit} envoyé")
        elif PREDICTION_CHANNEL_ID2:
            logger.warning(f"⚠️ Canal2 #{game_number} {suit} — ÉCHEC (bot admin? droits d'écriture?)")

        if ch3_msg_id:
            logger.info(f"✅ Canal3 #{game_number} {suit} envoyé")
        elif PREDICTION_CHANNEL_ID3:
            logger.warning(f"⚠️ Canal3 #{game_number} {suit} — ÉCHEC (bot admin? droits d'écriture?)")

        if ch4_msg_id:
            logger.info(f"✅ Canal4 #{game_number} {suit} envoyé")
        elif PREDICTION_CHANNEL_ID4:
            logger.warning(f"⚠️ Canal4 #{game_number} {suit} — ÉCHEC (bot admin? droits d'écriture?)")

        if msg_id:
            last_prediction_time = datetime.now()
            pending_predictions[game_number]['message_id'] = msg_id
            pending_predictions[game_number]['status'] = 'en_cours'
            if ch2_msg_id:
                pending_predictions[game_number]['channel2_message_id'] = ch2_msg_id
            if ch3_msg_id:
                pending_predictions[game_number]['channel3_message_id'] = ch3_msg_id
            if ch4_msg_id:
                pending_predictions[game_number]['channel4_message_id'] = ch4_msg_id
            if sec_msg_id:
                pending_predictions[game_number]['secondary_message_id'] = sec_msg_id
                pending_predictions[game_number]['secondary_channel_id'] = secondary_channel_id
            canal_pred_msg_ids[msg_id] = game_number
            add_prediction_to_history(game_number, suit, [game_number, game_number + 1, game_number + 2], prediction_type, queued_reason, meta=queued_meta)
            db.db_schedule(db.db_set_prediction_message_id(game_number, suit, msg_id))
            success = True
            recently_predicted.add(game_number)
            if len(recently_predicted) > 30:
                oldest = min(recently_predicted)
                recently_predicted.discard(oldest)
            logger.info(f"✅ Prédiction #{game_number} {suit} envoyée ({prediction_type})")
            start_animation(game_number, game_number)
            save_pending_predictions()
        else:
            if game_number in pending_predictions and pending_predictions[game_number]['status'] == 'sending':
                del pending_predictions[game_number]
            last_prediction_number_sent = old_last

    return success

async def notify_b_augmente(suit: str, old_b: int, new_b: int, game_number: int, rattrapage: int):
    """Envoie une notification privée à l'admin quand le B d'un costume augmente."""
    try:
        if not ADMIN_ID or ADMIN_ID == 0:
            return
        suit_emoji = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}.get(suit, suit)
        suit_display = SUIT_DISPLAY.get(suit, suit)
        r_label = f"R{rattrapage}" if rattrapage > 0 else "Direct"
        msg = (
            f"📈 **B augmenté — {suit_emoji} {suit_display}**\n"
            f"Jeu **#{game_number}** → PERDU ({r_label})\n"
            f"B : **{old_b}** → **{new_b}**"
        )
        admin_entity = await client.get_entity(ADMIN_ID)
        await client.send_message(admin_entity, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Notif B augmenté: {e}")

async def send_parole_auto_delete(statut_key: str, game_number: int):
    """Envoie une parole biblique sur tous les canaux et la supprime automatiquement après 30s."""
    texte = get_parole(statut_key, game_number, count=1)
    for ch_id in [PREDICTION_CHANNEL_ID, PREDICTION_CHANNEL_ID2, PREDICTION_CHANNEL_ID3, PREDICTION_CHANNEL_ID4]:
        if not ch_id:
            continue
        try:
            entity = await resolve_channel(ch_id)
            if not entity:
                continue
            msg = await client.send_message(entity, texte, parse_mode='markdown')
            await asyncio.sleep(30)
            try:
                await client.delete_messages(entity, [msg.id])
            except Exception as e:
                logger.debug(f"Suppression parole #{game_number} canal {ch_id} ignorée: {e}")
        except Exception as e:
            logger.debug(f"send_parole_auto_delete #{game_number} canal {ch_id}: {e}")


async def update_prediction_message(game_number: int, status: str, rattrapage: int = 0):
    if game_number not in pending_predictions:
        return

    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    new_msg = format_prediction_message(game_number, suit, status, rattrapage=rattrapage)

    # Déterminer la clé de parole selon le statut
    parole_key = None
    if 'gagne' in status:
        logger.info(f"✅ Gagné: #{game_number} (R{rattrapage})")
        parole_key = f'gagne_r{rattrapage}'
    elif status == 'expirée_api':
        logger.warning(f"🔌 Prédiction #{game_number} expirée — jeu sauté par l'API (R{rattrapage})")
    else:
        logger.info(f"❌ Perdu: #{game_number}")
        parole_key = 'perdu'
        block_suit(suit, 5)
        # Enregistrer l'événement PERDU
        old_b = compteur2_seuil_B_per_suit.get(suit, compteur2_seuil_B)
        new_b = old_b + B_LOSS_INCREMENT
        compteur2_seuil_B_per_suit[suit] = new_b
        perdu_events.append({
            'game': game_number,
            'suit': suit,
            'time': datetime.now(),
            'rattrapage': rattrapage,
            'b_before': old_b,
            'b_after': new_b
        })
        logger.info(f"📈 B({suit}) augmenté: {old_b} → {new_b} après PERDU #{game_number}")
        asyncio.create_task(send_perdu_pdf())
        asyncio.create_task(notify_b_augmente(suit, old_b, new_b, game_number, rattrapage))

    # Arrêter l'animation AVANT d'éditer le résultat final
    stop_animation(game_number)
    # Pause courte : laisse les édits d'animation en vol terminer avant l'édition finale
    await asyncio.sleep(0.5)
    del pending_predictions[game_number]
    save_pending_predictions()  # Mise à jour persistance (prediction résolue)

    prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
    if prediction_entity:
        if msg_id:
            edited = await safe_edit_message(prediction_entity, msg_id, new_msg,
                                             label=f"finale #{game_number}")
            if not edited:
                logger.warning(
                    f"⚠️ Édition finale #{game_number} échouée "
                    f"(msg_id={msg_id}) → envoi du résultat en nouveau message"
                )
                try:
                    await client.delete_messages(prediction_entity, [msg_id])
                except Exception as _de:
                    logger.debug(f"Suppression ancienne prédiction #{game_number}: {_de}")
                try:
                    await client.send_message(prediction_entity, new_msg, parse_mode='markdown')
                except Exception as _se:
                    logger.error(f"❌ Fallback send #{game_number} échoué: {_se}")
        else:
            logger.warning(
                f"⚠️ update_prediction_message #{game_number}: msg_id manquant "
                "→ envoi du résultat en nouveau message"
            )
            try:
                await client.send_message(prediction_entity, new_msg, parse_mode='markdown')
            except Exception as _se:
                logger.error(f"❌ Fallback send #{game_number} (msg_id None): {_se}")

    # ── Canal 2 — mise à jour résultat ───────────────────────────────────────
    ch2_msg_id = pred.get('channel2_message_id')
    if PREDICTION_CHANNEL_ID2:
        prediction_entity2 = await resolve_channel(PREDICTION_CHANNEL_ID2)
        if prediction_entity2:
            if ch2_msg_id:
                edited2 = await safe_edit_message(prediction_entity2, ch2_msg_id, new_msg,
                                                  label=f"finale2 #{game_number}")
                if not edited2:
                    try:
                        await client.delete_messages(prediction_entity2, [ch2_msg_id])
                    except Exception:
                        pass
                    try:
                        await client.send_message(prediction_entity2, new_msg, parse_mode='markdown')
                    except Exception as _se2:
                        logger.error(f"❌ Fallback send canal2 #{game_number}: {_se2}")
            else:
                try:
                    await client.send_message(prediction_entity2, new_msg, parse_mode='markdown')
                except Exception as _se2:
                    logger.error(f"❌ Fallback send canal2 #{game_number} (msg_id None): {_se2}")

    # ── Canal 3 — mise à jour résultat ───────────────────────────────────────
    ch3_msg_id = pred.get('channel3_message_id')
    if PREDICTION_CHANNEL_ID3:
        prediction_entity3 = await resolve_channel(PREDICTION_CHANNEL_ID3)
        if prediction_entity3:
            if ch3_msg_id:
                edited3 = await safe_edit_message(prediction_entity3, ch3_msg_id, new_msg,
                                                  label=f"finale3 #{game_number}")
                if not edited3:
                    try:
                        await client.delete_messages(prediction_entity3, [ch3_msg_id])
                    except Exception:
                        pass
                    try:
                        await client.send_message(prediction_entity3, new_msg, parse_mode='markdown')
                    except Exception as _se3:
                        logger.error(f"❌ Fallback send canal3 #{game_number}: {_se3}")
            else:
                try:
                    await client.send_message(prediction_entity3, new_msg, parse_mode='markdown')
                except Exception as _se3:
                    logger.error(f"❌ Fallback send canal3 #{game_number} (msg_id None): {_se3}")

    # ── Canal 4 — mise à jour résultat ───────────────────────────────────────
    ch4_msg_id = pred.get('channel4_message_id')
    if PREDICTION_CHANNEL_ID4:
        prediction_entity4 = await resolve_channel(PREDICTION_CHANNEL_ID4)
        if prediction_entity4:
            if ch4_msg_id:
                edited4 = await safe_edit_message(prediction_entity4, ch4_msg_id, new_msg,
                                                  label=f"finale4 #{game_number}")
                if not edited4:
                    try:
                        await client.delete_messages(prediction_entity4, [ch4_msg_id])
                    except Exception:
                        pass
                    try:
                        await client.send_message(prediction_entity4, new_msg, parse_mode='markdown')
                    except Exception as _se4:
                        logger.error(f"❌ Fallback send canal4 #{game_number}: {_se4}")
            else:
                try:
                    await client.send_message(prediction_entity4, new_msg, parse_mode='markdown')
                except Exception as _se4:
                    logger.error(f"❌ Fallback send canal4 #{game_number} (msg_id None): {_se4}")

    sec_msg_id = pred.get('secondary_message_id')
    sec_channel_id = pred.get('secondary_channel_id')
    if sec_msg_id and sec_channel_id:
        sec_entity = await resolve_channel(sec_channel_id)
        if sec_entity:
            await safe_edit_message(sec_entity, sec_msg_id, new_msg,
                                    label=f"finale-sec #{game_number}")

    # Envoyer la parole biblique (auto-supprimée après 60s)
    if parole_key:
        asyncio.create_task(send_parole_auto_delete(parole_key, game_number))

async def update_prediction_progress(game_number: int, current_check: int):
    if game_number not in pending_predictions:
        return
    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    verified_games = pred.get('verified_games', [])
    pred['current_check'] = current_check
    # Relancer l'animation depuis le max précédent pour la continuité visuelle
    new_rattrapage = pred.get('rattrapage', 0)
    prev_rattrapage = max(0, new_rattrapage - 1)
    start_frame = BAR_MAX_BY_RATTRAPAGE[min(prev_rattrapage, len(BAR_MAX_BY_RATTRAPAGE) - 1)]
    start_animation(game_number, current_check, start_frame)
    msg = format_prediction_message(game_number, suit, 'en_cours', current_check, verified_games)
    formation_suffix = pred.get('formation_suffix', '')
    if formation_suffix:
        msg += formation_suffix
    prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
    if prediction_entity:
        await safe_edit_message(prediction_entity, msg_id, msg,
                                label=f"progress #{game_number}")

    # ── Canal 2 — mise à jour progression ────────────────────────────────────
    ch2_msg_id = pred.get('channel2_message_id')
    if PREDICTION_CHANNEL_ID2 and ch2_msg_id:
        prediction_entity2 = await resolve_channel(PREDICTION_CHANNEL_ID2)
        if prediction_entity2:
            await safe_edit_message(prediction_entity2, ch2_msg_id, msg,
                                    label=f"progress2 #{game_number}")

    # ── Canal 3 — mise à jour progression ────────────────────────────────────
    ch3_msg_id = pred.get('channel3_message_id')
    if PREDICTION_CHANNEL_ID3 and ch3_msg_id:
        prediction_entity3 = await resolve_channel(PREDICTION_CHANNEL_ID3)
        if prediction_entity3:
            await safe_edit_message(prediction_entity3, ch3_msg_id, msg,
                                    label=f"progress3 #{game_number}")

    # ── Canal 4 — mise à jour progression ────────────────────────────────────
    ch4_msg_id = pred.get('channel4_message_id')
    if PREDICTION_CHANNEL_ID4 and ch4_msg_id:
        prediction_entity4 = await resolve_channel(PREDICTION_CHANNEL_ID4)
        if prediction_entity4:
            await safe_edit_message(prediction_entity4, ch4_msg_id, msg,
                                    label=f"progress4 #{game_number}")

    sec_msg_id = pred.get('secondary_message_id')
    sec_channel_id = pred.get('secondary_channel_id')
    if sec_msg_id and sec_channel_id:
        sec_entity = await resolve_channel(sec_channel_id)
        if sec_entity:
            await safe_edit_message(sec_entity, sec_msg_id, msg,
                                    label=f"progress-sec #{game_number}")

async def check_prediction_result(game_number: int, player_suits: Set[str], is_finished: bool = False) -> bool:
    """
    Vérifie les prédictions en attente contre les cartes joueur.
    - Victoire immédiate si le costume est trouvé (même partie non finie).
    - Échec (rattrapage) uniquement quand la partie est terminée (is_finished=True).
    - Catch-up : si le jeu attendu a été sauté par l'API, on récupère depuis l'historique.
    """
    found = False

    # ─── Vérification directe (rattrapage=0, game_number == numéro prédit) ───
    if game_number in pending_predictions:
        pred = pending_predictions[game_number]
        if pred['status'] == 'en_cours':
            target_suit = pred['suit']

            if game_number not in pred['verified_games']:
                logger.info(f"🔍 Vérif #{game_number} (fini={is_finished}): {target_suit} dans {player_suits}?")

                if target_suit in player_suits:
                    # ✅ Costume trouvé → victoire immédiate
                    pred['verified_games'].append(game_number)
                    await update_prediction_message(game_number, 'gagne', 0)
                    update_prediction_in_history(game_number, target_suit, game_number, 0, 'gagne_r0')
                    found = True
                elif is_finished:
                    # ❌ Partie terminée sans le costume → passer au rattrapage R1
                    pred['verified_games'].append(game_number)
                    pred['rattrapage'] = 1
                    next_check = game_number + 1
                    logger.info(f"❌ #{game_number} terminé sans {target_suit}, attente R1 #{next_check}")
                    # Formation : jeu prédit terminé → comparer ses 3 cartes → costume pour #N+1
                    try:
                        await _trigger_formation_follow_up(game_number, target_suit, game_number, dict(pred))
                    except Exception as _fex:
                        logger.error(f"❌ Formation follow-up #{game_number}: {_fex}")
                    await update_prediction_progress(game_number, next_check)
                else:
                    # ⏳ Partie en cours, costume pas encore là → re-vérifier au prochain poll
                    logger.debug(f"⏳ #{game_number} en cours, {target_suit} pas encore là")

    # ─── Vérification rattrapage (R1/R2/R3) ──────────────────────────────────
    for original_game, pred in list(pending_predictions.items()):
        if pred['status'] != 'en_cours':
            continue
        rattrapage = pred.get('rattrapage', 0)
        if rattrapage == 0:
            # Si le jeu original a été sauté par l'API → passer automatiquement à R1
            if game_number > original_game and original_game not in pred.get('verified_games', []):
                logger.warning(
                    f"🔌 Jeu #{original_game} sauté par l'API — passage automatique R1"
                )
                pred['verified_games'].append(original_game)
                pred['rattrapage'] = 1
                await update_prediction_progress(original_game, original_game + 1)
            continue  # Géré dans la section directe (ou passage R1 ci-dessus)

        target_suit  = pred['suit']
        expected_game = original_game + rattrapage

        # ── Sécurité timeout : si > 8 jeux après la prédiction sans résolution ──
        # → supprimer le message du canal + nettoyer l'état interne
        if game_number > original_game + 8:
            logger.warning(
                f"⏰ Timeout #{original_game} R{rattrapage}: {game_number - original_game} jeux "
                "sans résolution → suppression du canal"
            )
            stop_animation(original_game)
            msg_id  = pred.get('message_id')
            msg_id2 = pred.get('channel2_message_id')
            msg_id3 = pred.get('channel3_message_id')
            msg_id4 = pred.get('channel4_message_id')
            for _ch_id, _mid in [(PREDICTION_CHANNEL_ID, msg_id), (PREDICTION_CHANNEL_ID2, msg_id2), (PREDICTION_CHANNEL_ID3, msg_id3), (PREDICTION_CHANNEL_ID4, msg_id4)]:
                if _ch_id and _mid:
                    try:
                        _ent = await resolve_channel(_ch_id)
                        if _ent:
                            await client.delete_messages(_ent, [_mid])
                    except Exception as _e:
                        logger.debug(f"Suppression message timeout #{original_game} canal {_ch_id}: {_e}")
            # Nettoyage de toute entrée formation_follow_ups liée à cette prédiction
            for _fg in list(formation_follow_ups.keys()):
                if formation_follow_ups[_fg].get('original_game') == original_game:
                    formation_follow_ups.pop(_fg, None)
            del pending_predictions[original_game]
            save_pending_predictions()
            update_prediction_in_history(original_game, target_suit, game_number, rattrapage, 'perdu')
            compteur11_add_perdu(original_game, target_suit)
            found = True
            continue

        # Ignorer les jeux antérieurs au jeu attendu
        if game_number < expected_game:
            continue

        # ── Catch-up : le jeu attendu a peut-être été sauté par l'API ──
        # On cherche d'abord dans game_result_cache (cache live), puis game_history (terminés).
        check_game       = expected_game
        check_suits      = player_suits
        check_finished   = is_finished
        api_skipped      = False   # True si le jeu attendu est introuvable dans les deux caches

        if game_number > expected_game and expected_game not in pred['verified_games']:
            # 1. Cache live (game_result_cache) — priorité maximale
            cached = game_result_cache.get(expected_game)
            if cached and cached.get('is_finished', False):
                check_suits    = get_player_suits(cached.get('player_cards', []))
                check_finished = True
                logger.info(f"🔁 Catch-up R{rattrapage}: #{expected_game} récupéré depuis cache live")
            else:
                # 2. Historique terminés (game_history)
                hist = game_history.get(expected_game)
                if hist and hist.get('is_finished', False):
                    check_suits    = get_player_suits(hist.get('player_cards', []))
                    check_finished = True
                    logger.info(f"🔁 Catch-up R{rattrapage}: #{expected_game} récupéré depuis historique")
                else:
                    # Jeu introuvable dans les deux caches → API a sauté ce jeu
                    api_skipped = True
                    logger.warning(f"🔌 Catch-up R{rattrapage}: #{expected_game} introuvable — API sautée")

        # Ne pas re-traiter si ce jeu de vérification est déjà enregistré
        if check_game in pred['verified_games']:
            continue

        # ── Jeu sauté par l'API : marquer EXPIRÉ et passer à la suite ──────
        if api_skipped:
            pred['verified_games'].append(expected_game)
            await update_prediction_message(original_game, 'expirée_api', rattrapage)
            update_prediction_in_history(original_game, target_suit, expected_game, rattrapage, 'expirée_api')
            # Nettoyer les entrées de cache devenues inutiles
            game_result_cache.pop(expected_game, None)
            found = True
            continue

        logger.info(f"🔍 Vérif R{rattrapage} #{check_game} (fini={check_finished}): {target_suit} dans {check_suits}?")

        if target_suit in check_suits:
            # ✅ Statut final : GAGNÉ → nettoyer le cache de ce jeu
            pred['verified_games'].append(check_game)
            await update_prediction_message(original_game, 'gagne', rattrapage)
            update_prediction_in_history(original_game, target_suit, check_game, rattrapage, f'gagne_r{rattrapage}')
            game_result_cache.pop(check_game, None)   # nettoyage cache — statut final trouvé
            found = True

        elif check_finished:
            pred['verified_games'].append(check_game)
            if rattrapage < 2:
                # Intermédiaire : passage au rattrapage suivant — cache conservé
                pred['rattrapage'] = rattrapage + 1
                next_check = original_game + rattrapage + 1
                logger.info(f"❌ R{rattrapage} terminé sans {target_suit}, attente R{rattrapage+1} #{next_check}")
                await update_prediction_progress(original_game, next_check)
            else:
                # ❌ Statut final : PERDU R2 → nettoyer le cache de ce jeu
                logger.info(f"❌ R2 terminé sans {target_suit}, prédiction PERDUE #{original_game}")
                await update_prediction_message(original_game, 'perdu', 2)
                update_prediction_in_history(original_game, target_suit, check_game, 2, 'perdu')
                compteur11_add_perdu(original_game, target_suit)
                game_result_cache.pop(check_game, None)   # nettoyage cache — statut final trouvé
                found = True

        else:
            # ⏳ Partie en cours, costume pas encore là → re-vérifier au prochain poll
            logger.debug(f"⏳ R{rattrapage} #{check_game} en cours, {target_suit} pas encore là")

    return found

# ============================================================================
# GESTION DE LA FILE D'ATTENTE
# ============================================================================

def can_accept_prediction(pred_number: int) -> bool:
    global prediction_queue, pending_predictions, last_prediction_number_sent, MIN_GAP_BETWEEN_PREDICTIONS

    # Règle 1 : jamais de nouvelle prédiction si une est en cours de vérification
    if pending_predictions:
        logger.debug(f"🚫 #{pred_number} ignoré — prédiction en attente de vérification")
        return False

    # Règle 2 : intervalle minimum de {MIN_GAP} jeux entre numéros de prédiction
    if last_prediction_number_sent > 0:
        gap = pred_number - last_prediction_number_sent
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            logger.debug(f"🚫 #{pred_number} ignoré — écart {gap} < {MIN_GAP_BETWEEN_PREDICTIONS} (dernière #{last_prediction_number_sent})")
            return False

    for queued_pred in prediction_queue:
        existing_num = queued_pred['game_number']
        gap = abs(pred_number - existing_num)
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            return False

    return True

def add_to_prediction_queue(game_number: int, suit: str, prediction_type: str, reason: str = '',
                            trigger_game: Optional[int] = None,
                            skip_c6: bool = False, meta: Optional[Dict] = None) -> bool:
    global prediction_queue

    for pred in prediction_queue:
        if pred['game_number'] == game_number:
            return False

    if not can_accept_prediction(game_number):
        return False

    # trigger_game = jeu lors duquel la prédiction sera envoyée
    # Par défaut : game_number - PREDICTION_DF (comportement historique)
    tg = trigger_game if trigger_game is not None else (game_number - PREDICTION_DF)

    prediction_queue.append({
        'game_number': game_number,
        'trigger_game': tg,
        'suit': suit,
        'type': prediction_type,
        'reason': reason,
        'skip_c6': skip_c6,
        'meta': meta or {},
        'added_at': datetime.now()
    })
    prediction_queue.sort(key=lambda x: x['game_number'])
    logger.info(f"📥 #{game_number} ({suit}) en file [envoi@{tg}, skip_c6={skip_c6}]. Total: {len(prediction_queue)}")
    return True

async def process_prediction_queue(current_game: int, is_finished: bool = False):
    """
    Traite la file de prédictions selon le système df.
    - Envoi  : dès que la main joueur est complète (is_finished OU joueur ≥3 cartes)
               ET current_game + df == pred_number
    - Expiry : si current_game > pred_number (le jeu prédit est dépassé)
    Note: is_finished ici représente player_hand_complete (main joueur définitive).
    """
    global prediction_queue, pending_predictions

    if pending_predictions:
        return

    to_remove = []
    to_send = None

    for pred in list(prediction_queue):
        pred_number = pred['game_number']

        # Expiry : le jeu prédit est déjà passé
        if current_game > pred_number:
            logger.warning(f"⏰ #{pred_number} EXPIRÉ (jeu courant #{current_game})")
            to_remove.append(pred)
            continue

        # Envoi : jeu courant == trigger_game stocké dans la file
        trigger_g = pred.get('trigger_game', pred_number - PREDICTION_DF)
        if is_finished and current_game == trigger_g:
            to_send = pred
            break

    for pred in to_remove:
        prediction_queue.remove(pred)

    if to_send:
        if pending_predictions:
            return
        pred_number    = to_send['game_number']
        suit           = to_send['suit']
        pred_type      = to_send['type']

        pred_skip_c6 = to_send.get('skip_c6', False)
        logger.info(f"📤 Envoi depuis file: #{pred_number} (jeu #{current_game}, skip_c6={pred_skip_c6})")
        success = await send_prediction_multi_channel(pred_number, suit, pred_type, skip_c6=pred_skip_c6)
        if success:
            prediction_queue.remove(to_send)

# ============================================================================
# MISE À JOUR COMPTEUR2
# ============================================================================

def update_compteur2(game_number: int, player_suits: Set[str]):
    global compteur2_trackers
    for suit in ALL_SUITS:
        tracker = compteur2_trackers[suit]
        if suit in player_suits:
            tracker.reset(game_number)
        else:
            tracker.increment(game_number)

# ============================================================================
# TRAITEMENT DES JEUX (API)
# ============================================================================

async def send_bilan_and_reset_at_1440():
    """
    Fin de cycle jeu #1440 — séquence exacte :
      1. Bilan général → admin (chat privé)
      2. PDF Compteur4, Compteur5, Perdus → admin (avant tout reset)
      3. Attente 20 secondes
      4. Reset du stock de données (prédictions, historiques, compteurs)
         — Les perdu_events ne sont JAMAIS effacés (comparaison inter-journées)
         — Les B par costume sont remis à la valeur B admin
         — Toutes les configurations admin sont préservées
      5. Notification de reset → admin (chat privé)
    """
    global prediction_history, bilan_1440_sent
    global pending_predictions, prediction_queue, finalized_messages_history
    global processed_games, prediction_checked_games, perdu_pdf_msg_id
    global compteur4_trackers, compteur4_events, compteur4_pdf_msg_id
    global compteur5_trackers, compteur5_events, compteur5_pdf_msg_id
    global compteur2_trackers, compteur2_seuil_B_per_suit
    global compteur1_trackers, compteur1_history
    global last_prediction_time, last_prediction_number_sent, suit_block_until
    global animation_tasks

    bilan_1440_sent = True

    # ── ÉTAPE 1 : Bilan → admin uniquement ──────────────────────────────────
    txt = get_bilan_text()
    total_finalized = sum(
        1 for p in prediction_history
        if p.get('status', '') not in ('en_cours', '')
    )
    header = (
        "🔔 **FIN DE CYCLE — JEU #1440**\n"
        f"Bilan sur **{total_finalized}** prédiction(s) finalisées.\n"
        "Le bot repart à neuf dans 20 secondes.\n\n"
    )
    # Bilan #1440 → admin uniquement (chat privé)
    if ADMIN_ID and ADMIN_ID != 0:
        try:
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_message(admin_entity, header + txt, parse_mode='markdown')
            logger.info("📊 Bilan #1440 envoyé à l'administrateur (chat privé).")
        except Exception as e:
            logger.error(f"❌ Erreur envoi bilan #1440 admin: {e}")

    # ── ÉTAPE 1.5 : Concours par costume → canal public ─────────────────────
    global concours_last_winner, concours_last_pct
    try:
        concours_txt1, concours_txt2 = get_concours_par_costume_text()

        # Identifier le vainqueur actuel pour le sauvegarder comme "précédent"
        _stats_tmp = {s: {'wins': 0, 'total': 0} for s in ALL_SUITS}
        for _p in prediction_history:
            _s = _p.get('suit', '')
            if _s in _stats_tmp:
                _st = _p.get('status', '')
                if 'gagne' in _st:
                    _stats_tmp[_s]['wins']  += 1
                    _stats_tmp[_s]['total'] += 1
                elif _st == 'perdu':
                    _stats_tmp[_s]['total'] += 1
        for _s in _stats_tmp:
            _t = _stats_tmp[_s]['total']
            _stats_tmp[_s]['pct'] = (_stats_tmp[_s]['wins'] / _t * 100) if _t > 0 else 0.0
        _current_winner = max(ALL_SUITS, key=lambda s: (_stats_tmp[s]['pct'], _stats_tmp[s]['total']))
        _current_pct    = _stats_tmp[_current_winner]['pct']

        # Persister en DB avant le reset (sera chargé au prochain démarrage)
        await db.db_save_kv('concours_last_winner', {
            'suit': _current_winner,
            'pct':  round(_current_pct, 2),
        })
        # Mettre à jour les globaux pour la prochaine fois que la fonction est appelée
        concours_last_winner = _current_winner
        concours_last_pct    = _current_pct
        logger.info(f"💾 Vainqueur concours sauvegardé : {_current_winner} ({_current_pct:.1f}%)")

        for _ch_id in [PREDICTION_CHANNEL_ID, PREDICTION_CHANNEL_ID2, PREDICTION_CHANNEL_ID3, PREDICTION_CHANNEL_ID4]:
            if not _ch_id:
                continue
            canal_entity = await resolve_channel(_ch_id)
            if canal_entity:
                await client.send_message(canal_entity, concours_txt1, parse_mode='markdown')
                await asyncio.sleep(2)
                await client.send_message(canal_entity, concours_txt2, parse_mode='markdown')
                logger.info(f"🏆 Messages concours envoyés dans le canal {_ch_id}.")
            else:
                logger.warning(f"⚠️ Canal {_ch_id} introuvable — concours non envoyé.")
    except Exception as e:
        logger.error(f"❌ Erreur envoi concours #1440 canal: {e}")

    # ── ÉTAPE 2 : Envoi de tous les PDFs AVANT le reset ─────────────────────
    logger.info("📄 Envoi des PDFs avant reset #1440...")

    # PDF Compteur4 (snapshot — données persistantes, NON effacées au reset)
    try:
        if compteur4_events:
            pdf4 = generate_compteur4_pdf(compteur4_events)
            buf4 = io.BytesIO(pdf4)
            buf4.name = "compteur4_absences_cycle.pdf"
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_file(
                admin_entity, buf4,
                caption=(
                    "🔴 **COMPTEUR4 — SNAPSHOT FIN DE CYCLE**\n"
                    f"Total séries d'absences : **{len(compteur4_events)}**\n"
                    "⚠️ Ces données sont persistantes — elles ne seront PAS effacées au reset"
                ),
                parse_mode='markdown',
                file_name="compteur4_absences_cycle.pdf"
            )
            logger.info("✅ PDF Compteur4 snapshot envoyé avant reset")
    except Exception as e:
        logger.error(f"❌ PDF Compteur4 avant reset: {e}")

    # PDF Compteur5
    try:
        if compteur5_events:
            pdf5 = generate_compteur5_pdf(compteur5_events)
            buf5 = io.BytesIO(pdf5)
            buf5.name = "compteur5_presences_final.pdf"
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_file(
                admin_entity, buf5,
                caption=(
                    "✅ **COMPTEUR5 — PDF FINAL DU CYCLE**\n"
                    f"Total présences : **{len(compteur5_events)}**\n"
                    "_(Sauvegarde avant reset)_"
                ),
                parse_mode='markdown',
                file_name="compteur5_presences_final.pdf"
            )
            logger.info("✅ PDF Compteur5 final envoyé avant reset")
    except Exception as e:
        logger.error(f"❌ PDF Compteur5 avant reset: {e}")

    # PDF Perdus (perdu_events ne sera JAMAIS effacé — comparaison inter-journées)
    try:
        if perdu_events:
            await send_perdu_pdf()
            logger.info("✅ PDF Perdus final envoyé avant reset")
    except Exception as e:
        logger.error(f"❌ PDF Perdus avant reset: {e}")

    # ── ÉTAPE 3 : Attente 20 secondes ───────────────────────────────────────
    logger.info("⏳ Attente 20 secondes avant reset #1440...")
    await asyncio.sleep(20)

    # ── ÉTAPE 4 : Reset du stock de données ─────────────────────────────────
    nb_pending = len(pending_predictions)
    nb_queue   = len(prediction_queue)
    nb_history = len(prediction_history)
    nb_c5      = len(compteur5_events)
    nb_perdu   = len(perdu_events)     # conservé, juste pour le rapport

    stop_all_animations()

    # Prédictions
    pending_predictions.clear()
    prediction_queue.clear()
    prediction_history.clear()
    finalized_messages_history.clear()
    processed_games.clear()
    prediction_checked_games.clear()
    recently_predicted.clear()
    suit_block_until.clear()

    # Compteur 11 : rotation des perdus jour J → jour J+1
    global compteur11_perdu_hier, compteur11_perdu_today, compteur11_triggered
    compteur11_perdu_hier  = list(compteur11_perdu_today)
    compteur11_perdu_today = []
    compteur11_triggered.clear()
    save_compteur11()   # Sauvegarde avec liste vide (nouveau jour)

    last_prediction_time        = None
    last_prediction_number_sent = 0
    perdu_pdf_msg_id            = None

    # Événements Compteur5 (vidés — PDF déjà envoyé)
    compteur5_events.clear()
    compteur5_pdf_msg_id = None
    # ⚠️ compteur4_events N'EST PAS EFFACÉ — persistant entre cycles (comme C7)
    compteur4_pdf_msg_id = None

    # Compteurs remis à 0
    for suit in ALL_SUITS:
        compteur4_trackers[suit] = 0
        compteur5_trackers[suit] = 0
        # Reset de la série d'absence courante (l'historique persistant reste intact)
        compteur4_current[suit] = {'count': 0, 'start_game': None, 'start_time': None, 'alerted': False}

    for tracker in compteur2_trackers.values():
        tracker.counter = 0
        tracker.last_increment_game = 0

    for tracker in compteur1_trackers.values():
        tracker.counter    = 0
        tracker.start_game = 0
        tracker.last_game  = 0
    compteur1_history.clear()

    # B par costume remis à la valeur B admin (les hausses du cycle sont effacées)
    for suit in ALL_SUITS:
        compteur2_seuil_B_per_suit[suit] = compteur2_seuil_B
    logger.info(f"🔄 B par costume remis à B admin ({compteur2_seuil_B}) pour tous les costumes")

    # Compteur8 : reset des streaks courants (les séries terminées sont persistantes)
    for suit in ALL_SUITS:
        compteur8_current[suit] = {'count': 0, 'start_game': None, 'start_time': None}
    logger.info("🔄 Compteur8 streaks remis à 0 (séries persistantes conservées)")

    # ⚠️ perdu_events N'EST JAMAIS EFFACÉ — comparaison inter-journées préservée

    # Données horaires (heures favorables) : reset quotidien pour que les heures
    # reflètent le JOUR ACTUEL et non l'historique cumulé de tous les jours
    global hourly_suit_data, hourly_game_count
    hourly_suit_data  = {h: {'♠': 0, '♥': 0, '♦': 0, '♣': 0} for h in range(24)}
    hourly_game_count = {h: 0 for h in range(24)}
    save_hourly_data()
    logger.info("🔄 Données horaires remises à 0 (heures favorables recalculées demain)")

    logger.info("🔄 Reset complet du stock #1440 — configs admin et perdu_events préservés.")

    # ── ÉTAPE 5 : Notification de reset → admin ──────────────────────────────
    if ADMIN_ID and ADMIN_ID != 0:
        try:
            admin_entity = await client.get_entity(ADMIN_ID)
            msg = (
                "♻️ **RESET EFFECTUÉ — FIN DU CYCLE #1440**\n\n"
                "**Données effacées :**\n"
                f"  • {nb_pending} prédiction(s) en attente\n"
                f"  • {nb_queue} prédiction(s) en file\n"
                f"  • {nb_history} entrées d'historique\n"
                f"  • {nb_c5} événement(s) Compteur5\n"
                f"  • B par costume remis à B admin ({compteur2_seuil_B})\n\n"
                "**Préservé (persistant entre cycles) :**\n"
                f"  • {nb_perdu} pertes historiques (inter-journées)\n"
                f"  • {len(compteur4_events)} séries Compteur4 (absences persistantes)\n"
                f"  • {len(compteur7_completed)} séries Compteur7 (présences ≥{COMPTEUR7_THRESHOLD}) — PDF inchangé\n"
                f"  • {len(compteur8_completed)} séries Compteur8 (absences ≥{COMPTEUR8_THRESHOLD}) — PDF inchangé\n"
                f"  • B admin : {compteur2_seuil_B}\n"
                f"  • Seuil Compteur4 : {COMPTEUR4_THRESHOLD}\n"
                f"  • Seuil Compteur5 : {COMPTEUR5_THRESHOLD}\n"
                f"  • Restriction horaire : {'Active' if PREDICTION_HOURS else 'Inactive'}\n"
                "  • Toutes les configurations admin\n\n"
                "✅ Le bot est neuf et prêt pour le prochain cycle."
            )
            await client.send_message(admin_entity, msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Erreur notif admin #1440: {e}")


async def process_game_result(game_number: int, player_suits: Set[str], player_cards_raw: list, is_finished: bool = False):
    """Traite un résultat de jeu venant de l'API 1xBet."""
    global current_game_number, processed_games, bilan_1440_sent

    if game_number > current_game_number:
        current_game_number = game_number

    # ─────────────────────────────────────────────────────────────────────────
    # player_hand_complete : vrai dès que le JOUEUR a terminé ses cartes.
    # Le banquier n'est pas attendu — ses cartes ne concernent pas nos prédictions.
    #   • ≥ 3 cartes joueur → a tiré la 3ème  → terminé
    #   • 2 cartes, score ≥ 6 → reste ou naturelle → terminé
    #   • jeu is_finished → terminé de toute façon (filet de sécurité)
    # ─────────────────────────────────────────────────────────────────────────
    player_hand_complete = _is_player_hand_complete(player_cards_raw) or is_finished

    # Vérification dynamique des prédictions (TOUJOURS — même partie en cours)
    # Victoire immédiate si costume trouvé, échec seulement si partie entièrement terminée
    await check_prediction_result(game_number, player_suits, is_finished)

    # ── Vérification formation (1 seul check au jeu prédit+1, pas de rattrapage) ──
    if player_hand_complete and game_number in formation_follow_ups:
        fup         = formation_follow_ups.pop(game_number)
        rec_suit    = fup['recommended_suit']
        orig_game   = fup['original_game']
        card_pos    = fup.get('card_position', '?')   # '1ère', '2ème' ou '3ème'
        rec_disp    = SUIT_DISPLAY.get(rec_suit, rec_suit)
        active_pred = pending_predictions.get(orig_game)

        # Vérifier toutes les cartes du jeu prédit (#N) présentes au jeu #N+1
        # pour savoir quelle position est sortie (informatif)
        cards_orig  = fup.get('cards_at_predicted', [])  # [suit1, suit2, suit3] de #N
        pos_labels  = ['1ère', '2ème', '3ème']
        found_pos   = None
        for idx, cs in enumerate(cards_orig):
            if cs in player_suits:
                found_pos = pos_labels[idx] if idx < len(pos_labels) else f'{idx+1}ème'
                break  # on enregistre la 1ère trouvée par ordre d'apparition

        if rec_suit in player_suits:
            # ✅ La carte recommandée est présente → formation réussie
            logger.info(f"✅ Formation validée #{orig_game} → {rec_suit} ({card_pos} carte) présent au #{game_number}")
            if active_pred:
                active_pred['formation_suffix'] = (
                    f"\n\n♟️ **Formation** : **{rec_disp}** ({card_pos} carte) au jeu **#{game_number}**\n"
                    f"✅ Présent — formation réussie !"
                )
        else:
            # ❌ La carte recommandée est absente — on note quelle autre carte est sortie si applicable
            note = f" (c'est la **{found_pos}** carte qui est sortie)" if found_pos else ""
            logger.info(f"❌ Formation ratée #{orig_game} → {rec_suit} absent au #{game_number}{note}")
            if active_pred:
                active_pred['formation_suffix'] = (
                    f"\n\n♟️ **Formation** : **{rec_disp}** ({card_pos} carte) au jeu **#{game_number}**\n"
                    f"❌ Absent{note}"
                )
        # Formation terminée — pas de rattrapage R1/R2

    # File de prédictions : envoie dès que la main joueur est complète (N+df match)
    await process_prediction_queue(game_number, player_hand_complete)

    # ─────────────────────────────────────────────────────────────────────────
    # COMPTEURS : dès que la main JOUEUR est complète (banquier non attendu).
    #   • 3 cartes joueur → a tiré la 3ème → on enregistre immédiatement
    #   • 2 cartes, score ≥ 6 → joueur ne tire plus → on enregistre
    #   • 2 cartes, score 0-5 → joueur va tirer → on attend la 3ème carte
    # Les costumes du joueur sont définitifs → aucun risque de données partielles.
    # ─────────────────────────────────────────────────────────────────────────
    if player_hand_complete and game_number not in processed_games:
        processed_games.add(game_number)

        add_to_history(game_number, player_suits)
        asyncio.ensure_future(db.db_save_game_log(game_number, list(player_suits)))
        update_compteur1(game_number, player_suits)
        update_compteur2(game_number, player_suits)

        # ── 216 trackers silencieux indépendants (C13 + C2 par combo) ──────
        update_silent_combos(game_number, player_suits)
        # Sauvegarde périodique : toutes les 20 parties
        if game_number % 20 == 0:
            asyncio.ensure_future(save_silent_combo_stats())

        # Compteur4: séries d'absences (seuil + série complète, persistant)
        threshold4, completed4 = update_compteur4(game_number, player_suits, player_cards_raw)
        for suit in threshold4:
            cur4 = compteur4_current[suit]
            asyncio.create_task(send_compteur4_threshold_alert(suit, game_number, cur4['start_game']))
            # ── Compteur C4 → fenêtre favorable (2 déclenchements = fenêtre) ──
            global c4_favorable_event_count
            c4_favorable_event_count += 1
            logger.info(f"⭐ C4 favorable event #{c4_favorable_event_count} ({suit})")
            if c4_favorable_event_count >= 2:
                c4_favorable_event_count = 0
                asyncio.create_task(trigger_favorable_window_from_c4())
        for series4 in completed4:
            asyncio.create_task(send_compteur4_series_alert(series4))
            asyncio.create_task(send_compteur4_pdf())

        # Compteur5: détecter les présences consécutives de 10
        triggered5 = update_compteur5(game_number, player_suits, player_cards_raw)
        if triggered5:
            asyncio.create_task(send_compteur5_alert(triggered5, game_number))
            asyncio.create_task(send_compteur5_pdf())

        # Compteur7: séries consécutives de présences (min 5) — persistant entre resets
        completed7 = update_compteur7(game_number, player_suits)
        for series in completed7:
            asyncio.create_task(send_compteur7_alert(series))
            asyncio.create_task(send_compteur7_pdf())

        # Compteur8: séries consécutives d'ABSENCES (≥5) — miroir exact du Compteur7
        completed8 = update_compteur8(game_number, player_suits)
        for series8 in completed8:
            asyncio.create_task(send_compteur8_series_alert(series8))
            asyncio.create_task(send_compteur8_pdf())

        # ── C8 PRÉDICTION : seuil COMPTEUR8_PRED_SEUIL atteint → prédit le manque ──
        # Si absence d'un costume atteint exactement le seuil → prédit ce costume
        # au jeu suivant (game_number + 1) et bloque C2 / C13 pour ce cycle.
        c8_pred_suits: List[str] = []
        for _suit in ALL_SUITS:
            if compteur8_current[_suit]['count'] == COMPTEUR8_PRED_SEUIL:
                c8_pred_suits.append(_suit)

        c8_blocks_others = len(c8_pred_suits) > 0  # C8 s'impose ce jeu

        for _suit in c8_pred_suits:
            _pred_game_c8 = game_number + 1
            _cur8         = compteur8_current[_suit]
            _suit_disp    = SUIT_DISPLAY.get(_suit, _suit)
            _reason_c8    = (
                f"C8 : {_suit_disp} absent {COMPTEUR8_PRED_SEUIL} fois de suite "
                f"(depuis #{_cur8['start_game']}). "
                f"Seuil {COMPTEUR8_PRED_SEUIL} atteint → C8 s'impose et prédit "
                f"ce costume manquant au jeu #{_pred_game_c8}."
            )
            asyncio.create_task(
                send_compteur8_pred_alert(_suit, game_number, _pred_game_c8, _reason_c8, [])
            )
            logger.info(
                f"🔴 C8 PRED: {_suit} absent {COMPTEUR8_PRED_SEUIL}x "
                f"→ prédit #{_pred_game_c8} [C8 bloque C2/C13]"
            )
        # ─────────────────────────────────────────────────────────────────────

        # Compteur13: costumes consécutifs → prédiction miroir validée par C2
        # Bloqué si C8 s'impose ce jeu
        # C13 est prédicteur principal : s'il se déclenche, C2 est bloqué sur ce jeu
        c13_firing = False
        if compteur13_active and not c8_blocks_others:
            triggers13 = update_compteur13(game_number, player_suits)
            for trig13 in triggers13:
                # Filtre présence : refuser si le costume prédit est trop présent (≥ PRES_BLOCK_SEUIL)
                _sp13       = trig13['suit_pred']
                _pres_count = compteur1_trackers[_sp13].counter if _sp13 in compteur1_trackers else 0
                if _pres_count >= PRES_BLOCK_SEUIL:
                    logger.info(
                        f"⛔ C13 #{game_number} {_sp13} refusée : "
                        f"présent {_pres_count}x consécutif (seuil {PRES_BLOCK_SEUIL})"
                    )
                elif trig13.get('c2_mirror_blocked'):
                    # Filtre miroir bloqué : le costume que C13 veut prédire est déjà
                    # un manque bloqué dans C2 (absent ≥ B fois) → prédiction annulée
                    _b_pred = compteur2_seuil_B_per_suit.get(_sp13, compteur2_seuil_B)
                    logger.info(
                        f"⛔ C13 #{game_number} {_sp13} bloquée : "
                        "miroir prédit est manque bloqué C2 "
                        f"(absent {compteur2_trackers[_sp13].counter}x ≥ B={_b_pred})"
                    )
                else:
                    asyncio.create_task(send_compteur13_alert(trig13, game_number))
        elif compteur13_active and c8_blocks_others:
            # Consommer les triggers C13 sans envoyer, noter le blocage
            triggers13_blocked = update_compteur13(game_number, player_suits)
            if triggers13_blocked:
                logger.info(
                    f"⏭️ C13 ignoré ce jeu (C8 s'impose, seuil {COMPTEUR8_PRED_SEUIL} atteint)"
                )

        # Données horaires pour /comparaison
        update_hourly_data(player_suits)

        # Compteur14: fréquence absolue des costumes (cycle de 1440 jeux)
        c14_cycle_done = update_compteur14(game_number, player_suits)
        if c14_cycle_done:
            # Le rapport est envoyé AVANT le reset : on enchaîne les deux dans la même tâche
            async def _c14_finalize(_gn=game_number):
                await send_compteur14_report(_gn, is_final=True)
                reset_compteur14()
                logger.info(f"🔄 C14: cycle {COMPTEUR14_CYCLE_SIZE} jeux terminé → rapport envoyé + reset")
            asyncio.create_task(_c14_finalize())

        # ── Pré-détection C11 : C11 a-t-il priorité sur ce jeu ? ────────────
        # C11 se déclenche quand game_number == game_number_perdu_hier - PREDICTION_DF
        # Si oui, C2 est bloqué (C11 prioritaire, indépendant de C2 et C6)
        if compteur11_perdu_hier and is_finished:
            for entry in compteur11_perdu_hier:
                trigger_at = entry['game_number'] - PREDICTION_DF
                if game_number == trigger_at:
                    break
        # ────────────────────────────────────────────────────────────────────

        # C2 n'est PAS un prédicteur autonome.
        # C2 est uniquement un validateur consulté par C13 (et C8/C11 pour leurs propres règles).
        # Les trackers C2 (update_compteur2) continuent de fonctionner normalement
        # afin que C13 puisse lire les compteurs d'absence via check_threshold().

        logger.info(f"📊 Jeu #{game_number}: joueur {player_suits} | C4={dict(compteur4_trackers)}")

    # ── Compteur 11 : perdu hier → prédit aujourd'hui ───────────────────────
    # Déclenchement à game_number_perdu_hier - PREDICTION_DF (respecte l'écart df)
    # C11 est indépendant : priorité sur C2, bypass C6
    if compteur11_perdu_hier and is_finished:
        for entry in compteur11_perdu_hier:
            trigger_at = entry['game_number'] - PREDICTION_DF
            if game_number == trigger_at:
                asyncio.create_task(compteur11_fire(entry, game_number))
    # ────────────────────────────────────────────────────────────────────────

    # Fin de cycle : jeu #1440 terminé → bilan envoyé + reset historique
    if game_number == 1440 and is_finished and not bilan_1440_sent:
        asyncio.create_task(send_bilan_and_reset_at_1440())

    # Nouveau cycle détecté (jeu #1 ou #2) → réarmer le flag pour le prochain #1440
    if game_number <= 2 and bilan_1440_sent:
        bilan_1440_sent = False
        logger.info("🔄 Nouveau cycle détecté — bilan_1440 réarmé")

# ============================================================================
# BOUCLE DE POLLING API
# ============================================================================

async def api_polling_loop():
    """
    Boucle principale : interroge l'API 1xBet et traite les résultats.
    — Intervalle de base 4s avec jitter aléatoire ±1s pour éviter les patterns détectables
    — Backoff exponentiel automatique en cas d'échecs consécutifs (max 60s)
    """
    global game_history, game_result_cache, last_api_success_time, api_silence_alerted

    logger.info("🔄 Démarrage boucle de polling API (toutes les 4s ± jitter)...")
    _api_sem = asyncio.Semaphore(1)  # 1 seul appel API simultané max
    BASE_INTERVAL  = 4.0   # secondes entre chaque appel
    JITTER_RANGE   = 1.0   # ± cette valeur (ex: 3.0s – 5.0s)
    MAX_BACKOFF    = 60.0  # backoff max en secondes après de nombreux échecs

    while True:
        try:
            async with _api_sem:
                results = await asyncio.wait_for(
                    get_latest_results(),
                    timeout=35  # 35s max (légèrement supérieur au timeout interne api_utils)
                )

            if results:
                last_api_success_time = datetime.now()
                api_silence_alerted = False
                for result in results:
                    game_number  = result['game_number']
                    player_cards = result.get('player_cards', [])

                    if not player_cards:
                        continue

                    player_suits = get_player_suits(player_cards)
                    if not player_suits:
                        continue

                    is_finished = result.get('is_finished', False)

                    # Mettre à jour l'historique (jeux terminés uniquement)
                    game_history[game_number] = result

                    # ── Cache live : stocker TOUS les jeux (en cours + terminés) ──
                    # Un jeu terminé ne régresse jamais → on ne remplace pas is_finished=True
                    existing = game_result_cache.get(game_number, {})
                    if not existing.get('is_finished', False):
                        game_result_cache[game_number] = {
                            'player_cards': player_cards,
                            'player_suits': player_suits,
                            'is_finished': is_finished,
                        }

                    # Victoire immédiate si costume trouvé, échec seulement si partie terminée
                    await process_game_result(game_number, player_suits, player_cards, is_finished)

                # ── Nettoyage du cache live : conserver au max 200 entrées ──
                if len(game_result_cache) > 200:
                    cutoff = sorted(game_result_cache.keys())[:-150]
                    for k in cutoff:
                        game_result_cache.pop(k, None)

                # Garder l'historique propre (max 500 jeux)
                if len(game_history) > 500:
                    oldest = sorted(game_history.keys())[:100]
                    for k in oldest:
                        game_history.pop(k, None)
            else:
                logger.debug("🔄 API: aucun résultat")

        except Exception as e:
            logger.error(f"❌ Erreur polling API: {e}")

        # ── Calcul de l'intervalle avec jitter et backoff exponentiel ────────
        import api_utils as _au
        fails = getattr(_au, 'consecutive_failures', 0)
        if fails >= 3:
            # Backoff exponentiel plafonné : 4 * 2^(fails-3) avec max 60s
            backoff = min(BASE_INTERVAL * (2 ** (fails - 3)), MAX_BACKOFF)
            sleep_t = backoff + random.uniform(0, JITTER_RANGE)
            if fails == 3:
                logger.warning(f"⚠️ API: {fails} échecs consécutifs — backoff {backoff:.1f}s")
        else:
            # Intervalle normal avec jitter ±1s (entre 3.0 et 5.0s)
            sleep_t = BASE_INTERVAL + random.uniform(-JITTER_RANGE, JITTER_RANGE)

        await asyncio.sleep(max(3.0, sleep_t))

# ============================================================================
# RESET ET NETTOYAGE
# ============================================================================

async def cleanup_stale_predictions():
    global pending_predictions
    from config import PREDICTION_TIMEOUT_MINUTES
    now = datetime.now()
    stale = []

    for game_number, pred in list(pending_predictions.items()):
        sent_time = pred.get('sent_time')
        if sent_time:
            age_minutes = (now - sent_time).total_seconds() / 60
            if age_minutes >= PREDICTION_TIMEOUT_MINUTES:
                stale.append(game_number)
        else:
            # BUG FIX : sent_time=None → prédiction jamais nettoyée → bot bloqué.
            # Fallback : utiliser l'heure actuelle comme référence — on la retire immédiatement.
            logger.warning(f"🧹 #{game_number} sans sent_time — forcé en timeout")
            stale.append(game_number)

    for game_number in stale:
        pred = pending_predictions.get(game_number)
        if pred:
            suit = pred.get('suit', '?')
            logger.warning(f"🧹 #{game_number} ({suit}) expiré (timeout)")
            stop_animation(game_number)
            suit_display = SUIT_DISPLAY.get(suit, suit)
            expired_msg = f"⏰ **PRÉDICTION #{game_number}**\n🎯 {suit_display}\n⌛ **EXPIRÉE**"
            for _ch_id, _mid in [
                (PREDICTION_CHANNEL_ID,  pred.get('message_id')),
                (PREDICTION_CHANNEL_ID2, pred.get('channel2_message_id')),
                (PREDICTION_CHANNEL_ID3, pred.get('channel3_message_id')),
                (PREDICTION_CHANNEL_ID4, pred.get('channel4_message_id')),
            ]:
                if _ch_id and _mid:
                    _ent = await resolve_channel(_ch_id)
                    if _ent:
                        await safe_edit_message(_ent, _mid, expired_msg,
                                                label=f"expirée #{game_number}", max_retries=2)
            del pending_predictions[game_number]
            save_pending_predictions()

async def auto_reset_system():
    """Vérifie toutes les 30s les prédictions en attente et supprime celles expirées (>10min)."""
    while True:
        try:
            await asyncio.sleep(30)
            if pending_predictions:
                await cleanup_stale_predictions()
        except Exception as e:
            logger.error(f"❌ Erreur auto_reset: {e}")
            await asyncio.sleep(30)

# ─── Watchdog global : déblocage automatique ────────────────────────────────

_api_polling_task: Optional[asyncio.Task] = None

async def _api_polling_guardian():
    """Lance api_polling_loop et la redémarre automatiquement si elle s'arrête."""
    global _api_polling_task
    while True:
        try:
            logger.info("🔄 Démarrage/redémarrage api_polling_loop via guardian")
            _api_polling_task = asyncio.create_task(api_polling_loop())
            await _api_polling_task
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"❌ Guardian: api_polling_loop crash inattendu: {e}")
        logger.warning("⚠️ api_polling_loop terminée — redémarrage dans 5s")
        await asyncio.sleep(5)

async def auto_watchdog_task():
    """
    Watchdog global — s'exécute toutes les 60s.
    Détecte et débloque automatiquement :
      1. Prédictions bloquées au-delà de 15 min (sécurité post-timeout)
      2. Tous les costumes bloqués simultanément (suit_block_until)
      3. API 1xBet silencieuse depuis trop longtemps → alerte admin
      4. Notifie l'admin à chaque action
    """
    global pending_predictions, suit_block_until, prediction_queue, api_silence_alerted
    from config import PREDICTION_TIMEOUT_MINUTES, FORCE_RESTART_THRESHOLD

    HARD_TIMEOUT = max(PREDICTION_TIMEOUT_MINUTES, 8)  # 8 min minimum (API bloquée)

    while True:
        await asyncio.sleep(60)
        try:
            now = datetime.now()
            actions = []

            # ── 1. Prédictions bloquées au-delà du hard timeout ─────────────
            hard_stale = []
            for game_number, pred in list(pending_predictions.items()):
                sent_time = pred.get('sent_time')
                if sent_time is None or (now - sent_time).total_seconds() / 60 >= HARD_TIMEOUT:
                    hard_stale.append(game_number)

            if hard_stale:
                for gn in hard_stale:
                    pred = pending_predictions.pop(gn, None)
                    if pred:
                        stop_animation(gn)
                        suit = pred.get('suit', '?')
                        actions.append(f"🧹 Prédiction #{gn} ({suit}) forcée hors mémoire")
                        sd = SUIT_DISPLAY.get(suit, suit)
                        wd_msg = f"⏰ **PRÉDICTION #{gn}**\n🎯 {sd}\n⌛ **EXPIRÉE (watchdog)**"
                        for _ch_id, _mid in [
                            (PREDICTION_CHANNEL_ID,  pred.get('message_id')),
                            (PREDICTION_CHANNEL_ID2, pred.get('channel2_message_id')),
                            (PREDICTION_CHANNEL_ID3, pred.get('channel3_message_id')),
                            (PREDICTION_CHANNEL_ID4, pred.get('channel4_message_id')),
                        ]:
                            if _ch_id and _mid:
                                _ent = await resolve_channel(_ch_id)
                                if _ent:
                                    await safe_edit_message(_ent, _mid, wd_msg,
                                                            label=f"watchdog #{gn}", max_retries=2)

            # ── 2. Tous les costumes simultanément bloqués ──────────────────
            blocked_suits = [s for s in ALL_SUITS if s in suit_block_until and now < suit_block_until[s]]
            if len(blocked_suits) == len(ALL_SUITS):
                suit_block_until.clear()
                actions.append("🔓 Tous les costumes étaient bloqués — déblocage forcé")
                logger.warning("⚠️ Watchdog: tous les costumes bloqués → déblocage automatique")

            # ── 3. API 1xBet silencieuse (bloquée par le datacenter) ─────────
            if last_api_success_time is not None and not api_silence_alerted:
                silence_min = (now - last_api_success_time).total_seconds() / 60
                if silence_min >= API_SILENCE_ALERT_MINUTES:
                    api_silence_alerted = True
                    actions.append(
                        f"⚠️ API 1xBet silencieuse depuis {int(silence_min)} min\n"
                        "Cause probable : IP du serveur bloquée par 1xBet.\n"
                        "Le bot fonctionne mais ne reçoit plus de données de jeu."
                    )
                    logger.error(f"❌ Watchdog: API 1xBet muette depuis {int(silence_min)} min")

            # ── 4. Notification admin ────────────────────────────────────────
            if actions and ADMIN_ID:
                try:
                    admin_entity = await client.get_entity(ADMIN_ID)
                    msg = "🤖 **WATCHDOG — Alerte automatique**\n\n" + "\n".join(actions)
                    await client.send_message(admin_entity, msg, parse_mode='markdown')
                except Exception as e:
                    logger.warning(f"Watchdog: impossible de notifier admin: {e}")

        except Exception as e:
            logger.error(f"❌ Erreur watchdog: {e}")


async def keep_alive_task():
    """
    Anti-spin-down pour Render.com.
    - Ping /health toutes les 60 secondes (< délai de spin-down de 15 min)
    - Utilise RENDER_EXTERNAL_URL (URL publique externe) pour que Render compte la requête
    - Fallback local si l'URL externe n'est pas disponible
    """
    import gc
    ping_url = f"{RENDER_EXTERNAL_URL}/health" if RENDER_EXTERNAL_URL else f"http://localhost:{PORT}/health"
    logger.info(f"💓 Keep-alive démarré → {ping_url} (toutes les 60s)")
    ping_count = 0

    while True:
        try:
            async with _aiohttp.ClientSession() as session:
                async with session.get(ping_url, timeout=_aiohttp.ClientTimeout(total=15)) as resp:
                    if resp.status == 200:
                        logger.debug("💓 Keep-alive OK")
                    else:
                        logger.warning(f"⚠️ Keep-alive: status inattendu {resp.status}")
        except Exception as e:
            logger.warning(f"⚠️ Keep-alive ping échoué: {e}")

        ping_count += 1

        # ── GC toutes les 10 pings (~10 min) ─────────────────────────────
        if ping_count % 10 == 0:
            gc.collect()
            logger.debug(f"🧹 GC collecté (ping #{ping_count})")

        # ── Ping DB toutes les 5 pings (~5 min) — reconnecte si mort ──────
        if ping_count % 5 == 0:
            ok = await db.ping_db()
            if not ok:
                logger.warning("⚠️ DB inaccessible après reconnexion")
            else:
                logger.debug("💾 DB ping OK")

        # ── Sauvegarde automatique de la config runtime toutes les 60s ──────
        db.db_schedule(save_runtime_config())

        await asyncio.sleep(60)  # 60 secondes — bien en dessous du seuil de 15 min

async def perform_full_reset(reason: str):
    global pending_predictions, last_prediction_time
    global last_prediction_number_sent, compteur2_trackers, prediction_queue
    global compteur1_trackers, compteur1_history, processed_games, prediction_checked_games
    global compteur2_seuil_B_per_suit, compteur2_seuil_B, game_result_cache

    stats = len(pending_predictions)
    queue_stats = len(prediction_queue)

    for tracker in compteur1_trackers.values():
        if tracker.counter >= MIN_CONSECUTIVE_FOR_STATS:
            save_compteur1_series(tracker.suit, tracker.counter, tracker.start_game, tracker.last_game)

    for tracker in compteur2_trackers.values():
        tracker.counter = 0
        tracker.last_increment_game = 0

    for tracker in compteur1_trackers.values():
        tracker.counter = 0
        tracker.start_game = 0
        tracker.last_game = 0

    for suit in ALL_SUITS:
        compteur4_trackers[suit] = 0
        compteur4_current[suit] = {'count': 0, 'start_game': None, 'start_time': None, 'alerted': False}

    stop_all_animations()
    pending_predictions.clear()
    prediction_queue.clear()
    processed_games.clear()
    prediction_checked_games.clear()
    recently_predicted.clear()
    game_result_cache.clear()
    last_prediction_time = None
    last_prediction_number_sent = 0
    suit_block_until.clear()

    # Remettre les B dynamiques par costume à la valeur initiale
    for suit in ALL_SUITS:
        compteur2_seuil_B_per_suit[suit] = compteur2_seuil_B
    logger.info(f"🔄 B par costume réinitialisé à {compteur2_seuil_B} pour tous les costumes")

    logger.info(f"🔄 {reason} - {stats} actives, {queue_stats} file cleared")

    if ADMIN_ID and ADMIN_ID != 0:
        try:
            admin_entity = await client.get_entity(ADMIN_ID)
            msg = (
                "🔄 **RESET SYSTÈME**\n\n"
                f"{reason}\n\n"
                f"✅ {stats} prédictions actives effacées\n"
                f"✅ {queue_stats} prédictions en file effacées\n"
                "✅ Compteurs remis à zéro\n\n"
                "🤖 Baccarat AI"
            )
            await client.send_message(admin_entity, msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Impossible de notifier l'admin: {e}")

# ============================================================================
# COMMANDES ADMIN
# ============================================================================

async def cmd_heures(event):
    """Gestion des plages horaires de prédiction."""
    global PREDICTION_HOURS

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    try:
        parts = event.message.message.split()

        if len(parts) == 1:
            now = datetime.now()
            allowed = "✅ OUI" if is_prediction_time_allowed() else "❌ NON"
            await event.respond(
                "⏰ **RESTRICTION HORAIRE**\n\n"
                f"Heure actuelle: **{now.strftime('%H:%M')}**\n"
                f"Prédictions autorisées: {allowed}\n\n"
                f"**Plages actives:**\n{format_hours_config()}\n\n"
                "**Usage:**\n"
                "`/heures add HH-HH` — Ajouter une plage\n"
                "`/heures del HH-HH` — Supprimer une plage\n"
                "`/heures clear` — Supprimer toutes les plages (24h/24)"
            )
            return

        sub = parts[1].lower()

        if sub == 'clear':
            PREDICTION_HOURS.clear()
            await event.respond("✅ **Toutes les restrictions horaires supprimées** — prédictions 24h/24")
            return

        if sub == 'add' and len(parts) >= 3:
            raw = parts[2]
            if '-' not in raw:
                await event.respond("❌ Format: HH-HH (ex: `/heures add 18-17`)")
                return
            s_str, e_str = raw.split('-', 1)
            s_h, e_h = int(s_str.strip()), int(e_str.strip())
            if not (0 <= s_h <= 23 and 0 <= e_h <= 23):
                await event.respond("❌ Heures entre 0 et 23")
                return
            PREDICTION_HOURS.append((s_h, e_h))
            await event.respond(
                f"✅ **Plage ajoutée:** {s_h:02d}h00 → {e_h:02d}h00\n\n"
                f"**Plages actives:**\n{format_hours_config()}"
            )
            return

        if sub == 'del' and len(parts) >= 3:
            raw = parts[2]
            if '-' not in raw:
                await event.respond("❌ Format: HH-HH")
                return
            s_str, e_str = raw.split('-', 1)
            s_h, e_h = int(s_str.strip()), int(e_str.strip())
            if (s_h, e_h) in PREDICTION_HOURS:
                PREDICTION_HOURS.remove((s_h, e_h))
                await event.respond(f"✅ **Plage supprimée:** {s_h:02d}h00 → {e_h:02d}h00")
            else:
                await event.respond(f"❌ Plage {s_h:02d}h-{e_h:02d}h introuvable")
            return

        await event.respond(
            "❌ Usage:\n"
            "`/heures` — Voir config\n"
            "`/heures add HH-HH` — Ajouter plage\n"
            "`/heures del HH-HH` — Supprimer plage\n"
            "`/heures clear` — Tout supprimer"
        )

    except ValueError:
        await event.respond("❌ Format invalide. Utilisez des entiers (ex: `/heures add 18-17`)")
    except Exception as e:
        logger.error(f"Erreur cmd_heures: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur4(event):
    """Affiche le statut du Compteur4 et envoie le PDF des écarts."""
    global compteur4_trackers, compteur4_events, COMPTEUR4_THRESHOLD

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    try:
        parts = event.message.message.split()

        if len(parts) >= 2:
            sub = parts[1].lower()

            if sub == 'seuil' and len(parts) >= 3:
                try:
                    val = int(parts[2])
                    if not 5 <= val <= 50:
                        await event.respond("❌ Seuil entre 5 et 50")
                        return
                    old = COMPTEUR4_THRESHOLD
                    COMPTEUR4_THRESHOLD = val
                    await event.respond(f"✅ **Seuil Compteur4:** {old} → {val}")
                    return
                except ValueError:
                    await event.respond("❌ Usage: `/compteur4 seuil 10`")
                    return

            if sub == 'pdf':
                await event.respond("📄 Génération du PDF en cours...")
                await send_compteur4_pdf()
                return

            if sub == 'reset':
                for suit in ALL_SUITS:
                    compteur4_trackers[suit] = 0
                    compteur4_current[suit] = {'count': 0, 'start_game': None, 'start_time': None, 'alerted': False}
                compteur4_events.clear()
                save_compteur4_data()
                await event.respond("🔄 **Compteur4 reset** — Compteurs, séries courantes et historique effacés")
                return

        # Affichage statut
        suit_names  = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
        suit_emoji  = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
        lines = [
            f"🔴 **COMPTEUR4** — Absences consécutives (seuil ≥ {COMPTEUR4_THRESHOLD})\n",
            "**En cours :**",
        ]

        any_active = False
        for suit in ALL_SUITS:
            cur   = compteur4_current[suit]
            count = cur['count']
            name  = SUIT_DISPLAY.get(suit, suit)
            if count > 0:
                any_active = True
                bar = "█" * min(count, 12) + ("…" if count > 12 else "")
                alert = " 🚨" if count >= COMPTEUR4_THRESHOLD else ""
                lines.append(f"  {name}: [{bar}] {count}x (depuis #{cur['start_game']}){alert}")
            else:
                lines.append(f"  {name}: —")

        if not any_active:
            lines.append("  _(aucune série en cours)_")

        total = len(compteur4_events)
        lines.append(f"\n**Séries terminées enregistrées :** {total}")
        if total > 0:
            for s in compteur4_events[-5:]:
                emo = suit_emoji.get(s['suit'], s['suit'])
                end_date = s['end_time'].strftime('%d/%m %Hh%M')
                lines.append(
                    f"  • {end_date} — {emo} **{s['count']}x** "
                    f"(#{s['start_game']}→#{s['end_game']})"
                )
            lines.append("_(5 dernières — /compteur4 pdf pour le tableau complet)_")

        lines.append("\nUsage: `/compteur4` `pdf` `seuil N` `reset`")
        await event.respond("\n".join(lines), parse_mode='markdown')

    except Exception as e:
        logger.error(f"Erreur cmd_compteur4: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur5(event):
    """Affiche le statut du Compteur5 et envoie le PDF des présences consécutives."""
    global compteur5_trackers, compteur5_events, COMPTEUR5_THRESHOLD
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        raw   = event.message.message.strip()
        parts = raw.split()
        sub   = parts[1].lower() if len(parts) > 1 else ''

        if sub == 'pdf':
            await send_compteur5_pdf()
            await event.respond("✅ PDF Compteur5 envoyé.")
            return

        if sub == 'seuil' and len(parts) > 2:
            try:
                val = int(parts[2])
                if val < 1:
                    await event.respond("❌ Seuil minimum : 1")
                    return
                old = COMPTEUR5_THRESHOLD
                COMPTEUR5_THRESHOLD = val
                await event.respond(f"✅ **Seuil Compteur5:** {old} → {val}")
            except ValueError:
                await event.respond("❌ Usage: `/compteur5 seuil 10`")
            return

        if sub == 'reset':
            for suit in ALL_SUITS:
                compteur5_trackers[suit] = 0
            compteur5_events.clear()
            await event.respond("🔄 **Compteur5 reset** — Compteurs et historique effacés")
            return

        # Affichage du statut
        suit_emoji_map = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
        lines = [f"✅ **COMPTEUR5 — PRÉSENCES CONSÉCUTIVES** (seuil: {COMPTEUR5_THRESHOLD})", ""]
        for suit in ALL_SUITS:
            count   = compteur5_trackers.get(suit, 0)
            name    = SUIT_DISPLAY.get(suit, suit)
            bar_len = min(count, COMPTEUR5_THRESHOLD)
            bar     = "█" * bar_len + "░" * (COMPTEUR5_THRESHOLD - bar_len)
            pct     = f"{count}/{COMPTEUR5_THRESHOLD}"
            alert   = " 🔥" if count >= COMPTEUR5_THRESHOLD else ""
            lines.append(f"{name}: [{bar}] {pct}{alert}")

        lines.append(f"\n**Événements enregistrés:** {len(compteur5_events)}")

        if compteur5_events:
            lines.append("\n**Derniers enregistrements :**")
            for ev in compteur5_events[-5:][::-1]:
                emoji = suit_emoji_map.get(ev['suit'], ev['suit'])
                dt    = ev['datetime']
                lines.append(
                    f"  • Le {dt.strftime('%d/%m/%Y')} A {dt.strftime('%Hh%M')} "
                    f"{emoji} Numéro {ev['game_number']}"
                )

        lines.append(
            "\n**Usage:**\n`/compteur5 pdf` — Envoyer le PDF\n"
            f"`/compteur5 seuil N` — Changer le seuil (actuel: {COMPTEUR5_THRESHOLD})\n"
            "`/compteur5 reset` — Réinitialiser"
        )
        await event.respond("\n".join(lines))

    except Exception as e:
        logger.error(f"Erreur cmd_compteur5: {e}")
        await event.respond(f"❌ Erreur: {e}")




async def cmd_compteur7(event):
    """Affiche le statut du Compteur7 (séries consécutives) et permet de l'administrer."""
    global compteur7_current, compteur7_completed, COMPTEUR7_THRESHOLD
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        raw   = event.message.message.strip()
        parts = raw.split()
        sub   = parts[1].lower() if len(parts) > 1 else ''

        # /compteur7 pdf — envoyer le PDF manuellement
        if sub == 'pdf':
            await send_compteur7_pdf()
            await event.respond("📄 PDF Compteur7 envoyé.")
            return

        # /compteur7 seuil N — changer le seuil
        if sub == 'seuil' and len(parts) > 2:
            try:
                val = int(parts[2])
                if val < 2:
                    await event.respond("❌ Seuil minimum : 2")
                    return
                old = COMPTEUR7_THRESHOLD
                COMPTEUR7_THRESHOLD = val
                await event.respond(
                    f"✅ **Seuil Compteur7:** {old} → {val}\n"
                    f"Détection à partir de **{val}** présences consécutives"
                )
            except ValueError:
                await event.respond("❌ Usage: `/compteur7 seuil 5`")
            return

        # /compteur7 reset — effacer l'historique persistant
        if sub == 'reset':
            compteur7_completed.clear()
            for suit in ALL_SUITS:
                compteur7_current[suit] = {'count': 0, 'start_game': None, 'start_time': None}
            save_compteur7_data()
            await event.respond("🔄 **Compteur7 reset** — historique effacé du disque")
            return

        # Affichage statut
        suit_names = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
        lines = [f"📊 **COMPTEUR7** — Séries consécutives (seuil ≥ {COMPTEUR7_THRESHOLD})\n"]

        lines.append("**En cours :**")
        any_active = False
        for suit in ALL_SUITS:
            cur   = compteur7_current[suit]
            count = cur['count']
            name  = SUIT_DISPLAY.get(suit, suit)
            if count > 0:
                any_active = True
                bar = "█" * min(count, 12) + ("…" if count > 12 else "")
                lines.append(f"  {name}: [{bar}] {count}x (depuis #{cur['start_game']})")
            else:
                lines.append(f"  {name}: —")

        if not any_active:
            lines.append("  _(aucune série en cours)_")

        total = len(compteur7_completed)
        lines.append(f"\n**Séries terminées enregistrées :** {total}")
        if total > 0:
            for s in compteur7_completed[-5:]:
                end_date = s['end_time'].strftime('%d/%m %Hh%M')
                lines.append(
                    f"  • {end_date} — {s['suit']} **{s['count']}x** "
                    f"(#{s['start_game']}→#{s['end_game']})"
                )
            lines.append("_(5 dernières — /compteur7 pdf pour le tableau complet)_")

        lines.append("\nUsage: `/compteur7` `pdf` `seuil N` `reset`")
        await event.respond("\n".join(lines), parse_mode='markdown')

    except Exception as e:
        logger.error(f"Erreur cmd_compteur7: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur8(event):
    """Affiche le statut du Compteur8 (séries d'absences consécutives) et permet de l'administrer."""
    global compteur8_current, compteur8_completed
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        raw   = event.message.message.strip()
        parts = raw.split()
        sub   = parts[1].lower() if len(parts) > 1 else ''

        # /compteur8 pdf — envoyer le PDF Compteur8 seul (absences uniquement)
        if sub == 'pdf':
            await send_compteur8_only_pdf()
            await event.respond("📄 PDF Compteur8 (absences) envoyé.")
            return

        # /compteur8 reset — effacer l'historique persistant
        if sub == 'reset':
            compteur8_completed.clear()
            for suit in ALL_SUITS:
                compteur8_current[suit] = {'count': 0, 'start_game': None, 'start_time': None}
            save_compteur8_data()
            await event.respond("🔄 **Compteur8 reset** — historique d'absences effacé du disque")
            return

        # Affichage statut
        suit_names = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
        lines = [
            "📊 **COMPTEUR8** — Absences consécutives\n"
            f"_Série enregistrée quand streak d'absence ≥{COMPTEUR8_THRESHOLD}x se TERMINE_\n"
            f"_Miroir du Compteur7 (qui compte les présences ≥{COMPTEUR7_THRESHOLD}x)_\n"
            f"🔴 **Seuil prédiction C8 :** {COMPTEUR8_PRED_SEUIL}x absences → C8 prédit le manque\n"
            f"⛔ **Filtre présence :** costume présent ≥{PRES_BLOCK_SEUIL}x → prédiction refusée\n"
        ]

        lines.append("**Streaks d'absence en cours :**")
        any_active = False
        for suit in ALL_SUITS:
            cur   = compteur8_current[suit]
            count = cur['count']
            name  = SUIT_DISPLAY.get(suit, suit)
            if count > 0:
                any_active = True
                bar = "█" * min(count, 12) + ("…" if count > 12 else "")
                lines.append(f"  {name}: [{bar}] {count}x absents (depuis #{cur['start_game']})")
            else:
                lines.append(f"  {name}: —")

        if not any_active:
            lines.append("  _(aucun streak d'absence en cours)_")

        total = len(compteur8_completed)
        lines.append(f"\n**Séries d'absences ≥{COMPTEUR8_THRESHOLD} terminées :** {total}")
        if total > 0:
            for s in compteur8_completed[-5:]:
                end_date = s['end_time'].strftime('%d/%m %Hh%M')
                lines.append(
                    f"  • {end_date} — {s['suit']} **{s['count']}x absents** "
                    f"(#{s['start_game']}→#{s['end_game']})"
                )
            lines.append("_(5 dernières — /compteur8 pdf pour le tableau complet)_")

        lines.append("\nUsage: `/compteur8` `pdf` `reset`")
        await event.respond("\n".join(lines), parse_mode='markdown')

    except Exception as e:
        logger.error(f"Erreur cmd_compteur8: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_comparaison(event):
    """Analyse intelligente et naturelle des apparitions de costumes par heure de la journée."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        global comparaison_nb_jours
        suit_names = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
        suit_emoji = {'♠': '♠️', '♥': '❤️', '♦': '♦️', '♣': '♣️'}
        raw   = event.message.message.strip()
        parts = raw.split()
        sub   = parts[1].lower() if len(parts) > 1 else ''

        # /comparaison jours N — définir le nombre de jours par défaut
        if sub == 'jours' and len(parts) > 2:
            try:
                val = int(parts[2])
                if val < 1:
                    await event.respond("❌ Minimum 1 jour")
                    return
                comparaison_nb_jours = val
                await event.respond(f"✅ Nombre de jours de comparaison : **{val}**")
            except ValueError:
                await event.respond("❌ Usage: `/comparaison jours 5`")
            return

        # /comparaison c8 [N] — PDF comparaison C8 jour par jour
        if sub == 'c8':
            nb = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else comparaison_nb_jours
            await event.respond(f"⏳ Génération du PDF C8 sur {nb} jour(s)...")
            pdf_bytes  = generate_comparaison_c8_pdf(nb)
            pdf_buffer = io.BytesIO(pdf_bytes)
            pdf_buffer.name = f"comparaison_c8_{nb}j.pdf"
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_file(
                admin_entity, pdf_buffer,
                caption=f"📊 **Comparaison C8 — {nb} derniers jours**\nAbsences ≥{COMPTEUR8_THRESHOLD}x | Toutes données préservées",
                parse_mode='markdown',
                attributes=[], file_name=f"comparaison_c8_{nb}j.pdf"
            )
            return

        # /comparaison c7 [N] — PDF comparaison C7 jour par jour
        if sub == 'c7':
            nb = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else comparaison_nb_jours
            await event.respond(f"⏳ Génération du PDF C7 sur {nb} jour(s)...")
            pdf_bytes  = generate_comparaison_c7_pdf(nb)
            pdf_buffer = io.BytesIO(pdf_bytes)
            pdf_buffer.name = f"comparaison_c7_{nb}j.pdf"
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_file(
                admin_entity, pdf_buffer,
                caption=f"📊 **Comparaison C7 — {nb} derniers jours**\nPrésences ≥{COMPTEUR7_THRESHOLD}x | Toutes données préservées",
                parse_mode='markdown',
                attributes=[], file_name=f"comparaison_c7_{nb}j.pdf"
            )
            return

        # ── Heures ayant assez de données (analyse horaire existante) ─────────
        active_hours = sorted([h for h in range(24) if hourly_game_count[h] >= 3])
        total_games  = sum(hourly_game_count[h] for h in active_hours)

        if total_games < 10:
            await event.respond(
                "📊 **COMPARAISON HORAIRE**\n\n"
                "⏳ Pas encore assez de données (minimum 10 parties nécessaires).\n"
                "L'analyse sera disponible après quelques heures de collecte.\n\n"
                f"Parties enregistrées actuellement : **{total_games}**"
            )
            return

        # ── Calcul des taux par heure ─────────────────────────────────────────
        taux: Dict[str, Dict[int, float]] = {}
        for suit in ALL_SUITS:
            taux[suit] = {}
            for h in active_hours:
                cnt   = hourly_suit_data[h].get(suit, 0)
                tot_h = hourly_game_count[h]
                taux[suit][h] = round(cnt / tot_h * 100, 1) if tot_h > 0 else 0.0

        # Taux global
        overall: Dict[str, float] = {}
        for suit in ALL_SUITS:
            ts = sum(hourly_suit_data[h].get(suit, 0) for h in active_hours)
            overall[suit] = round(ts / total_games * 100, 1) if total_games > 0 else 0.0

        suit_order = sorted(ALL_SUITS, key=lambda s: overall[s], reverse=True)

        # ── Fonction utilitaire : grouper des heures consécutives en plages ──
        def group_hours_into_ranges(hours_list: List[int]) -> List[List[int]]:
            """Regroupe [12,13,14,17,18] en [[12,13,14],[17,18]]"""
            if not hours_list:
                return []
            sorted_h = sorted(hours_list)
            groups, grp = [], [sorted_h[0]]
            for h in sorted_h[1:]:
                if h == grp[-1] + 1:
                    grp.append(h)
                else:
                    groups.append(grp)
                    grp = [h]
            groups.append(grp)
            return groups

        def format_range(grp: List[int]) -> str:
            if len(grp) == 1:
                return f"{grp[0]:02d}h"
            return f"{grp[0]:02d}h à {grp[-1] + 1:02d}h"

        # ── Données Compteur7 (séries de présences) par heure ─────────────────
        c7_by_hour: Dict[int, List[Dict]] = {h: [] for h in range(24)}
        for s in compteur7_completed:
            h = s['end_time'].hour
            c7_by_hour[h].append(s)

        # ── Données Compteur4 (séries d'absences) par heure ──────────────────
        c4_by_hour: Dict[int, List[Dict]] = {h: [] for h in range(24)}
        for s in compteur4_events:
            h = s['end_time'].hour
            c4_by_hour[h].append(s)

        # ── En-tête du rapport ────────────────────────────────────────────────
        current_h = datetime.now().hour
        now_str   = datetime.now().strftime('%d/%m/%Y à %Hh%M')
        lines = [
            "📊 **ANALYSE COMPARAISON INTELLIGENTE**",
            f"📅 {now_str} — {total_games} parties analysées",
            f"⏰ {len(active_hours)} tranches horaires actives\n",
        ]

        # ── Analyse par costume ───────────────────────────────────────────────
        for suit in suit_order:
            name      = suit_names[suit]
            emoji     = suit_emoji[suit]
            avg       = overall[suit]
            ht        = taux[suit]
            threshold_strong = avg + 8
            threshold_weak   = avg - 8

            # Heures fortes et faibles
            strong_hours = sorted([h for h in active_hours if ht.get(h, 0) >= threshold_strong],
                                   key=lambda h: ht[h], reverse=True)
            weak_hours   = sorted([h for h in active_hours if ht.get(h, 0) <= threshold_weak],
                                   key=lambda h: ht[h])

            strong_sorted_asc = sorted(strong_hours)
            weak_sorted_asc   = sorted(weak_hours)

            strong_groups = group_hours_into_ranges(strong_sorted_asc)
            weak_groups   = group_hours_into_ranges(weak_sorted_asc)

            # Meilleure plage forte (la plus longue)
            best_strong_grp = max(strong_groups, key=len) if strong_groups else None
            best_weak_grp   = max(weak_groups,   key=len) if weak_groups   else None

            lines.append("━━━━━━━━━━━━━━━")
            lines.append(f"{emoji} **{name}** — moyenne globale : **{avg:.0f}%**")

            # Message principal en langage naturel
            if best_strong_grp and best_weak_grp:
                strong_pct_avg = round(sum(ht.get(h, 0) for h in best_strong_grp) / len(best_strong_grp))
                weak_pct_avg   = round(sum(ht.get(h, 0) for h in best_weak_grp) / len(best_weak_grp))
                lines.append(
                    f"  📌 Aujourd'hui **{name}** apparaît bien de **{format_range(best_strong_grp)}** "
                    f"({strong_pct_avg}%), mais arrivé sur "
                    f"**{format_range(best_weak_grp)}** il a baissé — devient **rare** ({weak_pct_avg}%)"
                )
            elif best_strong_grp:
                strong_pct_avg = round(sum(ht.get(h, 0) for h in best_strong_grp) / len(best_strong_grp))
                lines.append(
                    f"  📌 **{name}** est fort de **{format_range(best_strong_grp)}** "
                    f"({strong_pct_avg}%) — pas de zone faible notable"
                )
            elif best_weak_grp:
                weak_pct_avg = round(sum(ht.get(h, 0) for h in best_weak_grp) / len(best_weak_grp))
                lines.append(
                    f"  📌 **{name}** devient rare de **{format_range(best_weak_grp)}** "
                    f"({weak_pct_avg}%) — pas de zone forte notable"
                )
            else:
                lines.append(f"  📌 **{name}** apparaît de manière régulière toute la journée ({avg:.0f}%)")

            # Toutes les plages fortes
            if strong_groups:
                strong_details = []
                for grp in sorted(strong_groups, key=len, reverse=True)[:3]:
                    avg_t = round(sum(ht.get(h, 0) for h in grp) / len(grp))
                    strong_details.append(f"{format_range(grp)} ({avg_t}%)")
                lines.append(f"  ✅ **Zones favorables :** {' | '.join(strong_details)}")

            # Toutes les plages faibles
            if weak_groups:
                weak_details = []
                for grp in sorted(weak_groups, key=len, reverse=True)[:3]:
                    avg_t = round(sum(ht.get(h, 0) for h in grp) / len(grp))
                    weak_details.append(f"{format_range(grp)} ({avg_t}%)")
                lines.append(f"  ❄️ **Zones rares :** {' | '.join(weak_details)}")

            # Données C7 (séries de présences longues) pour ce costume
            c7_suit = [s for s in compteur7_completed if s['suit'] == suit]
            if c7_suit:
                by_h: Dict[int, int] = {}
                for s7 in c7_suit:
                    h7 = s7['end_time'].hour
                    by_h[h7] = by_h.get(h7, 0) + 1
                top_c7_h = max(by_h, key=by_h.get)
                lines.append(
                    f"  🔥 Séries longues souvent terminées vers **{top_c7_h:02d}h** "
                    f"({by_h[top_c7_h]}x enregistré)"
                )

            # Données C4 (séries d'absences longues) pour ce costume
            c4_suit = [s for s in compteur4_events if s['suit'] == suit]
            if c4_suit:
                by_h4: Dict[int, int] = {}
                for s4 in c4_suit:
                    h4 = s4['end_time'].hour
                    by_h4[h4] = by_h4.get(h4, 0) + 1
                top_c4_h = max(by_h4, key=by_h4.get)
                lines.append(
                    f"  ⚠️ Longues absences souvent terminées vers **{top_c4_h:02d}h** "
                    f"({by_h4[top_c4_h]}x enregistré)"
                )

        # ── Situation en temps réel ───────────────────────────────────────────
        lines.append("\n━━━━━━━━━━━━━━━")
        lines.append(f"🕐 **Situation MAINTENANT ({current_h:02d}h)**")
        if current_h in active_hours:
            ranked = sorted(ALL_SUITS, key=lambda s: taux[s].get(current_h, 0), reverse=True)
            best   = ranked[0]
            worst  = ranked[-1]
            best_p = taux[best].get(current_h, 0)
            worst_p= taux[worst].get(current_h, 0)
            trend_lines = []
            for s in ranked:
                p    = taux[s].get(current_h, 0)
                diff = round(p - overall[s], 1)
                sign = "▲" if diff > 2 else ("▼" if diff < -2 else "▶")
                trend_lines.append(
                    f"  {suit_emoji[s]} {suit_names[s]}: **{p:.0f}%** {sign} ({'+' if diff >= 0 else ''}{diff}% vs moy.)"
                )
            lines.extend(trend_lines)
            lines.append(
                f"\n  🏆 Le plus favorable maintenant : {suit_emoji[best]} **{suit_names[best]}** ({best_p:.0f}%)"
            )
            lines.append(
                f"  ⛔ Le plus rare maintenant : {suit_emoji[worst]} **{suit_names[worst]}** ({worst_p:.0f}%)"
            )

            # Prévision heure suivante
            next_h = (current_h + 1) % 24
            if next_h in active_hours:
                best_next = max(ALL_SUITS, key=lambda s: taux[s].get(next_h, 0))
                lines.append(
                    f"\n  📈 Dans 1h ({next_h:02d}h) : favorable pour "
                    f"{suit_emoji[best_next]} **{suit_names[best_next]}** "
                    f"({taux[best_next].get(next_h, 0):.0f}%)"
                )
        else:
            lines.append(f"  ℹ️ Pas encore assez de données pour {current_h:02d}h")

        # ── Conseils globaux du jour ──────────────────────────────────────────
        lines.append("\n━━━━━━━━━━━━━━━")
        lines.append("💡 **CONSEILS STRATÉGIQUES DU JOUR**")
        for suit in suit_order:
            name  = suit_names[suit]
            emoji = suit_emoji[suit]
            ht    = taux[suit]
            if not active_hours:
                continue
            sorted_desc = sorted(active_hours, key=lambda h: ht.get(h, 0), reverse=True)
            top_h   = sorted_desc[0]
            top_t   = ht.get(top_h, 0)
            low_h   = sorted_desc[-1]
            low_t   = ht.get(low_h, 0)
            delta   = round(top_t - low_t)

            # Phrase conseil
            if delta >= 20:
                conseil = f"Forte variation — privilégier **{top_h:02d}h** ({top_t:.0f}%), éviter **{low_h:02d}h** ({low_t:.0f}%)"
            elif delta >= 10:
                conseil = f"Variation modérée — meilleur créneau **{top_h:02d}h** ({top_t:.0f}%)"
            else:
                conseil = "Comportement stable — peut être joué à tout moment"

            lines.append(f"  {emoji} **{name}** : {conseil}")

        await event.respond("\n".join(lines), parse_mode='markdown')

    except Exception as e:
        logger.error(f"Erreur cmd_comparaison: {e}")
        import traceback; logger.error(traceback.format_exc())
        await event.respond(f"❌ Erreur: {e}")


async def cmd_df(event):
    """Paramètre df : quand le jeu N se termine → prédit le jeu N+df."""
    global PREDICTION_DF
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            await event.respond(
                "⏭️ **PARAMÈTRE DF**\n\n"
                f"Valeur actuelle : **{PREDICTION_DF}**\n\n"
                "**Usage :** `/df [1-10]`\n\n"
                "_Quand le jeu N se termine, le bot prédit le jeu N+df._\n"
                "_df=1 (défaut) = prédit le jeu suivant immédiatement._"
            )
            return
        val = int(parts[1])
        if not 1 <= val <= 10:
            await event.respond("❌ df doit être entre 1 et 10")
            return
        old = PREDICTION_DF
        PREDICTION_DF = val
        await event.respond(
            f"✅ **df modifié : {old} → {val}**\n"
            f"_Dès qu'un jeu se termine, le bot prédit le jeu N+{PREDICTION_DF}._"
        )
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")




async def cmd_gap(event):
    global MIN_GAP_BETWEEN_PREDICTIONS
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            await event.respond(f"📏 **ÉCART MINIMUM**\n\nValeur actuelle: **{MIN_GAP_BETWEEN_PREDICTIONS}**\n\n**Usage:** `/gap [2-10]`")
            return
        val = int(parts[1])
        if not 2 <= val <= 10:
            await event.respond("❌ L'écart doit être entre 2 et 10")
            return
        old = MIN_GAP_BETWEEN_PREDICTIONS
        MIN_GAP_BETWEEN_PREDICTIONS = val
        await event.respond(f"✅ **Écart modifié: {old} → {val}**")
        db.db_schedule(save_runtime_config())
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_stats(event):
    global compteur1_history, compteur1_trackers
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        lines = ["📊 **STATISTIQUES COMPTEUR1**", "Séries de présences consécutives (joueur, min 3)", ""]

        for tracker in compteur1_trackers.values():
            if tracker.counter >= MIN_CONSECUTIVE_FOR_STATS:
                already_saved = any(
                    e['suit'] == tracker.suit and e['count'] == tracker.counter and e['end_game'] == tracker.last_game
                    for e in compteur1_history[:5]
                )
                if not already_saved:
                    save_compteur1_series(tracker.suit, tracker.counter, tracker.start_game, tracker.last_game)

        stats_by_suit = {'♥': [], '♠': [], '♦': [], '♣': []}
        for entry in compteur1_history:
            suit = entry['suit']
            if suit in stats_by_suit:
                stats_by_suit[suit].append(entry)

        has_data = False
        for suit in ['♥', '♠', '♦', '♣']:
            entries = stats_by_suit[suit]
            if not entries:
                continue
            has_data = True
            record = get_compteur1_record(suit)
            lines.append(f"**{SUIT_DISPLAY.get(suit, suit)}** (Record: {record})")
            for i, entry in enumerate(entries[:5], 1):
                count = entry['count']
                start = entry['start_game']
                end = entry['end_game']
                star = "⭐" if count == record else ""
                lines.append(f"  {i}. {count} fois (#{start}-#{end}) {star}")
            lines.append("")

        if not has_data:
            lines.append("❌ Aucune série ≥3 enregistrée")

        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur2(event):
    global compteur2_seuil_B, compteur2_active, compteur2_trackers
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            status_str = "✅ ON" if compteur2_active else "❌ OFF"
            lines = ["📊 **COMPTEUR2** (Absences joueur)", f"Statut: {status_str} | Seuil B défaut: {compteur2_seuil_B}", "", "Progression (B dynamique par costume):"]
            for suit in ALL_SUITS:
                tracker = compteur2_trackers.get(suit)
                if tracker:
                    b = compteur2_seuil_B_per_suit.get(suit, compteur2_seuil_B)
                    progress = min(tracker.counter, b)
                    bar = f"[{'█' * progress}{'░' * max(0, b - progress)}]"
                    status = "🔮 PRÊT" if tracker.counter >= b else f"{tracker.counter}/{b}"
                    b_marker = f" (B={b})" if b != compteur2_seuil_B else ""
                    lines.append(f"{tracker.get_display_name()}: {bar} {status}{b_marker}")
            lines.append("\n**Usage:** `/compteur2 [B/on/off/reset]`")
            await event.respond("\n".join(lines))
            return

        arg = parts[1].lower()
        if arg == 'off':
            compteur2_active = False
            await event.respond("❌ **Compteur2 OFF**")
            db.db_schedule(save_runtime_config())
        elif arg == 'on':
            compteur2_active = True
            await event.respond("✅ **Compteur2 ON**")
            db.db_schedule(save_runtime_config())
        elif arg == 'reset':
            for tracker in compteur2_trackers.values():
                tracker.counter = 0
            await event.respond("🔄 **Compteur2 reset**")
        else:
            b_val = int(arg)
            if not 2 <= b_val <= 10:
                await event.respond("❌ B entre 2 et 10")
                return
            old_b = compteur2_seuil_B
            compteur2_seuil_B = b_val
            # Mettre à jour les B par costume :
            # - Les costumes au niveau admin précédent → passent au nouveau niveau admin
            # - Les costumes élevés par des pertes → ajustés par le même delta
            delta = b_val - old_b
            for s in ALL_SUITS:
                cur = compteur2_seuil_B_per_suit.get(s, old_b)
                excess = cur - old_b  # Nombre de pertes accumulées pour ce costume
                compteur2_seuil_B_per_suit[s] = b_val + max(0, excess)
            lines = [f"✅ **Seuil B admin = {b_val}** (ancien: {old_b})\n", "B par costume mis à jour:"]
            for s in ALL_SUITS:
                sd = SUIT_DISPLAY.get(s, s)
                new_val = compteur2_seuil_B_per_suit[s]
                losses = new_val - b_val
                suffix = f" (+{losses} perte(s))" if losses > 0 else " ✅"
                lines.append(f"  {sd}: **{new_val}**{suffix}")
            await event.respond("\n".join(lines), parse_mode='markdown')
            db.db_schedule(save_runtime_config())
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur13(event):
    """Affiche/configure le Compteur13 (consécutifs + miroir C2)."""
    global COMPTEUR13_THRESHOLD, compteur13_active, compteur13_trackers, compteur13_start
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.strip().split()

        if len(parts) == 1:
            status = "✅ ON" if compteur13_active else "❌ OFF"
            lines = [
                "🎯 **COMPTEUR 13** — Consécutifs + Miroir C2",
                f"Statut: {status} | Seuil wx: **{COMPTEUR13_THRESHOLD}**",
                "Paires miroir: ♦️↔❤️ | ♣️↔♠️",
                "",
                "**Progression par costume (consécutifs en cours) :**",
            ]
            for suit in ALL_SUITS:
                cnt     = compteur13_trackers.get(suit, 0)
                progress = min(cnt, COMPTEUR13_THRESHOLD)
                bar      = f"[{'█' * progress}{'░' * max(0, COMPTEUR13_THRESHOLD - progress)}]"
                miroir   = COMPTEUR13_MIRROR.get(suit, '?')
                miroir_disp = SUIT_DISPLAY.get(miroir, miroir)
                state    = "🔮 PRÊT" if cnt >= COMPTEUR13_THRESHOLD else f"{cnt}/{COMPTEUR13_THRESHOLD}"
                lines.append(f"  {SUIT_DISPLAY.get(suit, suit)}: {bar} {state} → miroir: {miroir_disp}")
            lines.append("\n**Usage:** `/compteur13 [wx N / on / off / reset]`")
            await event.respond("\n".join(lines), parse_mode='markdown')
            return

        arg = parts[1].lower()
        if arg == 'off':
            compteur13_active = False
            await event.respond("❌ **Compteur13 OFF** — prédictions C13 désactivées")
            db.db_schedule(save_runtime_config())
        elif arg == 'on':
            compteur13_active = True
            await event.respond("✅ **Compteur13 ON** — prédictions C13 activées")
            db.db_schedule(save_runtime_config())
        elif arg == 'reset':
            for suit in ALL_SUITS:
                compteur13_trackers[suit] = 0
                compteur13_start[suit]    = 0
            await event.respond("🔄 **Compteur13 reset** — tous les compteurs remis à zéro")
        elif arg == 'wx' and len(parts) >= 3:
            try:
                wx_val = int(parts[2])
            except ValueError:
                await event.respond("❌ Valeur wx invalide — entier requis (ex: `/compteur13 wx 5`)")
                return
            if not 2 <= wx_val <= 30:
                await event.respond("❌ wx doit être entre 2 et 30")
                return
            old_wx = COMPTEUR13_THRESHOLD
            COMPTEUR13_THRESHOLD = wx_val
            await event.respond(
                f"✅ **Seuil wx = {wx_val}** (ancien: {old_wx})\n"
                f"C13 se déclenchera après **{wx_val}** apparitions consécutives du même costume.",
                parse_mode='markdown'
            )
            db.db_schedule(save_runtime_config())
        else:
            await event.respond(
                "❓ **Usage Compteur13:**\n"
                "`/compteur13` — statut\n"
                "`/compteur13 wx N` — changer le seuil (2-30)\n"
                "`/compteur13 on/off` — activer/désactiver\n"
                "`/compteur13 reset` — remettre à zéro",
                parse_mode='markdown'
            )
    except Exception as e:
        logger.error(f"Erreur cmd_compteur13: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur14(event):
    """Affiche l'état du Compteur14 et permet le reset ou un rapport intermédiaire."""
    global COMPTEUR14_CYCLE_SIZE
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.strip().split()
        sub   = parts[1].lower() if len(parts) > 1 else ''

        if sub == 'reset':
            reset_compteur14()
            await event.respond(
                "🔄 **Compteur14 reset** — compteurs remis à zéro, nouveau cycle démarré.",
                parse_mode='markdown'
            )
            return

        if sub == 'rapport':
            await send_compteur14_report(compteur14_cycle_start + compteur14_cycle_games - 1, is_final=False)
            await event.respond("📊 Rapport C14 intermédiaire envoyé.", parse_mode='markdown')
            return

        # Affichage de l'état courant
        suit_names   = {'♠': 'Pique ♠', '♥': 'Cœur ❤️', '♦': 'Carreau ♦️', '♣': 'Trèfle ♣️'}
        total_appear = sum(compteur14_counts.values())
        total_safe   = total_appear or 1
        progress_pct = compteur14_cycle_games / COMPTEUR14_CYCLE_SIZE * 100

        lines = [
            "📊 **COMPTEUR 14 — Fréquence absolue des costumes**\n"
            f"Cycle : **{compteur14_cycle_games}/{COMPTEUR14_CYCLE_SIZE} jeux** ({progress_pct:.1f}%)\n"
            f"Début du cycle : jeu #{compteur14_cycle_start}\n"
        ]

        lines.append("**Apparitions par costume :**")
        for suit in ALL_SUITS:
            name  = suit_names.get(suit, suit)
            count = compteur14_counts.get(suit, 0)
            pct   = count / total_safe * 100
            bar   = "█" * int(pct / 5) + "░" * (20 - int(pct / 5))
            lines.append(f"  {name}: **{count}x** ({pct:.1f}%) [{bar}]")

        lines.append(f"\n**Total apparitions :** {total_appear}")
        lines.append(f"\n**Rapport automatique** à {COMPTEUR14_CYCLE_SIZE} jeux → reset automatique")
        lines.append("\n**Usage :** `/compteur14` · `/compteur14 rapport` · `/compteur14 reset`")

        await event.respond("\n".join(lines), parse_mode='markdown')
    except Exception as e:
        logger.error(f"Erreur cmd_compteur14: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_canaux(event):
    global DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID, PREDICTION_CHANNEL_ID, PREDICTION_CHANNEL_ID3, PREDICTION_CHANNEL_ID4
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.strip().split()
        sub = parts[1].lower() if len(parts) > 1 else ''

        if sub == 'distribution':
            if len(parts) < 3:
                st = f"✅ `{DISTRIBUTION_CHANNEL_ID}`" if DISTRIBUTION_CHANNEL_ID else "❌ Inactif"
                await event.respond(f"🎯 **Canal distribution:** {st}\n\nUsage: `/canaux distribution [ID|off]`")
                return
            arg = parts[2].lower()
            if arg == 'off':
                old = DISTRIBUTION_CHANNEL_ID; DISTRIBUTION_CHANNEL_ID = None
                await event.respond(f"❌ **Canal distribution désactivé** (était: `{old}`)")
            else:
                new_id = int(arg)
                if not await resolve_channel(new_id):
                    await event.respond(f"❌ Canal `{new_id}` inaccessible"); return
                old = DISTRIBUTION_CHANNEL_ID; DISTRIBUTION_CHANNEL_ID = new_id
                await event.respond(f"✅ **Canal distribution: {old} → {new_id}**")
            db.db_schedule(save_runtime_config())
            return

        if sub == 'compteur2':
            if len(parts) < 3:
                st = f"✅ `{COMPTEUR2_CHANNEL_ID}`" if COMPTEUR2_CHANNEL_ID else "❌ Inactif"
                await event.respond(f"📊 **Canal compteur2:** {st}\n\nUsage: `/canaux compteur2 [ID|off]`")
                return
            arg = parts[2].lower()
            if arg == 'off':
                old = COMPTEUR2_CHANNEL_ID; COMPTEUR2_CHANNEL_ID = None
                await event.respond(f"❌ **Canal compteur2 désactivé** (était: `{old}`)")
            else:
                new_id = int(arg)
                if not await resolve_channel(new_id):
                    await event.respond(f"❌ Canal `{new_id}` inaccessible"); return
                old = COMPTEUR2_CHANNEL_ID; COMPTEUR2_CHANNEL_ID = new_id
                await event.respond(f"✅ **Canal compteur2: {old} → {new_id}**")
            db.db_schedule(save_runtime_config())
            return

        if sub == 'canal3':
            if len(parts) < 3:
                st = f"✅ `{PREDICTION_CHANNEL_ID3}`" if PREDICTION_CHANNEL_ID3 else "❌ Inactif"
                await event.respond(
                    f"📡 **Canal 3 (prédictions + résultats):** {st}\n\n"
                    "Usage: `/canaux canal3 [ID|off]`\n"
                    "Le bot doit être **admin** dans ce canal.\n"
                    "Reçoit : prédictions initiales + résultats (gagné/perdu/expiré)."
                )
                return
            arg = parts[2].lower()
            if arg == 'off':
                old = PREDICTION_CHANNEL_ID3; PREDICTION_CHANNEL_ID3 = None
                await event.respond(f"❌ **Canal 3 désactivé** (était: `{old}`)")
            else:
                new_id = int(arg)
                entity = await resolve_channel(new_id)
                if not entity:
                    await event.respond(f"❌ Canal `{new_id}` inaccessible — le bot est-il admin?"); return
                old = PREDICTION_CHANNEL_ID3; PREDICTION_CHANNEL_ID3 = new_id
                await event.respond(
                    f"✅ **Canal 3 activé : {old or 'inactif'} → `{new_id}`**\n"
                    "Toutes les prédictions + résultats seront redirigés vers ce canal."
                )
            db.db_schedule(save_runtime_config())
            return

        if sub == 'canal4':
            if len(parts) < 3:
                st = f"✅ `{PREDICTION_CHANNEL_ID4}`" if PREDICTION_CHANNEL_ID4 else "❌ Inactif"
                await event.respond(
                    f"📡 **Canal 4 (prédictions + résultats):** {st}\n\n"
                    "Usage: `/canaux canal4 [ID|off]`\n"
                    "Le bot doit être **admin** dans ce canal.\n"
                    "Reçoit : prédictions initiales + résultats (gagné/perdu/expiré)."
                )
                return
            arg = parts[2].lower()
            if arg == 'off':
                old = PREDICTION_CHANNEL_ID4; PREDICTION_CHANNEL_ID4 = None
                await event.respond(f"❌ **Canal 4 désactivé** (était: `{old}`)")
            else:
                new_id = int(arg)
                entity = await resolve_channel(new_id)
                if not entity:
                    await event.respond(f"❌ Canal `{new_id}` inaccessible — le bot est-il admin?"); return
                old = PREDICTION_CHANNEL_ID4; PREDICTION_CHANNEL_ID4 = new_id
                await event.respond(
                    f"✅ **Canal 4 activé : {old or 'inactif'} → `{new_id}`**\n"
                    "Toutes les prédictions + résultats seront redirigés vers ce canal."
                )
            db.db_schedule(save_runtime_config())
            return

        c3_st = f"`{PREDICTION_CHANNEL_ID3}`" if PREDICTION_CHANNEL_ID3 else "❌ inactif"
        c4_st = f"`{PREDICTION_CHANNEL_ID4}`" if PREDICTION_CHANNEL_ID4 else "❌ inactif"
        lines = [
            "📡 **CONFIGURATION DES CANAUX**", "",
            f"📤 **Canal 1 (principal):** `{PREDICTION_CHANNEL_ID}`",
            f"📤 **Canal 2 (principal):** `{PREDICTION_CHANNEL_ID2}`",
            f"📡 **Canal 3 (redirect):** {c3_st}",
            f"📡 **Canal 4 (redirect):** {c4_st}",
            f"🎯 **Distribution:** {f'`{DISTRIBUTION_CHANNEL_ID}`' if DISTRIBUTION_CHANNEL_ID else '❌'}",
            f"📊 **Compteur2:** {f'`{COMPTEUR2_CHANNEL_ID}`' if COMPTEUR2_CHANNEL_ID else '❌'}",
            "",
            "**Modifier:**",
            "`/canaux canal3 [ID|off]` — Canal prédictions+résultats",
            "`/canaux canal4 [ID|off]` — Canal prédictions+résultats",
            "`/canaux distribution [ID|off]`",
            "`/canaux compteur2 [ID|off]`",
        ]
        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_queue(event):
    global prediction_queue, current_game_number, MIN_GAP_BETWEEN_PREDICTIONS, PREDICTION_DF
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        lines = [
            "📋 **FILE D'ATTENTE**",
            f"Écart: {MIN_GAP_BETWEEN_PREDICTIONS} | df={PREDICTION_DF} (prédit N+{PREDICTION_DF} à la fin du jeu N)",
            "",
        ]
        if not prediction_queue:
            lines.append("❌ Vide")
        else:
            lines.append(f"**{len(prediction_queue)} prédictions:**\n")
            for i, pred in enumerate(prediction_queue, 1):
                suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
                pred_type = pred['type']
                pred_num = pred['game_number']
                type_str = "📊C2" if pred_type == 'compteur2' else "🤖"
                trigger_game = pred_num - PREDICTION_DF
                if current_game_number >= trigger_game:
                    status = "🟢 PRÊT (attend fin du jeu)" if not pending_predictions else "⏳ Attente"
                else:
                    wait_num = trigger_game - current_game_number
                    status = f"⏳ Envoi après jeu #{trigger_game} (+{wait_num})"
                lines.append(f"{i}. #{pred_num} {suit} | {type_str} | {status}")
        lines.append(f"\n🎮 Jeu API actuel: #{current_game_number}")
        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {str(e)}")


async def cmd_pending(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    from config import PREDICTION_TIMEOUT_MINUTES
    now = datetime.now()
    try:
        if not pending_predictions:
            await event.respond("✅ **Aucune prédiction en cours**")
            return
        lines = [f"🔍 **PRÉDICTIONS EN COURS** ({len(pending_predictions)})", ""]
        for game_number, pred in pending_predictions.items():
            suit = pred.get('suit', '?')
            suit_display = SUIT_DISPLAY.get(suit, suit)
            rattrapage = pred.get('rattrapage', 0)
            current_check = pred.get('current_check', game_number)
            verified_games = pred.get('verified_games', [])
            sent_time = pred.get('sent_time')
            pred_type = pred.get('type', 'standard')
            type_str = "📊C2" if pred_type == 'compteur2' else "🤖"
            age_str = ""
            if sent_time:
                age_sec = int((now - sent_time).total_seconds())
                age_str = f"{age_sec // 60}m{age_sec % 60:02d}s"
            verif_parts = []
            for i in range(3):
                check_num = game_number + i
                if current_check == check_num:
                    verif_parts.append(f"🔵#{check_num}")
                elif check_num in verified_games:
                    verif_parts.append(f"❌#{check_num}")
                else:
                    verif_parts.append(f"⬜#{check_num}")
            lines.append(f"**#{game_number}** {suit_display} | {type_str} | R{rattrapage}")
            lines.append(f"  🔍 {' | '.join(verif_parts)}")
            lines.append(f"  ⏱️ Il y a {age_str}")
            lines.append("")
        lines.append(f"🎮 Jeu API actuel: #{current_game_number}")
        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_status(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    compteur2_str = "✅ ON" if compteur2_active else "❌ OFF"
    now = datetime.now()
    allowed = "✅" if is_prediction_time_allowed() else "❌"

    lines = [
        "📊 **STATUT COMPLET**",
        "",
        f"🎮 Jeu API actuel: #{current_game_number}",
        f"📊 Compteur2: {compteur2_str} (B={compteur2_seuil_B})",
        f"📏 Écart: {MIN_GAP_BETWEEN_PREDICTIONS}",
        f"⏰ Prédictions autorisées: {allowed} ({now.strftime('%H:%M')})",
        f"📋 File: {len(prediction_queue)} | Actives: {len(pending_predictions)}",
        f"📊 Écarts C4: {len(compteur4_events)}",
        "",
        f"**Plages horaires:**\n{format_hours_config()}",
        "",
        "**Compteur4 (absences):**",
    ]

    for suit in ALL_SUITS:
        count = compteur4_trackers.get(suit, 0)
        name = SUIT_DISPLAY.get(suit, suit)
        lines.append(f"  {name}: {count}/{COMPTEUR4_THRESHOLD}")

    if pending_predictions:
        lines.append("")
        lines.append("🔍 **En vérification:**")
        for game_number, pred in pending_predictions.items():
            suit_display = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            rattrapage = pred.get('rattrapage', 0)
            sent_time = pred.get('sent_time')
            age_str = ""
            if sent_time:
                age_sec = int((now - sent_time).total_seconds())
                age_str = f" ({age_sec // 60}m{age_sec % 60:02d}s)"
            lines.append(f"  • #{game_number} {suit_display} — R{rattrapage}{age_str}")

    await event.respond("\n".join(lines))


async def cmd_help(event):
    if event.is_group or event.is_channel:
        return

    help_text = (
        "📖 **BACCARAT AI — AIDE**\n\n"
        "💡 **Recommandé : utilisez `/menu` pour accéder à tout via des boutons cliquables.**\n\n"
        "**⚙️ Configuration:**\n"
        f"`/df [1-10]` — Décalage prédiction (actuel: df={PREDICTION_DF})\n"
        f"`/gap [2-10]` — Écart min entre prédictions ({MIN_GAP_BETWEEN_PREDICTIONS})\n\n"
        "**⏰ Restriction horaire:**\n"
        "`/heures` — Voir/gérer les plages (add/del/clear)\n\n"
        "**📊 Compteurs:**\n"
        "`/compteur2 [B/on/off/reset]` — Absences consécutives (prédictions)\n"
        "`/stats` — Séries Compteur1 (présences joueur)\n"
        f"`/compteur4 [pdf/seuil N]` — Absences longues (seuil: {COMPTEUR4_THRESHOLD})\n"
        "`/compteur5` — Patterns par costume\n"
        f"`/compteur7 [pdf/seuil N/reset]` — Présences ≥{COMPTEUR7_THRESHOLD} consécutives\n"
        f"`/compteur8 [pdf/reset]` — Absences ≥{COMPTEUR8_THRESHOLD} (miroir C7)\n"
        f"`/compteur13 [wx N/on/off/reset]` — Consécutifs + miroir C2 (seuil: {COMPTEUR13_THRESHOLD})\n\n"
        "**📡 Canaux:**\n"
        "`/canaux` — Voir config des canaux\n"
        "`/canaux canal3 [ID|off]` — Canal redirect (prédictions + résultats)\n"
        "`/canaux canal4 [ID|off]` — Canal redirect (prédictions + résultats)\n"
        "`/canaux distribution [ID|off]` — Canal secondaire\n"
        "`/canaux compteur2 [ID|off]` — Canal Compteur2\n\n"
        "**📋 Gestion prédictions:**\n"
        "`/raison` — 15 dernières prédictions + raison détaillée\n"
        "`/raison N` — Raison pour le jeu #N\n"
        "`/raison pdf` — PDF complet de toutes les prédictions\n"
        "`/raison2` — Top 10 meilleures combinaisons (miroir × wx × B)\n"
        "`/raison2 pdf` — PDF complet de la simulation (216 combinaisons)\n"
        "`/raison2 P1` `/raison2 P2` `/raison2 P3` — Tableau détaillé par miroir\n"
        "`/raison2 tout` — Toutes les 216 combinaisons triées\n"
        "`/pending` — Prédictions en vérification\n"
        "`/queue` — File d'attente\n"
        "`/status` — Statut complet\n"
        "`/reset` — Reset manuel\n"
        "`/debloquer` — Déblocage d'urgence\n\n"
        "**📈 Analyse:**\n"
        "`/perdus` — PDF des pertes\n"
        "`/favorables [on/off/canal]` — Heures favorables (auto 3h)\n"
        "`/comparaison` — Distribution costumes par heure\n\n"
        "**📊 Bilans:**\n"
        "`/bilan` — Bilan actuel (auto: 00h,04h,08h,12h,16h,20h)\n"
        "`/bilan now` — Envoyer le bilan maintenant\n"
        "`/b` — Seuils B par costume\n\n"
        "**🧠 Analyse IA:**\n"
        "`/strategie` — Évaluation stratégie + toutes les combinaisons miroir/inverse\n"
        "`Oui N` — Appliquer la combinaison numéro N proposée\n\n"
        "🤖 Baccarat AI | Source: 1xBet API"
    )
    await event.respond(help_text, buttons=[[Button.inline("🤖 Ouvrir le Menu", b"mn")]])


async def cmd_strategie(event):
    """
    Analyse les prédictions finalisées, évalue la qualité, montre toutes les
    combinaisons miroir/inverse possibles, recommande la meilleure et demande
    confirmation ('Oui N') pour l'appliquer immédiatement.
    """
    global pending_strategy_proposal, last_strategy_simulation

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    resolved = [p for p in prediction_history
                if p.get('status') not in ('en_cours', 'sending', None)]
    if len(resolved) < 1:
        await event.respond(
            "📊 Aucune prédiction finalisée disponible pour analyser."
        )
        return

    def classify(pred):
        st = pred.get('status', '')
        rl = pred.get('rattrapage_level', 0)
        if 'gagne' in st:
            return f'r{min(int(rl), 3)}'
        if st == 'perdu':
            return 'perdu'
        return None

    items = []
    for p in resolved:
        c = classify(p)
        if c:
            items.append({
                'class': c,
                'suit':  p.get('suit', '?'),
                'type':  p.get('type', 'inconnu'),
            })

    if not items:
        await event.respond("📊 Aucune prédiction finalisée trouvée.")
        return

    recent = items[:20]
    last5  = items[:5]
    total  = len(recent)

    r0c = sum(1 for r in recent if r['class'] == 'r0')
    r1c = sum(1 for r in recent if r['class'] == 'r1')
    r2c = sum(1 for r in recent if r['class'] == 'r2')
    r3c = sum(1 for r in recent if r['class'] == 'r3')
    pdc = sum(1 for r in recent if r['class'] == 'perdu')
    good_count = r0c + r1c
    late_count = r2c + r3c

    # ── Détection médiocre ──────────────────────────────────────────────────
    is_mediocre  = False
    mediocre_why = []

    for i in range(len(recent) - 1):
        if recent[i]['class'] == 'perdu' and recent[i+1]['class'] == 'perdu':
            is_mediocre = True
            mediocre_why.append("2 pertes consécutives")
            break

    for i in range(len(recent) - 2):
        w = [recent[i]['class'], recent[i+1]['class'], recent[i+2]['class']]
        if w.count('perdu') >= 2:
            is_mediocre = True
            if "2 pertes sur 3" not in mediocre_why:
                mediocre_why.append("2 pertes sur 3 prédictions consécutives")
            break

    for i in range(len(recent) - 1):
        if recent[i]['class'] in ('r2','r3') and recent[i+1]['class'] in ('r2','r3'):
            is_mediocre = True
            mediocre_why.append("2 victoires tardives ✅2️⃣/✅3️⃣ consécutives")
            break

    is_hyper = (len(last5) == 5 and all(r['class'] == 'r0' for r in last5))
    is_bonne = (not is_mediocre and not is_hyper
                and total > 0 and good_count / total >= 0.60)

    # ── Stats par costume ───────────────────────────────────────────────────
    suit_stats = {}
    for r in recent:
        s = r['suit']
        if s not in suit_stats:
            suit_stats[s] = {'gagnes': 0, 'perdus': 0}
        if r['class'] == 'perdu':
            suit_stats[s]['perdus'] += 1
        else:
            suit_stats[s]['gagnes'] += 1

    losing_suits = [s for s, v in suit_stats.items() if v['perdus'] > v['gagnes']]

    # ── Stats par prédicteur ────────────────────────────────────────────────
    by_type = {}
    for r in recent:
        t = r['type']
        if t not in by_type:
            by_type[t] = {'r0':0,'r1':0,'r2':0,'r3':0,'perdu':0,'total':0}
        by_type[t][r['class']] += 1
        by_type[t]['total']    += 1

    # ── 3 combinaisons miroir possibles entre les 4 costumes ────────────────
    # Il existe exactement 3 façons de former des paires miroir parfaites :
    #   P1 : ♦↔♥ / ♣↔♠  (miroir par défaut)
    #   P2 : ♦↔♣ / ♥↔♠
    #   P3 : ♦↔♠ / ♥↔♣
    COMBOS = [
        {
            'num':    1,
            'name':   'Joker Alpha (P1)',
            'mirror': {'♦':'♥','♥':'♦','♣':'♠','♠':'♣'},
            'disp':   '♦️↔️❤️ / ♣️↔️♠️',
        },
        {
            'num':    2,
            'name':   'Kouamé Standard (P2)',
            'mirror': {'♦':'♣','♣':'♦','♥':'♠','♠':'♥'},
            'disp':   '♦️↔️♣️ / ❤️↔️♠️',
        },
        {
            'num':    3,
            'name':   'Kouamé Delta (P3)',
            'mirror': {'♦':'♠','♠':'♦','♥':'♣','♣':'♥'},
            'disp':   '♦️↔️♠️ / ❤️↔️♣️',
        },
    ]

    # ── Propositions supplémentaires (paramètres wx / df) ──────────────────
    PARAM_PROPOSALS = []
    if late_count > good_count:
        new_df = max(1, PREDICTION_DF - 1)
        PARAM_PROPOSALS.append({
            'num':  len(COMBOS) + len(PARAM_PROPOSALS) + 1,
            'name': 'Kouamé Tempo',
            'desc': (f"Réduire l'écart df : {PREDICTION_DF} → {new_df}\n"
                     f"   Car {late_count} victoires tardives ✅2️⃣/✅3️⃣ — le costume arrive tôt."),
            'changes': {'df': new_df},
        })
    if pdc > total * 0.40:
        new_wx = COMPTEUR13_THRESHOLD + 2
        PARAM_PROPOSALS.append({
            'num':  len(COMBOS) + len(PARAM_PROPOSALS) + 1,
            'name': 'Kouamé Strict',
            'desc': (f"Augmenter le seuil wx de C13 : {COMPTEUR13_THRESHOLD} → {new_wx}\n"
                     f"   Car {pdc}/{total} prédictions perdues ({pdc/total*100:.0f}%)."),
            'changes': {'wx': new_wx},
        })

    # ── Choisir la recommandation principale ───────────────────────────────
    def _combo_num_by_name(name):
        for c in GLOBAL_COMBOS:
            if c['name'] == name:
                return c['num']
        return None

    recommended_num = None
    recommended_reason = ""
    if is_mediocre:
        has_sp = '♠' in losing_suits or '♥' in losing_suits
        has_dc = '♦' in losing_suits or '♣' in losing_suits
        if losing_suits:
            ls_disp = '/'.join(SUIT_DISPLAY.get(s, s) for s in losing_suits)
            if has_sp and not has_dc:
                recommended_num    = _combo_num_by_name('Kouamé Standard (P2)')
                recommended_reason = f"{ls_disp} perdent → essayer ♦↔♣/❤↔♠"
            elif has_dc and not has_sp:
                recommended_num    = _combo_num_by_name('Kouamé Delta (P3)')
                recommended_reason = f"{ls_disp} perdent → essayer ♦↔♠/❤↔♣"
            else:
                recommended_num    = _combo_num_by_name('Joker Alpha (P1)')
                recommended_reason = f"{ls_disp} perdent → revenir au miroir par défaut ♦↔♥/♣↔♠"
        elif PARAM_PROPOSALS:
            recommended_num    = PARAM_PROPOSALS[0]['num']
            recommended_reason = PARAM_PROPOSALS[0]['name']

    # ── Construction du message ─────────────────────────────────────────────
    now_str = datetime.now().strftime('%d/%m/%Y %H:%M')

    if is_hyper:
        verdict = "🌟 HYPER SYMPA 🌟"
        vd      = "5 dernières prédictions en ✅0️⃣ — performance parfaite !"
    elif is_bonne:
        verdict = "✅ BONNE STRATÉGIE"
        vd      = "Majorité de ✅0️⃣/✅1️⃣ — continue comme ça."
    elif is_mediocre:
        verdict = "⚠️ STRATÉGIE MÉDIOCRE"
        vd      = "Problèmes : " + " | ".join(mediocre_why) + "."
    else:
        verdict = "📊 STRATÉGIE NEUTRE"
        vd      = "Résultats mitigés — ni excellents, ni mauvais."

    lines = [
        "╔══════════════════════════════╗",
        "║   🧠 ANALYSE DE STRATÉGIE   ║",
        "╚══════════════════════════════╝",
        f"🕒 {now_str}  |  {total} prédictions analysées",
        "",
        f"**{verdict}**",
        f"_{vd}_",
        "",
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━",
        "📈 **RÉSULTATS**",
        f"✅0️⃣ Direct  : {r0c}  ({r0c/total*100:.0f}%)",
        f"✅1️⃣ R1      : {r1c}  ({r1c/total*100:.0f}%)",
        f"✅2️⃣ R2      : {r2c}  ({r2c/total*100:.0f}%)",
        f"✅3️⃣ R3      : {r3c}  ({r3c/total*100:.0f}%)",
        f"❌ Perdus   : {pdc}  ({pdc/total*100:.0f}%)",
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━",
    ]

    type_labels = {'compteur2':'C2','compteur13':'C13',
                   'compteur8_pred':'C8','compteur11':'C11'}
    if len(by_type) > 1:
        lines.append("🤖 **PAR PRÉDICTEUR**")
        for t, v in by_type.items():
            if v['total'] == 0:
                continue
            won  = v['r0'] + v['r1'] + v['r2'] + v['r3']
            lbl  = type_labels.get(t, t)
            lines.append(f"  • {lbl}: {won}/{v['total']} gagnées "
                         f"({won/v['total']*100:.0f}%) | ❌ {v['perdu']}")
        lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

    if suit_stats:
        lines.append("🃏 **PAR COSTUME**")
        for s in ALL_SUITS:
            if s not in suit_stats:
                continue
            v   = suit_stats[s]
            tot = v['gagnes'] + v['perdus']
            if tot == 0:
                continue
            flag = " ⚠️" if s in losing_suits else " ✅"
            lines.append(f"  • {SUIT_DISPLAY.get(s,s)}: "
                         f"{v['gagnes']} gagnées / {v['perdus']} perdues{flag}")
        lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

    # ── 216 trackers indépendants : lecture des stats temps réel ────────────
    # Chaque (combo, wx, B, df_sim) a ses propres C13 + C2 qui ont tourné en
    # parallèle sur TOUS les jeux depuis le démarrage du bot.
    _WX_RANGE = range(3, 9)
    _B_RANGE  = range(3, 9)
    cur_mirror = dict(COMPTEUR13_MIRROR)

    # Construire sim_matrix depuis les trackers (lecture directe)
    sim_matrix = {}
    pred_lists  = {}
    for c in GLOBAL_COMBOS:
        for wx in _WX_RANGE:
            for df_sim in (1, 2):
                ref_b = min(max(compteur2_seuil_B, 3), 8)
                preds_wx = []
                for b in _B_RANGE:
                    key   = (c['num'], wx, b, df_sim)
                    state = silent_combo_states.get(key, {})
                    w     = state.get('wins',   0)
                    l     = state.get('losses', 0)
                    tot   = state.get('total',  0)
                    sim_matrix[(c['num'], wx, b, df_sim)] = {
                        'wins':   w,
                        'losses': l,
                        'total':  tot,
                        'score':  (w - l) if tot > 0 else -99,
                        'df_sim': df_sim,
                    }
                    if b == ref_b:
                        for h in state.get('pred_history', []):
                            preds_wx.append({
                                'gn':   h.get('gn', 0),
                                'suit': h.get('suit', '?'),
                                'win':  h.get('win', False),
                                'r':    0 if h.get('win') else None,
                                'c2a':  b,
                                'st':   'gagne_r0' if h.get('win') else 'perdu',
                            })
                pred_lists[(c['num'], wx, df_sim)] = preds_wx

    # ── Trouver la meilleure combinaison globale ─────────────────────────────
    valid_entries = {k: v for k, v in sim_matrix.items() if v['total'] >= 1}
    best_combo_key = None
    best_combo_val = None
    if valid_entries:
        best_combo_key, best_combo_val = max(valid_entries.items(), key=lambda x: x[1]['score'])

    if best_combo_key and not recommended_num:
        bck_mirror, bck_wx, bck_b, bck_df = best_combo_key
        bck_name  = next((c['name'] for c in GLOBAL_COMBOS if c['num'] == bck_mirror), f"P{bck_mirror}")
        recommended_num    = bck_mirror
        recommended_reason = (
            f"Meilleur score ({best_combo_val['score']:+d} pts) avec {bck_name} "
            f"wx={bck_wx} B={bck_b} trigger+{bck_df} sur {best_combo_val['total']} prédictions"
        )

    # ── Pour chaque combo miroir : meilleur (wx, B, df_sim) ─────────────────
    combo_scores = {}
    for c in GLOBAL_COMBOS:
        entries_for_c = {
            (wx, b, df_s): sim_matrix[(c['num'], wx, b, df_s)]
            for wx in _WX_RANGE for b in _B_RANGE for df_s in (1, 2)
        }
        valid_c = {k: v for k, v in entries_for_c.items() if v['total'] >= 3}
        if valid_c:
            best_wbs, best_v = max(valid_c.items(), key=lambda x: x[1]['score'])
            combo_scores[c['num']] = {
                'best_wx':    best_wbs[0],
                'best_b':     best_wbs[1],
                'best_df':    best_wbs[2],
                'best_score': best_v['score'],
                'best_wins':  best_v['wins'],
                'best_losses':best_v['losses'],
                'best_total': best_v['total'],
                'df1_best': max(
                    {(wx, b): sim_matrix[(c['num'], wx, b, 1)]
                     for wx in _WX_RANGE for b in _B_RANGE}.items(),
                    key=lambda x: x[1]['score'], default=(None, None)
                ),
                'df2_best': max(
                    {(wx, b): sim_matrix[(c['num'], wx, b, 2)]
                     for wx in _WX_RANGE for b in _B_RANGE}.items(),
                    key=lambda x: x[1]['score'], default=(None, None)
                ),
            }
        else:
            combo_scores[c['num']] = None

    # ── Tableau des 3 combinaisons miroir ───────────────────────────────────
    total_tracker_preds = sum(
        silent_combo_states.get((c['num'], 5, compteur2_seuil_B, 1), {}).get('total', 0)
        for c in GLOBAL_COMBOS
    )
    lines.append("🔄 **COMBINAISONS MIROIR — TRACKERS INDÉPENDANTS**")
    lines.append(
        "_(3 miroirs × wx3-8 × B3-8 × trigger+1/+2 = 216 compteurs C13+C2 propres · "
        f"B_actif={compteur2_seuil_B})_"
    )
    lines.append("")
    for c in GLOBAL_COMBOS:
        is_active = (c['mirror'] == cur_mirror)
        is_reco   = (c['num'] == recommended_num)
        tag = ""
        if is_active:
            tag += " ◀ ACTIF"
        if is_reco:
            tag += " ⭐ RECOMMANDÉ"
        lines.append(f"**{c['num']}. {c['name']}**{tag}")
        lines.append(f"   Paires : {c['disp']}")
        sc_data = combo_scores.get(c['num'])
        if sc_data:
            lines.append(
                f"   🔬 Meilleur : wx={sc_data['best_wx']} B={sc_data['best_b']} "
                f"trigger+{sc_data['best_df']} → "
                f"✅{sc_data['best_wins']} / ❌{sc_data['best_losses']} | "
                f"Score: {sc_data['best_score']:+d} sur {sc_data['best_total']} pred."
            )
            d1k, d1v = sc_data['df1_best']
            d2k, d2v = sc_data['df2_best']
            if d1v and d1v['total'] >= 1 and d2v and d2v['total'] >= 1:
                lines.append(
                    f"   📊 trigger+1 score={d1v['score']:+d} ({d1v['total']} pred) | "
                    f"trigger+2 score={d2v['score']:+d} ({d2v['total']} pred)"
                )
        else:
            lines.append("   🔬 Données insuffisantes — trackers en accumulation")
        lines.append("")

    if PARAM_PROPOSALS:
        lines.append("⚙️ **AJUSTEMENTS DE PARAMÈTRES**")
        lines.append("")
        for pp in PARAM_PROPOSALS:
            is_reco = (pp['num'] == recommended_num)
            tag = " ⭐ RECOMMANDÉ" if is_reco else ""
            lines.append(f"**{pp['num']}. {pp['name']}**{tag}")
            lines.append(f"   {pp['desc']}")
            lines.append("")

    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

    # ── Construire best_auto : la meilleure configuration complète ──────────
    # Priorité : meilleur (combo, wx, B) trouvé dans la simulation 216 combos
    best_auto = None
    if best_combo_key:
        bck_combo_n, bck_wx, bck_b, bck_df = best_combo_key
        bck_combo = next((c for c in GLOBAL_COMBOS if c['num'] == bck_combo_n), None)
        if bck_combo:
            best_auto = {
                'combo_num': bck_combo_n,
                'mirror':    bck_combo['mirror'],
                'disp':      bck_combo['disp'],
                'name':      bck_combo['name'],
                'wx':        bck_wx,
                'b':         bck_b,
                'df_sim':    bck_df,
                'score':     best_combo_val['score'],
                'wins':      best_combo_val['wins'],
                'losses':    best_combo_val['losses'],
                'total':     best_combo_val['total'],
            }

    # ── Recommandation finale ───────────────────────────────────────────────
    lines.append("")
    if best_auto:
        lines.append("╔══════════════════════════════╗")
        lines.append("║  🤖 STRATÉGIE AUTO-APPLIQUÉE ║")
        lines.append("╚══════════════════════════════╝")
        lines.append(f"**{best_auto['name']}**")
        lines.append(f"  Miroir  : {best_auto['disp']}")
        lines.append(f"  wx C13 : **{best_auto['wx']}** fois consécutives")
        lines.append(f"  B  C2  : **{best_auto['b']}** absences")
        lines.append(f"  df     : **trigger+{best_auto['df_sim']}** (costume attendu au jeu trigger+{best_auto['df_sim']})")
        lines.append(
            f"  Score  : **{best_auto['score']:+d}** pts "
            f"(✅{best_auto['wins']} gagnées | ❌{best_auto['losses']} perdues "
            f"sur {best_auto['total']} prédictions)"
        )
        lines.append("")
        lines.append("✅ **Appliquée immédiatement** — notification avec bouton Annuler envoyée.")
    elif recommended_num:
        lines.append(f"💡 **Recommandation : Oui {recommended_num}**")
        lines.append(f"   {recommended_reason}")
        lines.append("")
        lines.append("👉 Tape **`Oui`** pour appliquer, ou `Oui N` pour un choix manuel.")
    else:
        lines.append("📊 _Données insuffisantes pour une recommandation automatique._")
        lines.append("   Accumulation en cours — relance `/strategie` dans quelques jeux.")

    all_proposals = list(range(1, len(COMBOS) + len(PARAM_PROPOSALS) + 1))
    lines.append("")
    lines.append(f"_Choix manuel : `Oui N` (ex: `Oui 2`) — options: {', '.join(str(n) for n in all_proposals)}_")
    lines.append("")
    lines.append("🤖 _Baccarat AI — Analyse automatique_")

    # ── Stocker toutes les propositions en attente ──────────────────────────
    pending_strategy_proposal = {
        'combos':      GLOBAL_COMBOS,
        'param_props': PARAM_PROPOSALS,
        'expires':     datetime.now().timestamp() + 300,  # 5 min
        'best_auto':   best_auto,   # configuration complète recommandée (ou None)
    }

    # ── Sauvegarder la simulation silencieuse pour /raison2 ─────────────────
    last_strategy_simulation = {
        'timestamp':          datetime.now(),
        'combos':             GLOBAL_COMBOS,
        'combo_scores':       combo_scores,
        'sim_matrix':         sim_matrix,
        'pred_lists':         pred_lists,
        'best_combo_key':     best_combo_key,
        'best_combo_val':     best_combo_val,
        'param_proposals':    PARAM_PROPOSALS,
        'recommended_num':    recommended_num,
        'recommended_reason': recommended_reason,
        'total_c13':          sum(s.get('total', 0) for s in silent_combo_states.values()),
        'total_analysed':     total,
        'verdict':            verdict,
        'vd':                 vd,
        'r0c': r0c, 'r1c': r1c, 'r2c': r2c, 'r3c': r3c, 'pdc': pdc,
    }
    # Persister en base de données pour survivre aux redémarrages
    asyncio.ensure_future(save_strategy_simulation())

    # ── Auto-appliquer la meilleure stratégie + notifier admin ──────────────
    if best_auto:
        asyncio.ensure_future(apply_best_strategy_auto(best_auto))

    await event.respond("\n".join(lines))


async def cmd_oui(event):
    """
    Applique la stratégie proposée par /strategie quand l'admin répond 'Oui N'.
    """
    global pending_strategy_proposal, COMPTEUR13_MIRROR, COMPTEUR13_THRESHOLD, COMPTEUR13_SKIP
    global PREDICTION_DF, compteur2_seuil_B, compteur2_seuil_B_per_suit

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        return

    msg = event.message.message.strip()
    if not msg.lower().startswith('oui'):
        return

    if not pending_strategy_proposal:
        await event.respond("❌ Aucune proposition en attente. Tape `/strategie` d'abord.")
        return

    if datetime.now().timestamp() > pending_strategy_proposal.get('expires', 0):
        pending_strategy_proposal = {}
        await event.respond("⏰ La proposition a expiré (5 min). Tape `/strategie` pour relancer.")
        return

    parts         = msg.split()
    combos        = pending_strategy_proposal.get('combos', [])
    param_props   = pending_strategy_proposal.get('param_props', [])
    best_auto     = pending_strategy_proposal.get('best_auto')
    changes_applied = []

    # ── Détecter le mode : "Oui" seul, "Oui N", ou message invalide ─────────
    is_auto   = (len(parts) == 1)                           # "Oui" → auto
    is_manual = (len(parts) >= 2 and parts[1].isdigit())   # "Oui 2" → manuel
    if not is_auto and not is_manual:
        max_n = len(combos) + len(param_props)
        await event.respond(
            f"❌ Usage : **`Oui`** (applique auto) ou **`Oui N`** (choix 1 à {max_n})."
        )
        return

    # ── Mode automatique : "Oui" seul → applique la meilleure config complète
    if is_auto:
        if not best_auto:
            await event.respond(
                "❌ Aucune configuration automatique disponible.\n"
                "Utilise `Oui N` (ex: `Oui 2`) pour un choix manuel, "
                "ou relance `/strategie`."
            )
            return

        # Appliquer miroir
        old_mirror = dict(COMPTEUR13_MIRROR)
        COMPTEUR13_MIRROR.clear()
        COMPTEUR13_MIRROR.update(best_auto['mirror'])
        changes_applied.append(
            f"✅ Miroir C13 : **{best_auto['disp']}**"
        )

        # Appliquer wx
        old_wx = COMPTEUR13_THRESHOLD
        COMPTEUR13_THRESHOLD = best_auto['wx']
        changes_applied.append(
            f"✅ Seuil wx C13 : {old_wx} → **{COMPTEUR13_THRESHOLD}** fois consécutives"
        )

        # Appliquer B (pour tous les costumes + global)
        old_b = compteur2_seuil_B
        compteur2_seuil_B = best_auto['b']
        for s in ALL_SUITS:
            compteur2_seuil_B_per_suit[s] = best_auto['b']
        changes_applied.append(
            f"✅ Seuil B  C2  : {old_b} → **{compteur2_seuil_B}** absences (tous costumes)"
        )

        # Appliquer df_sim → COMPTEUR13_SKIP
        old_df = COMPTEUR13_SKIP
        new_df_sim = best_auto.get('df_sim', 1)
        COMPTEUR13_SKIP = max(0, new_df_sim - PREDICTION_DF)
        if COMPTEUR13_SKIP != old_df:
            changes_applied.append(f"✅ df C13 : trigger+{old_df + PREDICTION_DF} → **trigger+{new_df_sim}**")

        pending_strategy_proposal = {}

        logger.info(
            f"🏆 Meilleure stratégie appliquée : {best_auto['name']} "
            f"miroir={dict(COMPTEUR13_MIRROR)} wx={COMPTEUR13_THRESHOLD} "
            f"B={compteur2_seuil_B} df+{new_df_sim}"
        )

        lines = [
            "🏆 **Meilleure stratégie appliquée avec succès !**",
            f"**{best_auto['name']}** · trigger+{new_df_sim}",
            "",
        ] + changes_applied + [
            "",
            f"Score simulation : **{best_auto['score']:+d}** pts "
            f"(✅{best_auto['wins']} gagnées | ❌{best_auto['losses']} perdues "
            f"sur {best_auto['total']} prédictions C13)",
            "",
            "Les nouveaux paramètres sont actifs immédiatement.",
            "Tape `/strategie` pour une nouvelle analyse après accumulation.",
        ]
        await event.respond("\n".join(lines))
        return

    # ── Mode manuel : "Oui N" → choix spécifique ────────────────────────────
    num = int(parts[1])
    combo_match = next((c for c in combos      if c['num'] == num), None)
    param_match = next((p for p in param_props if p['num'] == num), None)

    if not combo_match and not param_match:
        max_n = len(combos) + len(param_props)
        await event.respond(f"❌ Numéro invalide. Choix disponibles : 1 à {max_n}.")
        return

    if combo_match:
        old_mirror = dict(COMPTEUR13_MIRROR)
        COMPTEUR13_MIRROR.clear()
        COMPTEUR13_MIRROR.update(combo_match['mirror'])
        changes_applied.append(
            f"✅ Combinaison miroir C13 → **{combo_match['disp']}**"
        )
        logger.info(
            f"🔄 Stratégie '{combo_match['name']}' appliquée : "
            f"miroir {old_mirror} → {dict(COMPTEUR13_MIRROR)}"
        )

    if param_match:
        ch = param_match.get('changes', {})
        if 'df' in ch:
            old_df = PREDICTION_DF
            PREDICTION_DF = ch['df']
            changes_applied.append(f"✅ Écart df : {old_df} → **{PREDICTION_DF}**")
        if 'wx' in ch:
            old_wx = COMPTEUR13_THRESHOLD
            COMPTEUR13_THRESHOLD = ch['wx']
            changes_applied.append(f"✅ Seuil wx C13 : {old_wx} → **{COMPTEUR13_THRESHOLD}**")
        if 'b' in ch:
            old_b = compteur2_seuil_B
            compteur2_seuil_B = ch['b']
            for s in ALL_SUITS:
                compteur2_seuil_B_per_suit[s] = ch['b']
            changes_applied.append(f"✅ Seuil B C2 : {old_b} → **{compteur2_seuil_B}**")

    pending_strategy_proposal = {}

    name = combo_match['name'] if combo_match else param_match['name']
    lines = [
        f"🎯 **Stratégie « {name} » appliquée !**",
        "",
    ] + changes_applied + [
        "",
        "Les nouveaux paramètres sont actifs immédiatement.",
        "Tape `/strategie` pour une nouvelle analyse.",
    ]
    await event.respond("\n".join(lines))


async def cmd_reset(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    await event.respond("🔄 Reset en cours...")
    await perform_full_reset("Reset manuel")
    await event.respond("✅ Reset effectué!")


async def cmd_resetdb(event):
    """
    /resetdb confirm — efface TOUTES les données de la base PostgreSQL et remet
    les compteurs mémoire à zéro. Action irréversible, admin seulement.
    """
    global prediction_queue, pending_predictions, prediction_history
    global processed_games, game_history, game_result_cache
    global compteur2_trackers, compteur2_seuil_B_per_suit
    global countdown_panel_counter, hourly_game_count, hourly_suit_data, bilan_1440_sent
    global perdu_events, b_change_history

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()
    if len(parts) < 2 or parts[1].lower() != 'confirm':
        await event.respond(
            "⚠️ **SUPPRESSION DE TOUTES LES DONNÉES DB**\n\n"
            "Cette action efface :\n"
            "• Toutes les prédictions (pending + historique)\n"
            "• Toutes les données horaires\n"
            "• Tous les panneaux countdown\n"
            "• Toutes les clés kv_store (session, B, C7, C8, C11…)\n\n"
            "🔴 **Action irréversible !**\n\n"
            "Pour confirmer : `/resetdb confirm`"
        )
        return

    await event.respond("⏳ Suppression en cours…")

    # 1. Vider la base PostgreSQL
    counts = await db.db_reset_all()

    # 2. Remettre les compteurs mémoire à zéro
    prediction_queue.clear()
    pending_predictions.clear()
    prediction_history.clear()
    processed_games.clear()
    recently_predicted.clear()
    game_history.clear()
    game_result_cache.clear()
    perdu_events.clear()
    b_change_history.clear()
    bilan_1440_sent = False
    countdown_panel_counter = 0

    # C2 trackers
    for s in ALL_SUITS:
        compteur2_trackers[s].reset(0)
        compteur2_seuil_B_per_suit[s] = compteur2_seuil_B

    # Données horaires
    for h in range(24):
        hourly_game_count[h] = 0
        for s in ALL_SUITS:
            hourly_suit_data[h][s] = 0

    lines = ["✅ **RESET DB COMPLET**\n"]
    for table, cnt in counts.items():
        lines.append(f"• `{table}` : {cnt} ligne(s) supprimée(s)")
    lines.append("\n🟢 Compteurs mémoire remis à zéro.")
    lines.append("🔄 La session Telegram est aussi effacée — le bot va se reconnecter automatiquement au prochain démarrage.")
    logger.warning("🔴 RESETDB COMPLET effectué par l'admin")
    await event.respond("\n".join(lines), parse_mode='markdown')


async def cmd_debloquer(event):
    """Déblocage d'urgence : vide pending_predictions, suit_block_until et prediction_queue."""
    global pending_predictions, suit_block_until, prediction_queue
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    lines = []

    nb_pending = len(pending_predictions)
    if nb_pending:
        for gn, pred in list(pending_predictions.items()):
            stop_animation(gn)
        pending_predictions.clear()
        lines.append(f"🧹 {nb_pending} prédiction(s) bloquée(s) supprimée(s)")

    nb_blocked = len([s for s in suit_block_until if datetime.now() < suit_block_until[s]])
    if nb_blocked:
        suit_block_until.clear()
        lines.append(f"🔓 {nb_blocked} costume(s) débloqué(s)")

    nb_queue = len(prediction_queue)
    if nb_queue:
        prediction_queue.clear()
        lines.append(f"🗑️ {nb_queue} prédiction(s) en file supprimée(s)")

    if lines:
        rapport = "✅ **DÉBLOCAGE D'URGENCE**\n\n" + "\n".join(lines) + "\n\n🟢 Bot actif et prêt."
    else:
        rapport = "✅ Rien à débloquer — bot déjà actif."

    logger.warning(f"🔓 Déblocage manuel: {'; '.join(lines) if lines else 'rien'}")
    await event.respond(rapport, parse_mode='markdown')


# ============================================================================
# RAISON PDF
# ============================================================================

def pdf_safe(text: str) -> str:
    """Remplace les symboles hors Latin-1 par leur équivalent ASCII pour FPDF/Helvetica."""
    subs = [
        ('♠️', 'Pique'),  ('❤️', 'Coeur'),  ('♦️', 'Carreau'), ('♣️', 'Trefle'),
        ('♠', 'Pique'),   ('❤', 'Coeur'),   ('♦', 'Carreau'),  ('♣', 'Trefle'),
        ('♥', 'Coeur'),   ('\ufe0f', ''),
        ('Cœur', 'Coeur'), ('Trèfle', 'Trefle'),
        ('→', '->'),       ('←', '<-'),       ('–', '-'),        ('—', '-'),
        ('é', 'e'),        ('è', 'e'),        ('ê', 'e'),        ('à', 'a'),
        ('â', 'a'),        ('î', 'i'),        ('ô', 'o'),        ('ù', 'u'),
        ('û', 'u'),        ('ç', 'c'),        ('ï', 'i'),        ('ë', 'e'),
    ]
    for old, new in subs:
        text = text.replace(old, new)
    return text


def generate_raison2_pdf(sim: dict) -> bytes:
    """Génère un PDF rapport complet de la simulation C13 (216 combinaisons miroir × wx × B × skip)."""
    combos     = sim.get('combos', [])
    sim_matrix = sim.get('sim_matrix', {})
    ts         = sim['timestamp'].strftime('%d/%m/%Y %H:%M:%S')
    total_c13  = sim.get('total_c13', 0)
    total_an   = sim.get('total_analysed', 0)
    verdict    = sim.get('verdict', '')
    best_key   = sim.get('best_combo_key')
    best_val   = sim.get('best_combo_val')
    rec_num    = sim.get('recommended_num')
    rec_reason = sim.get('recommended_reason', '')

    _COMBO_NAMES = {c['num']: c['name'] for c in combos}
    _COMBO_DISP  = {c['num']: c.get('disp', '?') for c in combos}

    VIOLET  = (90, 0, 160)
    PURPLE2 = (130, 50, 200)
    WHITE   = (255, 255, 255)
    DARK    = (30, 30, 30)
    GREY    = (100, 100, 100)
    GREEN   = (0, 130, 0)
    RED     = (190, 0, 0)
    GOLD    = (180, 130, 0)
    BG_ALT  = (245, 240, 255)
    BG_P1   = (230, 245, 255)
    BG_P2   = (230, 255, 230)
    BG_P3   = (255, 245, 225)
    BG_BEST = (255, 248, 200)

    COMBO_COLORS = {1: BG_P1, 2: BG_P2, 3: BG_P3}

    pdf = FPDF(orientation='L', format='A4')
    pdf.set_auto_page_break(auto=True, margin=12)
    pdf.set_margins(8, 8, 8)
    pdf.add_page()

    # ── Titre ─────────────────────────────────────────────────────────────────
    pdf.set_font('Helvetica', 'B', 17)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    pdf.cell(0, 13, 'BACCARAT AI  -  SIMULATION C13  (108 COMBINAISONS)', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(2)

    pdf.set_font('Helvetica', '', 9)
    pdf.set_text_color(*GREY)
    pdf.cell(0, 6,
        f"Genere le {datetime.now().strftime('%d/%m/%Y %H:%M')}  |  "
        f"Derniere simulation : {ts}  |  "
        f"{total_c13} predictions C13 simulees  |  "
        f"{total_an} predictions totales analysees",
        new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.ln(3)

    # ── Verdict global ─────────────────────────────────────────────────────────
    pdf.set_font('Helvetica', 'B', 10)
    pdf.set_text_color(*DARK)
    pdf.cell(0, 7, pdf_safe(verdict), new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.ln(2)

    # ── Meilleure configuration ────────────────────────────────────────────────
    if best_key and best_val and len(best_key) == 4:
        bm, bwx, bb, bdf = best_key
        pdf.set_fill_color(*BG_BEST)
        pdf.set_draw_color(*GOLD)
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_text_color(*GOLD)
        txt = (f"MEILLEURE CONFIGURATION GLOBALE :  {_COMBO_NAMES.get(bm,'?')}  |  "
               f"wx={bwx}  |  B={bb}  |  df+{bdf}  |  Paires : {pdf_safe(_COMBO_DISP.get(bm,'?'))}")
        pdf.cell(0, 8, txt, border=1, new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
        pdf.set_font('Helvetica', '', 9)
        pdf.set_text_color(*DARK)
        stats = (f"Gagnes : {best_val['wins']}   |   Perdus : {best_val['losses']}   |   "
                 f"Score : {best_val['score']:+d}   |   Predictions qualifiees : {best_val['total']}")
        pdf.cell(0, 6, stats, new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
        pdf.ln(4)

    if rec_num:
        pdf.set_font('Helvetica', 'B', 9)
        pdf.set_text_color(*PURPLE2)
        pdf.cell(0, 6, f"Recommandation : Oui {rec_num}  -  {pdf_safe(rec_reason)}",
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
        pdf.ln(3)

    # ── TABLE PRINCIPALE — toutes les 216 combinaisons ─────────────────────────
    # Trier par score décroissant
    sorted_entries = sorted(
        [(k, v) for k, v in sim_matrix.items() if v['total'] >= 1],
        key=lambda x: x[1]['score'],
        reverse=True
    )

    # Colonnes (paysage A4 = 277mm, marges 16 → 261 mm utiles)
    cw = [8, 36, 34, 14, 14, 14, 20, 20, 22, 18, 20, 20]
    headers = ['#', 'Miroir', 'Paires', 'wx', 'B', 'd', 'Gagnes', 'Perdus',
               'Score', 'C2 wins', 'Total pred.', 'Score/Total']

    pdf.set_font('Helvetica', 'B', 8)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    for h, w in zip(headers, cw):
        pdf.cell(w, 8, h, border=1, fill=True, align='C')
    pdf.ln()

    pdf.set_font('Helvetica', '', 8)
    for rank, (key, val) in enumerate(sorted_entries, 1):
        combo_n, wx, b, df_s = key
        is_best = (key == best_key)
        bg = BG_BEST if is_best else COMBO_COLORS.get(combo_n, (255, 255, 255))
        wins      = val['wins']
        losses    = val['losses']
        score     = val['score']
        total     = val['total']
        c2w       = val.get('c2_conf_wins', 0)
        score_pct = f"{score/total*100:+.0f}%" if total else '--'

        pdf.set_fill_color(*bg)
        pdf.set_text_color(*DARK)
        row = [
            str(rank),
            _COMBO_NAMES.get(combo_n, f'P{combo_n}'),
            pdf_safe(_COMBO_DISP.get(combo_n, '?')),
            str(wx),
            str(b),
            f"df+{df_s}",
            str(wins),
            str(losses),
            f"{score:+d}",
            str(c2w),
            str(total),
            score_pct,
        ]
        aligns = ['C', 'L', 'L', 'C', 'C', 'C', 'C', 'C', 'C', 'C', 'C', 'C']
        for val_txt, w, align in zip(row, cw, aligns):
            # Colore le score
            if val_txt.startswith('+') and val_txt != '+0':
                pdf.set_text_color(*GREEN)
            elif val_txt.startswith('-'):
                pdf.set_text_color(*RED)
            else:
                pdf.set_text_color(*DARK)
            pdf.cell(w, 7, val_txt, border=1, fill=True, align=align)
        pdf.ln()

    # ── TABLEAUX DÉTAILLÉS PAR MIROIR (une section par miroir) ─────────────────
    for cnum in [1, 2, 3]:
        cname = _COMBO_NAMES.get(cnum, f'P{cnum}')
        cdisp = pdf_safe(_COMBO_DISP.get(cnum, '?'))
        bg_hdr = COMBO_COLORS.get(cnum, (240, 240, 240))

        pdf.add_page()
        pdf.set_font('Helvetica', 'B', 12)
        pdf.set_fill_color(*VIOLET)
        pdf.set_text_color(*WHITE)
        pdf.cell(0, 10, f"DETAIL — {cname}  |  Paires : {cdisp}",
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
        pdf.ln(4)

        # Tableau croisé wx (lignes) × B (colonnes)
        cell_w = 36
        cell_h = 9
        b_vals  = list(range(3, 9))
        wx_vals = list(range(3, 9))

        # En-tête colonnes B
        pdf.set_font('Helvetica', 'B', 9)
        pdf.set_fill_color(*VIOLET)
        pdf.set_text_color(*WHITE)
        pdf.cell(14, cell_h, 'wx \\ B', border=1, fill=True, align='C')
        for b in b_vals:
            pdf.cell(cell_w, cell_h, f"B = {b}", border=1, fill=True, align='C')
        pdf.ln()

        for wx in wx_vals:
            # Numéro de ligne
            pdf.set_fill_color(*bg_hdr)
            pdf.set_font('Helvetica', 'B', 9)
            pdf.set_text_color(*DARK)
            pdf.cell(14, cell_h, f"wx={wx}", border=1, fill=True, align='C')

            for b in b_vals:
                v = sim_matrix.get((cnum, wx, b, 0))
                if v and v['total'] >= 1:
                    sc = v['score']
                    tot = v['total']
                    label = f"Score:{sc:+d}  ({tot} pred.)"
                    txt2  = f"V:{v['wins']} / D:{v['losses']}"
                    is_b  = ((cnum, wx, b, 0) == best_key)
                    cell_bg = BG_BEST if is_b else (
                        (220, 255, 220) if sc > 0 else
                        (255, 220, 220) if sc < 0 else
                        (245, 245, 245)
                    )
                    pdf.set_fill_color(*cell_bg)
                    pdf.set_font('Helvetica', 'B', 8)
                    sc_color = GREEN if sc > 0 else (RED if sc < 0 else GREY)
                    pdf.set_text_color(*sc_color)
                    # Cellule multi-ligne (simulée avec 2 cellules empilées)
                    x0 = pdf.get_x()
                    y0 = pdf.get_y()
                    pdf.cell(cell_w, cell_h // 2 + 1, label, border='LTR', fill=True, align='C')
                    pdf.ln()
                    pdf.set_x(x0)
                    pdf.set_font('Helvetica', '', 7)
                    pdf.set_text_color(*DARK)
                    pdf.cell(cell_w, cell_h // 2, txt2, border='LBR', fill=True, align='C')
                    pdf.set_xy(x0 + cell_w, y0)
                else:
                    pdf.set_fill_color(250, 250, 250)
                    pdf.set_font('Helvetica', '', 8)
                    pdf.set_text_color(*GREY)
                    pdf.cell(cell_w, cell_h, '--', border=1, fill=True, align='C')
            pdf.ln()

        pdf.ln(4)
        pdf.set_font('Helvetica', 'I', 8)
        pdf.set_text_color(*GREY)
        pdf.cell(0, 5,
            'Score = Victoires - Defaites  |  pred. = predictions qualifiees (count >= wx)  |  '
            'Jaune = meilleure configuration globale',
            new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    # ── Pied de page final ────────────────────────────────────────────────────
    pdf.add_page()
    pdf.set_font('Helvetica', 'B', 13)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    pdf.cell(0, 10, 'RESUME GLOBAL', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(5)

    # Résumé par miroir
    for cnum in [1, 2, 3]:
        cname = _COMBO_NAMES.get(cnum, f'P{cnum}')
        cdisp = pdf_safe(_COMBO_DISP.get(cnum, '?'))
        # Trouver le meilleur (wx, B) pour ce miroir
        best_sub = None
        best_sub_val = None
        for wx in range(3, 9):
            for b in range(3, 9):
                v = sim_matrix.get((cnum, wx, b, 0))
                if v and v['total'] >= 1:
                    if best_sub_val is None or v['score'] > best_sub_val['score']:
                        best_sub = (wx, b)
                        best_sub_val = v
        pdf.set_fill_color(*COMBO_COLORS.get(cnum, (240, 240, 240)))
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_text_color(*DARK)
        pdf.cell(0, 8, f"{cname}  |  {cdisp}",
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, border=1, fill=True)
        if best_sub and best_sub_val:
            wx_b, b_b = best_sub
            pdf.set_font('Helvetica', '', 9)
            pdf.cell(0, 7,
                f"  Meilleur wx={wx_b}  B={b_b}  |  "
                f"Gagnes:{best_sub_val['wins']}  Perdus:{best_sub_val['losses']}  "
                f"Score:{best_sub_val['score']:+d}  sur {best_sub_val['total']} predictions",
                new_x=XPos.LMARGIN, new_y=YPos.NEXT, border=1)
        pdf.ln(3)

    pdf.ln(6)
    pdf.set_font('Helvetica', 'I', 8)
    pdf.set_text_color(*GREY)
    pdf.cell(0, 5,
        f"Rapport genere le {datetime.now().strftime('%d/%m/%Y  %H:%M')}  -  BACCARAT AI",
        new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    return pdf.output()


def generate_raison_pdf() -> bytes:
    """Génère un PDF tableau récapitulatif complet des prédictions avec raisons."""
    from collections import Counter as _Counter

    suit_names  = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
    suit_colors = {'♠': (20, 20, 20), '♥': (180, 0, 0), '♦': (0, 80, 180), '♣': (0, 120, 0)}
    status_labels = {
        'gagne_r0': 'GAGNE R0', 'gagne_r1': 'GAGNE R1',
        'gagne_r2': 'GAGNE R2', 'gagne_r3': 'GAGNE R3',
        'perdu':    'PERDU',    'en_cours': 'EN COURS',
    }
    status_colors = {
        'gagne_r0': (0, 130, 0),  'gagne_r1': (0, 130, 0),
        'gagne_r2': (0, 130, 0),  'gagne_r3': (0, 130, 0),
        'perdu':    (190, 0, 0),  'en_cours': (80, 80, 200),
    }

    VIOLET   = (90, 0, 160)
    WHITE    = (255, 255, 255)
    DARK     = (30, 30, 30)
    GREY_TXT = (100, 100, 100)

    preds = list(prediction_history)

    pdf = FPDF(orientation='L', format='A4')
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.set_margins(8, 8, 8)
    pdf.add_page()

    # ── En-tête ───────────────────────────────────────────────────────────────
    pdf.set_font('Helvetica', 'B', 17)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    pdf.cell(0, 13, 'BACCARAT AI  -  RAPPORT DES PREDICTIONS', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(2)

    pdf.set_font('Helvetica', '', 9)
    pdf.set_text_color(*GREY_TXT)
    wins   = sum(1 for p in preds if p.get('status','').startswith('gagne'))
    losses = sum(1 for p in preds if p.get('status') == 'perdu')
    pending_c = sum(1 for p in preds if p.get('status') == 'en_cours')
    total  = len(preds)
    pct    = f"{wins*100//total}%" if total else "0%"
    pdf.cell(0, 6,
        f"Genere le {datetime.now().strftime('%d/%m/%Y  %H:%M')}  |  "
        f"Total: {total}  |  Gagnes: {wins}  |  Perdus: {losses}  |  "
        f"En cours: {pending_c}  |  Taux de reussite: {pct}", new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.ln(5)

    # ── En-tête du tableau ────────────────────────────────────────────────────
    # Largeurs colonnes (paysage A4 = 277mm - 16 marges = 261mm usable)
    cw = [28, 16, 18, 24, 22, 90, 28, 14, 21]
    #      Date Heur  Jeu  Cost Cptr Raison         Statut  R.  Verif

    headers = ['Date', 'Heure', 'Jeu', 'Costume', 'Compteur',
               'Raison principale', 'Statut', 'R.', 'Verifie']

    pdf.set_font('Helvetica', 'B', 9)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    for h, w in zip(headers, cw):
        pdf.cell(w, 9, h, border=1, fill=True, align='C')
    pdf.ln()

    # ── Lignes du tableau ─────────────────────────────────────────────────────
    alt = False
    for pred in preds:
        suit     = pred.get('suit', '?')
        status   = pred.get('status', 'en_cours')
        pred_at  = pred['predicted_at']
        date_str = pred_at.strftime('%d/%m/%Y')
        heure_str= pred_at.strftime('%H:%M:%S')
        jeu_str  = f"#{pred['predicted_game']}"
        suit_nm  = pdf_safe(suit_names.get(suit, suit))
        _pdf_type_labels = {
            'compteur2':     'C2',
            'compteur11':    'C11',
            'compteur13':    'C13',
            'compteur8_pred':'C8★',
            'distribution':  'Dist',
        }
        cptr_str = _pdf_type_labels.get(pred.get('type', ''), pred.get('type', 'Auto') or 'Auto')
        reason   = pdf_safe(pred.get('reason', '') or '-')
        reason_s = reason[:52] + ('...' if len(reason) > 52 else '')
        stat_lbl = status_labels.get(status, status)
        ratk     = pred.get('rattrapage_level', 0)
        rat_str  = f"R{ratk}" if ratk else 'R0'
        verif    = f"#{pred['verified_by_game']}" if pred.get('verified_by_game') else '-'

        sr, sg, sb = suit_colors.get(suit, (0, 0, 0))
        cr, cg, cb = status_colors.get(status, (80, 80, 80))
        bg = (242, 242, 252) if alt else (255, 255, 255)

        pdf.set_fill_color(*bg)
        pdf.set_font('Helvetica', '', 8)
        pdf.set_text_color(*DARK)

        pdf.cell(cw[0], 8, date_str,  border=1, fill=True, align='C')
        pdf.cell(cw[1], 8, heure_str, border=1, fill=True, align='C')
        pdf.cell(cw[2], 8, jeu_str,   border=1, fill=True, align='C')

        pdf.set_font('Helvetica', 'B', 8)
        pdf.set_text_color(sr, sg, sb)
        pdf.cell(cw[3], 8, suit_nm,   border=1, fill=True, align='C')

        pdf.set_font('Helvetica', '', 8)
        pdf.set_text_color(*DARK)
        pdf.cell(cw[4], 8, cptr_str,  border=1, fill=True, align='C')
        pdf.cell(cw[5], 8, reason_s,  border=1, fill=True, align='L')

        pdf.set_font('Helvetica', 'B', 8)
        pdf.set_text_color(cr, cg, cb)
        pdf.cell(cw[6], 8, stat_lbl,  border=1, fill=True, align='C')

        pdf.set_text_color(*DARK)
        pdf.set_font('Helvetica', '', 8)
        pdf.cell(cw[7], 8, rat_str,   border=1, fill=True, align='C')
        pdf.cell(cw[8], 8, verif,     border=1, fill=True, align='C')
        pdf.ln()
        alt = not alt

    if not preds:
        pdf.set_text_color(*GREY_TXT)
        pdf.cell(0, 8, 'Aucune prediction enregistree', border=1, align='C')
        pdf.ln()

    # ── Résumé par costume ────────────────────────────────────────────────────
    pdf.ln(8)
    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    pdf.cell(0, 9, 'RESUME PAR COSTUME', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
    pdf.ln(3)

    for suit in ['♠', '♥', '♦', '♣']:
        sp = [p for p in preds if p.get('suit') == suit]
        if not sp:
            continue
        w_s  = sum(1 for p in sp if p.get('status','').startswith('gagne'))
        l_s  = sum(1 for p in sp if p.get('status') == 'perdu')
        en_s = sum(1 for p in sp if p.get('status') == 'en_cours')
        pct_s = f"{w_s*100//len(sp)}%" if sp else "0%"
        r, g, b = suit_colors.get(suit, (0,0,0))
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_text_color(r, g, b)
        pdf.cell(0, 7,
            f"  {pdf_safe(suit_names.get(suit,suit))} :  "
            f"{len(sp)} pred.  |  {w_s} gagnes  |  {l_s} perdus  |  "
            f"{en_s} en cours  |  Reussite: {pct_s}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── Résumé par compteur ───────────────────────────────────────────────────
    pdf.ln(4)
    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(*VIOLET)
    pdf.set_text_color(*WHITE)
    pdf.cell(0, 9, 'RESUME PAR COMPTEUR DECLENCHEUR', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
    pdf.ln(3)

    for ctype, label in [('compteur2', 'Compteur 2'), ('standard', 'Auto / Autres')]:
        sp = [p for p in preds if p.get('type','standard') == ctype or
              (ctype == 'standard' and p.get('type','standard') != 'compteur2')]
        if not sp:
            continue
        w_s  = sum(1 for p in sp if p.get('status','').startswith('gagne'))
        l_s  = sum(1 for p in sp if p.get('status') == 'perdu')
        pct_s = f"{w_s*100//len(sp)}%" if sp else "0%"
        pdf.set_font('Helvetica', 'B', 10)
        pdf.set_text_color(*DARK)
        pdf.cell(0, 7,
            f"  {label} :  {len(sp)} pred.  |  {w_s} gagnes  |  {l_s} perdus  |  Reussite: {pct_s}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── Détail des raisons complètes ──────────────────────────────────────────
    long_preds = [p for p in preds if len(p.get('reason','') or '') > 52]
    if long_preds:
        pdf.ln(8)
        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_fill_color(*VIOLET)
        pdf.set_text_color(*WHITE)
        pdf.cell(0, 9, 'DETAIL COMPLET DES RAISONS', new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align='C')
        pdf.ln(3)

        for pred in long_preds:
            suit   = pred.get('suit', '?')
            reason = pdf_safe(pred.get('reason', '') or '-')
            jeu    = pred['predicted_game']
            status = pred.get('status', 'en_cours')
            sr, sg, sb = suit_colors.get(suit, (0,0,0))
            cr, cg, cb = status_colors.get(status, (80,80,80))

            pdf.set_font('Helvetica', 'B', 9)
            pdf.set_text_color(sr, sg, sb)
            pdf.cell(0, 7,
                f"  Jeu #{jeu}  -  {pdf_safe(suit_names.get(suit,suit))}  "
                f"({pred['predicted_at'].strftime('%d/%m %H:%M')})", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

            pdf.set_font('Helvetica', '', 8)
            pdf.set_text_color(*DARK)
            for chunk in [reason[i:i+130] for i in range(0, len(reason), 130)]:
                pdf.cell(0, 5, f"    {chunk}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            pdf.ln(2)

    # ── Pied de page ─────────────────────────────────────────────────────────
    pdf.ln(5)
    pdf.set_font('Helvetica', 'I', 8)
    pdf.set_text_color(*GREY_TXT)
    pdf.cell(0, 5,
        'BACCARAT AI  -  Rapport raisons  -  '
        f'{datetime.now().strftime("%d/%m/%Y %H:%M")}', new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')

    return bytes(pdf.output())


# ============================================================================
# COMMANDES : POURQUOI / PERDUS / BILAN
# ============================================================================

async def cmd_raison(event):
    """
    /raison       — 15 dernières prédictions avec raison détaillée
    /raison N     — Cherche la prédiction du jeu #N
    /raison pdf   — PDF complet de toutes les prédictions avec raisons
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()
    sub   = parts[1] if len(parts) > 1 else ''

    STATUS_MAP = {
        'gagne_r0': '✅ GAGNE R0', 'gagne_r1': '✅ GAGNE R1',
        'gagne_r2': '✅ GAGNE R2', 'gagne_r3': '✅ GAGNE R3',
        'perdu': '❌ PERDU', 'en_cours': '⏳ EN COURS',
        'expirée_api': '🔌 EXPIRE API',
    }

    def format_pred_block(pred, index=None):
        game    = pred['predicted_game']
        suit    = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
        status  = STATUS_MAP.get(pred.get('status', ''), pred.get('status', '?'))
        pred_at = pred['predicted_at'].strftime('%d/%m %H:%M:%S')
        _type_labels = {
            'compteur2':     'C2',
            'compteur11':    'C11',
            'compteur13':    'C13',
            'compteur8_pred':'C8★',
            'distribution':  'Distrib',
        }
        ptype = _type_labels.get(pred.get('type', ''), pred.get('type', 'Auto') or 'Auto')
        reason  = pred.get('reason', '') or 'Raison non enregistree.'
        ratk    = pred.get('rattrapage_level', 0)
        rat_str = f" R{ratk}" if ratk else ""
        prefix  = f"{index}. " if index else ""
        return (
            f"{prefix}**#{game}** {suit} | {ptype} | {status}{rat_str}\n"
            f"   🕐 {pred_at}\n"
            f"   📖 _{reason}_"
        )

    # ── /raison pdf ──────────────────────────────────────────────────────────
    if sub.lower() == 'pdf':
        if not prediction_history:
            await event.respond("❌ Aucune prédiction dans l'historique.")
            return
        await event.respond("📄 Génération du PDF rapport prédictions...")
        try:
            wins   = sum(1 for p in prediction_history if p.get('status','').startswith('gagne'))
            losses = sum(1 for p in prediction_history if p.get('status') == 'perdu')
            buf = io.BytesIO(generate_raison_pdf())
            buf.name = 'rapport_predictions.pdf'
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_file(
                admin_entity, buf,
                caption=(
                    "📖 **RAPPORT PRÉDICTIONS**\n\n"
                    f"📊 {len(prediction_history)} prédictions\n"
                    f"✅ {wins} gagnées  |  ❌ {losses} perdues\n"
                    f"📅 {datetime.now().strftime('%d/%m/%Y %H:%M')}"
                ),
                parse_mode='markdown'
            )
        except Exception as e:
            logger.error(f"Erreur PDF raison: {e}")
            await event.respond(f"❌ Erreur PDF: {e}")
        return

    # ── /raison N — cherche un jeu précis ───────────────────────────────────
    if sub.isdigit():
        target = int(sub)
        found  = next((p for p in prediction_history if p['predicted_game'] == target), None)
        if not found:
            await event.respond(f"❌ Aucune prediction trouvee pour le jeu #{target}")
            return
        b_val = compteur2_seuil_B_per_suit.get(found['suit'], compteur2_seuil_B)
        await event.respond(
            f"🔎 **RAISON — JEU #{target}**\n\n"
            + format_pred_block(found) +
            f"\n   📏 Seuil B ({found['suit']}): **{b_val}**",
            parse_mode='markdown'
        )
        return

    # ── /raison — 15 dernières ───────────────────────────────────────────────
    recent = prediction_history[:15]
    if not recent:
        await event.respond("❌ Aucune prediction dans l'historique.")
        return
    lines = ["📖 **RAISONS DES 15 DERNIERES PREDICTIONS**\n"]
    for i, pred in enumerate(recent, 1):
        lines.append(format_pred_block(pred, index=i))
        lines.append("")
    lines.append("📄 `/raison pdf` — PDF complet | 🔎 `/raison N` — Jeu #N")
    await event.respond("\n".join(lines), parse_mode='markdown')


async def cmd_raison2(event):
    """
    /raison2        — Top 10 des meilleures combinaisons (miroir × wx × B)
    /raison2 pdf    — PDF complet de la simulation (216 combinaisons + tableaux détaillés)
    /raison2 tout   — Toutes les 216 combinaisons triées par score
    /raison2 P1     — Détail complet de la combinaison miroir P1 (toutes ses wx/B)
    /raison2 P2     — Idem pour P2
    /raison2 P3     — Idem pour P3
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    # ── Données depuis last_strategy_simulation (optionnel — pour rétrocompat) ──
    sim        = last_strategy_simulation or {}
    ts         = sim['timestamp'].strftime('%d/%m/%Y %H:%M:%S') if sim.get('timestamp') else datetime.now().strftime('%d/%m/%Y %H:%M:%S')
    combos     = sim.get('combos', GLOBAL_COMBOS)
    sim_matrix = sim.get('sim_matrix', {})
    pred_lists = sim.get('pred_lists', {})
    total_c13  = sim.get('total_c13', 0)
    total_an   = sim.get('total_analysed', 0)
    rec_num    = sim.get('recommended_num')
    rec_reason = sim.get('recommended_reason', '')
    cur_mirror = dict(COMPTEUR13_MIRROR)

    # ── Toujours lire best_key / best_val depuis silent_combo_states ──────────
    _valid = {k: v for k, v in silent_combo_states.items() if v.get('total', 0) >= 1}
    if _valid:
        best_key, _bv = max(_valid.items(), key=lambda x: (x[1]['wins'] - x[1]['losses'], x[1]['wins']))
        best_val = {**_bv, 'score': _bv['wins'] - _bv['losses']}
    else:
        best_key = sim.get('best_combo_key')
        best_val = sim.get('best_combo_val')

    verdict = sim.get('verdict', '')
    vd      = sim.get('vd', '')

    _R_EMOJI = {0: '0️⃣', 1: '1️⃣', 2: '2️⃣', 3: '3️⃣', 4: '4️⃣'}

    _COMBO_NAMES = {c['num']: c['name'] for c in combos}
    _COMBO_DISP  = {c['num']: c.get('disp', '?') for c in combos}
    _COMBO_MIR   = {c['num']: c['mirror'] for c in combos}

    parts = event.message.message.strip().split()
    sub   = parts[1].upper() if len(parts) > 1 else ''

    # ── En-tête commun ───────────────────────────────────────────────────────
    _tracker_total_preds = sum(s.get('total', 0) for s in silent_combo_states.values())
    _tracker_active = sum(1 for s in silent_combo_states.values() if s.get('total', 0) > 0)
    lines = [
        "╔══════════════════════════════╗",
        "║  🔬 RAISON2 — TRACKERS LIVE   ║",
        "╚══════════════════════════════╝",
        f"🕒 {ts}  |  216 trackers indépendants (C13+C2 propre à chaque combo)",
        f"📊 {_tracker_total_preds} prédictions cumulées · {_tracker_active}/216 combos actifs",
    ]
    if verdict:
        lines.append(f"**{verdict}** — _{vd}_")
    lines.append("")

    if best_key and len(best_key) == 4:
        bm, bwx, bb, bdf = best_key
        lines.append(
            "🏆 **MEILLEURE CONFIGURATION GLOBALE :**"
        )
        lines.append(
            f"   {_COMBO_NAMES.get(bm,'?')} | wx={bwx} | B={bb} | df+{bdf}"
        )
        lines.append(
            f"   Paires : {_COMBO_DISP.get(bm,'?')}"
        )
        if best_val:
            lines.append(
                f"   ✅{best_val['wins']} gagnés | ❌{best_val['losses']} perdus | "
                f"Score: {best_val['score']:+d} sur {best_val['total']} prédictions"
            )
        lines.append("")
        lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        lines.append("")

    # ── Mode PDF ─────────────────────────────────────────────────────────────
    if sub == 'PDF':
        tracker_total = sum(v.get('total', 0) for v in silent_combo_states.values())
        if tracker_total == 0:
            await event.respond("⏳ Aucune prédiction encore — trackers en accumulation, réessaie dans quelques minutes.")
            return
        await event.respond("⏳ Génération du PDF en cours…")
        try:
            # Construire la sim_matrix depuis les trackers live
            tracker_sim_matrix = {}
            for (cnum, wx, b, df_s), state in silent_combo_states.items():
                if state.get('total', 0) >= 1:
                    tracker_sim_matrix[(cnum, wx, b, df_s)] = {
                        'wins':   state['wins'],
                        'losses': state['losses'],
                        'total':  state['total'],
                        'score':  state['wins'] - state['losses'],
                    }
            # Best key depuis trackers
            _valid_pdf = {k: v for k, v in tracker_sim_matrix.items() if v['total'] >= 1}
            pdf_best_key, pdf_best_val = (None, None)
            if _valid_pdf:
                pdf_best_key, pdf_best_val = max(_valid_pdf.items(), key=lambda x: (x[1]['score'], x[1]['wins']))
            tracker_sim = {
                'timestamp':         datetime.now(),
                'combos':            GLOBAL_COMBOS,
                'sim_matrix':        tracker_sim_matrix,
                'pred_lists':        {},
                'total_c13':         tracker_total,
                'total_analysed':    tracker_total,
                'verdict':           '🔬 TRACKERS LIVE — 216 combinaisons',
                'vd':                '',
                'recommended_num':   pdf_best_key[0] if pdf_best_key else None,
                'recommended_reason': '',
                'best_combo_key':    pdf_best_key,
                'best_combo_val':    pdf_best_val,
            }
            pdf_bytes = generate_raison2_pdf(tracker_sim)
            buf = io.BytesIO(pdf_bytes)
            buf.name = f"trackers_c13_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"
            await event.respond(
                file=buf,
                message=(
                    f"📄 **Rapport Trackers C13 Live — {datetime.now().strftime('%d/%m/%Y %H:%M')}**\n"
                    f"216 combinaisons (miroir × wx × B × df+1/df+2) — {tracker_total} prédictions cumulées"
                )
            )
        except Exception as e:
            await event.respond(f"❌ Erreur génération PDF : {e}")
        return

    # ── Mode détail par combinaison miroir (P1 / P2 / P3) ──────────────────
    if sub in ('P1', 'P2', 'P3'):
        pnum = {'P1': 1, 'P2': 2, 'P3': 3}[sub]
        cname = _COMBO_NAMES.get(pnum, sub)
        cdisp = _COMBO_DISP.get(pnum, '?')
        c_active = (_COMBO_MIR.get(pnum) == cur_mirror)
        act_tag  = " ◀ ACTIF" if c_active else ""
        lines.append(f"**📋 DÉTAIL — {cname}{act_tag}**")
        lines.append(f"Paires : {cdisp}")
        lines.append("")

        # ── Tableau matriciel depuis silent_combo_states (trackers live) ────
        for df_mat, df_mat_label in ((1, "trigger+1"), (2, "trigger+2")):
            lines.append(f"📐 **df={df_mat}** _({df_mat_label})_")
            lines.append(f"{'wx\\B':>5}  " + "  ".join(f"B={b}" for b in range(3, 9)))
            lines.append("─" * 50)
            for wx in range(3, 9):
                row_parts = []
                for b in range(3, 9):
                    st = silent_combo_states.get((pnum, wx, b, df_mat), {})
                    tot = st.get('total', 0)
                    if tot >= 1:
                        sc = st['wins'] - st['losses']
                        row_parts.append(f"{sc:+3d}({tot})")
                    else:
                        row_parts.append("  --  ")
                lines.append(f"wx={wx}:  " + "  ".join(row_parts))
            lines.append("")
        lines.append("_Format : Score(nb prédictions)  |  Score = victoires − défaites_")
        lines.append("")

        # ── Prédictions individuelles par (wx, B) — lecture directe des trackers ─
        # Miroir du combo affiché
        c_obj    = GLOBAL_COMBOS_BY_NUM.get(pnum, {})
        c_mirror = c_obj.get('mirror', {})
        mir_disp = c_obj.get('disp', '?')
        mir_pairs = "  ".join(
            f"{SUIT_EMOJI.get(k,'?')}↔{SUIT_EMOJI.get(v,'?')}"
            for k, v in c_mirror.items() if k < v or k not in (x for x in c_mirror if c_mirror[x] == k)
        )

        for df_sim_show, df_label in ((1, "trigger+1"), (2, "trigger+2")):
            lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
            lines.append(
                f"**🔍 PRÉDICTIONS INDIVIDUELLES · {cname} · {df_label}**"
            )
            lines.append(f"_Miroir : {mir_disp}_")
            lines.append("")

            # Collecter tous les (wx, B) qui ont des prédictions pour ce df_sim
            active_combos = []
            for wx in range(3, 9):
                for b in range(3, 9):
                    key   = (pnum, wx, b, df_sim_show)
                    state = silent_combo_states.get(key, {})
                    hist  = state.get('pred_history', [])
                    if hist:
                        w = state.get('wins', 0)
                        l = state.get('losses', 0)
                        active_combos.append((wx, b, w, l, hist))

            if not active_combos:
                lines.append("_Aucune prédiction encore — trackers en accumulation…_")
                lines.append("")
                continue

            # Trier par score décroissant, afficher les 12 meilleurs
            active_combos.sort(key=lambda x: (x[2] - x[3]), reverse=True)
            shown = 0
            for wx, b, wins_c, losses_c, hist in active_combos:
                if shown >= 12:
                    rest = len(active_combos) - shown
                    lines.append(f"_… +{rest} combo(s) non affichés — voir la matrice ci-dessus_")
                    break
                score_c = wins_c - losses_c
                lines.append(
                    f"**wx={wx} | B={b}** — {wins_c + losses_c} pred · "
                    f"✅{wins_c} / ❌{losses_c} · Score: {score_c:+d}"
                )
                # Afficher les 5 dernières prédictions de ce tracker
                for h in hist[-5:]:
                    suit_em  = SUIT_EMOJI.get(h.get('suit', '?'), h.get('suit', '?'))
                    res_icon = "✅" if h.get('win') else "❌"
                    trigger  = h.get('trigger', '?')
                    gn       = h.get('gn', '?')
                    lines.append(
                        f"  #{gn} {suit_em} {res_icon}  _(trigger #{trigger})_"
                    )
                if len(hist) > 5:
                    lines.append(f"  _… +{len(hist)-5} prédictions antérieures_")
                lines.append("")
                shown += 1

        await event.respond("\n".join(lines), parse_mode='markdown')
        return

    # ── Mode TOUT : 3 messages (un par miroir), toutes les 216 combinaisons ──
    if sub == 'TOUT':
        # En-tête global déjà dans lines
        lines.append("📤 **TOUTES LES 216 COMBINAISONS** — envoi en 3 messages (P1 / P2 / P3)")
        lines.append("_Chaque message = 1 miroir × 6 wx × 6 B × 2 df = 72 combos_")
        lines.append("")
        if rec_num:
            lines.append(f"🏆 **Meilleur global :** {_COMBO_NAMES.get(rec_num,'?')} — {rec_reason}")
            lines.append("")
        lines.append("_Messages envoyés ci-dessous…_")
        await event.respond("\n".join(lines), parse_mode='markdown')

        # ── Un message par miroir ──────────────────────────────────────────
        for c in GLOBAL_COMBOS:
            pnum_t   = c['num']
            cname_t  = c['name']
            cdisp_t  = c.get('disp', '?')
            c_act    = (c['mirror'] == cur_mirror)
            act_tag  = " ◀ ACTIF" if c_act else ""
            is_reco  = (pnum_t == rec_num)
            reco_tag = " ⭐ RECOMMANDÉ" if is_reco else ""

            msg_lines = [
                "╔══════════════════════════════╗",
                f"║  🔬 {cname_t}{act_tag}{reco_tag}",
                "╚══════════════════════════════╝",
                f"Miroir : {cdisp_t}",
                "─────────── trigger+1 ───────────",
            ]

            for wx in range(3, 9):
                for b in range(3, 9):
                    key_t  = (pnum_t, wx, b, 1)
                    st_t   = silent_combo_states.get(key_t, {})
                    w_t    = st_t.get('wins',   0)
                    l_t    = st_t.get('losses', 0)
                    tot_t  = st_t.get('total',  0)
                    hist_t = st_t.get('pred_history', [])
                    is_best_t = (key_t == best_key)
                    best_m  = "🏆" if is_best_t else ""
                    is_act  = (c_act and wx == COMPTEUR13_THRESHOLD and b == compteur2_seuil_B)
                    act_m   = "◀" if is_act else ""
                    if tot_t == 0:
                        msg_lines.append(f"wx={wx} B={b} {best_m}{act_m}: — (0 pred)")
                    else:
                        sc_t = w_t - l_t
                        preds_disp = []
                        for h in hist_t[-3:]:
                            se = SUIT_EMOJI.get(h.get('suit','?'), h.get('suit','?'))
                            re = "✅" if h.get('win') else "❌"
                            preds_disp.append(f"#{h.get('gn','?')}{se}{re}")
                        msg_lines.append(
                            f"wx={wx} B={b} {best_m}{act_m}: ✅{w_t}/❌{l_t} {sc_t:+d} → "
                            + " ".join(preds_disp)
                        )

            msg_lines.append("─────────── trigger+2 ───────────")

            for wx in range(3, 9):
                for b in range(3, 9):
                    key_t  = (pnum_t, wx, b, 2)
                    st_t   = silent_combo_states.get(key_t, {})
                    w_t    = st_t.get('wins',   0)
                    l_t    = st_t.get('losses', 0)
                    tot_t  = st_t.get('total',  0)
                    hist_t = st_t.get('pred_history', [])
                    is_best_t = (key_t == best_key)
                    best_m  = "🏆" if is_best_t else ""
                    is_act  = (c_act and wx == COMPTEUR13_THRESHOLD and b == compteur2_seuil_B)
                    act_m   = "◀" if is_act else ""
                    if tot_t == 0:
                        msg_lines.append(f"wx={wx} B={b} {best_m}{act_m}: — (0 pred)")
                    else:
                        sc_t = w_t - l_t
                        preds_disp = []
                        for h in hist_t[-3:]:
                            se = SUIT_EMOJI.get(h.get('suit','?'), h.get('suit','?'))
                            re = "✅" if h.get('win') else "❌"
                            preds_disp.append(f"#{h.get('gn','?')}{se}{re}")
                        msg_lines.append(
                            f"wx={wx} B={b} {best_m}{act_m}: ✅{w_t}/❌{l_t} {sc_t:+d} → "
                            + " ".join(preds_disp)
                        )

            # Découper en chunks de 4000 chars si nécessaire (limite Telegram)
            full_text = "\n".join(msg_lines)
            chunk_size = 3800
            for i in range(0, len(full_text), chunk_size):
                await event.respond(full_text[i:i + chunk_size], parse_mode='markdown')

        return

    # ── Mode par défaut : Top 10 depuis silent_combo_states (trackers live) ───
    tracker_entries = [
        (k, {**v, 'score': v['wins'] - v['losses']})
        for k, v in silent_combo_states.items()
        if v.get('total', 0) >= 1
    ]
    sorted_entries = sorted(tracker_entries, key=lambda x: (x[1]['score'], x[1]['wins']), reverse=True)

    _tracker_total_preds2 = sum(v.get('total', 0) for v in silent_combo_states.values())
    _tracker_active2      = sum(1 for v in silent_combo_states.values() if v.get('total', 0) > 0)

    lines.append(f"🏅 **TOP 10 — TRACKERS SILENCIEUX** _(sur {_tracker_active2}/216 combos actifs · {_tracker_total_preds2} prédictions cumulées)_")
    lines.append("_Tape `/raison2 tout` pour les 216 | `/raison2 P1` `/raison2 P2` `/raison2 P3` pour le détail_")
    lines.append("")

    if not sorted_entries:
        lines.append("⏳ _Aucune prédiction encore — trackers en accumulation (quelques minutes)…_")
    else:
        for rank, (key, val) in enumerate(sorted_entries[:10], 1):
            combo_n, wx, b, df_s = key
            cname2   = next((c['name'] for c in GLOBAL_COMBOS if c['num'] == combo_n), f"P{combo_n}")
            cdisp2   = next((c['disp'] for c in GLOBAL_COMBOS if c['num'] == combo_n), '?')
            c_mirror = next((c['mirror'] for c in GLOBAL_COMBOS if c['num'] == combo_n), {})
            c_active = (c_mirror == cur_mirror and wx == COMPTEUR13_THRESHOLD and b == compteur2_seuil_B)
            act_tag  = " ◀ ACTIF" if c_active else ""
            is_best  = (key == best_key)
            best_tag = " 🏆" if is_best else ""
            hist_r   = val.get('pred_history', [])
            preds_r  = []
            for h in hist_r[-3:]:
                se = SUIT_EMOJI.get(h.get('suit','?'), h.get('suit','?'))
                re = "✅" if h.get('win') else "❌"
                preds_r.append(f"#{h.get('gn','?')}{se}{re}")
            preds_str = "  ".join(preds_r) if preds_r else "_aucune_"
            lines.append(f"**#{rank}{best_tag}{act_tag}** {cname2} | wx={wx} B={b} trigger+{df_s}")
            lines.append(f"   {cdisp2}")
            lines.append(f"   ✅{val['wins']} / ❌{val['losses']} | Score: **{val['score']:+d}** | {val['total']} pred")
            lines.append(f"   Dernières : {preds_str}")
            lines.append("")

        if len(sorted_entries) > 10:
            lines.append(f"_… et {len(sorted_entries) - 10} autres. `/raison2 tout` pour tout voir._")

    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    if best_key and best_val:
        bm, bwx, bb, bdf = best_key
        bname = next((c['name'] for c in GLOBAL_COMBOS if c['num'] == bm), f"P{bm}")
        lines.append(f"🤖 **Auto-sélection horaire :** {bname} | wx={bwx} B={bb} trigger+{bdf} | Score: **{best_val.get('score', best_val['wins']-best_val['losses']):+d}**")
    lines.append("")
    lines.append("_Détail : `/raison2 P1` `/raison2 P2` `/raison2 P3` `/raison2 tout`_")

    await event.respond("\n".join(lines), parse_mode='markdown')


async def cmd_perdus(event):
    """Envoie le PDF des pertes avec analyse horaire à l'admin."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    if not perdu_events:
        await event.respond("📊 Aucune perte enregistrée pour le moment.")
        return
    await event.respond("📉 Génération du rapport de pertes...")
    await send_perdu_pdf()


async def cmd_bilan(event):
    """Gère le bilan automatique : /bilan [now/on/0]."""
    global bilan_interval_hours
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    parts = event.message.message.strip().split()
    if len(parts) == 1:
        now = datetime.now()
        interval = 4
        hours_since_last  = now.hour % interval
        hours_until_next  = interval - hours_since_last
        minutes_left = hours_until_next * 60 - now.minute
        next_h = (now.hour + hours_until_next) % 24
        status = (
            f"✅ Actif — prochain envoi dans **{minutes_left} min** (à {next_h:02d}:00)"
            if bilan_interval_hours > 0 else "🔕 Désactivé"
        )
        await event.respond(
            "📊 **BILAN AUTOMATIQUE**\n\n"
            f"Statut: **{status}**\n"
            "Fréquence: **toutes les 4h pile** (00h, 04h, 08h, 12h, 16h, 20h)\n\n"
            "**Usage:**\n"
            "`/bilan now` — Envoyer le bilan immédiatement dans votre chat privé\n"
            "`/bilan 0` — Désactiver l'envoi automatique\n"
            "`/bilan on` — Réactiver l'envoi automatique\n\n"
            + get_bilan_text(),
            parse_mode='markdown'
        )
        return
    arg = parts[1].strip()
    if arg == 'now':
        txt = get_bilan_text()
        if ADMIN_ID and ADMIN_ID != 0:
            try:
                admin_entity = await client.get_entity(ADMIN_ID)
                await client.send_message(admin_entity, txt, parse_mode='markdown')
            except Exception as e:
                logger.error(f"❌ Bilan now admin: {e}")
        await event.respond("✅ Bilan envoyé dans votre chat privé.")
        return
    if arg == 'on':
        bilan_interval_hours = 4
        now = datetime.now()
        hours_since_last = now.hour % 4
        hours_until_next = 4 - hours_since_last
        next_h = (now.hour + hours_until_next) % 24
        await event.respond(f"✅ Bilan automatique réactivé — prochain envoi à **{next_h:02d}h00**.")
        return
    if arg == '0':
        bilan_interval_hours = 0
        await event.respond("🔕 Bilan automatique désactivé.")
        return
    await event.respond(
        "❌ Commande inconnue.\n"
        "`/bilan now` — Envoyer maintenant\n"
        "`/bilan on` — Activer\n"
        "`/bilan 0` — Désactiver"
    )


# ============================================================================
# COMMANDE /historique_strategies — HISTORIQUE DES PROPOSITIONS HORAIRES
# ============================================================================

async def cmd_historique_strategies(event):
    """/historique_strategies — affiche les N dernières propositions horaires depuis la DB."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()
    limit = 10
    if len(parts) >= 2 and parts[1].isdigit():
        limit = max(1, min(50, int(parts[1])))

    try:
        history = await db.db_load_kv('strategy_history') or []
    except Exception as e:
        await event.respond(f"❌ Erreur lecture DB : {e}")
        return

    if not history:
        await event.respond(
            "📭 **Aucune proposition horaire en DB.**\n"
            "_Les propositions sont stockées automatiquement chaque heure._"
        )
        return

    entries = history[-limit:]
    entries.reverse()

    dec_icons = {'confirmée': '✅', 'ignorée': '❌', 'en_attente': '⏳'}
    lines = [
        "╔══════════════════════════════════╗",
        f"║  📋 HISTORIQUE STRATÉGIES — {limit} dernières  ║",
        "╚══════════════════════════════════╝",
        "",
    ]
    for i, e in enumerate(entries, 1):
        dec     = e.get('decision', '?')
        icon    = dec_icons.get(dec, '❓')
        p       = e.get('params', {})
        ts      = e.get('timestamp', '')[:16].replace('T', ' ')
        lines.append(
            f"**{i}. {ts} ({e.get('heure', '?')})** {icon} {dec}\n"
            f"   {p.get('nom', '?')} | wx={p.get('wx','?')} | B={p.get('b','?')} | df+{p.get('df_sim','?')}\n"
            f"   Score **{p.get('score', 0):+d}** (✅{p.get('wins',0)} ❌{p.get('losses',0)} / {p.get('total',0)} pred.)"
        )
        if i < len(entries):
            lines.append("─" * 32)

    lines += ["", f"_Total stocké en DB : {len(history)} propositions._"]

    await event.respond("\n".join(lines), parse_mode='markdown')


# ============================================================================
# COMMANDE /formation — BACKTEST FORMATION DE MISE APRÈS PERTE
# ============================================================================

def _compute_formation_stats(resolved: list) -> dict:
    """
    Calcule les statistiques de formation sur les prédictions résolues.
    Pour chaque perte au jeu G (numéro prédit), teste si le 1er, 2ème ou 3ème
    costume apparu au jeu G se retrouve au jeu G+1.
    Retourne un dict avec f1/f2/f3 : (ok, total, rate) et best ("f1","f2","f3",None).
    """
    perdues = [p for p in resolved if p.get('status') == 'perdu']

    f1_ok = f1_total = 0
    f2_ok = f2_total = 0
    f3_ok = f3_total = 0

    for pred in perdues:
        G = pred['predicted_game']
        cache_G  = game_result_cache.get(G, {})
        cache_G1 = game_result_cache.get(G + 1, {})
        cards_G  = cache_G.get('player_cards', [])
        suits_G1 = cache_G1.get('player_suits', set())

        if not cards_G or not suits_G1:
            continue

        cards_appeared = [
            normalize_suit(c.get('S', '')) for c in cards_G
            if normalize_suit(c.get('S', '')) in ALL_SUITS
        ]

        f1s = cards_appeared[0] if len(cards_appeared) > 0 else None
        f2s = cards_appeared[1] if len(cards_appeared) > 1 else None
        f3s = cards_appeared[2] if len(cards_appeared) > 2 else None

        if f1s:
            f1_total += 1
            if f1s in suits_G1:
                f1_ok += 1
        if f2s:
            f2_total += 1
            if f2s in suits_G1:
                f2_ok += 1
        if f3s:
            f3_total += 1
            if f3s in suits_G1:
                f3_ok += 1

    f1_rate = round(f1_ok / f1_total * 100) if f1_total > 0 else 0
    f2_rate = round(f2_ok / f2_total * 100) if f2_total > 0 else 0
    f3_rate = round(f3_ok / f3_total * 100) if f3_total > 0 else 0

    rates = [(f1_rate, f1_total, 'f1'), (f2_rate, f2_total, 'f2'), (f3_rate, f3_total, 'f3')]
    eligible = [(r, t, k) for r, t, k in rates if t > 0]
    best = max(eligible, key=lambda x: x[0])[2] if eligible else None

    return {
        'f1': (f1_ok, f1_total, f1_rate),
        'f2': (f2_ok, f2_total, f2_rate),
        'f3': (f3_ok, f3_total, f3_rate),
        'best': best,
        'perdues': len(perdues),
    }


async def _trigger_formation_follow_up(original_game: int, original_suit: str, check_game: int, pred_snap: dict):
    """
    Appelée dès que le jeu prédit (original_game) se termine sans le costume attendu.
    1. Lit les 3 cartes joueur du jeu check_game (= jeu prédit).
    2. Détermine historiquement quel costume (1er/2ème/3ème) apparaît le plus souvent au jeu suivant.
    3. Recommande ce costume pour check_game+1 et l'injecte dans le message de prédiction.
    4. Enregistre formation_follow_ups[check_game+1] pour vérification (R0 → R1 → R2).
    """
    global formation_follow_ups

    # ── Cartes apparues au jeu check_game (jeu prédit, R0 raté) ─────────────
    cache = game_result_cache.get(check_game, {})
    raw_cards = cache.get('player_cards', [])
    cards_appeared = [
        normalize_suit(c.get('S', '')) for c in raw_cards
        if normalize_suit(c.get('S', '')) in ALL_SUITS
    ]
    if not cards_appeared:
        logger.warning(f"⚠️ Formation #{original_game}: aucune carte trouvée au jeu #{check_game} dans le cache — formation annulée")
        return

    # ── Meilleure formation sur l'historique résolu ──────────────────────────
    resolved = [
        p for p in prediction_history
        if p.get('status', 'en_cours') != 'en_cours'
    ][:50]

    rank_labels = {'f1': '1er', 'f2': '2ème', 'f3': '3ème'}
    if len(resolved) >= 1:
        stats = _compute_formation_stats(resolved)
        best  = stats['best'] or 'f1'
    else:
        best  = 'f1'

    # Labels position carte : f1=1ère, f2=2ème, f3=3ème
    pos_label_map = {'f1': '1ère', 'f2': '2ème', 'f3': '3ème'}
    rank_label    = rank_labels.get(best, best)
    card_pos      = pos_label_map.get(best, '1ère')

    # ── Costume recommandé (idx dans les cartes du jeu prédit) ───────────────
    idx_map = {'f1': 0, 'f2': 1, 'f3': 2}
    idx     = idx_map.get(best, 0)
    if idx >= len(cards_appeared):
        idx = 0
    recommended_suit = cards_appeared[idx]
    rec_disp = SUIT_DISPLAY.get(recommended_suit, recommended_suit)

    # ── Injecter le suffixe dans la prédiction en cours ──────────────────────
    next_game = check_game + 1
    formation_suffix = (
        f"\n\n♟️ **Formation** : **{rec_disp}** ({card_pos} carte du #**{check_game}**) → jeu **#{next_game}**\n"
        "⏳ _Analyse..._"
    )
    active_pred = pending_predictions.get(original_game)
    if active_pred:
        active_pred['formation_suffix'] = formation_suffix
        logger.info(f"✅ Formation injectée → prédiction #{original_game} | {rec_disp} ({card_pos} carte) → #{next_game}")
    else:
        logger.warning(f"⚠️ Formation #{original_game}: prédiction absente — suffixe non injecté")

    # ── Enregistrer le follow-up pour le jeu #N+1 (1 seul check, pas de rattrapage) ─
    formation_follow_ups[next_game] = {
        'recommended_suit':   recommended_suit,
        'original_game':      original_game,
        'original_suit':      original_suit,
        'card_position':      card_pos,           # '1ère', '2ème' ou '3ème'
        'cards_at_predicted': cards_appeared,     # liste ordonnée des costumes du jeu prédit
        'check_game_orig':    check_game,
    }
    logger.info(f"📊 Formation #{original_game} → {rec_disp} [{card_pos} carte de #{check_game}] vérif au #{next_game}")

    # ── Mémoriser le dernier exemple pour le message canal horaire ────────────
    global _last_formation_example
    _last_formation_example = {
        'original_game':    original_game,
        'original_suit':    original_suit,
        'card_position':    card_pos,
        'recommended_suit': recommended_suit,
        'next_game':        next_game,
    }


async def cmd_formation(event):
    """
    /formation [N]
    Teste la formation de mise sur les N dernières prédictions résolues.
    Formation : quand le bot perd au jeu G (numéro prédit), les costumes apparus
    à ce jeu sont testés au jeu G+1. Compare les 1er, 2ème et 3ème costumes.
    Conseille l'administrateur sur la meilleure formation à suivre.
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()
    n_pred = 30
    if len(parts) >= 2 and parts[1].isdigit():
        n_pred = max(5, min(100, int(parts[1])))

    # ── Récupérer les prédictions résolues (pas en_cours) ──
    resolved = [
        p for p in prediction_history
        if p.get('status', 'en_cours') != 'en_cours'
    ][:n_pred]

    if not resolved:
        await event.respond(
            "📭 **Aucune prédiction résolue en mémoire.**\n"
            "_L'historique se remplit au fil des prédictions._"
        )
        return

    wins_total   = sum(1 for p in resolved if 'gagne' in p.get('status', ''))
    losses_total = sum(1 for p in resolved if p.get('status') == 'perdu')

    perdues = [p for p in resolved if p.get('status') == 'perdu']
    stats   = _compute_formation_stats(resolved)
    f1_ok, f1_total, f1_rate = stats['f1']
    f2_ok, f2_total, f2_rate = stats['f2']
    f3_ok, f3_total, f3_rate = stats['f3']
    best = stats['best']

    # ── Détail des 15 dernières pertes ──
    detail_lines = []
    for pred in perdues[:15]:
        G         = pred['predicted_game']
        suit_pred = pred['suit']
        suit_disp = SUIT_DISPLAY.get(suit_pred, suit_pred)

        cache_G  = game_result_cache.get(G, {})
        cache_G1 = game_result_cache.get(G + 1, {})
        cards_G  = cache_G.get('player_cards', [])
        suits_G1 = cache_G1.get('player_suits', set())

        if not cards_G or not suits_G1:
            detail_lines.append(
                f"  ❌ Jeu #{G} : prédit {suit_disp} → PERDU | _cache manquant_"
            )
            continue

        cards_appeared = [
            normalize_suit(c.get('S', '')) for c in cards_G
            if normalize_suit(c.get('S', '')) in ALL_SUITS
        ]

        f1s = cards_appeared[0] if len(cards_appeared) > 0 else None
        f2s = cards_appeared[1] if len(cards_appeared) > 1 else None
        f3s = cards_appeared[2] if len(cards_appeared) > 2 else None

        f1d = SUIT_DISPLAY.get(f1s, '—') if f1s else '—'
        f2d = SUIT_DISPLAY.get(f2s, '—') if f2s else '—'
        f3d = SUIT_DISPLAY.get(f3s, '—') if f3s else '—'
        f1i = ('✅' if f1s in suits_G1 else '❌') if f1s else '—'
        f2i = ('✅' if f2s in suits_G1 else '❌') if f2s else '—'
        f3i = ('✅' if f3s in suits_G1 else '❌') if f3s else '—'

        detail_lines.append(
            f"  📍 **Jeu #{G}** prédit : {suit_disp} → ❌ PERDU\n"
            f"       Costumes apparus au jeu #{G} :\n"
            f"         1er costume : {f1d} → jeu #{G+1} : {f1i}\n"
            f"         2ème costume : {f2d} → jeu #{G+1} : {f2i}\n"
            f"         3ème costume : {f3d} → jeu #{G+1} : {f3i}"
        )

    # ── Recommandation ──
    rank_labels = {'f1': '1er costume du numéro prédit',
                   'f2': '2ème costume du numéro prédit',
                   'f3': '3ème costume du numéro prédit'}
    if best:
        ok_b, tot_b, rate_b = stats[best]
        label_b = rank_labels[best]
        rec_lines = [
            f"✅ Mise sur le **{label_b}**",
            f"   Taux de réussite : **{rate_b}%** ({ok_b}/{tot_b} pertes testées)",
        ]
        best_icon = "🥇"
    else:
        rec_lines = ["Données insuffisantes pour recommander une formation."]
        best_icon = "⚠️"

    # ── Construire le message final ──
    lines = [
        "╔═══════════════════════════════════╗",
        "║   📊 FORMATION DE MISE — BACKTEST  ║",
        "╚═══════════════════════════════════╝",
        "",
        f"Analyse : **{len(resolved)}** prédictions résolues",
        f"  ✅ Gagnées : **{wins_total}**  |  ❌ Perdues : **{losses_total}**",
        "",
        "─── Détail des 15 dernières pertes ───",
    ] + detail_lines + [
        "",
        "─── Résultats globaux de la formation ───",
        (f"  1er costume du jeu prédit → jeu suivant : **{f1_ok}/{f1_total}** ✅ ({f1_rate}%)"
         if f1_total > 0 else "  1er costume : données insuffisantes"),
        (f"  2ème costume du jeu prédit → jeu suivant : **{f2_ok}/{f2_total}** ✅ ({f2_rate}%)"
         if f2_total > 0 else "  2ème costume : données insuffisantes"),
        (f"  3ème costume du jeu prédit → jeu suivant : **{f3_ok}/{f3_total}** ✅ ({f3_rate}%)"
         if f3_total > 0 else "  3ème costume : données insuffisantes"),
        "",
        f"─── {best_icon} Recommandation ───",
    ] + rec_lines + [
        "",
        "💡 **Comment jouer après un PERDU au jeu N :**",
        "  1️⃣  Regarde les costumes qui sont apparus au jeu N (le numéro prédit)",
        "  2️⃣  Prends le costume recommandé dans la liste ci-dessus",
        "  3️⃣  Mise sur ce costume au jeu N+1",
        "  4️⃣  Si ce costume apparaît dans les cartes du jeu N+1 → ✅ Gagné",
        "",
        f"_Analyse basée sur {len(perdues)} pertes · données live du cache._",
    ]

    await event.respond(
        "\n".join(lines),
        parse_mode='markdown',
        buttons=[[Button.inline("📊 Rapport détaillé (admin)", b"send_formation_canal")]],
    )


async def cmd_sendformation(event):
    """
    /sendformation — Envoie le résumé de la formation dans le canal de prédiction.
    Réservé à l'admin. Identique au bouton '📢 Envoyer au canal' de /formation.
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    await _send_formation_to_canal()
    await event.respond("✅ Rapport de formation détaillé envoyé en privé.\n_Le canal reçoit le conseil simplifié à chaque heure pile._")


async def _send_formation_to_canal():
    """Construit et envoie le message de formation dans le canal de prédiction."""
    if not PREDICTION_CHANNEL_ID:
        return

    resolved = [
        p for p in prediction_history
        if p.get('status', 'en_cours') != 'en_cours'
    ][:50]

    if len(resolved) < 1:
        if ADMIN_ID:
            try:
                await client.send_message(
                    ADMIN_ID,
                    "⚠️ Aucune prédiction résolue disponible pour générer un rapport de formation.",
                    parse_mode='markdown',
                )
            except Exception:
                pass
        return

    stats   = _compute_formation_stats(resolved)
    f1_ok, f1_total, f1_rate = stats['f1']
    f2_ok, f2_total, f2_rate = stats['f2']
    f3_ok, f3_total, f3_rate = stats['f3']
    best    = stats['best']
    perdues = stats['perdues']

    wins_total   = sum(1 for p in resolved if 'gagne' in p.get('status', ''))
    losses_total = sum(1 for p in resolved if p.get('status') == 'perdu')

    rank_labels = {
        'f1': '1er costume du numéro prédit',
        'f2': '2ème costume du numéro prédit',
        'f3': '3ème costume du numéro prédit',
    }
    if best:
        ok_b, tot_b, rate_b = stats[best]
        label_b  = rank_labels[best]
        rec_lines = [
            f"✅ Mise sur le **{label_b}**",
            f"   Taux de réussite : **{rate_b}%** ({ok_b}/{tot_b} pertes testées)",
        ]
        best_icon = "🥇"
    else:
        rec_lines = ["⚠️ Données insuffisantes pour recommander une formation."]
        best_icon = "⚠️"

    lines = [
        "╔══════════════════════════════════════╗",
        "║     📊 FORMATION DE MISE — RÉSUMÉ     ║",
        "╚══════════════════════════════════════╝",
        "",
        f"Analyse : **{len(resolved)}** prédictions résolues",
        f"  ✅ Gagnées : **{wins_total}**  |  ❌ Perdues : **{losses_total}**",
        "",
        "─── Taux de réussite par costume ───",
    ]
    if f1_total > 0:
        star = ' ⭐' if best == 'f1' else ''
        lines.append(f"  🥇 **1er costume du jeu prédit**{star}")
        lines.append(f"       → **{f1_rate}%** ({f1_ok}/{f1_total})")
    else:
        lines.append("  🥇 1er costume : données insuffisantes")

    if f2_total > 0:
        star = ' ⭐' if best == 'f2' else ''
        lines.append(f"  🥈 **2ème costume du jeu prédit**{star}")
        lines.append(f"       → **{f2_rate}%** ({f2_ok}/{f2_total})")
    else:
        lines.append("  🥈 2ème costume : données insuffisantes")

    if f3_total > 0:
        star = ' ⭐' if best == 'f3' else ''
        lines.append(f"  🥉 **3ème costume du jeu prédit**{star}")
        lines.append(f"       → **{f3_rate}%** ({f3_ok}/{f3_total})")
    else:
        lines.append("  🥉 3ème costume : données insuffisantes")

    lines += [
        "",
        f"─── {best_icon} Recommandation ───",
    ] + rec_lines + [
        "",
        "💡 **Comment jouer après un PERDU au jeu N :**",
        "  1️⃣  Regarde les costumes apparus au jeu N (le numéro prédit)",
        "  2️⃣  Prends le costume recommandé ci-dessus",
        "  3️⃣  Mise sur ce costume au jeu N+1",
        "  4️⃣  Si ce costume apparaît au jeu N+1 → ✅ Gagné",
        "",
        f"_Analyse basée sur {perdues} pertes · {len(resolved)} prédictions résolues._",
    ]

    try:
        if ADMIN_ID:
            await client.send_message(ADMIN_ID, "\n".join(lines), parse_mode='markdown')
            logger.info("📊 Rapport de formation détaillé envoyé à l'admin")
    except Exception as e:
        logger.error(f"❌ _send_formation_to_canal (admin): {e}")


async def _send_formation_simple_to_canal(heure: str = ''):
    """
    Envoie chaque heure un message simple de formation dans le canal de prédiction.
    Message court : quelle carte jouer après un PERDU, avec exemple concret.
    Détails statistiques réservés à l'admin via _send_formation_to_canal().
    """
    if not PREDICTION_CHANNEL_ID:
        return

    resolved = [
        p for p in prediction_history
        if p.get('status', 'en_cours') != 'en_cours'
    ][:50]
    perdu_list = [p for p in resolved if p.get('status') == 'perdu']

    if len(perdu_list) < 3:
        logger.info("📊 Formation canal simple : pas assez de pertes pour envoyer un conseil")
        return

    stats = _compute_formation_stats(resolved)
    best  = stats['best'] or 'f1'

    pos_label = {'f1': '1ère', 'f2': '2ème', 'f3': '3ème'}.get(best, '1ère')
    ok_b, tot_b, rate_b = stats[best]

    # ── Construire l'exemple concret depuis le dernier exemple mémorisé ──────
    ex_lines = []
    if _last_formation_example:
        ex = _last_formation_example
        orig_disp = SUIT_DISPLAY.get(ex['original_suit'], ex['original_suit'])
        rec_disp  = SUIT_DISPLAY.get(ex['recommended_suit'], ex['recommended_suit'])
        ex_lines = [
            "",
            f"_Exemple (dernière prédiction) :_",
            f"Jeu **#{ex['original_game']}** prédit {orig_disp} — absent",
            f"→ Mise sur {rec_disp} ({ex['card_position']} carte) au jeu **#{ex['next_game']}**",
        ]

    heure_str = f" · {heure}" if heure else ''
    lines = [
        f"♟️ **Formation de mise**{heure_str}",
        "",
        "📌 **Conseil :**",
        f"Si le bot envoie une prédiction et qu'elle ne reçoit pas son costume,",
        f"misez sur la **{pos_label} carte** apparue au jeu prédit,",
        f"au jeu suivant.",
    ] + ex_lines

    try:
        channel = await resolve_channel(PREDICTION_CHANNEL_ID)
        if channel:
            await client.send_message(channel, "\n".join(lines), parse_mode='markdown')
            logger.info(f"📢 Conseil formation simple envoyé au canal ({pos_label} carte recommandée)")
    except Exception as e:
        logger.error(f"❌ _send_formation_simple_to_canal: {e}")


# ============================================================================
# COMMANDE /b — GESTION DU B DYNAMIQUE PAR COSTUME
# ============================================================================

# Historique des changements de B par costume : [(suit, old_b, new_b, datetime, raison)]
b_change_history: List[tuple] = []

# Costumes dont le reset a été planifié (jeu auto-analyse) : {suit: scheduled_datetime}
b_reset_scheduled: Dict[str, datetime] = {}


async def _execute_b_reset(suit: str, new_b: int, raison: str):
    """Réinitialise le B d'un costume et notifie l'admin."""
    global compteur2_seuil_B_per_suit
    old_b = compteur2_seuil_B_per_suit.get(suit, compteur2_seuil_B)
    compteur2_seuil_B_per_suit[suit] = new_b
    b_change_history.append((suit, old_b, new_b, datetime.now(), raison))
    b_reset_scheduled.pop(suit, None)
    suit_display = SUIT_DISPLAY.get(suit, suit)
    logger.info(f"🔄 B({suit}) réinitialisé: {old_b} → {new_b} ({raison})")
    if ADMIN_ID:
        try:
            admin = await client.get_entity(ADMIN_ID)
            await client.send_message(
                admin,
                f"✅ **B réinitialisé — {suit_display}**\n\n"
                f"Ancien B : **{old_b}**\n"
                f"Nouveau B : **{new_b}** (= B admin)\n"
                f"Raison : _{raison}_",
                parse_mode='markdown'
            )
        except Exception as e:
            logger.error(f"❌ Notif reset B: {e}")


async def _scheduled_b_reset(suit: str, delay_seconds: int, raison: str):
    """Reset différé du B d'un costume après délai."""
    await asyncio.sleep(delay_seconds)
    if suit in b_reset_scheduled:  # Vérifie que le reset n'a pas été annulé
        await _execute_b_reset(suit, compteur2_seuil_B, raison)


def _analyse_b_suit(suit: str, window: int = 100) -> dict:
    """
    Analyse si le B initial serait suffisant pour le costume donné.
    Retourne: {'would_trigger': bool, 'max_absence': int, 'initial_b': int, 'current_b': int}
    """
    initial_b = compteur2_seuil_B
    current_b  = compteur2_seuil_B_per_suit.get(suit, initial_b)

    # Récupérer les derniers jeux connus
    recent_games = sorted(game_history.keys())[-window:]
    if not recent_games:
        return {'would_trigger': False, 'max_absence': 0,
                'initial_b': initial_b, 'current_b': current_b}

    # Calculer la plus longue séquence d'absence consécutive
    max_streak = 0
    streak = 0
    example_start = 0
    example_end   = 0
    for gn in recent_games:
        result = game_history.get(gn, {})
        player_cards = result.get('player_cards', [])
        suits_in_game = set()
        for c in player_cards:
            s = c.get('suit') or c.get('color') or ''
            if s in ALL_SUITS:
                suits_in_game.add(s)
        if suit not in suits_in_game:
            if streak == 0:
                example_start = gn
            streak += 1
            example_end = gn
            if streak > max_streak:
                max_streak = streak
        else:
            streak = 0

    would_trigger = max_streak >= initial_b
    return {
        'would_trigger': would_trigger,
        'max_absence': max_streak,
        'initial_b': initial_b,
        'current_b': current_b,
        'example_start': example_start,
        'example_end': example_end,
    }


async def cmd_b(event):
    """Commande /b — affiche et gère le B dynamique par costume."""
    global compteur2_seuil_B_per_suit, B_LOSS_INCREMENT
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()

    # ── /b seul : tableau des B actuels + historique ────────────────────────
    if len(parts) == 1:
        lines = ["📏 **SEUILS B PAR COSTUME**", f"B admin (base) : **{compteur2_seuil_B}**\n"]
        for suit in ALL_SUITS:
            sd  = SUIT_DISPLAY.get(suit, suit)
            cur = compteur2_seuil_B_per_suit.get(suit, compteur2_seuil_B)
            ini = compteur2_seuil_B
            delta = cur - ini
            marker = f" (+{delta} après {delta} perte(s))" if delta > 0 else " ✅ égal au B admin"
            sched  = f"\n   ⏰ Reset prévu: {b_reset_scheduled[suit].strftime('%H:%M')}" \
                     if suit in b_reset_scheduled else ""
            lines.append(f"{sd} : B admin={ini} → actuel = **{cur}**{marker}{sched}")

        if b_change_history:
            lines.append("\n📜 **Historique des changements:**")
            for suit, old, new, dt, raison in b_change_history[-6:]:
                sd = SUIT_DISPLAY.get(suit, suit)
                lines.append(f"• {dt.strftime('%d/%m %H:%M')} {sd}: {old}→{new} ({raison})")

        lines.append(
            f"\n**Incrément B après perte : +{B_LOSS_INCREMENT}**\n"
            "\n**Commandes:**\n"
            "`/b set ♠ N` — Définir directement B=N pour ♠\n"
            "`/b increment N` — Changer l'incrément B après perte (défaut 1)\n"
            "`/b reset ♠` — Remettre ♠ au B admin\n"
            "`/b reset all` — Remettre tous les costumes au B admin\n"
            "`/b analyse` — Analyser et proposer un reset automatique\n"
            "`/b cancel ♠` — Annuler un reset planifié"
        )
        await event.respond("\n".join(lines), parse_mode='markdown')
        return

    arg = parts[1].lower()

    # ── /b set ♠ N — définit directement B d'un costume ──────────────────────
    if arg == 'set' and len(parts) >= 4:
        suit_input = parts[2]
        target = None
        for s in ALL_SUITS:
            if suit_input in (s, SUIT_DISPLAY.get(s, ''), s.strip()):
                target = s
                break
        if not target:
            await event.respond(f"❌ Costume inconnu: `{suit_input}`\nUtilisez ♠ ♥ ♦ ♣")
            return
        try:
            new_val = int(parts[3])
            assert 1 <= new_val <= 30
        except (ValueError, AssertionError):
            await event.respond("❌ La valeur N doit être un entier entre 1 et 30.")
            return
        old_val = compteur2_seuil_B_per_suit.get(target, compteur2_seuil_B)
        compteur2_seuil_B_per_suit[target] = new_val
        sd = SUIT_DISPLAY.get(target, target)
        await event.respond(
            f"✅ B({sd}) défini manuellement : {old_val} → **{new_val}**\n"
            f"(B admin reste à {compteur2_seuil_B})"
        )
        return

    # ── /b increment N — change l'incrément B après perte ────────────────────
    if arg == 'increment' and len(parts) >= 3:
        try:
            inc_val = int(parts[2])
            assert 0 <= inc_val <= 10
        except (ValueError, AssertionError):
            await event.respond("❌ L'incrément doit être un entier entre 0 et 10.")
            return
        old_inc = B_LOSS_INCREMENT
        B_LOSS_INCREMENT = inc_val
        await event.respond(
            f"✅ Incrément B après perte : **{old_inc}** → **{inc_val}**\n"
            "_(0 = pas d'augmentation automatique du B après une perte)_"
        )
        db.db_schedule(save_runtime_config())
        return

    # ── /b reset all ─────────────────────────────────────────────────────────
    if arg == 'reset' and len(parts) >= 3 and parts[2].lower() == 'all':
        for s in ALL_SUITS:
            if compteur2_seuil_B_per_suit.get(s, compteur2_seuil_B) != compteur2_seuil_B:
                await _execute_b_reset(s, compteur2_seuil_B, "Reset manuel (all)")
        await event.respond(f"✅ Tous les B remis à **{compteur2_seuil_B}** (valeur initiale).")
        return

    # ── /b reset ♠ ───────────────────────────────────────────────────────────
    if arg == 'reset' and len(parts) >= 3:
        suit_input = parts[2]
        # Cherche le costume correspondant
        target = None
        for s in ALL_SUITS:
            if suit_input in (s, SUIT_DISPLAY.get(s, ''), s.strip()):
                target = s
                break
        if not target:
            await event.respond(f"❌ Costume inconnu: `{suit_input}`\nUtilisez ♠ ♥ ♦ ♣")
            return
        old_b = compteur2_seuil_B_per_suit.get(target, compteur2_seuil_B)
        if old_b == compteur2_seuil_B:
            await event.respond(f"ℹ️ {SUIT_DISPLAY.get(target, target)} est déjà à B={compteur2_seuil_B}.")
            return
        await _execute_b_reset(target, compteur2_seuil_B, "Reset manuel admin")
        return

    # ── /b cancel ♠ ──────────────────────────────────────────────────────────
    if arg == 'cancel' and len(parts) >= 3:
        suit_input = parts[2]
        target = None
        for s in ALL_SUITS:
            if suit_input in (s, SUIT_DISPLAY.get(s, ''), s.strip()):
                target = s
                break
        if not target or target not in b_reset_scheduled:
            await event.respond(f"❌ Aucun reset planifié pour `{suit_input}`.")
            return
        b_reset_scheduled.pop(target)
        await event.respond(f"🚫 Reset planifié pour {SUIT_DISPLAY.get(target, target)} annulé.")
        return

    # ── /b analyse ───────────────────────────────────────────────────────────
    if arg == 'analyse':
        await event.respond("🔬 Analyse en cours…")
        lines = [f"🔬 **ANALYSE DES SEUILS B**\n_B admin actuel = {compteur2_seuil_B}_\n"]
        proposed = []
        for suit in ALL_SUITS:
            sd  = SUIT_DISPLAY.get(suit, suit)
            res = _analyse_b_suit(suit)
            cur = res['current_b']
            ini = res['initial_b']  # = compteur2_seuil_B (admin)
            if cur <= ini:
                lines.append(f"{sd}: B={cur} (= B admin) — aucun reset nécessaire")
                continue
            if res['would_trigger']:
                lines.append(
                    f"{sd}: B actuel={cur} | B admin={ini}\n"
                    "   ✅ Le B admin **aurait déclenché** une prédiction "
                    f"(absence max = {res['max_absence']} sur 100 jeux, "
                    f"jeux #{res.get('example_start','')}→#{res.get('example_end','')})\n"
                    "   → **Reset vers B admin recommandé dans 1h**"
                )
                proposed.append(suit)
            else:
                lines.append(
                    f"{sd}: B actuel={cur} | B admin={ini}\n"
                    "   ⚠️ Le B admin n'atteint pas encore le seuil "
                    f"(absence max = {res['max_absence']}/{ini}) — reset non recommandé"
                )

        if proposed:
            lines.append(f"\n🕐 Reset automatique vers B admin ({compteur2_seuil_B}) dans **1 heure** pour: "
                         + " ".join(SUIT_DISPLAY.get(s, s) for s in proposed))
            for suit in proposed:
                if suit not in b_reset_scheduled:
                    b_reset_scheduled[suit] = datetime.now() + timedelta(hours=1)
                    snap = _analyse_b_suit(suit)
                    asyncio.create_task(
                        _scheduled_b_reset(suit, 3600,
                                           "Auto-analyse: B admin suffisant "
                                           f"(absence max={snap['max_absence']})")
                    )
        else:
            lines.append("\n✅ Aucun reset recommandé pour le moment.")

        await event.respond("\n".join(lines), parse_mode='markdown')
        return

    await event.respond(
        "❌ Commande inconnue.\n"
        "`/b` — Voir tous les B\n"
        "`/b reset ♠` — Reset immédiat\n"
        "`/b reset all` — Reset tout\n"
        "`/b analyse` — Analyse automatique\n"
        "`/b cancel ♠` — Annuler un reset planifié"
    )


async def cmd_favorables(event):
    """
    /favorables — Affiche les heures favorables (admin) ou dans le canal.
    /favorables canal — Force l'envoi dans le canal de prédiction.
    /favorables on/off — Active/désactive les annonces automatiques toutes les 3h.
    """
    global heures_favorables_active
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.strip().split()
        sub   = parts[1].lower() if len(parts) > 1 else ''

        if sub == 'off':
            heures_favorables_active = False
            await event.respond("🔕 Fenêtres favorables **désactivées**.")
            db.db_schedule(save_runtime_config())
            return

        if sub == 'on':
            heures_favorables_active = True
            await event.respond("✅ Fenêtres favorables **réactivées** — déclenchement par 2 événements C4.")
            db.db_schedule(save_runtime_config())
            return

        # Affichage statut
        statut = "✅ Acti" if heures_favorables_active else "🔕 Désactivé"
        saved_panel = await db.db_load_kv('active_panel')
        panel_info = "Aucun panneau actif"
        if saved_panel and saved_panel.get('active'):
            panel_info = (
                f"Panneau #{saved_panel.get('panel_number','?')} — "
                f"{saved_panel.get('interval_str','?')} "
                f"(msg_id={saved_panel.get('msg_id','?')})"
            )
        await event.respond(
            "🕐 **Système fenêtres favorables**\n"
            f"Statut: {statut}\n"
            "Déclencheur: 2 événements C4 → fenêtre 3h (ou 30min si C14 équilibré)\n"
            f"C4 events accumulés: **{c4_favorable_event_count}/2**\n"
            f"Panneau actif: {panel_info}\n\n"
            "`/favorables on/off` — Activer/désactiver",
            parse_mode='markdown'
        )
    except Exception as e:
        logger.error(f"Erreur cmd_favorables: {e}")
        await event.respond(f"❌ Erreur: {e}")


# ============================================================================
# COMMANDE /panneaux — PDF historique des panneaux countdown
# ============================================================================

def generate_panneaux_pdf(panels: List[Dict]) -> bytes:
    """Génère un PDF avec l'historique complet des panneaux countdown envoyés."""
    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    # ── En-tête ──────────────────────────────────────────────────────────────
    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(0, 60, 160)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Historique Panneaux Heures Favorables',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(3)

    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(80, 80, 80)
    pdf.cell(0, 6,
        f'Total panneaux : {len(panels)} | '
        f'Genere le {datetime.now().strftime("%d/%m/%Y a %Hh%M")} (heure Cote d\'Ivoire)',
        new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C'
    )
    pdf.ln(6)

    # ── Tableau ───────────────────────────────────────────────────────────────
    col_widths = [18, 45, 22, 22, 35, 38]
    headers    = ['N°', 'Intervalle', 'De (h)', 'A (h)', 'Envoyé avant', 'Date & Heure']

    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(0, 60, 160)
    pdf.set_text_color(255, 255, 255)
    for h, w in zip(headers, col_widths):
        pdf.cell(w, 9, h, border=1, fill=True, align='C')
    pdf.ln()

    pdf.set_font('Helvetica', '', 10)
    alt = False
    for p in panels:
        if alt:
            pdf.set_fill_color(220, 232, 255)
        else:
            pdf.set_fill_color(255, 255, 255)
        pdf.set_text_color(0, 0, 0)
        alt = not alt

        num_str    = f"#{p['panel_number']}"
        itv_str    = pdf_safe(p['interval_str'])
        start_str  = f"{p['start_h']:02d}h00"
        end_str    = f"{p['end_h']:02d}h00"
        mb         = p['minutes_before']
        avant_str  = f"{mb // 60}h {mb % 60:02d}min" if mb >= 60 else f"{mb}min"
        sent_at    = p['sent_at']
        if hasattr(sent_at, 'strftime'):
            dt_str = sent_at.strftime('%d/%m/%Y %Hh%M')
        else:
            dt_str = str(sent_at)[:16]

        row = [num_str, itv_str, start_str, end_str, avant_str, dt_str]
        for val, w in zip(row, col_widths):
            pdf.cell(w, 8, val, border=1, fill=True, align='C')
        pdf.ln()

    return bytes(pdf.output())


def generate_recherche_pdf(
    date_from, date_to, hp: int,
    manques: list, apparents: list
) -> bytes:
    """
    Génère le PDF de recherche manques/apparents depuis C4/C7/C8.
    manques   = liste de {suit, count, start_game, end_game, start_time, end_time, source}
    apparents = liste de {suit, count, start_game, end_game, start_time, end_time, source}
    """
    suit_names  = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle',
                   '♠️': 'Pique', '♥️': 'Coeur', '♦️': 'Carreau', '♣️': 'Trefle'}
    suit_colors = {'♠': (30, 30, 30), '♥': (180, 0, 0), '♦': (0, 80, 200), '♣': (0, 120, 50),
                   '♠️':(30, 30, 30), '♥️':(180, 0, 0), '♦️':(0, 80, 200), '♣️':(0, 120, 50)}

    from_str = date_from.strftime('%d/%m/%Y %Hh%M')
    to_str   = date_to.strftime('%d/%m/%Y %Hh%M')
    gen_str  = datetime.now().strftime('%d/%m/%Y a %Hh%M')

    def _row_section(pdf, events, title, header_color, row_color_fn):
        """Génère une section tableau avec titre + lignes détaillées."""
        col_w   = [28, 20, 32, 22, 22, 22, 28]
        headers = ['Date', 'Heure', 'Costume', 'Jeu debut', 'Jeu fin', 'Nb fois', 'Source']

        pdf.set_font('Helvetica', 'B', 11)
        pdf.set_fill_color(*header_color)
        pdf.set_text_color(255, 255, 255)
        pdf.cell(0, 9, f'{title}  ({len(events)} serie(s))',
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
        pdf.ln(2)

        if not events:
            pdf.set_font('Helvetica', 'I', 10)
            pdf.set_text_color(150, 150, 150)
            pdf.cell(0, 8, 'Aucune serie trouvee dans cette periode', border=1, align='C',
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            pdf.ln(4)
            return

        # En-tête colonnes
        pdf.set_font('Helvetica', 'B', 9)
        pdf.set_fill_color(220, 230, 245)
        pdf.set_text_color(0, 0, 0)
        for h, w in zip(headers, col_w):
            pdf.cell(w, 8, h, border=1, fill=True, align='C')
        pdf.ln()

        pdf.set_font('Helvetica', '', 9)
        alt = False
        for ev in sorted(events, key=lambda x: x['end_time']):
            suit    = ev.get('suit', '')
            nom     = suit_names.get(suit, suit)
            r, g, b = suit_colors.get(suit, (0, 0, 0))
            end_dt  = ev.get('end_time')
            date_s  = end_dt.strftime('%d/%m/%Y') if end_dt else '-'
            heure_s = end_dt.strftime('%Hh%M')    if end_dt else '-'
            sg      = f"#{ev.get('start_game', '?')}"
            eg      = f"#{ev.get('end_game',   '?')}"
            nb      = f"{ev.get('count', '?')}x"
            src     = ev.get('source', 'C?')

            bg = (248, 248, 248) if alt else (255, 255, 255)
            pdf.set_fill_color(*bg)
            pdf.set_text_color(0, 0, 0)

            pdf.cell(col_w[0], 8, date_s,  border=1, fill=True, align='C')
            pdf.cell(col_w[1], 8, heure_s, border=1, fill=True, align='C')
            pdf.set_text_color(r, g, b)
            pdf.set_font('Helvetica', 'B', 9)
            pdf.cell(col_w[2], 8, nom,     border=1, fill=True, align='C')
            pdf.set_text_color(0, 0, 0)
            pdf.set_font('Helvetica', '', 9)
            pdf.cell(col_w[3], 8, sg,      border=1, fill=True, align='C')
            pdf.cell(col_w[4], 8, eg,      border=1, fill=True, align='C')
            pdf.set_font('Helvetica', 'B', 9)
            pdf.set_text_color(*row_color_fn())
            pdf.cell(col_w[5], 8, nb,      border=1, fill=True, align='C')
            pdf.set_text_color(80, 80, 80)
            pdf.set_font('Helvetica', '', 8)
            pdf.cell(col_w[6], 8, src,     border=1, fill=True, align='C')
            pdf.ln()
            alt = not alt
        pdf.ln(5)

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    # Titre
    pdf.set_font('Helvetica', 'B', 15)
    pdf.set_fill_color(20, 60, 120)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Recherche Manques / Apparents',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C', fill=True)
    pdf.ln(2)

    pdf.set_font('Helvetica', '', 9)
    pdf.set_text_color(60, 60, 60)
    pdf.cell(0, 6, f'Periode : {from_str}  ->  {to_str}',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.cell(0, 6,
             f'Seuil HP = {hp}x  |  Manques: {len(manques)}  |  Apparents: {len(apparents)}  |  Genere le {gen_str}',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align='C')
    pdf.ln(6)

    # ─── Section APPARENTS ───
    _row_section(pdf, apparents,
                 f'APPARENTS >= {hp}x (C7 - presences consecutives)',
                 (0, 120, 50),
                 lambda: (0, 120, 50))

    # ─── Section MANQUES ───
    _row_section(pdf, manques,
                 f'MANQUES >= {hp}x (C4/C8 - absences)',
                 (180, 0, 0),
                 lambda: (180, 0, 0))

    return bytes(pdf.output())


async def cmd_panneaux(event):
    """
    /panneaux — Admin : envoie un PDF avec l'historique de tous les panneaux countdown.
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        await event.respond("⏳ Génération du PDF panneaux...")
        panels = await db.db_load_countdown_panels(limit=500)
        if not panels:
            await event.respond("🟦 Aucun panneau countdown enregistré pour l'instant.")
            return
        pdf_bytes = generate_panneaux_pdf(panels)
        fname = f"panneaux_countdown_{datetime.now().strftime('%Y%m%d_%H%M')}.pdf"
        with open(fname, 'wb') as f:
            f.write(pdf_bytes)
        admin_entity = await client.get_entity(ADMIN_ID)
        await client.send_file(
            admin_entity, fname,
            caption=(
                "🟦 **Panneaux Heures Favorables**\n"
                f"📋 {len(panels)} panneau(x) enregistré(s)\n"
                f"🔢 Dernier N° : #{panels[0]['panel_number']}"
            ),
            parse_mode='markdown'
        )
        import os as _os
        try: _os.remove(fname)
        except Exception: pass
        logger.info(f"📄 PDF panneaux envoyé ({len(panels)} entrées)")
    except Exception as e:
        logger.error(f"Erreur cmd_panneaux: {e}")
        await event.respond(f"❌ Erreur: {e}")


# ============================================================================
# COMMANDE /recherche — manques/apparents sur une plage de dates + PDF
# ============================================================================

async def cmd_recherche(event):
    """
    /recherche JJ/MM/AAAA HHhMM JJ/MM/AAAA HHhMM HP
    Exemple : /recherche 28/03/2026 08h00 28/03/2026 20h00 10
    Aussi accepté : /recherche 28/03/2026 28/03/2026 10  (journée complète)
    HP = seuil minimum d'occurrences à afficher
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    AIDE = (
        "📖 **Formats acceptés :**\n\n"
        "1️⃣ **Une seule date (journée entière) :**\n"
        "   `/recherche 29/03/2026 5`\n\n"
        "2️⃣ **Plage de dates (journées entières) :**\n"
        "   `/recherche 28/03/2026 29/03/2026 5`\n\n"
        "3️⃣ **Plage avec heures précises :**\n"
        "   `/recherche 29/03/2026 08h00 29/03/2026 20h00 5`\n\n"
        "4️⃣ **Depuis une date/heure jusqu'à maintenant :**\n"
        "   `/recherche 29/03/2026 08h00 maintenant 5`\n\n"
        "5️⃣ **Toutes les données disponibles :**\n"
        "   `/recherche tout 5`\n\n"
        "_HP = nombre minimum d'occurrences à afficher_"
    )

    text  = event.raw_text.strip()
    parts = text.split()
    parts = parts[1:]  # Enlever /recherche

    def _parse_date(d_str, h_str="00:00", end_of_day=False):
        """Parse JJ/MM/AAAA + HHhMM → datetime. end_of_day=True → 23:59."""
        if end_of_day:
            h_str = "23:59"
        h_str = h_str.replace('h', ':').replace('H', ':')
        return datetime.strptime(f"{d_str} {h_str}", "%d/%m/%Y %H:%M")

    def _is_date(s):
        try:
            datetime.strptime(s, "%d/%m/%Y")
            return True
        except ValueError:
            return False

    def _is_heure(s):
        return 'h' in s.lower() and not _is_date(s)

    try:
        now = datetime.now()

        # ── Mode 1 : /recherche tout HP ──
        if len(parts) == 2 and parts[0].lower() in ('tout', 'all', 'tous'):
            date_from = datetime(2000, 1, 1)
            date_to   = now
            hp        = int(parts[1])

        # ── Mode 2 : /recherche JJ/MM/AAAA HP ── (une journée)
        elif len(parts) == 2 and _is_date(parts[0]):
            date_from = _parse_date(parts[0])
            date_to   = _parse_date(parts[0], end_of_day=True)
            hp        = int(parts[1])

        # ── Mode 3 : /recherche JJ/MM/AAAA JJ/MM/AAAA HP ── (2 journées)
        elif len(parts) == 3 and _is_date(parts[0]) and _is_date(parts[1]):
            date_from = _parse_date(parts[0])
            date_to   = _parse_date(parts[1], end_of_day=True)
            hp        = int(parts[2])

        # ── Mode 4 : /recherche JJ/MM/AAAA HHhMM maintenant HP ──
        elif len(parts) == 4 and _is_date(parts[0]) and _is_heure(parts[1]) and parts[2].lower() in ('maintenant', 'now', 'maintnt'):
            date_from = _parse_date(parts[0], parts[1])
            date_to   = now
            hp        = int(parts[3])

        # ── Mode 5 : /recherche JJ/MM/AAAA HHhMM JJ/MM/AAAA HHhMM HP ──
        elif len(parts) == 5 and _is_date(parts[0]) and _is_heure(parts[1]) and _is_date(parts[2]):
            date_from = _parse_date(parts[0], parts[1])
            date_to   = _parse_date(parts[2], parts[3])
            hp        = int(parts[4])

        else:
            await event.respond(AIDE, parse_mode='markdown')
            return

        if hp < 1:
            await event.respond("❌ HP doit être >= 1")
            return
        if date_from >= date_to:
            await event.respond("❌ La date de début doit être avant la date de fin.")
            return

    except (ValueError, IndexError):
        await event.respond(AIDE, parse_mode='markdown')
        return

    await event.respond("⏳ Recherche en cours…")

    # ── Filtrer C4 (absences), C7 (présences), C8 (absences) par plage ──
    def _in_range(ev):
        t = ev.get('end_time')
        if not isinstance(t, datetime):
            try:
                t = datetime.fromisoformat(str(t))
            except Exception:
                return False
        return date_from <= t <= date_to

    manques_ev   = [dict(ev, source='C4') for ev in compteur4_events  if ev.get('count', 0) >= hp and _in_range(ev)]
    manques_ev  += [dict(ev, source='C8') for ev in compteur8_completed if ev.get('count', 0) >= hp and _in_range(ev)]
    apparents_ev = [dict(ev, source='C7') for ev in compteur7_completed if ev.get('count', 0) >= hp and _in_range(ev)]

    if not manques_ev and not apparents_ev:
        from_s2 = date_from.strftime('%d/%m/%Y %Hh%M')
        to_s2   = date_to.strftime('%d/%m/%Y %Hh%M')

        # Calcule les stats disponibles (sans filtre HP) pour guider l'utilisateur
        all_c4  = [ev for ev in compteur4_events    if _in_range(ev)]
        all_c7  = [ev for ev in compteur7_completed if _in_range(ev)]
        all_c8  = [ev for ev in compteur8_completed if _in_range(ev)]
        all_ev  = all_c4 + all_c7 + all_c8
        if all_ev:
            max_c = max(ev.get('count', 0) for ev in all_ev)
            min_c = min(ev.get('count', 0) for ev in all_ev)
            dispo_msg = (
                f"📊 Données disponibles dans cette plage : {len(all_ev)} série(s)\n"
                f"   Comptes min={min_c} / max={max_c}\n"
                f"   ➡️ Essaie `/recherche tout {min_c}`"
            )
        else:
            total_ev = len(compteur4_events) + len(compteur7_completed) + len(compteur8_completed)
            dispo_msg = (
                "📭 Aucune série dans cette plage de dates.\n"
                f"   Total en base : {total_ev} série(s) (toutes dates confondues)\n"
                f"   Essaie `/recherche tout {max(1, hp - 5)}`"
            )
        await event.respond(
            f"📭 Aucune série (C4/C7/C8) avec HP≥{hp} entre {from_s2} et {to_s2}.\n\n"
            + dispo_msg
        )
        return

    # ── Générer le PDF ──
    pdf_bytes = generate_recherche_pdf(date_from, date_to, hp, manques_ev, apparents_ev)
    from_s = date_from.strftime('%d/%m/%Y %Hh%M')
    to_s   = date_to.strftime('%d/%m/%Y %Hh%M')
    fname  = f"recherche_{date_from.strftime('%Y%m%d_%H%M')}_{date_to.strftime('%Y%m%d_%H%M')}_hp{hp}.pdf"
    with open(fname, 'wb') as f:
        f.write(pdf_bytes)

    admin_entity = await client.get_entity(ADMIN_ID)
    suit_names_s = {'♠️': 'Pique', '♣️': 'Trefle', '♦️': 'Carreau', '♥️': 'Coeur'}

    # Résumé texte rapide
    lines = [
        f"🔍 **Recherche : {from_s} → {to_s}**",
        f"Seuil HP={hp}  |  Manques: {len(manques_ev)}  |  Apparents: {len(apparents_ev)}",
        ""
    ]
    lines.append("**APPARENTS >= HP :**")
    if apparents_ev:
        for ev in sorted(apparents_ev, key=lambda x: -x.get('count', 0)):
            suit = ev.get('suit', '')
            nom  = suit_names_s.get(suit, suit)
            lines.append(
                f"  {suit} {nom} : {ev.get('count')}x  "
                f"(#{ev.get('start_game')}→#{ev.get('end_game')})  "
                f"{ev.get('end_time').strftime('%d/%m %Hh%M') if ev.get('end_time') else ''}"
            )
    else:
        lines.append("  Aucun")
    lines.append("")
    lines.append("**MANQUES >= HP :**")
    if manques_ev:
        for ev in sorted(manques_ev, key=lambda x: -x.get('count', 0)):
            suit = ev.get('suit', '')
            nom  = suit_names_s.get(suit, suit)
            lines.append(
                f"  {suit} {nom} : {ev.get('count')}x  "
                f"(#{ev.get('start_game')}→#{ev.get('end_game')})  "
                f"{ev.get('end_time').strftime('%d/%m %Hh%M') if ev.get('end_time') else ''}  [{ev.get('source','')}]"
            )
    else:
        lines.append("  Aucun")

    await client.send_file(
        admin_entity, fname,
        caption="\n".join(lines),
        parse_mode='markdown'
    )
    import os as _os
    try: _os.remove(fname)
    except Exception: pass
    logger.info(f"📄 /recherche PDF envoyé : C4={len([e for e in manques_ev if e['source']=='C4'])} "
                f"C8={len([e for e in manques_ev if e['source']=='C8'])} C7={len(apparents_ev)} HP={hp}")


# ============================================================================
# COMMANDE /concours — résultats en cours du concours (avant le jeu #1440)
# ============================================================================

async def cmd_concours(event):
    """
    /concours — Admin : affiche les résultats actuels du concours par costume
    (mêmes statistiques que le message #1440 mais en temps réel).
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    try:
        rows = await db.db_load_prediction_history(limit=500)
    except Exception as e:
        await event.respond(f"❌ Erreur lecture DB: {e}")
        return

    if not rows:
        await event.respond("📭 Aucune prédiction enregistrée pour l'instant.")
        return

    SUITS_ORDER = ["♠️", "♣️", "♦️", "♥️"]
    SUIT_NAMES  = {"♠️": "PIQUE", "♣️": "TRÈFLE", "♦️": "CARREAU", "♥️": "CŒUR"}
    SUIT_EMOJI  = {"♠️": "♠️", "♣️": "♣️", "♦️": "♦️", "♥️": "♥️"}

    stats = {s: {"total": 0, "gagne": 0, "perdu": 0, "r0": 0, "r1": 0} for s in SUITS_ORDER}
    total_g = 0
    total_p = 0

    for row in rows:
        suit   = row.get("predicted_suit", "")
        status = row.get("status", "")
        if suit not in stats:
            continue
        stats[suit]["total"] += 1
        if status in ("gagne_r0", "gagne_r1", "gagne"):
            stats[suit]["gagne"] += 1
            total_g += 1
            if status == "gagne_r0":
                stats[suit]["r0"] += 1
            elif status == "gagne_r1":
                stats[suit]["r1"] += 1
        elif status == "perdu":
            stats[suit]["perdu"] += 1
            total_p += 1

    total_pred = total_g + total_p
    pct_global = round(total_g / total_pred * 100, 1) if total_pred else 0.0

    jeu_actuel = current_game_number
    GAME_FIN   = 1440
    restants   = max(0, GAME_FIN - jeu_actuel)

    now_str = datetime.now().strftime("%d/%m/%Y %H:%M")

    # ── Classement par taux de réussite ──
    classement = sorted(
        SUITS_ORDER,
        key=lambda s: (stats[s]["gagne"] / stats[s]["total"] if stats[s]["total"] else 0),
        reverse=True
    )
    champion = classement[0]
    champ_pct = round(stats[champion]["gagne"] / stats[champion]["total"] * 100, 1) if stats[champion]["total"] else 0.0

    # ─── Message 1 ───
    lines1 = [
        "🏆 **CONCOURS PAR COSTUME — EN COURS**",
        f"📅 {now_str}  |  🎮 Jeu actuel: **#{jeu_actuel}**",
        f"⏳ Jeux restants avant #1440: **{restants}**",
        "",
        f"📊 **Global:** {total_g}✅ / {total_p}❌  sur {total_pred} prédictions",
        f"🎯 **Taux global: {pct_global}%**",
        "",
    ]

    for suit in SUITS_ORDER:
        s = stats[suit]
        t = s["total"]
        g = s["gagne"]
        p = s["perdu"]
        pct = round(g / t * 100, 1) if t else 0.0
        bar_full  = round(pct / 10)
        bar_empty = 10 - bar_full
        bar = "█" * bar_full + "░" * bar_empty
        nom = SUIT_NAMES[suit]
        lines1 += [
            f"{'─'*28}",
            f"{SUIT_EMOJI[suit]} **{nom}**",
            f"  ✅ Gagnées : {g}  (R0:{s['r0']}  R1:{s['r1']})",
            f"  ❌ Perdues : {p}",
            f"  📈 Taux    : **{pct}%**  [{bar}]",
        ]

    # ─── Message 2 ───
    lines2 = [
        "🥇 **CLASSEMENT PROVISOIRE**",
        "",
    ]
    medals = ["🥇", "🥈", "🥉", "4️⃣"]
    for i, suit in enumerate(classement):
        s = stats[suit]
        t = s["total"]
        g = s["gagne"]
        pct = round(g / t * 100, 1) if t else 0.0
        lines2.append(f"{medals[i]} {SUIT_EMOJI[suit]} {SUIT_NAMES[suit]} — {pct}%  ({g}/{t})")

    lines2 += [
        "",
        f"👑 **CHAMPION PROVISOIRE: {SUIT_EMOJI[champion]} {SUIT_NAMES[champion]}** ({champ_pct}%)",
        "",
        "⚠️ Résultats provisoires — concours se termine au jeu **#1440**",
        f"🔢 Il reste **{restants} jeux** pour renverser le classement.",
    ]

    msg1 = "\n".join(lines1)
    msg2 = "\n".join(lines2)

    await event.respond(msg1, parse_mode='markdown')
    await asyncio.sleep(1)
    await event.respond(msg2, parse_mode='markdown')
    logger.info(f"📊 /concours envoyé : #{jeu_actuel} — {total_pred} prédictions ({pct_global}%)")


# ============================================================================
# COMMANDE /testpred — envoie une prédiction test sur le canal
# ============================================================================

async def cmd_testpred(event):
    """
    /testpred [♠/♥/♦/♣] — Admin : envoie une prédiction test sur le canal immédiatement.
    Utile pour vérifier que les réactions sont bien remontées.
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.strip().split()
        suit = parts[1] if len(parts) > 1 and parts[1] in ('♠', '♥', '♦', '♣') else '♠'
        fake_game = 9999

        if not PREDICTION_CHANNEL_ID:
            await event.respond("❌ PREDICTION_CHANNEL_ID non configuré")
            return

        channel_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not channel_entity:
            await event.respond("❌ Canal inaccessible")
            return

        msg = format_prediction_message(fake_game, suit, 'en_cours', fake_game, [])
        msg = "🧪 *[TEST]* " + msg
        sent = await client.send_message(channel_entity, msg, parse_mode='markdown')
        mid = sent.id

        canal_pred_msg_ids[mid] = fake_game
        # Insérer en DB pour que le message_id survive un redémarrage
        await db.db_add_prediction_history({
            'predicted_game': fake_game, 'suit': suit,
            'type': 'test', 'reason': 'test manuel', 'status': 'en_cours',
            'rattrapage_level': 0
        })
        await db.db_set_prediction_message_id(fake_game, suit, mid)

        await event.respond(
            "✅ Prédiction test envoyée sur le canal\n"
            f"👁 message_id = `{mid}` → game #{fake_game} {suit}\n"
            "Réagis au message dans le canal pour tester 🔔"
        )
    except Exception as e:
        logger.error(f"Erreur cmd_testpred: {e}")
        await event.respond(f"❌ Erreur: {e}")


# ============================================================================
# COMMANDE /verifier — test du suivi réactions
# ============================================================================

async def cmd_verifier(event):
    """
    /verifier — Admin : vérifie si le bot a déjà prédit et si le suivi réactions est actif.
    Affiche les dernières prédictions avec leur message_id Telegram.
    """
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        total_preds = len(prediction_history)
        total_tracked = len(canal_pred_msg_ids)

        lines = [
            "🔍 **VÉRIFICATION — Prédictions & Réactions**\n",
            f"📊 Total prédictions en mémoire : **{total_preds}**",
            f"👁 Messages suivis pour réactions : **{total_tracked}**\n",
        ]

        if total_preds == 0:
            lines.append("_Aucune prédiction trouvée. Le bot n'a pas encore prédit._")
        else:
            suit_names = {'♠': 'Pique', '♥': 'Cœur', '♦': 'Carreau', '♣': 'Trèfle'}
            status_icons = {
                'en_cours': '⏳', 'perdu': '❌', 'void': '⬜',
            }
            lines.append("📋 **15 dernières prédictions :**\n")
            for p in prediction_history[:15]:
                gn    = p.get('predicted_game', '?')
                suit  = p.get('suit', '?')
                st    = p.get('status', '?')
                mid   = p.get('canal_message_id')
                icon  = '✅' if str(st).startswith('gagne') else status_icons.get(st, '❓')
                react = '🔔' if mid else '🔕'
                name  = suit_names.get(suit, suit)
                mid_str = f"msg#{mid}" if mid else "pas de msg_id"
                lines.append(f"  {icon} #{gn} {suit} {name} — {react} {mid_str}")

        lines += [
            "",
            "🔔 = suivi réactions actif",
            "🔕 = pas encore de message_id enregistré",
        ]
        await event.respond("\n".join(lines), parse_mode='markdown')
    except Exception as e:
        logger.error(f"Erreur cmd_verifier: {e}")
        await event.respond(f"❌ Erreur: {e}")


# ============================================================================
# RÉACTIONS AUX MESSAGES DE PRÉDICTION
# ============================================================================

REACTIONS_SUIVIES = {
    # ── Réactions Telegram officielles ──────────────────────────────────────
    '👍', '👎', '❤', '❤️', '🔥', '🥰', '👏', '😁', '🤔', '🤯',
    '😱', '🤬', '😢', '🎉', '🤩', '🤮', '💩', '🙏', '👌', '🕊',
    '🤡', '🥱', '🥴', '😍', '🐳', '❤‍🔥', '🌚', '🌭', '💯', '🤣',
    '⚡', '🍌', '🏆', '💔', '🤨', '😐', '🍓', '🍾', '💋', '🖕',
    '😈', '😴', '😭', '🤓', '👻', '🎃', '🙈', '😇', '😨', '🤝',
    '✍', '🤗', '🫡', '🎅', '🎄', '☃', '💅', '🤪', '🗿', '🆒',
    '💘', '🙉', '🦄', '😘', '💊', '🙊', '😎', '👾', '😡', '🥳',
    '🫠', '😤', '🤭', '🥺', '😏', '🙄', '😒', '🤑', '😜', '😝',
    '😛', '😋', '🤤', '🤢', '🤧', '🥵', '🥶', '😵', '🤠', '🤥',
    '🤫', '🧐', '😬', '😳', '😞', '😔', '😟', '😕', '😣', '😖',
    # ── Variantes peau claire (🏻) ───────────────────────────────────────
    '👍🏻', '👎🏻', '👏🏻', '🙏🏻', '👌🏻', '✍🏻', '🤝🏻', '💅🏻', '🤗🏻',
    '👊🏻', '✊🏻', '🤛🏻', '🤜🏻', '🤞🏻', '🖖🏻', '🤙🏻', '💪🏻', '🦾',
    # ── Variantes peau (🏼🏽🏾🏿) ─────────────────────────────────────────
    '👍🏼', '👍🏽', '👍🏾', '👍🏿',
    '👎🏼', '👎🏽', '👎🏾', '👎🏿',
    '👏🏼', '👏🏽', '👏🏾', '👏🏿',
    '🙏🏼', '🙏🏽', '🙏🏾', '🙏🏿',
    '👌🏼', '👌🏽', '👌🏾', '👌🏿',
    # ── Symboles et divers ───────────────────────────────────────────────
    '💯', '✅', '❌', '‼️', '⁉️', '💢', '💥', '💫', '⭐', '🌟',
    '🎯', '🎰', '🃏', '🀄', '♠️', '♥️', '♦️', '♣️', '🃁', '🂡',
    '💰', '💵', '💸', '🤑', '💎', '👑', '🏅', '🥇', '🎖', '🎗',
    # ── Réactions spéciales et gestuelle ───────────────────────────────
    '🤷‍♂️', '🤷‍♀️', '🤷', '😚', '🫶', '🫶🏻', '🫶🏽', '🫶🏿',
    '🙌', '🙌🏻', '🙌🏽', '🙌🏿', '🫂', '💝', '💖', '💗', '💓', '💞',
}

async def on_reaction_event(update):
    """Notifie l'admin quand un membre réagit à un message de prédiction du canal."""
    global notified_reactions
    try:
        if not isinstance(update, UpdateMessageReactions):
            return
        msg_id = update.msg_id
        logger.info(f"🔔 UpdateMessageReactions reçu → msg_id={msg_id} | suivi={msg_id in canal_pred_msg_ids} | dict_size={len(canal_pred_msg_ids)}")
        if msg_id not in canal_pred_msg_ids:
            return
        game_number = canal_pred_msg_ids[msg_id]

        reactions = update.reactions
        if not reactions:
            return

        # ── Cas 1 : recent_reactors disponible (groupes / petits canaux) ───
        recent = getattr(reactions, 'recent_reactors', None) or []
        if recent:
            for reactor in recent:
                try:
                    reaction_obj = getattr(reactor, 'reaction', None)
                    emoji = getattr(reaction_obj, 'emoticon', None)
                    if not emoji or emoji not in REACTIONS_SUIVIES:
                        continue
                    peer = getattr(reactor, 'peer_id', None)
                    user_id = getattr(peer, 'user_id', None)
                    if not user_id:
                        continue
                    key = (msg_id, user_id, emoji)
                    if key in notified_reactions:
                        continue
                    notified_reactions.add(key)
                    if len(notified_reactions) > 2000:
                        notified_reactions = set(list(notified_reactions)[-1000:])
                    try:
                        user = await client.get_entity(user_id)
                        first = getattr(user, 'first_name', '') or ''
                        last  = getattr(user, 'last_name',  '') or ''
                        name  = f"{first} {last}".strip() or f"@{getattr(user, 'username', user_id)}"
                    except Exception:
                        name = f"ID#{user_id}"
                    if ADMIN_ID and ADMIN_ID != 0:
                        admin_entity = await client.get_entity(ADMIN_ID)
                        await client.send_message(
                            admin_entity,
                            "🔔 **Réaction détectée**\n"
                            f"👤 **{name}** a réagi avec **{emoji}**\n"
                            f"📌 Prédiction jeu **#{game_number}**",
                            parse_mode='markdown'
                        )
                        logger.info(f"🔔 Réaction {emoji} de {name} sur prédiction #{game_number}")
                except Exception as e:
                    logger.info(f"⚠️ Réaction ignorée: {e}")
            return

        # ── Cas 2 : canal broadcast — recent_reactors vide, on notifie par comptage ──
        results = getattr(reactions, 'results', None) or []
        summary_parts = []
        for r in results:
            reaction_obj = getattr(r, 'reaction', None)
            emoji = getattr(reaction_obj, 'emoticon', None)
            count = getattr(r, 'count', 0)
            if emoji and count > 0 and emoji in REACTIONS_SUIVIES:
                summary_parts.append(f"{emoji} ×{count}")

        if not summary_parts:
            return

        # Clé de déduplication basée sur l'état total des réactions
        state_key = (msg_id, tuple(sorted(summary_parts)))
        if state_key in notified_reactions:
            return
        notified_reactions.add(state_key)
        if len(notified_reactions) > 2000:
            notified_reactions = set(list(notified_reactions)[-1000:])

        if ADMIN_ID and ADMIN_ID != 0:
            admin_entity = await client.get_entity(ADMIN_ID)
            await client.send_message(
                admin_entity,
                "🔔 **Réaction sur canal** (broadcast)\n"
                f"📌 Prédiction jeu **#{game_number}**\n"
                f"{'  '.join(summary_parts)}",
                parse_mode='markdown'
            )
            logger.info(f"🔔 Réaction canal sur prédiction #{game_number}: {' '.join(summary_parts)}")

    except Exception as e:
        logger.info(f"⚠️ on_reaction_event: {e}")


# ============================================================================
# MENU BOUTONS — INTERFACE INLINE KEYBOARD ADMIN
# ============================================================================

def _fake_ev(chat_id: int, cmd_text: str):
    """Crée un faux événement pour appeler les handlers de commandes depuis les boutons."""
    class _FE:
        is_group   = False
        is_channel = False
        async def respond(self, text, **kw):
            await client.send_message(self._cid, text, **kw)
    fe = _FE()
    fe.sender_id = ADMIN_ID
    fe._cid      = chat_id
    fe.chat_id   = chat_id
    fe.message   = type('M', (), {'message': cmd_text})()
    return fe


def _btns_main():
    return [
        [Button.inline("⚙️ Configuration",   b"cfg"), Button.inline("📊 Compteurs",    b"cmp")],
        [Button.inline("📋 Prédictions",      b"prd"), Button.inline("📡 Canaux",       b"cnx")],
        [Button.inline("📈 Analyse",          b"anl"), Button.inline("🛠️ Outils",       b"ool")],
    ]


def _btns_cfg():
    return [
        [Button.inline(f"⏭️  df = {PREDICTION_DF}   [modifier]",         b"df_s")],
        [Button.inline(f"📏  gap = {MIN_GAP_BETWEEN_PREDICTIONS}   [modifier]", b"gp_s")],
        [Button.inline("⏰  Heures de prédiction",                        b"hrs")],
        [Button.inline("⬅️  Retour",                                      b"mn")],
    ]


def _btns_hrs():
    return [
        [Button.inline("👁  Voir plages actives",   b"h_v"),  Button.inline("➕  Ajouter HH-HH", b"h_a")],
        [Button.inline("❌  Supprimer une plage",   b"h_d"),  Button.inline("🗑  Tout effacer",   b"h_c")],
        [Button.inline("⬅️  Config",                b"cfg")],
    ]


def _btns_cmp():
    return [
        [Button.inline("C2 — Absences préd.",  b"c2"), Button.inline("C4 — Longues abs.", b"c4")],
        [Button.inline("C5 — Patterns",        b"c5"), Button.inline("C13 — Stratégie",   b"c6")],
        [Button.inline("C7 — Présences cons.", b"c7"), Button.inline("C8 — Absences mir.", b"c8")],
        [Button.inline("📊  Stats C1",          b"st_v")],
        [Button.inline("⬅️  Retour",            b"mn")],
    ]


def _btns_c2():
    s = "✅ ON" if compteur2_active else "❌ OFF"
    return [
        [Button.inline(f"📊  Voir statut  ({s})",            b"c2_v")],
        [Button.inline("✅  Activer",  b"c2_on"), Button.inline("❌  Désactiver", b"c2_off")],
        [Button.inline(f"⚙️  Seuil B  (actuel: {compteur2_seuil_B})", b"c2_b"),
         Button.inline("🔄  Reset",    b"c2_rs")],
        [Button.inline("⬅️  Compteurs", b"cmp")],
    ]


def _btns_c4():
    return [
        [Button.inline("📊  Voir statut",                          b"c4_v")],
        [Button.inline("📄  PDF",  b"c4_p"), Button.inline("🔄  Reset", b"c4_r")],
        [Button.inline(f"⚙️  Seuil  (actuel: {COMPTEUR4_THRESHOLD})", b"c4_s")],
        [Button.inline("⬅️  Compteurs", b"cmp")],
    ]


def _btns_c7():
    return [
        [Button.inline("📊  Voir statut",                            b"c7_v")],
        [Button.inline("📄  PDF",  b"c7_p"), Button.inline("🔄  Reset", b"c7_r")],
        [Button.inline(f"⚙️  Seuil  (actuel: {COMPTEUR7_THRESHOLD})", b"c7_s")],
        [Button.inline("⬅️  Compteurs", b"cmp")],
    ]


def _btns_c8():
    return [
        [Button.inline("📊  Voir statut",                           b"c8_v")],
        [Button.inline("📄  PDF",  b"c8_p"), Button.inline("🔄  Reset", b"c8_r")],
        [Button.inline("⬅️  Compteurs", b"cmp")],
    ]


def _btns_prd():
    return [
        [Button.inline("📋  15 dernières raisons", b"rz_l"), Button.inline("📋  Raison jeu #N", b"rz_n")],
        [Button.inline("📄  PDF toutes raisons",   b"rz_p")],
        [Button.inline("⏳  Pending",  b"pnd"), Button.inline("📂  Queue", b"que"), Button.inline("📡  Status", b"sts")],
        [Button.inline("🔓  Débloquer urgence",    b"dbl"), Button.inline("🔄  Reset bot",        b"rst")],
        [Button.inline("⬅️  Retour", b"mn")],
    ]


def _btns_cnx():
    dist = f"✅ {DISTRIBUTION_CHANNEL_ID}" if DISTRIBUTION_CHANNEL_ID else "❌ inactif"
    c2ch = f"✅ {COMPTEUR2_CHANNEL_ID}"    if COMPTEUR2_CHANNEL_ID    else "❌ inactif"
    c3ch = f"✅ {PREDICTION_CHANNEL_ID3}"  if PREDICTION_CHANNEL_ID3  else "❌ inactif"
    c4ch = f"✅ {PREDICTION_CHANNEL_ID4}"  if PREDICTION_CHANNEL_ID4  else "❌ inactif"
    return [
        [Button.inline("📡  Voir config canaux",                    b"cn_v")],
        [Button.inline(f"📡  Canal 3 (redirect) : {c3ch}",         b"cn_3m")],
        [Button.inline("   ✏️  Modifier ID", b"cn_3s"), Button.inline("   ❌  Désactiver", b"cn_3o")],
        [Button.inline(f"📡  Canal 4 (redirect) : {c4ch}",         b"cn_4m")],
        [Button.inline("   ✏️  Modifier ID", b"cn_4s"), Button.inline("   ❌  Désactiver", b"cn_4o")],
        [Button.inline(f"🎯  Distribution : {dist}",                b"cn_dm")],
        [Button.inline("   ✏️  Modifier ID", b"cn_ds"), Button.inline("   ❌  Désactiver", b"cn_do")],
        [Button.inline(f"📊  Compteur2 : {c2ch}",                   b"cn_cm")],
        [Button.inline("   ✏️  Modifier ID", b"cn_cs"), Button.inline("   ❌  Désactiver", b"cn_co")],
        [Button.inline("⬅️  Retour", b"mn")],
    ]


def _btns_anl():
    fav_state = "✅ ON" if heures_favorables_active else "❌ OFF"
    return [
        [Button.inline("🤖  Stratégie auto",   b"strat_v"), Button.inline("🔬  Raison2",       b"r2_v")],
        [Button.inline("🔬  Raison2 P1",        b"r2_p1"),   Button.inline("🔬  P2",            b"r2_p2"),  Button.inline("🔬  P3", b"r2_p3")],
        [Button.inline("📉  PDF Perdus",        b"pd_v"),    Button.inline("📊  Comparaison",   b"cmp_v")],
        [Button.inline(f"⭐  Heures favorables  ({fav_state})", b"fv_v")],
        [Button.inline("✅  Fav ON", b"fv_on"), Button.inline("❌  Fav OFF", b"fv_off"),
         Button.inline("📤  → Canal", b"fv_c")],
        [Button.inline("📈  Bilan actuel",      b"bl_v"),    Button.inline("📈  Maintenant",    b"bl_n")],
        [Button.inline("⬅️  Retour", b"mn")],
    ]


def _btns_ool():
    return [
        [Button.inline("📖  Mode emploi",      b"em_v"), Button.inline("💰  Seuils B",     b"bv")],
        [Button.inline("🖼  Panneaux",          b"pn_v"), Button.inline("✅  Vérifier",     b"vr_v")],
        [Button.inline("🧪  Test prédiction #N", b"tp")],
        [Button.inline("⬅️  Retour", b"mn")],
    ]


async def cmd_menu(event):
    """Affiche le menu principal avec boutons inline."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    await event.respond("🤖 **BACCARAT AI — Menu principal**\nChoisissez une section :", buttons=_btns_main())


async def handle_callback(event):
    """Gestionnaire central de tous les boutons inline."""
    global PREDICTION_DF, MIN_GAP_BETWEEN_PREDICTIONS, PREDICTION_HOURS
    global compteur2_active, compteur2_seuil_B, compteur2_seuil_B_per_suit
    global COMPTEUR4_THRESHOLD, COMPTEUR7_THRESHOLD, COMPTEUR8_THRESHOLD
    global DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID, heures_favorables_active
    global compteur4_trackers, compteur4_current, compteur4_events
    global compteur7_current, compteur8_current
    global COMPTEUR13_MIRROR, COMPTEUR13_THRESHOLD, COMPTEUR13_SKIP
    global auto_strategy_revert, hourly_pending_auto

    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.answer("🔒 Admin uniquement", alert=True)
        return

    data = event.data.decode('utf-8')
    cid  = event.chat_id

    try:
        # ── Navigation principale ─────────────────────────────────────────────
        if data == 'mn':
            await event.edit("🤖 **BACCARAT AI — Menu principal**\nChoisissez une section :", buttons=_btns_main())
            await event.answer()

        elif data == 'cfg':
            await event.edit("⚙️ **CONFIGURATION**", buttons=_btns_cfg())
            await event.answer()

        elif data == 'hrs':
            now     = datetime.now()
            allowed = "✅ OUI" if is_prediction_time_allowed() else "❌ NON"
            txt = ("⏰ **HEURES DE PRÉDICTION**\n"
                   f"Heure actuelle : **{now.strftime('%H:%M')}**  |  Autorisé : {allowed}\n"
                   f"Plages actives : {format_hours_config()}")
            await event.edit(txt, buttons=_btns_hrs())
            await event.answer()

        elif data == 'cmp':
            await event.edit("📊 **COMPTEURS** — Choisissez :", buttons=_btns_cmp())
            await event.answer()

        elif data == 'prd':
            await event.edit("📋 **PRÉDICTIONS**", buttons=_btns_prd())
            await event.answer()

        elif data == 'cnx':
            await event.edit("📡 **CANAUX**", buttons=_btns_cnx())
            await event.answer()

        elif data == 'anl':
            await event.edit("📈 **ANALYSE**", buttons=_btns_anl())
            await event.answer()

        elif data == 'ool':
            await event.edit("🛠️ **OUTILS**", buttons=_btns_ool())
            await event.answer()

        # ── Annulation de l'auto-stratégie ────────────────────────────────────
        elif data == 'cancel_auto_strat':
            if not auto_strategy_revert:
                await event.answer("Aucune stratégie auto à annuler.", alert=True)
                return

            # Restaurer les paramètres précédents
            COMPTEUR13_MIRROR.clear()
            COMPTEUR13_MIRROR.update(auto_strategy_revert['mirror'])
            COMPTEUR13_THRESHOLD = auto_strategy_revert['wx']
            COMPTEUR13_SKIP      = auto_strategy_revert.get('df_sim', 1)
            compteur2_seuil_B    = auto_strategy_revert['b']
            for _s in ALL_SUITS:
                compteur2_seuil_B_per_suit[_s] = auto_strategy_revert['b_per_suit'].get(_s, auto_strategy_revert['b'])

            logger.info(
                f"🔙 Auto-stratégie annulée — restauré : miroir={dict(COMPTEUR13_MIRROR)} "
                f"wx={COMPTEUR13_THRESHOLD} B={compteur2_seuil_B} df+{COMPTEUR13_SKIP}"
            )

            prev_name   = auto_strategy_revert.get('name_prev', '?')
            prev_df_sim = auto_strategy_revert.get('df_sim', 1)
            auto_strategy_revert = {}

            await event.edit(
                "🔙 **Stratégie annulée** — paramètres précédents restaurés.\n"
                f"  Miroir : **{prev_name}** · df+{prev_df_sim}\n"
                f"  wx C13 : **{COMPTEUR13_THRESHOLD}** | B C2 : **{compteur2_seuil_B}**",
                buttons=None,
            )
            await event.answer("✅ Paramètres précédents restaurés.")

        # ── Confirmation / Ignore proposition horaire auto ─────────────────────
        elif data == 'confirm_hourly':
            if not hourly_pending_auto:
                await event.answer("❌ Aucune proposition en attente.", alert=True)
                return

            ba = hourly_pending_auto['best_auto']
            heure_prop = hourly_pending_auto.get('heure', '?')

            # Sauvegarder l'état actuel pour annulation éventuelle
            auto_strategy_revert = {
                'mirror':     dict(COMPTEUR13_MIRROR),
                'wx':         COMPTEUR13_THRESHOLD,
                'b':          compteur2_seuil_B,
                'df_sim':     COMPTEUR13_SKIP,
                'b_per_suit': dict(compteur2_seuil_B_per_suit),
                'name_prev':  next(
                    (c['name'] for c in GLOBAL_COMBOS if c['mirror'] == dict(COMPTEUR13_MIRROR)),
                    'inconnu'
                ),
                'msg_id': None,
            }

            # Appliquer la stratégie
            new_df_sim = ba.get('df_sim', 1)
            COMPTEUR13_MIRROR.clear()
            COMPTEUR13_MIRROR.update(ba['mirror'])
            COMPTEUR13_THRESHOLD = ba['wx']
            COMPTEUR13_SKIP      = max(0, new_df_sim - PREDICTION_DF)
            compteur2_seuil_B    = ba['b']
            for _s in ALL_SUITS:
                compteur2_seuil_B_per_suit[_s] = ba['b']

            db.db_schedule(save_runtime_config())
            logger.info(
                f"✅ Stratégie horaire confirmée par l'admin : {ba['name']} "
                f"wx={ba['wx']} B={ba['b']} df+{new_df_sim}"
            )

            # Mettre à jour la décision dans l'historique DB
            async def _update_history_confirmed(h: str):
                try:
                    history = await db.db_load_kv('strategy_history') or []
                    for e in reversed(history):
                        if e.get('heure') == h and e.get('decision') == 'en_attente':
                            e['decision'] = 'confirmée'
                            break
                    await db.db_save_kv('strategy_history', history)
                except Exception as ex:
                    logger.error(f"❌ update history confirmed: {ex}")
            db.db_schedule(_update_history_confirmed(heure_prop))

            hourly_pending_auto = None

            await event.edit(
                "✅ **Stratégie confirmée et appliquée !**\n\n"
                f"  Miroir : **{ba['name']}** ({ba['disp']})\n"
                f"  wx C13 : **{ba['wx']}** | B C2 : **{ba['b']}** | df+{new_df_sim}\n"
                f"  Score  : **{ba['score']:+d}** (✅{ba['wins']} ❌{ba['losses']} / {ba['total']})\n\n"
                "_Appuie sur Annuler dans la notification précédente pour revenir en arrière si besoin._",
                buttons=[[Button.inline("❌ Annuler cette stratégie", b"cancel_auto_strat")]],
            )
            await event.answer("✅ Stratégie appliquée !")

        elif data == 'ignore_hourly':
            if not hourly_pending_auto:
                await event.answer("Aucune proposition en attente.", alert=True)
                return

            heure_prop = hourly_pending_auto.get('heure', '?')
            ba_name    = hourly_pending_auto.get('best_auto', {}).get('name', '?')

            async def _update_history_ignored(h: str):
                try:
                    history = await db.db_load_kv('strategy_history') or []
                    for e in reversed(history):
                        if e.get('heure') == h and e.get('decision') == 'en_attente':
                            e['decision'] = 'ignorée'
                            break
                    await db.db_save_kv('strategy_history', history)
                except Exception as ex:
                    logger.error(f"❌ update history ignored: {ex}")
            db.db_schedule(_update_history_ignored(heure_prop))

            hourly_pending_auto = None
            logger.info(f"❌ Proposition horaire {heure_prop} ignorée par l'admin.")

            await event.edit(
                f"❌ **Proposition ignorée** ({heure_prop} — {ba_name})\n"
                "_La stratégie actuelle reste inchangée._",
                buttons=None,
            )
            await event.answer("❌ Proposition ignorée.")

        elif data == 'send_formation_canal':
            await event.answer("📊 Rapport envoyé en privé…")
            await _send_formation_to_canal()
            try:
                await event.edit(
                    event.message.text + "\n\n✅ _Rapport détaillé reçu en privé._",
                    buttons=None,
                    parse_mode='markdown',
                )
            except Exception:
                pass

        # ── Configuration ─────────────────────────────────────────────────────
        elif data == 'df_s':
            pending_input[event.sender_id] = {'action': 'set_d', 'cid': cid}
            await event.answer()
            await client.send_message(cid, f"⏭️ **Modifier df**\nValeur actuelle : **{PREDICTION_DF}**\nEnvoyez la nouvelle valeur (1-10) :")

        elif data == 'gp_s':
            pending_input[event.sender_id] = {'action': 'set_gap', 'cid': cid}
            await event.answer()
            await client.send_message(cid, f"📏 **Modifier gap**\nValeur actuelle : **{MIN_GAP_BETWEEN_PREDICTIONS}**\nEnvoyez la nouvelle valeur (2-10) :")

        elif data == 'h_v':
            now     = datetime.now()
            allowed = "✅ OUI" if is_prediction_time_allowed() else "❌ NON"
            txt = (f"⏰ **Plages actives**\nHeure : {now.strftime('%H:%M')}  |  Autorisé : {allowed}\n{format_hours_config()}")
            await event.answer(txt, alert=True)

        elif data == 'h_a':
            pending_input[event.sender_id] = {'action': 'h_add', 'cid': cid}
            await event.answer()
            await client.send_message(cid, "➕ **Ajouter plage horaire**\nFormat **HH-HH** (ex: `18-23`) :")

        elif data == 'h_d':
            pending_input[event.sender_id] = {'action': 'h_del', 'cid': cid}
            await event.answer()
            await client.send_message(cid, f"❌ **Supprimer plage**\nPlages actuelles : {format_hours_config()}\nFormat **HH-HH** (ex: `18-23`) :")

        elif data == 'h_c':
            PREDICTION_HOURS.clear()
            await event.answer("✅ Toutes les plages supprimées — prédictions 24h/24", alert=True)

        # ── Compteur 2 ────────────────────────────────────────────────────────
        elif data == 'c2':
            s = "✅ ON" if compteur2_active else "❌ OFF"
            await event.edit(f"📊 **COMPTEUR 2** — Statut : {s} | Seuil B : {compteur2_seuil_B}", buttons=_btns_c2())
            await event.answer()

        elif data == 'c2_v':
            await event.answer()
            await cmd_compteur2(_fake_ev(cid, '/compteur2'))

        elif data == 'c2_on':
            compteur2_active = True
            await event.answer("✅ Compteur2 activé", alert=True)

        elif data == 'c2_off':
            compteur2_active = False
            await event.answer("❌ Compteur2 désactivé", alert=True)

        elif data == 'c2_rs':
            for tr in compteur2_trackers.values():
                tr.counter = 0
            await event.answer("🔄 Compteur2 reset", alert=True)

        elif data == 'c2_b':
            pending_input[event.sender_id] = {'action': 'set_c2b', 'cid': cid}
            await event.answer()
            await client.send_message(cid, f"⚙️ **Seuil B — Compteur2**\nValeur actuelle : **{compteur2_seuil_B}**\nEnvoyez la nouvelle valeur (2-10) :")

        # ── Compteur 4 ────────────────────────────────────────────────────────
        elif data == 'c4':
            await event.edit(f"🔴 **COMPTEUR 4** — Seuil : {COMPTEUR4_THRESHOLD}", buttons=_btns_c4())
            await event.answer()

        elif data == 'c4_v':
            await event.answer()
            await cmd_compteur4(_fake_ev(cid, '/compteur4'))

        elif data == 'c4_p':
            await event.answer("📄 Génération PDF C4…")
            await send_compteur4_pdf()

        elif data == 'c4_r':
            for suit in ALL_SUITS:
                compteur4_trackers[suit] = 0
                compteur4_current[suit]  = {'count': 0, 'start_game': None, 'start_time': None, 'alerted': False}
            compteur4_events.clear()
            save_compteur4_data()
            await event.answer("🔄 Compteur4 reset", alert=True)

        elif data == 'c4_s':
            pending_input[event.sender_id] = {'action': 'set_c4s', 'cid': cid}
            await event.answer()
            await client.send_message(cid, f"⚙️ **Seuil — Compteur4**\nValeur actuelle : **{COMPTEUR4_THRESHOLD}**\nEnvoyez la nouvelle valeur (5-50) :")

        # ── Compteur 5 ────────────────────────────────────────────────────────
        elif data == 'c5':
            await event.answer("📊 Chargement C5…")
            await cmd_compteur5(_fake_ev(cid, '/compteur5'))

        # ── Compteur 7 ────────────────────────────────────────────────────────
        elif data == 'c7':
            await event.edit(f"🟢 **COMPTEUR 7** — Seuil : {COMPTEUR7_THRESHOLD}", buttons=_btns_c7())
            await event.answer()

        elif data == 'c7_v':
            await event.answer()
            await cmd_compteur7(_fake_ev(cid, '/compteur7'))

        elif data == 'c7_p':
            await event.answer("📄 Génération PDF C7…")
            await send_compteur7_pdf()

        elif data == 'c7_r':
            for suit in ALL_SUITS:
                compteur7_current[suit] = {'count': 0, 'start_game': None, 'start_time': None}
            save_compteur7_data()
            await event.answer("🔄 Compteur7 reset", alert=True)

        elif data == 'c7_s':
            pending_input[event.sender_id] = {'action': 'set_c7s', 'cid': cid}
            await event.answer()
            await client.send_message(cid, f"⚙️ **Seuil — Compteur7**\nValeur actuelle : **{COMPTEUR7_THRESHOLD}**\nEnvoyez la nouvelle valeur (3-20) :")

        # ── Compteur 8 ────────────────────────────────────────────────────────
        elif data == 'c8':
            await event.edit(f"🔴 **COMPTEUR 8** — Seuil : {COMPTEUR8_THRESHOLD}", buttons=_btns_c8())
            await event.answer()

        elif data == 'c8_v':
            await event.answer()
            await cmd_compteur8(_fake_ev(cid, '/compteur8'))

        elif data == 'c8_p':
            await event.answer("📄 Génération PDF C8…")
            await send_compteur8_pdf()

        elif data == 'c8_r':
            for suit in ALL_SUITS:
                compteur8_current[suit] = {'count': 0, 'start_game': None, 'start_time': None}
            save_compteur8_data()
            await event.answer("🔄 Compteur8 reset", alert=True)

        # ── Prédictions ───────────────────────────────────────────────────────
        elif data == 'rz_l':
            await event.answer("📋 Chargement…")
            await cmd_raison(_fake_ev(cid, '/raison'))

        elif data == 'rz_p':
            await event.answer("📄 Génération PDF raisons…")
            await cmd_raison(_fake_ev(cid, '/raison pdf'))

        elif data == 'rz_n':
            pending_input[event.sender_id] = {'action': 'raison_n', 'cid': cid}
            await event.answer()
            await client.send_message(cid, "📋 **Raison pour un jeu précis**\nEnvoyez le numéro du jeu :")

        elif data == 'pnd':
            await event.answer("⏳ Chargement…")
            await cmd_pending(_fake_ev(cid, '/pending'))

        elif data == 'que':
            await event.answer("📂 Chargement…")
            await cmd_queue(_fake_ev(cid, '/queue'))

        elif data == 'sts':
            await event.answer("📡 Chargement…")
            await cmd_status(_fake_ev(cid, '/status'))

        elif data == 'dbl':
            await event.answer("🔓 Déblocage…")
            await cmd_debloquer(_fake_ev(cid, '/debloquer'))

        elif data == 'rst':
            await event.answer("🔄 Reset en cours…")
            await client.send_message(cid, "🔄 Reset en cours…")
            await perform_full_reset("Reset via menu boutons")
            await client.send_message(cid, "✅ Reset effectué !")

        # ── Canaux ────────────────────────────────────────────────────────────
        elif data == 'cn_v':
            dist = f"`{DISTRIBUTION_CHANNEL_ID}`" if DISTRIBUTION_CHANNEL_ID else "❌ inactif"
            c2ch = f"`{COMPTEUR2_CHANNEL_ID}`"    if COMPTEUR2_CHANNEL_ID    else "❌ inactif"
            c3ch = f"`{PREDICTION_CHANNEL_ID3}`"  if PREDICTION_CHANNEL_ID3  else "❌ inactif"
            c4ch = f"`{PREDICTION_CHANNEL_ID4}`"  if PREDICTION_CHANNEL_ID4  else "❌ inactif"
            txt  = ("📡 **CONFIGURATION DES CANAUX**\n\n"
                    f"📤 Canal 1 (principal) : `{PREDICTION_CHANNEL_ID}`\n"
                    f"📤 Canal 2 (principal) : `{PREDICTION_CHANNEL_ID2}`\n"
                    f"📡 Canal 3 (redirect)  : {c3ch}\n"
                    f"📡 Canal 4 (redirect)  : {c4ch}\n"
                    f"🎯 Distribution        : {dist}\n"
                    f"📊 Compteur2           : {c2ch}\n\n"
                    "Canaux 3 et 4 reçoivent toutes les prédictions + résultats.")
            await event.answer()
            await client.send_message(cid, txt)

        elif data in ('cn_dm', 'cn_cm', 'cn_3m', 'cn_4m'):
            await event.answer()

        elif data == 'cn_3s':
            pending_input[event.sender_id] = {'action': 'set_cn_3', 'cid': cid}
            await event.answer()
            cur = f"`{PREDICTION_CHANNEL_ID3}`" if PREDICTION_CHANNEL_ID3 else "inactif"
            await client.send_message(cid,
                "📡 **Canal 3 — Redirect prédictions + résultats**\n"
                f"Actuel : {cur}\n\n"
                "Envoyez le nouvel ID de canal (nombre négatif, ex: `-1001234567890`).\n"
                "⚠️ Le bot doit être **admin** dans ce canal."
            )

        elif data == 'cn_3o':
            old = PREDICTION_CHANNEL_ID3
            PREDICTION_CHANNEL_ID3 = None
            await event.answer(f"❌ Canal 3 désactivé (était : {old})", alert=True)
            db.db_schedule(save_runtime_config())

        elif data == 'cn_4s':
            pending_input[event.sender_id] = {'action': 'set_cn_4', 'cid': cid}
            await event.answer()
            cur = f"`{PREDICTION_CHANNEL_ID4}`" if PREDICTION_CHANNEL_ID4 else "inactif"
            await client.send_message(cid,
                "📡 **Canal 4 — Redirect prédictions + résultats**\n"
                f"Actuel : {cur}\n\n"
                "Envoyez le nouvel ID de canal (nombre négatif, ex: `-1001234567890`).\n"
                "⚠️ Le bot doit être **admin** dans ce canal."
            )

        elif data == 'cn_4o':
            old = PREDICTION_CHANNEL_ID4
            PREDICTION_CHANNEL_ID4 = None
            await event.answer(f"❌ Canal 4 désactivé (était : {old})", alert=True)
            db.db_schedule(save_runtime_config())

        elif data == 'cn_ds':
            pending_input[event.sender_id] = {'action': 'set_cn_dist', 'cid': cid}
            await event.answer()
            cur = f"`{DISTRIBUTION_CHANNEL_ID}`" if DISTRIBUTION_CHANNEL_ID else "inactif"
            await client.send_message(cid, f"🎯 **Canal Distribution** (actuel : {cur})\nEnvoyez le nouvel ID de canal (nombre négatif) :")

        elif data == 'cn_do':
            old = DISTRIBUTION_CHANNEL_ID
            DISTRIBUTION_CHANNEL_ID = None
            await event.answer(f"❌ Canal distribution désactivé (était : {old})", alert=True)
            db.db_schedule(save_runtime_config())

        elif data == 'cn_cs':
            pending_input[event.sender_id] = {'action': 'set_cn_c2', 'cid': cid}
            await event.answer()
            cur = f"`{COMPTEUR2_CHANNEL_ID}`" if COMPTEUR2_CHANNEL_ID else "inactif"
            await client.send_message(cid, f"📊 **Canal Compteur2** (actuel : {cur})\nEnvoyez le nouvel ID de canal (nombre négatif) :")

        elif data == 'cn_co':
            old = COMPTEUR2_CHANNEL_ID
            COMPTEUR2_CHANNEL_ID = None
            await event.answer(f"❌ Canal compteur2 désactivé (était : {old})", alert=True)
            db.db_schedule(save_runtime_config())

        # ── Analyse ───────────────────────────────────────────────────────────
        elif data == 'strat_v':
            await event.answer("🤖 Stratégie en cours…")
            await cmd_strategie(_fake_ev(cid, '/strategie'))

        elif data == 'r2_v':
            await event.answer("🔬 Raison2…")
            await cmd_raison2(_fake_ev(cid, '/raison2'))

        elif data == 'r2_p1':
            await event.answer("🔬 Raison2 P1…")
            await cmd_raison2(_fake_ev(cid, '/raison2 P1'))

        elif data == 'r2_p2':
            await event.answer("🔬 Raison2 P2…")
            await cmd_raison2(_fake_ev(cid, '/raison2 P2'))

        elif data == 'r2_p3':
            await event.answer("🔬 Raison2 P3…")
            await cmd_raison2(_fake_ev(cid, '/raison2 P3'))

        elif data == 'pd_v':
            await event.answer("📄 Génération PDF perdus…")
            await cmd_perdus(_fake_ev(cid, '/perdus'))

        elif data == 'fv_v':
            await event.answer("⭐ Chargement…")
            await cmd_favorables(_fake_ev(cid, '/favorables'))

        elif data == 'fv_on':
            heures_favorables_active = True
            now    = datetime.now()
            next_h = (now.hour + (3 - now.hour % 3)) % 24
            await event.answer(f"✅ Heures favorables ON — prochain : {next_h:02d}h00", alert=True)
            db.db_schedule(save_runtime_config())

        elif data == 'fv_off':
            heures_favorables_active = False
            await event.answer("🔕 Heures favorables OFF", alert=True)
            db.db_schedule(save_runtime_config())

        elif data == 'fv_c':
            await event.answer("📤 Envoi dans le canal…")
            await cmd_favorables(_fake_ev(cid, '/favorables canal'))

        elif data == 'cmp_v':
            await event.answer("📊 Génération comparaison…")
            await cmd_comparaison(_fake_ev(cid, '/comparaison'))

        elif data == 'bl_v':
            await event.answer("📈 Génération bilan…")
            await cmd_bilan(_fake_ev(cid, '/bilan'))

        elif data == 'bl_n':
            await event.answer("📈 Envoi bilan maintenant…")
            await cmd_bilan(_fake_ev(cid, '/bilan now'))

        elif data == 'st_v':
            await event.answer("📊 Génération stats C1…")
            await cmd_stats(_fake_ev(cid, '/stats'))

        # ── Outils ────────────────────────────────────────────────────────────
        elif data == 'bv':
            await event.answer("💰 Chargement…")
            await cmd_b(_fake_ev(cid, '/b'))

        elif data == 'pn_v':
            await event.answer("🖼 Chargement…")
            await cmd_panneaux(_fake_ev(cid, '/panneaux'))

        elif data == 'vr_v':
            await event.answer("✅ Vérification…")
            await cmd_verifier(_fake_ev(cid, '/verifier'))

        elif data == 'tp':
            pending_input[event.sender_id] = {'action': 'testpred', 'cid': cid}
            await event.answer()
            await client.send_message(cid, "🧪 **Test prédiction**\nEnvoyez le numéro du jeu cible (ex : `1080`) :")

        # ── Mode emploi ───────────────────────────────────────────────────────
        elif data == 'em_v':
            await event.answer("📖 Chargement mode emploi…")
            await cmd_help(_fake_ev(cid, '/help'))

        # ── C6 → redirigé vers stratégie C13 (Raison2) ───────────────────────
        elif data == 'c6':
            await event.answer("📊 Chargement stratégie C13…")
            await cmd_raison2(_fake_ev(cid, '/raison2'))

        # ── Infos canaux (boutons titre — affichent statut en popup) ──────────
        elif data == 'cn_3m':
            ch3 = PREDICTION_CHANNEL_ID3
            txt = f"📡 Canal 3 : {'✅ Actif — ID ' + str(ch3) if ch3 else '❌ Inactif'}"
            await event.answer(txt, alert=True)

        elif data == 'cn_4m':
            ch4 = PREDICTION_CHANNEL_ID4
            txt = f"📡 Canal 4 : {'✅ Actif — ID ' + str(ch4) if ch4 else '❌ Inactif'}"
            await event.answer(txt, alert=True)

        elif data == 'cn_dm':
            txt = f"🎯 Distribution : {'✅ Actif — ID ' + str(DISTRIBUTION_CHANNEL_ID) if DISTRIBUTION_CHANNEL_ID else '❌ Inactif'}"
            await event.answer(txt, alert=True)

        elif data == 'cn_cm':
            txt = f"📊 Compteur2 : {'✅ Actif — ID ' + str(COMPTEUR2_CHANNEL_ID) if COMPTEUR2_CHANNEL_ID else '❌ Inactif'}"
            await event.answer(txt, alert=True)

        else:
            await event.answer()

    except Exception as e:
        logger.error(f"❌ Erreur handle_callback [{data}]: {e}", exc_info=True)
        try:
            await event.answer(f"❌ Erreur: {e}", alert=True)
        except Exception:
            pass


async def handle_admin_input(event):
    """Intercepte la saisie de valeurs numériques/texte après clic sur un bouton."""
    global PREDICTION_DF, MIN_GAP_BETWEEN_PREDICTIONS, PREDICTION_HOURS
    global compteur2_seuil_B, compteur2_seuil_B_per_suit
    global COMPTEUR4_THRESHOLD, COMPTEUR7_THRESHOLD
    global DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID

    if event.is_group or event.is_channel:
        return
    if event.sender_id not in pending_input:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        return
    text = event.message.message.strip()
    if text.startswith('/'):
        pending_input.pop(event.sender_id, None)
        return

    state  = pending_input.pop(event.sender_id)
    action = state['action']

    try:
        if action == 'set_df':
            val = int(text)
            if not 1 <= val <= 10:
                await event.respond("❌ df doit être entre 1 et 10")
                return
            old = PREDICTION_DF
            PREDICTION_DF = val
            await event.respond(f"✅ **df : {old} → {val}**\n_Prédit le jeu N+{val} à la fin de N._")

        elif action == 'set_gap':
            val = int(text)
            if not 2 <= val <= 10:
                await event.respond("❌ gap doit être entre 2 et 10")
                return
            old = MIN_GAP_BETWEEN_PREDICTIONS
            MIN_GAP_BETWEEN_PREDICTIONS = val
            await event.respond(f"✅ **gap : {old} → {val}**")

        elif action == 'h_add':
            if '-' not in text:
                await event.respond("❌ Format : HH-HH (ex : `18-23`)")
                return
            s_str, e_str = text.split('-', 1)
            s_h, e_h = int(s_str.strip()), int(e_str.strip())
            if not (0 <= s_h <= 23 and 0 <= e_h <= 23):
                await event.respond("❌ Heures entre 0 et 23")
                return
            PREDICTION_HOURS.append((s_h, e_h))
            await event.respond(f"✅ **Plage ajoutée : {s_h:02d}h → {e_h:02d}h**\nPlages : {format_hours_config()}")

        elif action == 'h_del':
            if '-' not in text:
                await event.respond("❌ Format : HH-HH")
                return
            s_str, e_str = text.split('-', 1)
            s_h, e_h = int(s_str.strip()), int(e_str.strip())
            if (s_h, e_h) in PREDICTION_HOURS:
                PREDICTION_HOURS.remove((s_h, e_h))
                await event.respond(f"✅ **Plage supprimée : {s_h:02d}h → {e_h:02d}h**")
            else:
                await event.respond(f"❌ Plage {s_h:02d}h-{e_h:02d}h introuvable")

        elif action == 'set_c2b':
            val = int(text)
            if not 2 <= val <= 10:
                await event.respond("❌ B entre 2 et 10")
                return
            old_b = compteur2_seuil_B
            compteur2_seuil_B = val
            for s in ALL_SUITS:
                cur    = compteur2_seuil_B_per_suit.get(s, old_b)
                excess = cur - old_b
                compteur2_seuil_B_per_suit[s] = val + max(0, excess)
            await event.respond(f"✅ **Seuil B Compteur2 : {old_b} → {val}**")

        elif action == 'set_c4s':
            val = int(text)
            if not 5 <= val <= 50:
                await event.respond("❌ Seuil entre 5 et 50")
                return
            old = COMPTEUR4_THRESHOLD
            COMPTEUR4_THRESHOLD = val
            await event.respond(f"✅ **Seuil Compteur4 : {old} → {val}**")
            db.db_schedule(save_runtime_config())

        elif action == 'set_c7s':
            val = int(text)
            if not 3 <= val <= 20:
                await event.respond("❌ Seuil entre 3 et 20")
                return
            old = COMPTEUR7_THRESHOLD
            COMPTEUR7_THRESHOLD = val
            await event.respond(f"✅ **Seuil Compteur7 : {old} → {val}**")
            db.db_schedule(save_runtime_config())

        elif action == 'set_cn_3':
            global PREDICTION_CHANNEL_ID3
            try:
                new_id = int(text)
            except ValueError:
                await event.respond("❌ ID invalide — entrez un nombre négatif, ex: `-1001234567890`")
                return
            entity = await resolve_channel(new_id)
            if not entity:
                await event.respond(f"❌ Canal `{new_id}` inaccessible — le bot est-il **admin** dans ce canal?")
                return
            old = PREDICTION_CHANNEL_ID3
            PREDICTION_CHANNEL_ID3 = new_id
            await event.respond(
                f"✅ **Canal 3 activé : {old or 'inactif'} → `{new_id}`**\n"
                "Toutes les prédictions + résultats seront redirigés vers ce canal."
            )
            db.db_schedule(save_runtime_config())

        elif action == 'set_cn_4':
            global PREDICTION_CHANNEL_ID4
            try:
                new_id = int(text)
            except ValueError:
                await event.respond("❌ ID invalide — entrez un nombre négatif, ex: `-1001234567890`")
                return
            entity = await resolve_channel(new_id)
            if not entity:
                await event.respond(f"❌ Canal `{new_id}` inaccessible — le bot est-il **admin** dans ce canal?")
                return
            old = PREDICTION_CHANNEL_ID4
            PREDICTION_CHANNEL_ID4 = new_id
            await event.respond(
                f"✅ **Canal 4 activé : {old or 'inactif'} → `{new_id}`**\n"
                "Toutes les prédictions + résultats seront redirigés vers ce canal."
            )
            db.db_schedule(save_runtime_config())

        elif action == 'set_cn_dist':
            new_id = int(text)
            if not await resolve_channel(new_id):
                await event.respond(f"❌ Canal `{new_id}` inaccessible")
                return
            old = DISTRIBUTION_CHANNEL_ID
            DISTRIBUTION_CHANNEL_ID = new_id
            await event.respond(f"✅ **Canal distribution : {old} → {new_id}**")
            db.db_schedule(save_runtime_config())

        elif action == 'set_cn_c2':
            new_id = int(text)
            if not await resolve_channel(new_id):
                await event.respond(f"❌ Canal `{new_id}` inaccessible")
                return
            old = COMPTEUR2_CHANNEL_ID
            COMPTEUR2_CHANNEL_ID = new_id
            await event.respond(f"✅ **Canal Compteur2 : {old} → {new_id}**")
            db.db_schedule(save_runtime_config())

        elif action == 'raison_n':
            if not text.isdigit():
                await event.respond("❌ Entrez un numéro de jeu valide (ex : `1062`)")
                return
            await cmd_raison(_fake_ev(event.chat_id, f'/raison {text}'))

        elif action == 'testpred':
            await cmd_testpred(_fake_ev(event.chat_id, f'/testpred {text}'))

    except ValueError:
        await event.respond("❌ Valeur invalide — entrez un nombre.")
    except Exception as e:
        await event.respond(f"❌ Erreur : {e}")


# ============================================================================
# SETUP ET DÉMARRAGE
# ============================================================================

def setup_handlers():
    # ── Saisie de valeurs (intercepté en priorité avant les commandes) ─────────
    client.add_event_handler(handle_admin_input, events.NewMessage(outgoing=False))
    # ── Boutons inline ─────────────────────────────────────────────────────────
    client.add_event_handler(handle_callback, events.CallbackQuery())
    # ── Menu principal ─────────────────────────────────────────────────────────
    client.add_event_handler(cmd_menu,      events.NewMessage(pattern=r'^/menu$'))
    # ── Commandes texte (toujours disponibles) ─────────────────────────────────
    client.add_event_handler(cmd_heures,    events.NewMessage(pattern=r'^/heures'))
    client.add_event_handler(cmd_df,        events.NewMessage(pattern=r'^/df'))
    client.add_event_handler(cmd_gap,       events.NewMessage(pattern=r'^/gap'))
    client.add_event_handler(cmd_canaux,    events.NewMessage(pattern=r'^/canaux'))
    client.add_event_handler(cmd_stats,     events.NewMessage(pattern=r'^/stats$'))
    client.add_event_handler(cmd_queue,     events.NewMessage(pattern=r'^/queue$'))
    client.add_event_handler(cmd_pending,   events.NewMessage(pattern=r'^/pending$'))
    client.add_event_handler(cmd_status,    events.NewMessage(pattern=r'^/status$'))
    client.add_event_handler(cmd_reset,     events.NewMessage(pattern=r'^/reset$'))
    client.add_event_handler(cmd_resetdb,   events.NewMessage(pattern=r'^/resetdb'))
    client.add_event_handler(cmd_debloquer, events.NewMessage(pattern=r'^/debloquer$'))
    client.add_event_handler(cmd_help,      events.NewMessage(pattern=r'^/help$'))
    client.add_event_handler(cmd_raison,    events.NewMessage(pattern=r'^/raison(?!2)'))
    client.add_event_handler(cmd_raison2,   events.NewMessage(pattern=r'^/raison2'))
    client.add_event_handler(cmd_perdus,    events.NewMessage(pattern=r'^/perdus$'))
    client.add_event_handler(cmd_bilan,     events.NewMessage(pattern=r'^/bilan'))
    client.add_event_handler(cmd_b,         events.NewMessage(pattern=r'^/b($|\s)'))
    client.add_event_handler(cmd_compteur2, events.NewMessage(pattern=r'^/compteur2'))
    client.add_event_handler(cmd_compteur4, events.NewMessage(pattern=r'^/compteur4'))
    client.add_event_handler(cmd_compteur5, events.NewMessage(pattern=r'^/compteur5'))
    client.add_event_handler(cmd_compteur7, events.NewMessage(pattern=r'^/compteur7'))
    client.add_event_handler(cmd_compteur8,  events.NewMessage(pattern=r'^/compteur8'))
    client.add_event_handler(cmd_compteur13, events.NewMessage(pattern=r'^/compteur13'))
    client.add_event_handler(cmd_strategie,           events.NewMessage(pattern=r'^/strategie$'))
    client.add_event_handler(cmd_historique_strategies, events.NewMessage(pattern=r'^/historique_strategies'))
    client.add_event_handler(cmd_formation,             events.NewMessage(pattern=r'^/formation(?!_)'))
    client.add_event_handler(cmd_sendformation,         events.NewMessage(pattern=r'^/sendformation'))
    client.add_event_handler(cmd_oui,        events.NewMessage(pattern=r'(?i)^oui\s*\d*$'))
    client.add_event_handler(cmd_compteur14, events.NewMessage(pattern=r'^/compteur14'))
    client.add_event_handler(cmd_comparaison, events.NewMessage(pattern=r'^/comparaison'))
    client.add_event_handler(cmd_favorables,  events.NewMessage(pattern=r'^/favorables'))
    client.add_event_handler(cmd_panneaux,    events.NewMessage(pattern=r'^/panneaux$'))
    client.add_event_handler(cmd_recherche,   events.NewMessage(pattern=r'^/recherche'))
    client.add_event_handler(cmd_concours,    events.NewMessage(pattern=r'^/concours$'))
    client.add_event_handler(cmd_testpred,    events.NewMessage(pattern=r'^/testpred'))
    client.add_event_handler(cmd_verifier,    events.NewMessage(pattern=r'^/verifier$'))
    client.add_event_handler(on_reaction_event, events.Raw(UpdateMessageReactions))


async def start_bot():
    global client, prediction_channel_ok

    # ── Initialiser PostgreSQL en premier pour charger la session persistée ──
    await db.init_db()

    # ── Rapport de santé DB au démarrage ─────────────────────────────────────
    if db.is_connected():
        _db_keys = [
            'runtime_config', 'bot_session', 'silent_combo_stats',
            'compteur4', 'compteur7', 'compteur8', 'compteur11', 'compteur14',
            'strategy_simulation', 'active_panel', 'concours_last_winner',
        ]
        _found, _missing = [], []
        for _k in _db_keys:
            _v = await db.db_load_kv(_k)
            (_found if _v else _missing).append(_k)
        _pending_count = len(await db.db_load_pending())
        logger.info(
            f"📋 DB startup — ✅ présents: {', '.join(_found) or 'aucun'} | "
            f"⚠️ absents: {', '.join(_missing) or 'aucun'} | "
            f"pending_predictions: {_pending_count}"
        )
    else:
        logger.error("❌ DB non connectée au démarrage — données en mémoire uniquement")

    # ── Charger la configuration runtime depuis la DB (canaux, seuils, écart…) ──
    await load_runtime_config()

    # ── Charger la session depuis la DB (aucune variable d'environnement requise) ──
    saved = await db.db_load_kv('bot_session')
    session_str = saved.get('session', '') if isinstance(saved, dict) else ''
    if session_str:
        logger.info("🔑 Session bot chargée depuis la DB")
    else:
        logger.info("🔑 Aucune session en DB — nouvelle authentification avec BOT_TOKEN")

    client = TelegramClient(
        StringSession(session_str),
        API_ID,
        API_HASH,
        connection_retries=10,
        retry_delay=3,
        auto_reconnect=True,
        request_retries=5,
    )

    try:
        await client.start(bot_token=BOT_TOKEN)

        # ── Sauvegarder la session en DB après connexion réussie ─────────────
        new_session = client.session.save()
        await db.db_save_kv('bot_session', {'session': new_session})
        logger.info("💾 Session bot sauvegardée en DB")

        setup_handlers()
        initialize_trackers()

        # Charger données persistantes depuis PostgreSQL (avec fallback JSON)
        await load_compteur4_data()
        await load_compteur7_data()
        await load_compteur8_data()
        await load_compteur14_data()
        await load_hourly_data()
        save_hourly_data()                # Persiste immédiatement en DB (migration JSON si besoin)
        await load_compteur11()           # Charge les perdus d'hier pour les rejouer aujourd'hui
        await load_pending_predictions()  # Reprend les prédictions en cours après redémarrage
        await load_prediction_history()   # Charge l'historique pour les heures favorables
        await load_strategy_simulation()  # Restaure la simulation silencieuse C13 (pour /raison2)
        await load_silent_combo_stats()   # Charge les 216 trackers indépendants (C13+C2 par combo)

        # Charger le vainqueur du dernier concours (comparaison inter-cycles)
        global concours_last_winner, concours_last_pct
        _last = await db.db_load_kv('concours_last_winner')
        if isinstance(_last, dict) and _last.get('suit') in SUIT_NAMES_FR:
            concours_last_winner = _last['suit']
            concours_last_pct    = float(_last.get('pct', 0.0))
            logger.info(f"🏆 Dernier vainqueur concours chargé : {concours_last_winner} ({concours_last_pct:.1f}%)")
        else:
            logger.info("🏆 Aucun vainqueur concours précédent en DB")
        # Charger le compteur de panneaux depuis la DB
        global countdown_panel_counter
        countdown_panel_counter = await db.db_get_countdown_panel_count()
        logger.info(f"🟦 {countdown_panel_counter} panneau(x) countdown chargé(s) depuis DB")

        if PREDICTION_CHANNEL_ID:
            try:
                pred_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                if pred_entity:
                    prediction_channel_ok = True
                    logger.info(f"✅ Canal 1 OK ({PREDICTION_CHANNEL_ID})")
                else:
                    logger.error(f"❌ Canal 1 inaccessible ({PREDICTION_CHANNEL_ID})")
            except Exception as e:
                logger.error(f"❌ Erreur canal 1: {e}")

        if PREDICTION_CHANNEL_ID2:
            try:
                pred_entity2 = await resolve_channel(PREDICTION_CHANNEL_ID2)
                if pred_entity2:
                    logger.info(f"✅ Canal 2 OK ({PREDICTION_CHANNEL_ID2})")
                else:
                    logger.error(f"❌ Canal 2 inaccessible ({PREDICTION_CHANNEL_ID2}) — le bot n'est pas admin ou n'a pas accès")
                    try:
                        await client.send_message(ADMIN_ID,
                            "⚠️ **CANAL 2 INACCESSIBLE**\n"
                            f"ID : `{PREDICTION_CHANNEL_ID2}`\n"
                            "Le bot ne peut pas envoyer dans ce canal.\n"
                            "→ Vérifie que le bot est **admin** du canal."
                        )
                    except Exception:
                        pass
            except Exception as e:
                logger.error(f"❌ Erreur canal 2: {e}")

        if PREDICTION_CHANNEL_ID3:
            try:
                pred_entity3 = await resolve_channel(PREDICTION_CHANNEL_ID3)
                if pred_entity3:
                    logger.info(f"✅ Canal 3 OK ({PREDICTION_CHANNEL_ID3})")
                else:
                    logger.error(f"❌ Canal 3 inaccessible ({PREDICTION_CHANNEL_ID3})")
                    try:
                        await client.send_message(ADMIN_ID,
                            "⚠️ **CANAL 3 INACCESSIBLE**\n"
                            f"ID : `{PREDICTION_CHANNEL_ID3}`\n"
                            "Le bot ne peut pas envoyer dans ce canal.\n"
                            "→ Vérifie que le bot est **admin** du canal."
                        )
                    except Exception:
                        pass
            except Exception as e:
                logger.error(f"❌ Erreur canal 3: {e}")
        else:
            logger.info("📡 Canal 3 : désactivé (configurable via /canaux canal3 [ID])")

        if PREDICTION_CHANNEL_ID4:
            try:
                pred_entity4 = await resolve_channel(PREDICTION_CHANNEL_ID4)
                if pred_entity4:
                    logger.info(f"✅ Canal 4 OK ({PREDICTION_CHANNEL_ID4})")
                else:
                    logger.error(f"❌ Canal 4 inaccessible ({PREDICTION_CHANNEL_ID4})")
                    try:
                        await client.send_message(ADMIN_ID,
                            "⚠️ **CANAL 4 INACCESSIBLE**\n"
                            f"ID : `{PREDICTION_CHANNEL_ID4}`\n"
                            "Le bot ne peut pas envoyer dans ce canal.\n"
                            "→ Vérifie que le bot est **admin** du canal."
                        )
                    except Exception:
                        pass
            except Exception as e:
                logger.error(f"❌ Erreur canal 4: {e}")
        else:
            logger.info("📡 Canal 4 : désactivé (configurable via /canaux canal4 [ID])")

        logger.info("🤖 Bot démarré")
        return True

    except (AuthKeyError, SessionExpiredError) as e:
        logger.error(f"❌ Session invalide ou expirée: {e} — suppression et retry au prochain démarrage")
        await db.db_save_kv('bot_session', {'session': ''})
        return False
    except Exception as e:
        logger.error(f"❌ Erreur démarrage: {e}")
        return False


async def main():
    # ── Démarrage du serveur web (une seule fois) ──
    app = web.Application()
    app.router.add_get('/health', lambda r: web.Response(text="OK"))
    app.router.add_get('/', lambda r: web.Response(text="BACCARAT AI 🤖 Running | Source: 1xBet API"))
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, '0.0.0.0', PORT)
    await site.start()
    logger.info(f"🌐 Web server port {PORT}")

    # ── Boucle de reconnexion automatique ──
    background_started = False
    retry_delay = 5
    while True:
        try:
            if not await start_bot():
                logger.error("❌ start_bot() a échoué — nouvelle tentative dans 30s")
                await asyncio.sleep(30)
                continue

            # Tâches de fond : démarrées UNE SEULE FOIS après le premier start_bot réussi
            if not background_started:
                asyncio.create_task(auto_reset_system())
                asyncio.create_task(_api_polling_guardian())   # guardian redémarre si crash
                asyncio.create_task(auto_watchdog_task())      # watchdog déblocage automatique
                asyncio.create_task(keep_alive_task())         # anti spin-down Render.com
                asyncio.create_task(bilan_loop())
                asyncio.create_task(auto_strategy_hourly_loop())
                asyncio.create_task(restore_countdown_panel_if_needed())
                background_started = True

            logger.info(f"📏 Écart: {MIN_GAP_BETWEEN_PREDICTIONS}")
            logger.info("📡 Source: 1xBet API (polling toutes les 4s)")
            logger.info(f"📊 Compteur4 seuil: {COMPTEUR4_THRESHOLD}")
            logger.info(f"⏰ Restriction horaire: {'ACTIVE' if PREDICTION_HOURS else 'INACTIVE (24h/24)'}")
            if RENDER_EXTERNAL_URL:
                logger.info(f"🌐 Render URL: {RENDER_EXTERNAL_URL}")

            retry_delay = 5   # reset après connexion réussie
            await client.run_until_disconnected()
            logger.warning("⚠️ Telegram déconnecté — reconnexion dans 5s...")

        except KeyboardInterrupt:
            logger.info("Arrêt manuel demandé.")
            break
        except (AuthKeyError, SessionExpiredError) as e:
            logger.error(f"❌ Session expirée: {e} — réinitialisation et retry dans 30s")
            await db.db_save_kv('bot_session', {'session': ''})
            await asyncio.sleep(30)
            continue
        except Exception as e:
            logger.error(f"❌ Erreur boucle principale: {e} — reconnexion dans {retry_delay}s")

        await asyncio.sleep(retry_delay)
        retry_delay = min(retry_delay * 2, 120)   # backoff exponentiel max 2 min

        try:
            if client and client.is_connected():
                await client.disconnect()
        except Exception:
            pass


if __name__ == '__main__':
    import time as _time
    _restart_delay = 10
    while True:
        try:
            asyncio.run(main())
            # main() ne doit jamais retourner normalement — si oui, on relance
            logger.warning("⚠️ main() a retourné — relance dans 10s")
        except KeyboardInterrupt:
            logger.info("Arrêté manuellement")
            break
        except Exception as e:
            logger.error(f"💥 Erreur fatale hors boucle: {e} — relance dans {_restart_delay}s")
        _time.sleep(_restart_delay)
        _restart_delay = min(_restart_delay * 2, 120)  # backoff max 2 min
