"""
Configuration du bot Baccarat AI
=================================
ZÉRO variable d'environnement requise sur Render.com.

Toutes les valeurs ont des FALLBACKS codés directement ici :
  - API_ID / API_HASH / BOT_TOKEN    → credentials Telegram
  - ADMIN_ID                         → ID administrateur
  - PREDICTION_CHANNEL_ID/ID2        → canaux de prédiction
  - DATABASE_URL                     → base de données PostgreSQL (URL externe)
  - SESSION TELEGRAM                 → chargée depuis la DB au démarrage

Les variables d'environnement Render (DATABASE_URL, PORT) sont lues en priorité
si elles existent (Render les injecte automatiquement), sinon les fallbacks
ci-dessous sont utilisés.
"""

import os

# ============================================================================
# TELEGRAM API CREDENTIALS
# Fallbacks intégrés — pas besoin de les définir sur Render
# ============================================================================

API_ID    = int(os.environ.get("API_ID")    or 29177661)
API_HASH  = os.environ.get("API_HASH")      or "a8639172fa8d35dbfd8ea46286d349ab"
BOT_TOKEN = os.environ.get("BOT_TOKEN")     or "8442253971:AAEisYucgZ49Ej2b-mK9_6DhNrqh9WOc_XU"

# NOTE : TELEGRAM_SESSION est lue directement dans main.py via os.getenv('TELEGRAM_SESSION', '')
#        C'est la seule variable qui N'A PAS de fallback → obligatoire sur Render.

# ============================================================================
# ADMIN ET CANAUX
# Fallbacks intégrés — pas besoin de les définir sur Render
# ============================================================================

ADMIN_ID               = int(os.environ.get("ADMIN_ID")               or 1190237801)

# ── Canaux de prédiction (principaux — reçoivent TOUTES les prédictions) ──────
PREDICTION_CHANNEL_ID  = int(os.environ.get("PREDICTION_CHANNEL_ID")  or -1003848194038)
PREDICTION_CHANNEL_ID2 = int(os.environ.get("PREDICTION_CHANNEL_ID2") or -1003329818758)

# ── Canaux secondaires optionnels (activables via /canaux dans le bot) ─────────
# Laisser à 0 pour désactiver ; le bot peut aussi les changer via le menu admin.
_raw_dist = os.environ.get("DISTRIBUTION_CHANNEL_ID") or 0
_raw_c2   = os.environ.get("COMPTEUR2_CHANNEL_ID")    or 0
_raw_c3   = os.environ.get("PREDICTION_CHANNEL_ID3")  or 0
_raw_c4   = os.environ.get("PREDICTION_CHANNEL_ID4")  or 0
DISTRIBUTION_CHANNEL_ID  = int(_raw_dist) if _raw_dist and int(_raw_dist) != 0 else None
COMPTEUR2_CHANNEL_ID     = int(_raw_c2)   if _raw_c2   and int(_raw_c2)   != 0 else None
# Canal 3 & 4 : canaux supplémentaires recevant prédictions + résultats (désactivés par défaut)
PREDICTION_CHANNEL_ID3   = int(_raw_c3)   if _raw_c3   and int(_raw_c3)   != 0 else None
PREDICTION_CHANNEL_ID4   = int(_raw_c4)   if _raw_c4   and int(_raw_c4)   != 0 else None

# ============================================================================
# PARAMÈTRES DU SERVEUR WEB
# PORT : Render.com l'injecte automatiquement → pas besoin de le définir
# RENDER_EXTERNAL_URL : URL publique pour le keep-alive
# ============================================================================

PORT                = int(os.environ.get("PORT") or 8000)
RENDER_EXTERNAL_URL = os.environ.get("RENDER_EXTERNAL_URL") or "https://vip-joker-et-kouam-2026-mars-i9hq.onrender.com"

# ============================================================================
# CONFIGURATION COSTUMES
# ============================================================================

ALL_SUITS = ['♠', '♥', '♦', '♣']

SUIT_DISPLAY = {
    '♠': '♠️ Pique',
    '♥': '❤️ Cœur',
    '♦': '♦️ Carreau',
    '♣': '♣️ Trèfle'
}

# ============================================================================
# PARAMÈTRES COMPTEUR2
# ============================================================================

COMPTEUR2_SEUIL_B_DEFAULT = 5
COMPTEUR2_ACTIVE_DEFAULT  = True

# ============================================================================
# PARAMÈTRE DF — DÉCALAGE DE PRÉDICTION
# Quand le jeu N se termine → bot prédit le jeu N+df
# df=1 par défaut (prédit le jeu suivant immédiatement après la fin du jeu N)
# ============================================================================

PREDICTION_DF_DEFAULT = 1

# ============================================================================
# OFFSETS GH / GK — DISTANCES DE PRÉDICTION (Compteur2)
# GH : offset pour prédire le manquant confirmé (B absent, C6 confirme)
# GK : offset pour prédire l'inverse du manquant (C6 redirige vers l'inverse)
# ============================================================================

GH_DEFAULT = 2   # prédit le manquant à dernier_numéro + GH
GK_DEFAULT = 1   # prédit l'inverse  à dernier_numéro + GK

# ============================================================================
# INCRÉMENT B APRÈS ÉCHEC
# B_INCREMENT_DEFAULT : combien de points est ajouté au B d'un costume après un PERDU
# ============================================================================

B_INCREMENT_DEFAULT = 1

# ============================================================================
# COMPTEUR8 — ABSENCES CONSÉCUTIVES
# Même logique que C7 : C7 compte les présences ≥5, C8 les absences ≥5
# ============================================================================

COMPTEUR8_THRESHOLD = 5
COMPTEUR8_DATA_FILE = 'compteur8_data.json'

# ============================================================================
# PARAMÈTRES DE SÉCURITÉ
# ============================================================================

FORCE_RESTART_THRESHOLD    = 20
RESET_AT_GAME_NUMBER       = 1440
PREDICTION_TIMEOUT_MINUTES = 10

# Durée (minutes) sans résultat API avant d'alerter l'admin
API_SILENCE_ALERT_MINUTES = 5

# ============================================================================
# BASE DE DONNÉES POSTGRESQL (Render.com)
#
# Sur Render (service déployé) :
#   → Render injecte DATABASE_URL automatiquement avec l'URL INTERNE
#     postgresql://...@dpg-d72p2h3uibrs73a8tojg-a/prediction_baccara
#     (pas de SSL requis pour les connexions internes Render)
#   → Le code lit DATABASE_URL en priorité (env var Render) → URL interne utilisée
#
# Sur Replit (développement) :
#   → Pas de variable DATABASE_URL → fallback vers l'URL EXTERNE ci-dessous
#     (SSL requis avec vérification désactivée pour les connexions cloud externes)
#
# ============================================================================

DATABASE_URL = (
    os.environ.get("DATABASE_URL")
    or "postgresql://prediction_baccara_user:GAd3ljzVMfK3BUld9w7hHjYeQQGixTUG@dpg-d72p2h3uibrs73a8tojg-a.oregon-postgres.render.com/prediction_baccara"
)

# ============================================================================
# LOGGING
# ============================================================================

LOG_LEVEL = os.environ.get("LOG_LEVEL") or "INFO"
