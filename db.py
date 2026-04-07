"""
Module de persistance PostgreSQL — BACCARAT AI
Remplace tous les fichiers JSON locaux.
Toutes les fonctions sont async (asyncpg).
Pour les contextes synchrones, utiliser db_schedule() pour planifier une sauvegarde.
"""

import asyncio
import json
import logging
import ssl as _ssl
from datetime import datetime
from typing import Any, Dict, List, Optional

import asyncpg

logger = logging.getLogger(__name__)

_pool: Optional[asyncpg.Pool] = None


# ============================================================================
# CONNEXION & INITIALISATION
# ============================================================================

async def init_db(database_url: str = None):
    """Crée le pool de connexion et initialise les tables."""
    global _pool
    if database_url is None:
        from config import DATABASE_URL
        database_url = DATABASE_URL
    if not database_url:
        logger.warning("⚠️ DATABASE_URL non configurée — persistance JSON uniquement")
        return
    try:
        # Détection du mode SSL :
        #   - Replit interne (helium / localhost / 127.0.0.1) → pas de SSL
        #   - Render URL interne (dpg-xxxx-a sans .render.com)  → pas de SSL
        #   - Render URL externe (.oregon-postgres.render.com)   → SSL requis
        #   - Toute autre DB cloud externe                       → SSL requis
        is_local = (
            'helium'      in database_url or
            'localhost'   in database_url or
            '127.0.0.1'   in database_url
        )
        is_render_internal = (
            'dpg-' in database_url and
            'postgres.render.com' not in database_url
        )
        needs_ssl = not (is_local or is_render_internal)
        if needs_ssl:
            # Connexion externe (URL Replit / cloud) : SSL sans vérif de certificat
            ssl_ctx = _ssl.create_default_context()
            ssl_ctx.check_hostname = False
            ssl_ctx.verify_mode    = _ssl.CERT_NONE
        else:
            ssl_ctx = False  # Connexion interne Render : pas de SSL
        _pool = await asyncpg.create_pool(
            database_url,
            min_size=1,
            max_size=5,
            command_timeout=30,
            max_inactive_connection_lifetime=180,  # ferme les conn. inactives > 3 min
            ssl=ssl_ctx,
        )
        await _create_tables()
        logger.info("✅ Connexion PostgreSQL établie")
    except Exception as e:
        logger.error(f"❌ Impossible de se connecter à PostgreSQL: {e}")
        _pool = None


async def ping_db() -> bool:
    """Vérifie que le pool est vivant avec un SELECT 1. Reconnecte si nécessaire."""
    global _pool
    if _pool is None:
        logger.warning("⚠️ DB pool None — tentative reconnexion...")
        await init_db()
        return _pool is not None
    try:
        async with _pool.acquire() as conn:
            await conn.execute("SELECT 1")
        return True
    except Exception as e:
        logger.error(f"❌ DB ping KO: {e} — reconnexion...")
        try:
            await _pool.close()
        except Exception:
            pass
        _pool = None
        await init_db()
        return _pool is not None


async def _create_tables():
    """Crée toutes les tables nécessaires si elles n'existent pas."""
    async with _pool.acquire() as conn:
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS kv_store (
                key         VARCHAR(64) PRIMARY KEY,
                data        JSONB       NOT NULL,
                updated_at  TIMESTAMPTZ DEFAULT NOW()
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS hourly_suit_data (
                heure  INT         NOT NULL,
                suit   VARCHAR(4)  NOT NULL,
                count  INT         DEFAULT 0,
                PRIMARY KEY (heure, suit)
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS pending_predictions (
                game_number  INT     PRIMARY KEY,
                data         JSONB   NOT NULL,
                updated_at   TIMESTAMPTZ DEFAULT NOW()
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS prediction_history (
                id               SERIAL      PRIMARY KEY,
                predicted_game   INT         NOT NULL,
                suit             VARCHAR(4)  NOT NULL,
                prediction_type  VARCHAR(32) DEFAULT 'standard',
                reason           TEXT        DEFAULT '',
                status           VARCHAR(32) DEFAULT 'en_cours',
                rattrapage_level INT         DEFAULT 0,
                predicted_at     TIMESTAMPTZ DEFAULT NOW(),
                verified_at      TIMESTAMPTZ,
                verified_by_game INT,
                UNIQUE (predicted_game, suit)
            )
        """)
        await conn.execute("""
            ALTER TABLE prediction_history
            ADD COLUMN IF NOT EXISTS canal_message_id BIGINT DEFAULT NULL
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS countdown_panels (
                id             SERIAL       PRIMARY KEY,
                panel_number   INT          NOT NULL,
                interval_str   VARCHAR(32)  NOT NULL,
                start_h        INT          NOT NULL,
                end_h          INT          NOT NULL,
                minutes_before INT          NOT NULL,
                sent_at        TIMESTAMPTZ  DEFAULT NOW()
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS game_log (
                id           SERIAL      PRIMARY KEY,
                game_number  INT         NOT NULL UNIQUE,
                suits        TEXT        NOT NULL,
                recorded_at  TIMESTAMPTZ DEFAULT NOW()
            )
        """)
        await conn.execute("""
            CREATE INDEX IF NOT EXISTS idx_game_log_recorded_at
            ON game_log (recorded_at)
        """)
    logger.info("📋 Tables PostgreSQL prêtes")


def is_connected() -> bool:
    return _pool is not None


def db_schedule(coro):
    """
    Planifie une coroutine de sauvegarde depuis un contexte synchrone.
    Utiliser depuis les fonctions save_* non-async.
    """
    try:
        loop = asyncio.get_event_loop()
        if loop.is_running():
            asyncio.ensure_future(coro)
        else:
            loop.run_until_complete(coro)
    except Exception as e:
        logger.error(f"❌ db_schedule: {e}")


# ============================================================================
# KV STORE — C4, C7, C8, C9, C11 (JSON blobs)
# ============================================================================

async def db_save_kv(key: str, data: Any):
    """Sauvegarde un blob JSON dans kv_store."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            await conn.execute("""
                INSERT INTO kv_store (key, data, updated_at)
                VALUES ($1, $2::jsonb, NOW())
                ON CONFLICT (key) DO UPDATE
                SET data=$2::jsonb, updated_at=NOW()
            """, key, json.dumps(data, default=str))
    except Exception as e:
        logger.error(f"❌ db_save_kv({key}): {e}")


async def db_load_kv(key: str) -> Optional[Any]:
    """Charge un blob JSON depuis kv_store."""
    if _pool is None:
        return None
    try:
        async with _pool.acquire() as conn:
            row = await conn.fetchrow(
                "SELECT data FROM kv_store WHERE key=$1", key
            )
            if row:
                val = row['data']
                return json.loads(val) if isinstance(val, str) else val
            return None
    except Exception as e:
        logger.error(f"❌ db_load_kv({key}): {e}")
        return None


# ============================================================================
# DONNÉES HORAIRES — hourly_suit_data
# ============================================================================

async def db_save_hourly(hourly_suit_data: Dict, hourly_game_count: Dict):
    """Sauvegarde les données horaires (upsert par heure+costume)."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            rows = []
            for h, suits in hourly_suit_data.items():
                for suit, count in suits.items():
                    rows.append((int(h), suit, count))
            await conn.executemany("""
                INSERT INTO hourly_suit_data (heure, suit, count)
                VALUES ($1, $2, $3)
                ON CONFLICT (heure, suit) DO UPDATE SET count=$3
            """, rows)
            # Stocker les totaux dans kv_store
            totals = {str(h): cnt for h, cnt in hourly_game_count.items()}
            await db_save_kv('hourly_totals', totals)
    except Exception as e:
        logger.error(f"❌ db_save_hourly: {e}")


async def db_load_hourly() -> Optional[Dict]:
    """
    Charge les données horaires.
    Retourne {'suits': {h: {suit: count}}, 'totals': {h: count}} ou None.
    """
    if _pool is None:
        return None
    try:
        async with _pool.acquire() as conn:
            rows = await conn.fetch("SELECT heure, suit, count FROM hourly_suit_data")
        suits: Dict[str, Dict[str, int]] = {}
        for row in rows:
            h = str(row['heure'])
            if h not in suits:
                suits[h] = {}
            suits[h][row['suit']] = row['count']
        totals = await db_load_kv('hourly_totals') or {}
        return {'suits': suits, 'totals': totals}
    except Exception as e:
        logger.error(f"❌ db_load_hourly: {e}")
        return None


# ============================================================================
# PENDING PREDICTIONS
# ============================================================================

def _serialize(val):
    if isinstance(val, datetime):
        return val.isoformat()
    return val


async def db_save_pending(game_number: int, pred: Dict):
    """Sauvegarde ou met à jour une prédiction en attente."""
    if _pool is None:
        return
    try:
        serializable = {k: _serialize(v) for k, v in pred.items()}
        async with _pool.acquire() as conn:
            await conn.execute("""
                INSERT INTO pending_predictions (game_number, data, updated_at)
                VALUES ($1, $2::jsonb, NOW())
                ON CONFLICT (game_number) DO UPDATE
                SET data=$2::jsonb, updated_at=NOW()
            """, game_number, json.dumps(serializable, default=str))
    except Exception as e:
        logger.error(f"❌ db_save_pending({game_number}): {e}")


async def db_delete_pending(game_number: int):
    """Supprime une prédiction en attente résolue."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            await conn.execute(
                "DELETE FROM pending_predictions WHERE game_number=$1",
                game_number
            )
    except Exception as e:
        logger.error(f"❌ db_delete_pending({game_number}): {e}")


async def db_save_all_pending(pending_predictions: Dict):
    """Sauvegarde tout le dict pending_predictions (vidage complet + réinsertion)."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            await conn.execute("DELETE FROM pending_predictions")
            for gn, pred in pending_predictions.items():
                serializable = {k: _serialize(v) for k, v in pred.items()}
                await conn.execute("""
                    INSERT INTO pending_predictions (game_number, data, updated_at)
                    VALUES ($1, $2::jsonb, NOW())
                """, int(gn), json.dumps(serializable, default=str))
    except Exception as e:
        logger.error(f"❌ db_save_all_pending: {e}")


async def db_load_pending() -> Dict:
    """Charge toutes les prédictions en attente depuis PostgreSQL."""
    if _pool is None:
        return {}
    try:
        async with _pool.acquire() as conn:
            rows = await conn.fetch("SELECT game_number, data FROM pending_predictions")
        result = {}
        for row in rows:
            gn = row['game_number']
            val = row['data']
            pred = json.loads(val) if isinstance(val, str) else dict(val)
            for field in ('sent_time',):
                if field in pred and pred[field]:
                    try:
                        pred[field] = datetime.fromisoformat(pred[field])
                    except Exception:
                        pass
            pred['status'] = 'en_cours'
            result[gn] = pred
        return result
    except Exception as e:
        logger.error(f"❌ db_load_pending: {e}")
        return {}


# ============================================================================
# PREDICTION HISTORY
# ============================================================================

async def db_add_prediction_history(entry: Dict):
    """Ajoute une prédiction dans l'historique PostgreSQL."""
    if _pool is None:
        return
    try:
        predicted_at = entry.get('predicted_at') or datetime.now()
        async with _pool.acquire() as conn:
            await conn.execute("""
                INSERT INTO prediction_history
                    (predicted_game, suit, prediction_type, reason, status,
                     rattrapage_level, predicted_at)
                VALUES ($1,$2,$3,$4,$5,$6,$7)
                ON CONFLICT (predicted_game, suit) DO NOTHING
            """,
                entry.get('predicted_game'),
                entry.get('suit'),
                entry.get('type', 'standard'),
                entry.get('reason', ''),
                entry.get('status', 'en_cours'),
                entry.get('rattrapage_level', 0),
                predicted_at if isinstance(predicted_at, datetime) else datetime.now(),
            )
    except Exception as e:
        logger.error(f"❌ db_add_prediction_history: {e}")


async def db_update_prediction_history(
    predicted_game: int, suit: str, status: str,
    rattrapage_level: int, verified_by_game: int
):
    """Met à jour le statut d'une prédiction dans PostgreSQL."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            await conn.execute("""
                UPDATE prediction_history
                SET status=$3, rattrapage_level=$4, verified_by_game=$5, verified_at=NOW()
                WHERE predicted_game=$1 AND suit=$2
            """, predicted_game, suit, status, rattrapage_level, verified_by_game)
    except Exception as e:
        logger.error(f"❌ db_update_prediction_history: {e}")


async def db_load_prediction_history(limit: int = 200) -> List[Dict]:
    """Charge les dernières prédictions depuis PostgreSQL."""
    if _pool is None:
        return []
    try:
        async with _pool.acquire() as conn:
            rows = await conn.fetch("""
                SELECT predicted_game, suit, prediction_type, reason, status,
                       rattrapage_level, predicted_at, verified_at, verified_by_game,
                       canal_message_id
                FROM prediction_history
                ORDER BY predicted_at DESC
                LIMIT $1
            """, limit)
        result = []
        for row in rows:
            result.append({
                'predicted_game':    row['predicted_game'],
                'suit':              row['suit'],
                'type':              row['prediction_type'],
                'reason':            row['reason'],
                'status':            row['status'],
                'rattrapage_level':  row['rattrapage_level'],
                'predicted_at':      row['predicted_at'],
                'verified_at':       row['verified_at'],
                'verified_by_game':  row['verified_by_game'],
                'verification_games': [],
                'canal_message_id':  row['canal_message_id'],
            })
        return result
    except Exception as e:
        logger.error(f"❌ db_load_prediction_history: {e}")
        return []


async def db_set_prediction_message_id(predicted_game: int, suit: str, canal_message_id: int):
    """Met à jour le canal_message_id d'une prédiction dans l'historique."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            await conn.execute("""
                UPDATE prediction_history
                SET canal_message_id = $1
                WHERE predicted_game = $2 AND suit = $3
            """, canal_message_id, predicted_game, suit)
    except Exception as e:
        logger.error(f"❌ db_set_prediction_message_id: {e}")


async def db_save_countdown_panel(panel_number: int, interval_str: str,
                                   start_h: int, end_h: int, minutes_before: int):
    """Sauvegarde un panneau countdown dans la table countdown_panels."""
    if _pool is None:
        return
    try:
        async with _pool.acquire() as conn:
            await conn.execute("""
                INSERT INTO countdown_panels
                    (panel_number, interval_str, start_h, end_h, minutes_before, sent_at)
                VALUES ($1, $2, $3, $4, $5, NOW())
            """, panel_number, interval_str, start_h, end_h, minutes_before)
    except Exception as e:
        logger.error(f"❌ db_save_countdown_panel: {e}")


async def db_load_countdown_panels(limit: int = 500) -> List[Dict]:
    """Charge l'historique des panneaux countdown depuis la DB."""
    if _pool is None:
        return []
    try:
        async with _pool.acquire() as conn:
            rows = await conn.fetch("""
                SELECT panel_number, interval_str, start_h, end_h,
                       minutes_before, sent_at
                FROM countdown_panels
                ORDER BY sent_at DESC
                LIMIT $1
            """, limit)
            return [dict(r) for r in rows]
    except Exception as e:
        logger.error(f"❌ db_load_countdown_panels: {e}")
        return []


async def db_get_countdown_panel_count() -> int:
    """Retourne le nombre total de panneaux envoyés."""
    if _pool is None:
        return 0
    try:
        async with _pool.acquire() as conn:
            row = await conn.fetchrow("SELECT COUNT(*) AS cnt FROM countdown_panels")
            return int(row['cnt']) if row else 0
    except Exception as e:
        logger.error(f"❌ db_get_countdown_panel_count: {e}")
        return 0


async def db_save_game_log(game_number: int, suits: list):
    """Enregistre les costumes apparus lors d'un jeu dans game_log."""
    if _pool is None:
        return
    try:
        suits_str = ','.join(sorted(set(str(s) for s in suits)))
        async with _pool.acquire() as conn:
            await conn.execute("""
                INSERT INTO game_log (game_number, suits, recorded_at)
                VALUES ($1, $2, NOW())
                ON CONFLICT (game_number) DO NOTHING
            """, game_number, suits_str)
    except Exception as e:
        logger.error(f"❌ db_save_game_log({game_number}): {e}")


async def db_search_game_log(date_from: datetime, date_to: datetime) -> List[Dict]:
    """
    Charge tous les jeux entre date_from et date_to depuis game_log.
    Retourne une liste de dicts {game_number, suits (set), recorded_at}.
    """
    if _pool is None:
        return []
    try:
        async with _pool.acquire() as conn:
            rows = await conn.fetch("""
                SELECT game_number, suits, recorded_at
                FROM game_log
                WHERE recorded_at >= $1 AND recorded_at <= $2
                ORDER BY recorded_at ASC
            """, date_from, date_to)
        result = []
        for row in rows:
            raw = row['suits'] or ''
            suits_set = set(s for s in raw.split(',') if s)
            result.append({
                'game_number': row['game_number'],
                'suits':       suits_set,
                'recorded_at': row['recorded_at'],
            })
        return result
    except Exception as e:
        logger.error(f"❌ db_search_game_log: {e}")
        return []


async def db_reset_all() -> dict:
    """
    Efface TOUTES les données des tables PostgreSQL.
    Préserve la structure (tables non supprimées).
    Retourne un dict {table: nb_lignes_supprimées}.
    """
    if _pool is None:
        return {}
    tables = [
        'pending_predictions',
        'prediction_history',
        'countdown_panels',
        'hourly_suit_data',
        'kv_store',
    ]
    counts = {}
    try:
        async with _pool.acquire() as conn:
            for table in tables:
                row = await conn.fetchrow(f"SELECT COUNT(*) AS cnt FROM {table}")
                cnt = int(row['cnt']) if row else 0
                await conn.execute(f"DELETE FROM {table}")
                counts[table] = cnt
                logger.info(f"🗑️ DB reset: {table} → {cnt} ligne(s) supprimée(s)")
        logger.warning("🔴 BASE DE DONNÉES ENTIÈREMENT VIDÉE (db_reset_all)")
    except Exception as e:
        logger.error(f"❌ db_reset_all: {e}")
    return counts


async def db_reset_cycle() -> dict:
    """
    Reset complet de fin de cycle #1440.
    Vide toutes les tables et tous les kv_store,
    SAUF les 4 clés critiques :
      - bot_session      (session Telegram — indispensable)
      - runtime_config   (configuration admin : canaux, seuils, etc.)
      - sms_subscribers  (numéros des abonnés SMS)
      - infobip_api_keys (clés API Infobip)
    Retourne un dict {table_ou_cle: nb_lignes_supprimées}.
    """
    if _pool is None:
        return {}

    # Clés kv_store à NE PAS effacer
    PRESERVE_KEYS = {'bot_session', 'runtime_config', 'sms_subscribers', 'infobip_api_keys'}

    counts = {}
    try:
        async with _pool.acquire() as conn:
            # ── Tables entièrement vidées ─────────────────────────────────────
            for table in ('pending_predictions', 'prediction_history',
                          'countdown_panels', 'hourly_suit_data', 'game_log'):
                try:
                    row = await conn.fetchrow(f"SELECT COUNT(*) AS cnt FROM {table}")
                    cnt = int(row['cnt']) if row else 0
                    await conn.execute(f"DELETE FROM {table}")
                    counts[table] = cnt
                    logger.info(f"🗑️ Cycle reset: {table} → {cnt} ligne(s) supprimée(s)")
                except Exception:
                    pass   # table peut ne pas exister encore

            # ── kv_store : tout sauf les clés préservées ─────────────────────
            preserved_rows = await conn.fetch(
                "SELECT key FROM kv_store WHERE key = ANY($1::text[])",
                list(PRESERVE_KEYS)
            )
            preserved = {r['key'] for r in preserved_rows}

            row = await conn.fetchrow(
                "SELECT COUNT(*) AS cnt FROM kv_store WHERE key <> ALL($1::text[])",
                list(PRESERVE_KEYS)
            )
            cnt = int(row['cnt']) if row else 0
            await conn.execute(
                "DELETE FROM kv_store WHERE key <> ALL($1::text[])",
                list(PRESERVE_KEYS)
            )
            counts['kv_store (hors clés critiques)'] = cnt
            logger.info(
                f"🗑️ Cycle reset: kv_store → {cnt} clé(s) supprimée(s) "
                f"| préservées : {sorted(preserved)}"
            )

        logger.warning(
            "🔴 RESET CYCLE #1440 — DB vidée (bot_session, runtime_config, "
            "sms_subscribers, infobip_api_keys préservés)"
        )
    except Exception as e:
        logger.error(f"❌ db_reset_cycle: {e}")
    return counts
