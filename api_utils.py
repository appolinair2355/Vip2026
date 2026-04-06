import json
import asyncio
import random
import aiohttp

API_URL = "https://1xbet.com/service-api/LiveFeed/GetSportsShortZip"
API_PARAMS = {
    "sports": 236,
    "champs": 2050671,
    "lng": "en",
    "gr": 285,
    "country": 96,
    "virtualSports": "true",
    "groupChamps": "true"
}

# ── User-Agents mis à jour (2025/2026) ───────────────────────────────────────
# Chaque entrée : (ua_string, sec_ch_ua, platform, mobile)
_UA_PROFILES = [
    {
        "ua":       "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
        "ch_ua":    '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
        "platform": '"Windows"',
        "mobile":   "?0",
    },
    {
        "ua":       "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36 Edg/130.0.0.0",
        "ch_ua":    '"Microsoft Edge";v="130", "Chromium";v="130", "Not_A Brand";v="99"',
        "platform": '"Windows"',
        "mobile":   "?0",
    },
    {
        "ua":       "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
        "ch_ua":    '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
        "platform": '"macOS"',
        "mobile":   "?0",
    },
    {
        "ua":       "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36",
        "ch_ua":    '"Google Chrome";v="130", "Chromium";v="130", "Not_A Brand";v="24"',
        "platform": '"Linux"',
        "mobile":   "?0",
    },
    {
        "ua":       "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:132.0) Gecko/20100101 Firefox/132.0",
        "ch_ua":    None,
        "platform": None,
        "mobile":   None,
    },
    {
        "ua":       "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.1 Safari/605.1.15",
        "ch_ua":    None,
        "platform": None,
        "mobile":   None,
    },
    {
        "ua":       "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/129.0.0.0 Safari/537.36",
        "ch_ua":    '"Google Chrome";v="129", "Chromium";v="129", "Not_A Brand";v="24"',
        "platform": '"Windows"',
        "mobile":   "?0",
    },
    {
        "ua":       "Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:131.0) Gecko/20100101 Firefox/131.0",
        "ch_ua":    None,
        "platform": None,
        "mobile":   None,
    },
]

SUIT_MAP = {0: "♠️", 1: "♣️", 2: "♦️", 3: "♥️"}

# Cookie jar initialisé à la demande (nécessite une boucle asyncio active)
_cookie_jar: "aiohttp.CookieJar | None" = None

# Compteur d'échecs consécutifs (mis à jour par get_latest_results)
consecutive_failures: int = 0


def _get_cookie_jar() -> aiohttp.CookieJar:
    """Retourne le cookie jar partagé, en le créant si nécessaire."""
    global _cookie_jar
    if _cookie_jar is None:
        _cookie_jar = aiohttp.CookieJar(unsafe=True)
    return _cookie_jar


def _get_headers() -> dict:
    """Construit un jeu de headers réaliste en choisissant un profil UA aléatoire."""
    profile = random.choice(_UA_PROFILES)
    headers = {
        "User-Agent":      profile["ua"],
        "Accept":          "application/json, text/plain, */*",
        "Accept-Language": random.choice([
            "en-US,en;q=0.9",
            "en-GB,en;q=0.9,en-US;q=0.8",
            "fr-FR,fr;q=0.9,en-US;q=0.8,en;q=0.7",
        ]),
        "Accept-Encoding": "gzip, deflate, br, zstd",
        "Connection":      "keep-alive",
        "Cache-Control":   "no-cache",
        "Pragma":          "no-cache",
        "DNT":             "1",
        "Referer":         "https://1xbet.com/",
        "Origin":          "https://1xbet.com",
        "Sec-Fetch-Dest":  "empty",
        "Sec-Fetch-Mode":  "cors",
        "Sec-Fetch-Site":  "same-origin",
    }
    # Sec-Ch-Ua uniquement pour les profils Chromium (Firefox/Safari n'envoient pas ces headers)
    if profile["ch_ua"]:
        headers["Sec-Ch-Ua"]          = profile["ch_ua"]
        headers["Sec-Ch-Ua-Mobile"]   = profile["mobile"]
        headers["Sec-Ch-Ua-Platform"] = profile["platform"]
    return headers


def _parse_cards(sc_s_list):
    player_cards = []
    banker_cards = []
    for entry in sc_s_list:
        key = entry.get("Key", "")
        val = entry.get("Value", "[]")
        try:
            cards = json.loads(val)
        except Exception:
            cards = []
        if key == "P":
            player_cards = cards
        elif key == "B":
            banker_cards = cards
    return player_cards, banker_cards


def _parse_winner(sc_s_list):
    for entry in sc_s_list:
        if entry.get("Key") == "S":
            val = entry.get("Value", "")
            if val == "Win1":
                return "Player"
            elif val == "Win2":
                return "Banker"
            elif val == "Tie":
                return "Tie"
    return None


def _fmt_cards(cards):
    return [
        {"S": SUIT_MAP.get(c.get("S"), "?"), "R": c.get("R", "?"), "raw": c.get("S", -1)}
        for c in cards
    ]


async def get_latest_results() -> list:
    """
    Récupère les derniers résultats de Baccara depuis l'API 1xBet.
    — Sélection aléatoire du profil User-Agent à chaque appel
    — Headers complets (Sec-Fetch-*, Sec-Ch-Ua, Accept-Encoding, DNT…)
    — Retry jusqu'à 3 tentatives avec backoff aléatoire (jitter)
    — Cookie jar partagé pour simuler une session navigateur persistante
    — Met à jour `consecutive_failures` pour la boucle de polling
    """
    global consecutive_failures

    max_attempts = 3
    last_error   = None

    for attempt in range(max_attempts):
        # Timeouts progressifs
        connect_t = 6 + attempt * 2
        read_t    = 10 + attempt * 4
        timeout   = aiohttp.ClientTimeout(connect=connect_t, total=connect_t + read_t)

        # Jitter aléatoire avant chaque tentative (sauf la première)
        if attempt > 0:
            jitter = random.uniform(1.5, 3.5 + attempt)
            await asyncio.sleep(jitter)

        try:
            connector = aiohttp.TCPConnector(ssl=True, limit=5, ttl_dns_cache=300)
            async with aiohttp.ClientSession(
                headers=_get_headers(),
                cookie_jar=_get_cookie_jar(),
                connector=connector,
            ) as session:
                async with session.get(
                    API_URL,
                    params=API_PARAMS,
                    timeout=timeout,
                    allow_redirects=True,
                ) as resp:
                    if resp.status == 429:
                        # Rate-limited — backoff long
                        wait = random.uniform(15, 30)
                        await asyncio.sleep(wait)
                        last_error = f"429 Too Many Requests (tentative {attempt+1})"
                        continue
                    if resp.status == 403:
                        # Blocked — backoff moyen et rotation UA au prochain appel
                        wait = random.uniform(8, 15)
                        await asyncio.sleep(wait)
                        last_error = f"403 Forbidden (tentative {attempt+1})"
                        continue
                    if resp.status != 200:
                        last_error = f"HTTP {resp.status} (tentative {attempt+1})"
                        continue

                    data = await resp.json(content_type=None)

            if "Value" not in data or not isinstance(data["Value"], list):
                last_error = "Structure API inattendue (champ Value manquant)"
                continue

            baccara_sport = None
            for sport in data["Value"]:
                if sport.get("N") == "Baccarat" or sport.get("I") == 236:
                    if "L" in sport:
                        baccara_sport = sport
                        break

            if baccara_sport is None:
                last_error = "Sport Baccarat introuvable dans la réponse"
                continue

            results = []
            for championship in baccara_sport["L"]:
                for game in championship.get("G", []):
                    if "DI" not in game:
                        continue
                    game_number = int(game["DI"])
                    sc    = game.get("SC", {})
                    sc_s  = sc.get("S", [])
                    is_finished = game.get("F", False) or sc.get("CPS") == "Match finished"
                    player_cards, banker_cards = _parse_cards(sc_s)
                    winner = _parse_winner(sc_s)
                    results.append({
                        "game_number":   game_number,
                        "player_cards":  _fmt_cards(player_cards),
                        "banker_cards":  _fmt_cards(banker_cards),
                        "winner":        winner,
                        "is_finished":   is_finished,
                        "score":         sc.get("FS", {}),
                    })

            consecutive_failures = 0
            return results

        except (aiohttp.ClientConnectionError, aiohttp.ServerDisconnectedError):
            last_error = f"Connexion refusée (tentative {attempt+1}/{max_attempts})"
        except asyncio.TimeoutError:
            last_error = f"Timeout (tentative {attempt+1}/{max_attempts})"
        except aiohttp.ClientResponseError as e:
            last_error = f"Erreur réponse HTTP {e.status} (tentative {attempt+1})"
        except Exception as e:
            last_error = f"Erreur inattendue: {e}"

    consecutive_failures += 1
    if last_error:
        logger.warning(f"⚠️ API: toutes les tentatives échouées — {last_error}")
    return []


def update_history(results, history):
    for result in results:
        if result["is_finished"]:
            game_number = result["game_number"]
            new_entry = {
                "player_cards": result["player_cards"],
                "banker_cards": result["banker_cards"],
                "winner":       result.get("winner"),
                "score":        result.get("score"),
                "is_finished":  True
            }
            if game_number not in history:
                history[game_number] = new_entry
            else:
                old = history[game_number]
                if len(result["banker_cards"]) > len(old.get("banker_cards", [])):
                    history[game_number] = new_entry
    return history
