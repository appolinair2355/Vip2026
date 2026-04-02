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

_USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36 Edg/120.0.0.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_3) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Safari/605.1.15",
]

SUIT_MAP = {0: "♠️", 1: "♣️", 2: "♦️", 3: "♥️"}

_last_ua_index = 0


def _get_headers():
    global _last_ua_index
    ua = _USER_AGENTS[_last_ua_index % len(_USER_AGENTS)]
    _last_ua_index += 1
    return {
        "User-Agent": ua,
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": "https://1xbet.com/",
        "Origin": "https://1xbet.com",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    }


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
    Async — utilise aiohttp (pas de requests).
    Retry automatique jusqu'à 3 tentatives avec backoff et rotation User-Agent.
    """
    max_attempts = 3
    last_error = None

    for attempt in range(max_attempts):
        connect_t = 5 + attempt * 2
        read_t    = 8 + attempt * 3
        timeout   = aiohttp.ClientTimeout(connect=connect_t, total=connect_t + read_t)
        try:
            async with aiohttp.ClientSession(headers=_get_headers()) as session:
                async with session.get(API_URL, params=API_PARAMS, timeout=timeout) as resp:
                    if resp.status != 200:
                        last_error = f"HTTP {resp.status}"
                        if attempt < max_attempts - 1:
                            await asyncio.sleep(1 + attempt)
                        continue

                    data = await resp.json(content_type=None)

            if "Value" not in data or not isinstance(data["Value"], list):
                last_error = "Structure API inattendue (champ Value manquant)"
                if attempt < max_attempts - 1:
                    await asyncio.sleep(1)
                continue

            baccara_sport = None
            for sport in data["Value"]:
                if sport.get("N") == "Baccarat" or sport.get("I") == 236:
                    if "L" in sport:
                        baccara_sport = sport
                        break

            if baccara_sport is None:
                last_error = "Sport Baccarat non trouvé dans la réponse"
                if attempt < max_attempts - 1:
                    await asyncio.sleep(1)
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
            return results

        except (aiohttp.ClientConnectionError, aiohttp.ServerDisconnectedError) as e:
            last_error = f"Connexion refusée (tentative {attempt+1}/{max_attempts})"
            if attempt < max_attempts - 1:
                await asyncio.sleep(2 + attempt)
        except asyncio.TimeoutError:
            last_error = f"Timeout (tentative {attempt+1}/{max_attempts})"
            if attempt < max_attempts - 1:
                await asyncio.sleep(1 + attempt)
        except Exception as e:
            last_error = f"Erreur inattendue: {e}"
            if attempt < max_attempts - 1:
                await asyncio.sleep(1)

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
