import time
import io
import os
import json
import glob
import difflib
import threading
import requests
import pandas as pd
import streamlit as st
from concurrent.futures import ThreadPoolExecutor, as_completed
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
from openpyxl.utils import get_column_letter

# ══════════════════════════════════════════════════════════════════════════════
# CONSTANTES Y DICCIONARIOS
# ══════════════════════════════════════════════════════════════════════════════
TRADUCCIONES_ES_EN = {
    "órdenes de jefe": "Boss's Orders", "ordenes de jefe": "Boss's Orders",
    "órdenes del jefe": "Boss's Orders", "sabio": "Cynthia",
    "juicio de lillie": "Lillie", "investigación del profesor": "Professor's Research",
    "investigación del profesor juniper": "Professor's Research",
    "naranja académica": "Iono", "iono": "Iono", "miriam": "Miriam",
    "arven": "Arven", "penny": "Penny", "jacq": "Jacq", "tulip": "Tulip",
    "larry": "Larry", "ultra ball": "Ultra Ball", "ultra bola": "Ultra Ball",
    "nido ball": "Nest Ball", "nest ball": "Nest Ball", "poké ball": "Poké Ball",
    "gran ball": "Great Ball", "bola rápida": "Quick Ball", "quick ball": "Quick Ball",
    "poción": "Potion", "súper poción": "Super Potion", "hiperpoción": "Hyper Potion",
    "cinturón luchador": "Choice Belt", "banda elegida": "Choice Band",
    "banda de combate": "Choice Band", "guante de combate": "Counter Catcher",
    "escudo mental": "Collapsed Stadium", "energizador": "Energy Recycler",
    "parche turbo": "Turbo Patch", "roca lisa": "Smooth Stone",
    "bucle brillante": "Pal Pad", "repetición de película": "Lure Ball",
    "estadio roto": "Collapsed Stadium", "academia naranja": "Orange Academy",
    "gimnasio pokémon": "Pokémon League Headquarters",
    "energía agua": "Water Energy", "energía fuego": "Fire Energy",
    "energía eléctrica": "Lightning Energy", "energía planta": "Grass Energy",
    "energía psíquica": "Psychic Energy", "energía lucha": "Fighting Energy",
    "energía oscuridad": "Darkness Energy", "energía metal": "Metal Energy",
    "energía hada": "Fairy Energy", "energía doble": "Double Colorless Energy",
}

KEYWORDS_LIGA = ["promo", "league", "player cup", "professor program"]

# ── Normalización de apóstrofes ───────────────────────────────────────────────
def _normalizar_apostrofe(texto: str) -> str:
    return texto.replace("\u2019", "'").replace("\u2018", "'").replace("\u02bc", "'")

TIPOS_API = {
    "pokemon": "Pokémon", "pokémon": "Pokémon",
    "trainer": "Trainer", "entrenador": "Trainer",
    "energy": "Energy", "energía": "Energy", "energia": "Energy",
}

# Colores para tipos de carta en las tarjetas
TIPO_COLORES = {
    "Pokémon":  {"bg": "#1a2a1a", "border": "#48BB78", "badge": "#276749", "text": "#9AE6B4"},
    "pokemon":  {"bg": "#1a2a1a", "border": "#48BB78", "badge": "#276749", "text": "#9AE6B4"},
    "Trainer":  {"bg": "#1a1a2e", "border": "#63B3ED", "badge": "#2C5282", "text": "#90CDF4"},
    "trainer":  {"bg": "#1a1a2e", "border": "#63B3ED", "badge": "#2C5282", "text": "#90CDF4"},
    "Energy":   {"bg": "#2a1a10", "border": "#F6AD55", "badge": "#7B341E", "text": "#FBD38D"},
    "energy":   {"bg": "#2a1a10", "border": "#F6AD55", "badge": "#7B341E", "text": "#FBD38D"},
}
COLOR_DEFAULT = {"bg": "#1E2530", "border": "#4A5568", "badge": "#2D3748", "text": "#CBD5E0"}

BASE_URL               = "https://api.pokemontcg.io/v2/cards"
DELAY_ENTRE_CONSULTAS  = 1.2   # segundos

# ── Caché global de consultas (segura entre hilos) ────────────────────────────
# A diferencia de st.session_state (que NO es accesible de forma fiable desde los
# hilos del ThreadPoolExecutor), un dict de módulo + Lock sí es thread-safe.
# Persiste mientras el servidor esté encendido; se vacía al reiniciar la app.
_QUERY_CACHE: dict = {}
_QUERY_LOCK = threading.Lock()

# ── Métricas de diagnóstico (para entender lentitud / rate limit en vivo) ─────
_STATS = {"requests": 0, "cache_hits": 0, "rate_limited": 0, "errores": 0, "tiempo_red": 0.0}
_STATS_LOCK = threading.Lock()

# Config ajustable desde el sidebar (la lee _raw_query y el loop de proceso)
_CFG = {"throttle": 0.2, "max_workers": 4}

# ── Base de datos LOCAL (opcional, recomendada) ───────────────────────────────
# Si el usuario descarga la base de pokemontcg.io (repo PokemonTCG/pokemon-tcg-data,
# carpeta cards/en renombrada a card_data), la cargamos en memoria y buscamos ahí:
# instantáneo, completo y sin depender de que la API esté en pie.
_DB_CARDS: list = []
_DB_NAMES: list = []       # nombres únicos, para sugerencias "¿quisiste decir…?"
_DB_LOADED = False


def cargar_base_local(carpeta: str) -> int:
    """Carga todos los .json de una carpeta (cada uno es una lista de cartas)."""
    global _DB_CARDS, _DB_NAMES, _DB_LOADED
    cards = []
    for path in sorted(glob.glob(os.path.join(carpeta, "*.json"))):
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                cards.extend(data)
            elif isinstance(data, dict) and "data" in data:
                cards.extend(data["data"])
        except Exception:
            continue
    _DB_CARDS = cards
    _DB_NAMES = sorted({c.get("name", "") for c in cards if c.get("name")})
    _DB_LOADED = bool(cards)
    return len(cards)


def _buscar_local(nombre_en: str) -> list:
    """Match parcial por nombre en la base local (imita el comportamiento de la API)."""
    q = nombre_en.strip().lower()
    if not q:
        return []
    return [c for c in _DB_CARDS if q in c.get("name", "").lower()]


def _pool_nombre(nombre_en: str, api_key: str | None) -> list:
    """Pool de cartas por nombre: de la base local si está cargada, si no de la API."""
    if _DB_LOADED:
        return _buscar_local(nombre_en)
    return _raw_query(f'name:"{nombre_en}"', api_key, page_size=50)


def sugerir_nombres(nombre: str, api_key: str | None = None, n: int = 4) -> list:
    """Devuelve nombres de cartas parecidos a 'nombre' (para corregir typos).

    Usa la base local si está cargada (instantáneo y completo). Si no, intenta
    una búsqueda suelta en la API como aproximación.
    """
    q = (nombre or "").strip()
    if not q:
        return []
    universo = _DB_NAMES
    if not universo:
        # Sin base local: aproximación vía API con la primera palabra
        try:
            primera = q.split()[0]
            res = _raw_query(f'name:"{primera}*"', api_key, page_size=25)
            universo = sorted({c.get("name", "") for c in res if c.get("name")})
        except Exception:
            universo = []
    if not universo:
        return []
    # Coincidencias por similitud (typos) + por subcadena (prefijos)
    cercanos = difflib.get_close_matches(q, universo, n=n, cutoff=0.6)
    ql = q.lower()
    subcadena = [x for x in universo if ql in x.lower() and x not in cercanos]
    salida = (cercanos + subcadena)[:n]
    return salida


def _reset_stats():
    with _STATS_LOCK:
        for k in _STATS:
            _STATS[k] = 0 if k != "tiempo_red" else 0.0

# ── Estado/condición de la carta (clave para una herramienta de venta) ────────
# Cada estado tiene una descripción y un multiplicador sobre el precio NM.
# Estos multiplicadores son una convención de mercado aproximada y editables.
ESTADOS = {
    "NM":  ("Near Mint",          1.00),
    "LP":  ("Lightly Played",     0.85),
    "MP":  ("Moderately Played",  0.70),
    "HP":  ("Heavily Played",     0.50),
    "DMG": ("Damaged",            0.35),
}
# Alias aceptados en el Excel (español/inglés) → código estándar
ESTADO_ALIASES = {
    "nm": "NM", "near mint": "NM", "mint": "NM", "m": "NM", "nuevo": "NM", "nueva": "NM",
    "lp": "LP", "lightly played": "LP", "light": "LP", "casi nuevo": "LP", "casi nueva": "LP",
    "mp": "MP", "moderately played": "MP", "moderate": "MP", "jugada": "MP", "jugado": "MP",
    "hp": "HP", "heavily played": "HP", "heavy": "HP", "muy jugada": "HP", "muy jugado": "HP",
    "dmg": "DMG", "damaged": "DMG", "dañada": "DMG", "danada": "DMG", "dañado": "DMG", "poor": "DMG",
}
# Colores de badge por estado
ESTADO_COLOR = {
    "NM":  ("#1C4532", "#9AE6B4"), "LP": ("#234E52", "#9DECF9"),
    "MP":  ("#5F4B1B", "#FBD38D"), "HP": ("#652B19", "#F6AD55"),
    "DMG": ("#742A2A", "#FEB2B2"),
}


def traducir_nombre(nombre: str) -> str:
    return TRADUCCIONES_ES_EN.get(nombre.strip().lower(), nombre.strip())


def normalizar_estado(raw) -> str:
    """Convierte cualquier variante de estado a su código estándar (def. NM)."""
    s = str(raw or "").strip().lower()
    if s in ("", "nan", "none"):
        return "NM"
    if s in ESTADO_ALIASES:
        return ESTADO_ALIASES[s]
    return s.upper() if s.upper() in ESTADOS else "NM"


# ══════════════════════════════════════════════════════════════════════════════
# CAPA API — BÚSQUEDA EN CASCADA
# ══════════════════════════════════════════════════════════════════════════════

def _raw_query(query: str, api_key: str | None, page_size: int = 10) -> list:
    # Normalizar apóstrofes ANTES de todo (caché y petición real)
    query = _normalizar_apostrofe(query)

    # ── Caché global thread-safe (NO usa session_state, que falla entre hilos) ─
    ckey = (query, page_size)
    with _QUERY_LOCK:
        if ckey in _QUERY_CACHE:
            with _STATS_LOCK:
                _STATS["cache_hits"] += 1
            return _QUERY_CACHE[ckey]

    # ── Throttle configurable desde el sidebar (s entre peticiones reales) ────
    time.sleep(_CFG.get("throttle", 0.2) if api_key else max(_CFG.get("throttle", 0.2), 0.6))

    headers = {"Content-Type": "application/json"}
    if api_key:
        headers["X-Api-Key"] = api_key
    params = {"q": query, "pageSize": page_size, "orderBy": "-set.releaseDate"}
    data = []
    t0 = time.time()
    try:
        resp = requests.get(BASE_URL, headers=headers, params=params, timeout=10)
        with _STATS_LOCK:
            _STATS["requests"] += 1
        if resp.status_code == 429:
            with _STATS_LOCK:
                _STATS["rate_limited"] += 1
            time.sleep(3.0)
            resp = requests.get(BASE_URL, headers=headers, params=params, timeout=10)
        resp.raise_for_status()
        data = resp.json().get("data", [])
    except Exception:
        with _STATS_LOCK:
            _STATS["errores"] += 1
        data = []
    finally:
        with _STATS_LOCK:
            _STATS["tiempo_red"] += time.time() - t0

    # Solo cacheamos resultados válidos: así un fallo de red puntual no queda
    # "pegado" como si la carta no existiera.
    if data:
        with _QUERY_LOCK:
            _QUERY_CACHE[ckey] = data
    return data

def buscar_carta(nombre_en, tipo, regulation_mark, numero, api_key) -> tuple[list, str]:
    """
    Cascada de 5 niveles:
      1a. nombre + número + bloque    → arte preciso con set confirmado (más exacto)
      1b. nombre + número             → arte por número sin bloque
      2.  nombre + bloque (+ tipo)    → fallback estándar
      3.  nombre + tipo (sin bloque)
      4.  solo nombre                 → salvavidas final
    """
    tiene_numero = bool(numero and numero not in ("", "nan", "-"))
    tiene_mark   = bool(regulation_mark and regulation_mark.lower() not in ("", "nan"))
    tipo_api     = TIPOS_API.get(tipo.strip().lower(), "") if tipo.strip() else ""
    nn = nombre_en.strip().lower()

    def _exactos(lst):
        return [c for c in lst if c.get("name", "").strip().lower() == nn]

    # ── VÍA RÁPIDA: pool por nombre (base local si está cargada; si no, API) ──
    amplia = _pool_nombre(nombre_en, api_key)
    ex = _exactos(amplia)
    if ex:  # encontramos el nombre EXACTO
        if tiene_numero:
            por_num = [c for c in ex if str(c.get("number", "")).lower() == numero.lower()]
            if por_num:
                return por_num, "número exacto"
        if tiene_mark:
            pm = [c for c in ex if str(c.get("regulationMark", "")).upper() == regulation_mark.upper()]
            if tipo_api:
                pm = [c for c in pm if c.get("supertype", "") == tipo_api] or pm
            if pm:
                return pm, "nombre + bloque"
        if tipo_api:
            pt = [c for c in ex if c.get("supertype", "") == tipo_api]
            if pt:
                return pt, "nombre + tipo"
        return ex, "solo nombre"

    # ── FALLBACK DIRIGIDO (solo en modo API; en modo local el pool ya es total)
    if not _DB_LOADED:
        if tiene_numero:
            r = _raw_query(f'name:"{nombre_en}" number:"{numero}"', api_key)
            rex = _exactos(r)
            if rex:
                return rex, "número exacto"
            if r:
                return r, "número exacto"
        if tiene_mark:
            partes = [f'name:"{nombre_en}"', f"regulationMark:{regulation_mark.upper()}"]
            if tipo_api:
                partes.append(f"supertype:{tipo_api}")
            r = _raw_query(" ".join(partes), api_key)
            rex = _exactos(r) or r
            if rex:
                return rex, "nombre + bloque"
        if tipo_api:
            r = _raw_query(f'name:"{nombre_en}" supertype:{tipo_api}', api_key)
            rex = _exactos(r) or r
            if rex:
                return rex, "nombre + tipo"

    # Último recurso: lo que haya devuelto el pool por nombre
    if amplia:
        return amplia, "solo nombre"
    return [], "sin resultados"


# ══════════════════════════════════════════════════════════════════════════════
# SELECCIÓN INTELIGENTE (liga vs. regular)
# ══════════════════════════════════════════════════════════════════════════════

def _tiene_precio(c: dict) -> bool:
    """¿Esta impresión trae algún precio de mercado en tcgplayer?"""
    prices = (c.get("tcgplayer", {}) or {}).get("prices", {}) or {}
    for p in prices.values():
        if p and (p.get("market") or p.get("mid")):
            return True
    return False


def seleccionar_carta(resultados: list, es_de_liga: bool, nombre_en: str = "") -> dict:
    if not resultados:
        return {}

    # Filtro de nombre EXACTO: la API hace match parcial, así "Iono" devuelve
    # también "Iono's Bellibolt ex". Si hay resultados con nombre exacto, solo
    # usamos esos; si no hay ninguno, usamos todos (comportamiento anterior).
    nombre_norm = nombre_en.strip().lower()
    if nombre_norm:
        exactos = [c for c in resultados if c.get("name", "").strip().lower() == nombre_norm]
        if exactos:
            resultados = exactos

    def sn(c):
        return c.get("set", {}).get("name", "").lower()

    # Candidatos según preferencia de liga/promo (o no), con fallback a todos.
    if es_de_liga:
        candidatos = [c for c in resultados if any(kw in sn(c) for kw in KEYWORDS_LIGA)] or resultados
    else:
        candidatos = [c for c in resultados if not any(kw in sn(c) for kw in KEYWORDS_LIGA)] or resultados

    # Cuando hay varias versiones (caso de fallback sin número exacto), preferimos
    # una que SÍ tenga precio de referencia, para no devolver "sin precio" si
    # existe otra impresión equivalente con valor de mercado.
    con_precio = [c for c in candidatos if _tiene_precio(c)]
    return (con_precio or candidatos)[0]


# ══════════════════════════════════════════════════════════════════════════════
# CONFIANZA DEL MATCH (clave para vender sin equivocarse de versión)
# ══════════════════════════════════════════════════════════════════════════════

def calcular_confianza(metodo: str, tiene_numero: bool, numero_coincide: bool) -> tuple[str, bool]:
    """
    Devuelve (confianza, necesita_revision).
    'necesita_revision' = True SOLO cuando el match de carta es dudoso
    (se pidió un número pero la API trajo otra versión).
    La ausencia de precio NO activa revisión — eso es dato faltante, no match incorrecto.
    """
    if metodo == "sin resultados":
        return "ninguna", True
    if tiene_numero:
        if metodo == "número exacto" and numero_coincide:
            return "alta", False
        # Se pidió un número pero la cascada trajo OTRA versión → revisar arte
        return "baja", True
    # Sin número: no hay certeza de arte exacto, pero no es un error crítico
    if metodo == "nombre + bloque":
        return "media", False
    return "baja", False   # antes era True; sin número no hay nada que "revisar"


# ══════════════════════════════════════════════════════════════════════════════
# PRECIO DE REFERENCIA (tcgplayer, viene en la misma respuesta de la API)
# ══════════════════════════════════════════════════════════════════════════════

def extraer_precio(card_data: dict) -> tuple:
    """
    Devuelve (precio_usd_mercado, variante, fecha_actualizacion).
    Importante: el precio NO es en tiempo real; tcgplayer lo actualiza ~1 vez al
    día, por eso devolvemos también 'updatedAt' para mostrarlo con honestidad.
    Dentro de cada variante se prueba market → mid → low; solo se pasa a la
    siguiente variante si los tres son None o 0 (antes se saltaba la variante
    si solo 'market' era None, perdiendo el valor de 'low').
    """
    tcg = card_data.get("tcgplayer", {}) or {}
    prices = tcg.get("prices", {}) or {}
    fecha = tcg.get("updatedAt", "-")
    orden = ("holofoil", "normal", "reverseHolofoil", "1stEditionHolofoil",
             "unlimitedHolofoil", "1stEdition", "unlimited")
    for v in orden:
        p = prices.get(v)
        if not p:
            continue
        valor = p.get("market") or p.get("mid") or p.get("low")
        if valor and valor > 0:
            return valor, v, fecha
    if prices:  # fallback: cualquier variante disponible
        for v, p in prices.items():
            valor = p.get("market") or p.get("mid") or p.get("low")
            if valor and valor > 0:
                return valor, v, fecha
    return None, None, fecha


# ══════════════════════════════════════════════════════════════════════════════
# PROCESAMIENTO DE CARTA
# ══════════════════════════════════════════════════════════════════════════════


def _candidato_liviano(c: dict) -> dict:
    """Versión recortada de una carta para guardar como opción de variante."""
    return {
        "name": c.get("name", ""),
        "number": c.get("number", "-"),
        "rarity": c.get("rarity", "-"),
        "regulationMark": c.get("regulationMark", ""),
        "set": {"name": c.get("set", {}).get("name", "-")},
        "images": {"small": c.get("images", {}).get("small", "")},
        "tcgplayer": c.get("tcgplayer", {}) or {},
    }


def _resultado_desde_carta(base: dict, carta: dict, numero: str, tiene_numero: bool,
                           mult: float, clp_rate: float) -> dict:
    """Construye los campos de salida a partir de una carta elegida.
    Reutilizable tanto en el procesamiento automático como en la selección
    manual de variante desde la interfaz."""
    numero_carta = str(carta.get("number", "-"))
    numero_coincide = bool(tiene_numero and numero_carta.lower() == numero.lower())
    conf, revisar = calcular_confianza(base.get("Método Búsqueda", ""), tiene_numero, numero_coincide)

    precio_usd, variante, fecha_precio = extraer_precio(carta)
    precio_aj  = round(precio_usd * mult, 2) if precio_usd else None
    precio_clp = int(round((precio_aj * clp_rate) / 100.0)) * 100 if (precio_aj and clp_rate) else None

    return {
        **base,
        "Card ID":       carta.get("id", "-"),
        "Set":           carta.get("set", {}).get("name", "-"),
        "Número Carta":  numero_carta,
        "Número Coincide": "Sí" if numero_coincide else ("No" if tiene_numero else "-"),
        "Rareza":        carta.get("rarity", "-"),
        "Confianza":     conf,
        "Revisar":       "Sí" if revisar else "No",
        "Precio USD Mercado":  precio_usd,
        "Precio USD Ajustado": precio_aj,
        "Precio CLP Sugerido": precio_clp,
        "Variante Precio":     variante or "-",
        "Fecha Precio":        fecha_precio,
        "URL Imagen":    carta.get("images", {}).get("small", ""),
    }


def fetch_precio_por_id(card_id: str, api_key: str | None) -> dict | None:
    """Consulta un solo card-id en la API y devuelve el objeto carta con precios.

    Esta es la consulta más eficiente posible: un GET directo a /v2/cards/{id},
    sin búsqueda de texto. Solo se usa en el segundo paso (enriquecimiento de precios)
    cuando la base local ya identificó la carta pero no tenía precios embebidos.
    """
    if not card_id or card_id == "-":
        return None
    url = f"{BASE_URL}/{card_id}"
    headers = {"Content-Type": "application/json"}
    if api_key:
        headers["X-Api-Key"] = api_key
    time.sleep(_CFG.get("throttle", 0.2))
    try:
        resp = requests.get(url, headers=headers, timeout=10)
        with _STATS_LOCK:
            _STATS["requests"] += 1
        if resp.status_code == 429:
            with _STATS_LOCK:
                _STATS["rate_limited"] += 1
            time.sleep(3.0)
            resp = requests.get(url, headers=headers, timeout=10)
        if resp.status_code == 200:
            return resp.json().get("data")
    except Exception:
        with _STATS_LOCK:
            _STATS["errores"] += 1
    return None


def enriquecer_precios_en_lote(
    df: "pd.DataFrame",
    api_key: str | None,
    clp_rate: float,
    progress_bar=None,
    status_box=None,
) -> "pd.DataFrame":
    """Segundo paso: busca precios vía API para cada carta que ya fue identificada.

    Solo consulta las cartas que:
      - Tienen un Card ID (la base local lo incluye en cada objeto)
      - No tienen precio aún (Precio USD Mercado es None/NaN)

    Devuelve el mismo DataFrame con las columnas de precio rellenas.
    """
    df = df.copy()
    # Necesitamos la columna Card ID (la agregamos en _resultado_desde_carta)
    if "Card ID" not in df.columns:
        if status_box:
            status_box.warning("No hay columna 'Card ID' — no se puede enriquecer.")
        return df

    # Mask: sin precio (None o NaN)
    def _es_sin_precio(v):
        if v is None:
            return True
        try:
            return pd.isna(v)
        except Exception:
            return False

    mask_sin_precio = df["Precio USD Mercado"].apply(_es_sin_precio)
    mask_con_id = (
        df["Card ID"].notna() &
        (df["Card ID"].astype(str).str.strip() != "-") &
        (df["Card ID"].astype(str).str.strip() != "")
    )

    filas_a_enriquecer = df[mask_sin_precio & mask_con_id].index.tolist()

    total = len(filas_a_enriquecer)
    if total == 0:
        if status_box:
            status_box.info("✅ Todas las cartas ya tienen precio (o no hay ID para consultar).")
        return df

    completadas = [0]
    max_workers = _CFG.get("max_workers", 4)

    def _enriquecer_fila(idx):
        card_id  = df.at[idx, "Card ID"]
        estado   = str(df.at[idx, "Estado"]) if "Estado" in df.columns else "NM"
        _, mult  = ESTADOS.get(estado, ("Near Mint", 1.0))
        carta    = fetch_precio_por_id(card_id, api_key)
        if carta is None:
            return idx, None, None, None, None, None
        precio_usd, variante, fecha = extraer_precio(carta)
        precio_aj  = round(precio_usd * mult, 2) if precio_usd else None
        precio_clp = int(round((precio_aj * clp_rate) / 100.0)) * 100 if (precio_aj and clp_rate) else None
        return idx, precio_usd, precio_aj, precio_clp, variante or "-", fecha

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(_enriquecer_fila, idx): idx for idx in filas_a_enriquecer}
        for future in as_completed(futures):
            idx, p_usd, p_aj, p_clp, variante, fecha = future.result()
            if p_usd is not None:
                df.at[idx, "Precio USD Mercado"]  = p_usd
                df.at[idx, "Precio USD Ajustado"] = p_aj
                df.at[idx, "Precio CLP Sugerido"] = p_clp
                df.at[idx, "Variante Precio"]     = variante
                df.at[idx, "Fecha Precio"]        = fecha
            completadas[0] += 1
            nombre = df.at[idx, "Nombre Original"] if "Nombre Original" in df.columns else str(idx)
            if status_box:
                status_box.markdown(
                    f"💰 **{completadas[0]}/{total}** precios obtenidos — última: **{nombre}**"
                )
            if progress_bar:
                progress_bar.progress(completadas[0] / total)

    return df


def procesar_carta(fila: dict, api_key: str | None = None, clp_rate: float = 0) -> dict:
    nombre_original = str(fila.get("nombre", "")).strip()
    tipo_carta      = str(fila.get("tipo", "")).strip()
    regulation_mark = str(fila.get("regulation_mark", "")).strip()
    es_liga_raw     = str(fila.get("es_de_liga", "")).strip().lower()
    es_de_liga      = es_liga_raw in ("sí", "si", "yes", "true", "1")

    numero_raw = str(fila.get("numero", "")).strip()
    numero     = "" if numero_raw.lower() in ("nan", "none", "") else numero_raw

    # Override opcional: forzar un set concreto (ej: "Ascended Heroes")
    set_forzado = str(fila.get("set_forzado", "")).strip()
    set_forzado = "" if set_forzado.lower() in ("nan", "none", "") else set_forzado

    estado  = normalizar_estado(fila.get("estado", ""))
    _, mult = ESTADOS.get(estado, ("Near Mint", 1.0))

    try:
        c = fila.get("cantidad", 1)
        cantidad = int(c) if str(c).strip() not in ("", "nan") else 1
    except (ValueError, TypeError):
        cantidad = 1

    nombre_en = traducir_nombre(nombre_original)
    resultados, metodo = buscar_carta(nombre_en, tipo_carta, regulation_mark, numero, api_key)
    tiene_numero = bool(numero)
    mark_disp = regulation_mark if (regulation_mark and regulation_mark.lower() != "nan") else "-"

    base = {
        "Cantidad":        cantidad,
        "Estado":          estado,
        "Nombre Original": nombre_original,
        "Nombre EN":       nombre_en,
        "Tipo":            tipo_carta,
        "Número Buscado":  numero if numero else "-",
        "Regulation Mark": mark_disp,
        "Es de Liga":      "Sí" if es_de_liga else "No",
        "Método Búsqueda": metodo,
    }

    if not resultados:
        conf, revisar = calcular_confianza(metodo, tiene_numero, False)
        return {
            **base,
            "Card ID": "-",
            "Set": "No encontrado", "Número Carta": "-", "Número Coincide": "-",
            "Rareza": "-", "Confianza": conf, "Revisar": "Sí" if revisar else "No",
            "Precio USD Mercado": None, "Precio USD Ajustado": None,
            "Precio CLP Sugerido": None, "Variante Precio": "-", "Fecha Precio": "-",
            "URL Imagen": "", "_candidatos": [],
        }

    # Filtrar a nombre exacto para construir la lista de variantes mostrable.
    nn = nombre_en.strip().lower()
    exactos = [c for c in resultados if c.get("name", "").strip().lower() == nn] or resultados

    # Override por set: si el usuario forzó un set, intentamos esa impresión.
    carta = None
    if set_forzado:
        sf = set_forzado.lower()
        for c in exactos:
            if sf in c.get("set", {}).get("name", "").lower():
                carta = c
                base["Método Búsqueda"] = "set forzado"
                break
    if carta is None:
        carta = seleccionar_carta(resultados, es_de_liga, nombre_en)

    resultado = _resultado_desde_carta(base, carta, numero, tiene_numero, mult, clp_rate)
    # Guardamos hasta 8 variantes (livianas) por si el usuario quiere re-elegir.
    resultado["_candidatos"] = [_candidato_liviano(c) for c in exactos[:8]]
    return resultado


# ══════════════════════════════════════════════════════════════════════════════
# FORMATO DE PRECIOS (maneja None y NaN sin romperse)
# ══════════════════════════════════════════════════════════════════════════════

def _has(v) -> bool:
    """True si v es un valor numérico real (no None ni NaN)."""
    try:
        return v is not None and pd.notna(v)
    except Exception:
        return v is not None


def _fmt_usd(v) -> str:
    return f"${v:,.2f}" if _has(v) else "-"


def _fmt_clp(v) -> str:
    # Chile usa el punto como separador de miles: 11700 -> $11.700
    return f"${v:,.0f}".replace(",", ".") if _has(v) else "-"


# ══════════════════════════════════════════════════════════════════════════════
# EXPORTAR EXCEL
# ══════════════════════════════════════════════════════════════════════════════

def exportar_excel(df: pd.DataFrame) -> bytes:
    # Card ID es un campo interno de enriquecimiento; no va al Excel del cliente.
    df = df.drop(columns=["Card ID"], errors="ignore")
    buffer = io.BytesIO()
    with pd.ExcelWriter(buffer, engine="openpyxl") as writer:
        df.to_excel(writer, index=False, sheet_name="Catálogo TCG")
        ws = writer.sheets["Catálogo TCG"]

        hf = Font(bold=True, color="FFFFFF", name="Arial", size=11)
        hfill = PatternFill("solid", start_color="1A1A2E")
        ha = Alignment(horizontal="center", vertical="center", wrap_text=True)
        bf = Font(name="Arial", size=10)
        fp = PatternFill("solid", start_color="F0F2F6")
        fi = PatternFill("solid", start_color="FFFFFF")
        fv = PatternFill("solid", start_color="D4EDDA")
        fr = PatternFill("solid", start_color="F8D7DA")
        fl = PatternFill("solid", start_color="FFF3CD")
        fm = PatternFill("solid", start_color="E9D8FD")
        fn = PatternFill("solid", start_color="BEE3F8")
        # Fills para las columnas nuevas (confianza / revisar)
        fconf_alta  = PatternFill("solid", start_color="C6F6D5")
        fconf_media = PatternFill("solid", start_color="FEEBC8")
        fconf_baja  = PatternFill("solid", start_color="FED7D7")
        frev        = PatternFill("solid", start_color="FFE0E0")
        borde = Border(
            left=Side(style="thin", color="D0D0D0"),
            right=Side(style="thin", color="D0D0D0"),
            top=Side(style="thin", color="D0D0D0"),
            bottom=Side(style="thin", color="D0D0D0"),
        )
        centro = Alignment(horizontal="center", vertical="center")

        for cell in ws[1]:
            cell.font = hf; cell.fill = hfill; cell.alignment = ha; cell.border = borde
        ws.row_dimensions[1].height = 32

        cols = {name: idx + 1 for idx, name in enumerate(df.columns)}
        usd_cols = {cols.get("Precio USD Mercado"), cols.get("Precio USD Ajustado")}

        for row_idx, row in enumerate(ws.iter_rows(min_row=2, max_row=ws.max_row), start=2):
            fb = fp if row_idx % 2 == 0 else fi
            for cell in row:
                cell.font = bf; cell.border = borde
                cell.alignment = Alignment(vertical="center")
                c = cell.column
                if c == cols.get("Confianza"):
                    cell.alignment = centro
                    v = str(cell.value)
                    cell.fill = (fconf_alta if v == "alta" else fconf_media if v == "media"
                                 else fconf_baja if v == "baja" else fb)
                elif c == cols.get("Revisar"):
                    cell.alignment = centro
                    cell.fill = frev if str(cell.value) == "Sí" else (fv if str(cell.value) == "No" else fb)
                elif c == cols.get("Es de Liga"):
                    cell.alignment = centro
                    cell.fill = fl if str(cell.value) == "Sí" else fb
                elif c == cols.get("Método Búsqueda"):
                    cell.alignment = centro; cell.fill = fm
                    cell.font = Font(name="Arial", size=9, italic=True)
                elif c == cols.get("Número Buscado"):
                    cell.alignment = centro; cell.fill = fn
                elif c in usd_cols:
                    cell.alignment = centro; cell.fill = fb
                    if isinstance(cell.value, (int, float)):
                        cell.number_format = '"$"#,##0.00'
                elif c == cols.get("Precio CLP Sugerido"):
                    cell.alignment = centro; cell.fill = fb
                    if isinstance(cell.value, (int, float)):
                        cell.number_format = '"$"#,##0'
                elif c in (cols.get("Cantidad"), cols.get("Estado"),
                           cols.get("Número Coincide"), cols.get("Número Carta")):
                    cell.alignment = centro; cell.fill = fb
                else:
                    cell.fill = fb

        anchos = {
            "Cantidad": 9, "Estado": 9, "Nombre Original": 22, "Nombre EN": 22, "Tipo": 12,
            "Número Buscado": 14, "Regulation Mark": 14, "Es de Liga": 11,
            "Método Búsqueda": 16, "Set": 28, "Número Carta": 13, "Número Coincide": 12,
            "Rareza": 24, "Confianza": 12, "Revisar": 10,
            "Precio USD Mercado": 13, "Precio USD Ajustado": 13, "Precio CLP Sugerido": 15,
            "Variante Precio": 14, "Fecha Precio": 14, "URL Imagen": 48,
        }
        for i, col_name in enumerate(df.columns, start=1):
            ws.column_dimensions[get_column_letter(i)].width = anchos.get(col_name, 16)
        ws.freeze_panes = "A2"

    buffer.seek(0)
    return buffer.read()


# ══════════════════════════════════════════════════════════════════════════════
# CSS — MODO OSCURO COMPLETO + TARJETAS
# ══════════════════════════════════════════════════════════════════════════════

DARK_CSS = """
<style>
/* ── Base ── */
html, body,
[data-testid="stAppViewContainer"],
[data-testid="stApp"], .stApp {
    background-color: #0E1117 !important;
    color: #FFFFFF !important;
}

/* ── Sidebar ── */
[data-testid="stSidebar"] {
    background-color: #161B22 !important;
}
[data-testid="stSidebar"] * { color: #FFFFFF !important; }

/* ── Textos globales ── */
label, p, span, div, h1, h2, h3, h4, h5, h6,
.stMarkdown p, .stMarkdown span,
[data-testid="stCheckbox"] span,
[data-testid="stCheckbox"] p {
    color: #FFFFFF !important;
}

/* ── Inputs ── */
input, textarea,
[data-testid="stTextInput"] input,
[data-testid="stNumberInput"] input {
    background-color: #1E2530 !important;
    color: #FFFFFF !important;
    border-color: #3A4556 !important;
}

/* ── Selectbox ── */
[data-testid="stSelectbox"] > div > div {
    background-color: #1E2530 !important;
    color: #FFFFFF !important;
    border-color: #3A4556 !important;
}

/* ── File uploader ── */
[data-testid="stFileUploader"] {
    background-color: #1E2530 !important;
    border: 2px dashed #3A4556 !important;
    border-radius: 8px !important;
}
[data-testid="stFileUploadDropzone"] * { color: #A0AEC0 !important; }

/* ── Tabs ── */
[data-testid="stTabs"] {
    background-color: #0E1117 !important;
}
button[data-baseweb="tab"] {
    background-color: #161B22 !important;
    color: #A0AEC0 !important;
    border-bottom: 2px solid transparent !important;
}
button[data-baseweb="tab"][aria-selected="true"] {
    color: #FFFFFF !important;
    border-bottom: 2px solid #3182CE !important;
    background-color: #1E2530 !important;
}

/* ── Dataframe ── */
[data-testid="stDataFrame"], .stDataFrame, iframe {
    background-color: #161B22 !important;
}

/* ── Métricas ── */
[data-testid="stMetric"] {
    background-color: #1E2530 !important;
    border-radius: 10px !important;
    padding: 0.75rem 1rem !important;
    border: 1px solid #3A4556 !important;
}
[data-testid="stMetricValue"],
[data-testid="stMetricLabel"] { color: #FFFFFF !important; }

/* ── Alerts / Info ── */
[data-testid="stAlert"] {
    background-color: #1A2332 !important;
    border-left-color: #3182CE !important;
}
[data-testid="stAlert"] * { color: #BEE3F8 !important; }

/* ── Progress ── */
[data-testid="stProgressBar"] > div { background-color: #2B6CB0 !important; }

/* ── Botones ── */
button[kind="primary"] {
    background-color: #2B6CB0 !important;
    color: #FFFFFF !important; border: none !important;
}
button[kind="secondary"] {
    background-color: #1E2530 !important;
    color: #FFFFFF !important;
    border: 1px solid #3A4556 !important;
}

/* ── Expandir / Expander ── */
[data-testid="stExpander"] {
    background-color: #1E2530 !important;
    border: 1px solid #3A4556 !important;
    border-radius: 8px !important;
}

/* ─────────────────────────────────────────────────────────────────────────
   FIX FASE 6 — menú desplegable de selectbox/slider (popover de BaseWeb).
   Antes salía texto blanco sobre fondo blanco al abrir el selector. Estas
   reglas pintan la lista desplegable en oscuro y dejan el texto legible.
   ───────────────────────────────────────────────────────────────────────── */
[data-baseweb="popover"] { background-color: #1E2530 !important; }
[data-baseweb="popover"] * { color: #FFFFFF !important; }
[data-baseweb="menu"],
ul[role="listbox"] {
    background-color: #1E2530 !important;
    border: 1px solid #3A4556 !important;
}
[data-baseweb="menu"] li,
ul[role="listbox"] li,
li[role="option"],
[role="option"] {
    background-color: #1E2530 !important;
    color: #FFFFFF !important;
}
li[role="option"]:hover,
[role="option"]:hover,
[role="option"][aria-selected="true"] {
    background-color: #2D3748 !important;
    color: #FFFFFF !important;
}
[data-baseweb="select"] * { color: #FFFFFF !important; }

/* ── Código inline (los chips `nombre`, `tipo`… del sidebar): legibles ── */
code, [data-testid="stSidebar"] code, .stMarkdown code {
    background-color: #2D3748 !important;
    color: #9AE6B4 !important;
    padding: 1px 6px !important;
    border-radius: 5px !important;
    font-size: 0.82em !important;
    font-weight: 600 !important;
}

/* ── Tarjetas: hover sutil para un look más profesional ── */
.tcg-card { transition: transform 0.15s ease, box-shadow 0.15s ease; }
.tcg-card:hover { transform: translateY(-4px); box-shadow: 0 12px 30px rgba(0,0,0,0.65) !important; }

/* ── Botones primary con degradado ── */
button[kind="primary"] {
    background: linear-gradient(135deg,#2B6CB0 0%,#3182CE 100%) !important;
}

/* ── data_editor en oscuro ── */
[data-testid="stDataEditor"], [data-testid="stDataEditorContainer"] {
    background-color: #161B22 !important;
}

/* ── Scrollbar ── */
::-webkit-scrollbar { width: 6px; height: 6px; }
::-webkit-scrollbar-track { background: #0E1117; }
::-webkit-scrollbar-thumb { background: #3A4556; border-radius: 3px; }

/* ── Tarjetas personalizadas ── */
.card-wrapper {
    border-radius: 12px;
    padding: 0;
    overflow: hidden;
    transition: transform 0.15s ease;
}
</style>
"""


# ══════════════════════════════════════════════════════════════════════════════
# HELPERS DE RENDERIZADO
# ══════════════════════════════════════════════════════════════════════════════

def _clean(html: str) -> str:
    """
    Colapsa el HTML a una sola línea sin indentación.
    Streamlit (markdown) trata como 'bloque de código' cualquier línea indentada
    que venga después de una línea en blanco, y entonces muestra el HTML como
    texto crudo en vez de renderizarlo. Esto lo evita por completo.
    """
    return "".join(linea.strip() for linea in html.splitlines())


def texto_publicacion(row: dict, mi_precio=None) -> tuple[str, str]:
    """Genera (título, descripción) listos para copiar/pegar en una publicación."""
    nom = row.get("Nombre Original", "-")
    set_ = row.get("Set", "-")
    num = row.get("Número Carta", "-")
    est = row.get("Estado", "NM")
    est_desc = ESTADOS.get(est, ("", 0))[0]
    rar = row.get("Rareza", "-")
    mark = row.get("Regulation Mark", "-")
    precio = mi_precio if _has(mi_precio) else row.get("Precio CLP Sugerido")

    titulo = f"{nom} — {set_} #{num} ({est})"
    lineas = [
        f"🃏 {nom}",
        f"📦 Set: {set_}  ·  N° {num}  ·  Bloque {mark}",
        f"⭐ Rareza: {rar}",
        f"🛡️ Estado: {est} ({est_desc})",
    ]
    if _has(precio):
        lineas.append(f"💲 Precio: {_fmt_clp(precio)} CLP")
    return titulo, "\n".join(lineas)


def validar_entrada(df) -> tuple[list, list]:
    """Revisa el archivo de entrada y devuelve (errores, advertencias) legibles."""
    errores, advert = [], []
    if df is None or len(df) == 0:
        errores.append("El archivo está vacío o no se pudo leer.")
        return errores, advert

    cols = set(df.columns)
    for req in ("nombre", "tipo"):
        if req not in cols:
            errores.append(f"Falta la columna obligatoria «{req}».")

    if "nombre" in cols:
        vacias = int(df["nombre"].isna().sum()
                     + (df["nombre"].astype(str).str.strip() == "").sum())
        if vacias:
            advert.append(f"{vacias} fila(s) sin nombre: se ignorarán o fallarán.")

    if "estado" in cols:
        validos = set(ESTADO_ALIASES) | {k.lower() for k in ESTADOS}
        malos = sorted({str(v).strip() for v in df["estado"].dropna()
                        if str(v).strip() and str(v).strip().lower() not in validos
                        and str(v).strip().upper() not in ESTADOS})
        if malos:
            advert.append("Estados no reconocidos (se usará NM): " + ", ".join(malos[:6]))

    if "cantidad" in cols:
        def _malo(x):
            s = str(x).strip()
            if s in ("", "nan", "none"):
                return False
            try:
                int(float(s)); return False
            except ValueError:
                return True
        nb = int(sum(_malo(x) for x in df["cantidad"].dropna()))
        if nb:
            advert.append(f"{nb} valor(es) de «cantidad» no son números (se usará 1).")

    return errores, advert



def _badge_metodo(metodo: str) -> str:
    paleta = {
        "número exacto":   ("#1A365D", "#90CDF4", "🎯"),
        "nombre + bloque": ("#1C4532", "#9AE6B4", "📦"),
        "nombre + tipo":   ("#322659", "#D6BCFA", "🔤"),
        "solo nombre":     ("#652B19", "#FBD38D", "🔍"),
        "set forzado":     ("#234E52", "#9DECF9", "📌"),
        "selección manual":("#2A4365", "#90CDF4", "✋"),
        "sin resultados":  ("#1A202C", "#718096", "⚠️"),
    }
    bg, fg, ico = paleta.get(metodo, ("#1A202C", "#718096", "•"))
    return (
        f'<span style="background:{bg};color:{fg};font-size:0.65rem;'
        f'font-weight:600;padding:2px 7px;border-radius:20px;">{ico} {metodo}</span>'
    )


def _badge_confianza(conf: str) -> str:
    m = {
        "alta":    ("#1C4532", "#9AE6B4", "🟢 Alta"),
        "media":   ("#5F4B1B", "#FBD38D", "🟡 Media"),
        "baja":    ("#742A2A", "#FEB2B2", "🔴 Baja"),
        "ninguna": ("#2D3748", "#A0AEC0", "⚪ Sin datos"),
    }
    bg, fg, txt = m.get(conf, m["ninguna"])
    return (
        f'<span style="background:{bg};color:{fg};font-size:0.65rem;'
        f'font-weight:700;padding:2px 8px;border-radius:20px;">{txt}</span>'
    )


def _badge_estado(est: str) -> str:
    bg, fg = ESTADO_COLOR.get(est, ("#2D3748", "#CBD5E0"))
    return (
        f'<span style="background:{bg};color:{fg};font-size:0.65rem;'
        f'font-weight:700;padding:2px 8px;border-radius:20px;">{est}</span>'
    )


def _precio_html(row: dict) -> str:
    usd = row.get("Precio USD Mercado")
    clp = row.get("Precio CLP Sugerido")
    if not _has(usd):
        return ('<div style="text-align:center;font-size:0.7rem;color:#718096;'
                'margin-bottom:6px;">— sin precio de referencia —</div>')
    clp_txt = f'≈ {_fmt_clp(clp)} CLP' if _has(clp) else ""
    return (
        f'<div style="background:#0E1117;border-radius:8px;padding:6px 8px;'
        f'text-align:center;margin-bottom:7px;">'
        f'<span style="color:#718096;font-size:0.68rem;">ref. mercado:</span> '
        f'<span style="color:#CBD5E0;font-size:0.74rem;font-weight:600;">{_fmt_usd(usd)} USD</span><br>'
        f'<span style="color:#90CDF4;font-size:0.8rem;font-weight:700;">{clp_txt}</span></div>'
    )


def _tarjeta_html(row: dict) -> str:
    tipo  = row.get("Tipo", "")
    c     = TIPO_COLORES.get(tipo, COLOR_DEFAULT)
    img   = row.get("URL Imagen", "")
    met   = row.get("Método Búsqueda", "")
    cant  = row.get("Cantidad", 1)
    set_  = row.get("Set", "-")
    rar   = row.get("Rareza", "-")
    nom   = row.get("Nombre Original", row.get("Nombre EN", ""))
    num   = row.get("Número Carta", "-")
    mark  = row.get("Regulation Mark", "-")
    conf  = row.get("Confianza", "ninguna")
    est   = row.get("Estado", "NM")
    revisar = row.get("Revisar", "No") == "Sí"

    # Borde rojo + cinta de aviso si la carta necesita revisión antes de publicar
    borde = "#E53E3E" if revisar else c['border']
    ribbon = (
        '<div style="background:#742A2A;color:#FEB2B2;font-size:0.62rem;'
        'font-weight:700;text-align:center;border-radius:6px;padding:3px;'
        'margin-bottom:8px;">⚠️ REVISAR ANTES DE PUBLICAR</div>'
        if revisar else ''
    )

    img_html = (
        f'<img src="{img}" style="width:100%;max-width:180px;border-radius:8px;'
        f'display:block;margin:0 auto 10px;box-shadow:0 4px 15px rgba(0,0,0,0.5);">'
        if img else
        '<div style="width:130px;height:180px;background:#2D3748;border-radius:8px;'
        'margin:0 auto 10px;display:flex;align-items:center;justify-content:center;'
        'color:#4A5568;font-size:2rem;">🃏</div>'
    )

    return _clean(f"""
<div class="tcg-card" style="
    background:{c['bg']};
    border:1px solid {borde};
    border-radius:12px;
    padding:14px 12px 12px;
    height:100%;
    box-shadow:0 2px 12px rgba(0,0,0,0.4);
">
    {ribbon}
    {img_html}
    <p style="margin:0 0 4px;font-size:0.82rem;font-weight:700;
              color:#FFFFFF;text-align:center;line-height:1.2;">{nom}</p>
    <p style="margin:0 0 8px;font-size:0.7rem;color:{c['text']};text-align:center;">
        {set_}
    </p>
    <div style="text-align:center;margin-bottom:7px;">
        {_badge_estado(est)}
    </div>
    <div style="
        background:#0E1117;border-radius:8px;padding:8px 10px;
        font-size:0.72rem;color:#CBD5E0;line-height:1.8;margin-bottom:7px;
    ">
        <span style="color:#718096;">Tipo:</span>
        <span style="color:{c['text']};font-weight:600;"> {tipo}</span><br>
        <span style="color:#718096;">Rareza:</span> {rar}<br>
        <span style="color:#718096;">N° carta:</span> {num}
        &nbsp;&nbsp;<span style="color:#718096;">Bloque:</span> {mark}<br>
        <span style="color:#718096;">Cantidad:</span>
        <span style="color:#FFFFFF;font-weight:700;"> ×{cant}</span>
    </div>
    {_precio_html(row)}
    <div style="text-align:center;">{_badge_metodo(met)}&nbsp;{_badge_confianza(conf)}</div>
</div>
""")


def _ficha_detalle_html(row: dict) -> str:
    """Ficha técnica alternativa (helper disponible; el Inspector arma su tabla)."""
    tipo  = row.get("Tipo", "")
    c     = TIPO_COLORES.get(tipo, COLOR_DEFAULT)
    img   = row.get("URL Imagen", "")
    met   = row.get("Método Búsqueda", "")
    est   = row.get("Estado", "NM")

    img_html = (
        f'<img src="{img}" style="width:100%;max-width:260px;border-radius:12px;'
        f'box-shadow:0 6px 24px rgba(0,0,0,0.6);display:block;margin:0 auto;">'
        if img else
        '<div style="width:200px;height:280px;background:#2D3748;border-radius:12px;'
        'margin:0 auto;display:flex;align-items:center;justify-content:center;'
        'color:#4A5568;font-size:3rem;">🃏</div>'
    )

    campos = [
        ("Nombre Original",  row.get("Nombre Original", "-")),
        ("Nombre EN",        row.get("Nombre EN", "-")),
        ("Tipo",             row.get("Tipo", "-")),
        ("Set / Expansión",  row.get("Set", "-")),
        ("Número de Carta",  row.get("Número Carta", "-")),
        ("Número Buscado",   row.get("Número Buscado", "-")),
        ("N° Coincide",      row.get("Número Coincide", "-")),
        ("Regulation Mark",  row.get("Regulation Mark", "-")),
        ("Rareza",           row.get("Rareza", "-")),
        ("Estado",           f"{est} · {ESTADOS.get(est, ('', 0))[0]}"),
        ("Confianza",        row.get("Confianza", "-")),
        ("Es de Liga",       row.get("Es de Liga", "-")),
        ("Cantidad",         str(row.get("Cantidad", 1))),
        ("Precio ref. USD",  _fmt_usd(row.get("Precio USD Mercado"))),
        ("Precio CLP",       _fmt_clp(row.get("Precio CLP Sugerido"))),
        ("Método Búsqueda",  row.get("Método Búsqueda", "-")),
    ]

    filas_html = "".join(
        f'<tr>'
        f'<td style="padding:7px 12px;color:#718096;font-size:0.8rem;'
        f'white-space:nowrap;border-bottom:1px solid #2D3748;">{k}</td>'
        f'<td style="padding:7px 12px;color:#FFFFFF;font-size:0.85rem;'
        f'font-weight:500;border-bottom:1px solid #2D3748;">{v}</td>'
        f'</tr>'
        for k, v in campos
    )

    return _clean(f"""
<div style="
    background:{c['bg']};border:1px solid {c['border']};
    border-radius:16px;padding:24px 20px;
    box-shadow:0 4px 24px rgba(0,0,0,0.5);
">
    <div style="margin-bottom:20px;">{img_html}</div>
    <div style="text-align:center;margin-bottom:16px;">
        {_badge_metodo(met)}
    </div>
    <table style="width:100%;border-collapse:collapse;">
        {filas_html}
    </table>
</div>
""")


# ══════════════════════════════════════════════════════════════════════════════
# SECCIÓN 4 — DASHBOARD DE RESULTADOS
# ══════════════════════════════════════════════════════════════════════════════

def _rebuild_row(row: dict, carta: dict, clp_rate: float) -> dict:
    """Recalcula una fila a partir de una carta elegida manualmente."""
    estado = row.get("Estado", "NM")
    _, mult = ESTADOS.get(estado, ("", 1.0))
    numero = row.get("Número Buscado", "-")
    numero = "" if numero in ("-", "") else numero
    base = {k: row.get(k) for k in ["Cantidad", "Estado", "Nombre Original", "Nombre EN",
                                     "Tipo", "Número Buscado", "Regulation Mark", "Es de Liga"]}
    base["Método Búsqueda"] = "selección manual"
    nuevo = _resultado_desde_carta(base, carta, numero, bool(numero), mult, clp_rate)
    # El humano confirmó la versión: ya no necesita revisión.
    nuevo["Revisar"] = "No"
    nuevo["Confianza"] = "alta"
    nuevo["Número Coincide"] = "Sí"
    return nuevo


def render_dashboard(df_result: pd.DataFrame, clp_rate: float = 0, comision: float = 0.0):
    st.markdown("---")
    st.subheader("4. Dashboard del Catálogo de Venta")

    # ── Métricas ─────────────────────────────────────────────────────────────
    total_u   = int(df_result["Cantidad"].sum())
    alta      = int((df_result["Confianza"] == "alta").sum())
    por_rev   = int((df_result["Revisar"] == "Sí").sum())
    de_liga   = int((df_result["Es de Liga"] == "Sí").sum())
    ref_total = int(df_result.apply(
        lambda r: (r["Precio CLP Sugerido"] * r["Cantidad"]) if pd.notna(r["Precio CLP Sugerido"]) else 0,
        axis=1).sum())

    m1, m2, m3, m4, m5 = st.columns(5)
    m1.metric("📦 Unidades",       total_u)
    m2.metric("🟢 Alta confianza", alta)
    m3.metric("⚠️ Por revisar",    por_rev)
    m4.metric("🏆 De Liga",        de_liga)
    m5.metric("💲 Valor inventario (ref.)", _fmt_clp(ref_total),
              help="Suma de precio de referencia × cantidad de las cartas del último procesamiento.")

    # ── Bandeja de revisión (cartas con match dudoso) ────────────────────────
    df_rev = df_result[df_result["Revisar"] == "Sí"]
    if not df_rev.empty:
        st.markdown(
            f'<div style="background:#742A2A;border-radius:8px;padding:10px 14px;margin:10px 0;">'
            f'<span style="color:#FEB2B2;font-weight:700;font-size:0.95rem;">'
            f'⚠️ {len(df_rev)} carta(s) necesitan revisión antes de publicar</span></div>',
            unsafe_allow_html=True)
        with st.expander("Ver cartas a revisar — el N° pedido no se encontró o el match es ambiguo", expanded=True):
            st.caption("Verifica el arte real en el Inspector antes de listar. Si el número buscado "
                       "no coincide con el encontrado, probablemente sea otra versión de la carta.")
            cols_rev = ["Nombre Original", "Número Buscado", "Número Carta", "Número Coincide",
                        "Set", "Método Búsqueda", "Confianza"]
            st.dataframe(df_rev[cols_rev], use_container_width=True, hide_index=True)

            # ── Selección manual de variante ──────────────────────────────
            candidatos_all = st.session_state.get("candidatos", {})
            corregibles = [i for i in df_rev.index if len(candidatos_all.get(i, [])) > 1]
            if corregibles:
                st.markdown("**🔧 Corregir versión manualmente**")
                st.caption("Si el sistema eligió la versión equivocada, escoge la correcta y confírmala.")
                for idx in corregibles:
                    row = df_result.loc[idx].to_dict()
                    cands = candidatos_all.get(idx, [])
                    labels = [
                        f"{c['set']['name']} · #{c['number']} · {c.get('rarity', '-')}"
                        f" · marca {c.get('regulationMark') or '-'}"
                        + ("  💲 con precio" if _tiene_precio(c) else "  (sin precio)")
                        for c in cands
                    ]
                    default_i = next(
                        (j for j, c in enumerate(cands)
                         if c['set']['name'] == row.get('Set')
                         and str(c['number']) == str(row.get('Número Carta'))), 0)
                    ca, cb = st.columns([4, 1])
                    with ca:
                        sel_var = st.selectbox(
                            f"Versión de «{row.get('Nombre Original')}»",
                            labels, index=default_i, key=f"variant_{idx}")
                    with cb:
                        st.markdown("<div style='height:28px'></div>", unsafe_allow_html=True)
                        if st.button("✅ Usar", key=f"usevar_{idx}"):
                            chosen = cands[labels.index(sel_var)]
                            nuevo = _rebuild_row(row, chosen, clp_rate)
                            for k, v in nuevo.items():
                                df_result.at[idx, k] = v
                            st.session_state["df_result"] = df_result
                            st.rerun()
    else:
        st.success("✅ Todas las cartas tienen match confiable. Listas para publicar.")

    st.markdown("---")

    # ── Tabs: Cuadrícula · Tabla · Inspector ─────────────────────────────────
    tab_grid, tab_tabla, tab_inspector, tab_precios = st.tabs(
        ["🃏 Vista Cuadrícula", "📋 Vista Tabla", "🔍 Inspector de Carta", "💲 Precios y venta"]
    )

    # ┌─────────────────────────────────────────────────────────────────────┐
    # │  TAB 1 — CUADRÍCULA DE TARJETAS                                       │
    # └─────────────────────────────────────────────────────────────────────┘
    with tab_grid:
        # Filtros rápidos
        fc1, fc2, fc3 = st.columns([2, 1.6, 1.6])
        with fc1:
            filtro_tipo = st.selectbox(
                "Filtrar por Tipo",
                ["Todos"] + sorted(df_result["Tipo"].dropna().unique().tolist()),
                key="filtro_tipo",
            )
        with fc2:
            n_cols = st.select_slider(
                "Cartas por fila",
                options=[2, 3, 4, 5, 6],
                value=4,
                key="n_cols",
            )
        with fc3:
            solo_rev = st.checkbox("Solo por revisar", value=False, key="solo_rev")

        # Aplicar filtros
        df_vis = df_result.copy()
        if filtro_tipo != "Todos":
            df_vis = df_vis[df_vis["Tipo"] == filtro_tipo]
        if solo_rev:
            df_vis = df_vis[df_vis["Revisar"] == "Sí"]

        if df_vis.empty:
            st.warning("No hay cartas que coincidan con los filtros aplicados.")
        else:
            st.caption(f"Mostrando {len(df_vis)} carta(s)")
            filas = [df_vis.iloc[i:i+n_cols] for i in range(0, len(df_vis), n_cols)]
            for fila_df in filas:
                cols_grid = st.columns(n_cols)
                for col_st, (_, row) in zip(cols_grid, fila_df.iterrows()):
                    with col_st:
                        st.markdown(_tarjeta_html(row.to_dict()), unsafe_allow_html=True)
                        st.markdown("<div style='height:12px'></div>", unsafe_allow_html=True)

    # ┌─────────────────────────────────────────────────────────────────────┐
    # │  TAB 2 — TABLA CLÁSICA                                                │
    # └─────────────────────────────────────────────────────────────────────┘
    with tab_tabla:
        st.info(
            "🖼️ La columna **Arte** muestra la imagen exacta devuelta por la API. "
            "Usa **Confianza** / **Revisar** para auditar el match antes de vender."
        )
        col_config = {
            "URL Imagen": st.column_config.ImageColumn(
                "🖼️ Arte", help="Imagen de la variante encontrada", width="medium"
            ),
            "Cantidad":        st.column_config.NumberColumn("Cant.", format="%d", width="small"),
            "Estado":          st.column_config.TextColumn("Estado", width="small"),
            "Confianza":       st.column_config.TextColumn("Confianza", width="small"),
            "Revisar":         st.column_config.TextColumn("Revisar", width="small"),
            "Número Coincide": st.column_config.TextColumn("N° OK", width="small"),
            "Método Búsqueda": st.column_config.TextColumn("Método", width="medium"),
            "Número Buscado":  st.column_config.TextColumn("N° Buscado", width="small"),
            "Precio USD Mercado":  st.column_config.NumberColumn("USD ref.", format="$%.2f", width="small"),
            "Precio USD Ajustado": st.column_config.NumberColumn("USD ajust.", format="$%.2f", width="small"),
            "Precio CLP Sugerido": st.column_config.NumberColumn("CLP sug.", format="$%d", width="small"),
        }
        st.dataframe(df_result, column_config=col_config, use_container_width=True, height=480)

    # ┌─────────────────────────────────────────────────────────────────────┐
    # │  TAB 3 — INSPECTOR INTERACTIVO                                        │
    # └─────────────────────────────────────────────────────────────────────┘
    with tab_inspector:
        st.markdown("""
        <p style="color:#A0AEC0;font-size:0.9rem;margin-bottom:1rem;">
        Selecciona cualquier carta del inventario para ver su ficha técnica completa
        y verificar que el arte encontrado coincide con tu carta física.
        </p>
        """, unsafe_allow_html=True)

        opciones = [
            f"{i+1}. {r['Nombre Original']}  ·  #{r['Número Carta']}  ·  {r['Set']}"
            + ("  ⚠️" if r['Revisar'] == "Sí" else "")
            for i, (_, r) in enumerate(df_result.iterrows())
        ]

        sel = st.selectbox(
            "🔍 Inspeccionar Carta del Inventario",
            opciones,
            key="inspector_sel",
        )
        idx_sel = opciones.index(sel)
        row_sel = df_result.iloc[idx_sel].to_dict()

        # Aviso si la carta seleccionada está marcada para revisión
        if row_sel.get("Revisar") == "Sí":
            st.markdown(
                '<div style="background:#742A2A;color:#FEB2B2;border-radius:8px;'
                'padding:10px 14px;margin-bottom:12px;font-size:0.88rem;font-weight:600;">'
                '⚠️ Esta carta necesita revisión: el match puede no corresponder a tu carta '
                'física. Confirma el arte antes de publicar.</div>',
                unsafe_allow_html=True)

        # Panel de dos columnas: imagen grande · ficha técnica
        col_img, col_datos = st.columns([1, 1], gap="large")

        with col_img:
            img_url = row_sel.get("URL Imagen", "")
            if img_url:
                st.markdown(f"""
                <div style="text-align:center;padding:16px;">
                    <img src="{img_url}"
                         style="max-width:100%;width:280px;border-radius:14px;
                                box-shadow:0 8px 32px rgba(0,0,0,0.7);">
                </div>
                """, unsafe_allow_html=True)
            else:
                st.markdown("""
                <div style="
                    width:200px;height:280px;background:#2D3748;
                    border-radius:12px;margin:0 auto;
                    display:flex;align-items:center;justify-content:center;
                    color:#4A5568;font-size:3rem;
                ">🃏</div>
                """, unsafe_allow_html=True)
                st.caption("Sin imagen disponible")

        with col_datos:
            tipo_c = TIPO_COLORES.get(row_sel.get("Tipo", ""), COLOR_DEFAULT)
            est    = row_sel.get("Estado", "NM")
            est_desc = ESTADOS.get(est, ("", 0))[0]

            filas_tabla = [
                ("Set",                       row_sel.get('Set', '-')),
                ("Número",                    f"{row_sel.get('Número Carta', '-')} "
                                              f"(buscado: {row_sel.get('Número Buscado', '-')})"),
                ("N° coincide",               row_sel.get('Número Coincide', '-')),
                ("Rareza",                    row_sel.get('Rareza', '-')),
                ("Tipo",                      row_sel.get('Tipo', '-')),
                ("Reg. Mark",                 row_sel.get('Regulation Mark', '-')),
                ("Estado",                    f"{est} · {est_desc}"),
                ("Liga/Promo",                row_sel.get('Es de Liga', '-')),
                ("Cantidad",                  f"×{row_sel.get('Cantidad', 1)}"),
                ("Precio ref. (USD)",         _fmt_usd(row_sel.get('Precio USD Mercado'))),
                ("Precio ajustado x estado",  _fmt_usd(row_sel.get('Precio USD Ajustado'))),
                ("Precio sugerido (CLP)",     _fmt_clp(row_sel.get('Precio CLP Sugerido'))),
                ("Precio actualizado",        row_sel.get('Fecha Precio', '-')),
            ]
            filas_html = "".join(
                f"<tr><td style='color:#718096;padding:5px 8px;border-bottom:1px solid #2D3748;'>{k}</td>"
                f"<td style='color:#FFFFFF;padding:5px 8px;border-bottom:1px solid #2D3748;font-weight:500;'>{v}</td></tr>"
                for k, v in filas_tabla
            )

            st.markdown(f"""
            <div style="
                background:{tipo_c['bg']};
                border:1px solid {tipo_c['border']};
                border-radius:14px;padding:20px;
            ">
                <h3 style="color:#FFFFFF;margin:0 0 4px;font-size:1.15rem;">
                    {row_sel.get('Nombre Original', '-')}
                </h3>
                <p style="color:{tipo_c['text']};margin:0 0 12px;font-size:0.85rem;">
                    {row_sel.get('Nombre EN', '-')}
                </p>
                <div style="margin-bottom:12px;">
                    {_badge_estado(est)}&nbsp;
                    {_badge_confianza(row_sel.get('Confianza', 'ninguna'))}&nbsp;
                    {_badge_metodo(row_sel.get('Método Búsqueda', ''))}
                </div>
                <table style="width:100%;border-collapse:collapse;font-size:0.83rem;">
                    {filas_html}
                </table>
            </div>
            """, unsafe_allow_html=True)

        st.markdown("---")
        titulo_pub, desc_pub = texto_publicacion(row_sel)
        st.markdown("**📣 Texto para publicar** — usa el botón de copiar del recuadro:")
        st.code(f"{titulo_pub}\n\n{desc_pub}", language=None)

    # ┌─────────────────────────────────────────────────────────────────────┐
    # │  TAB 4 — PRECIOS Y VENTA (precio editable + comisión)                │
    # └─────────────────────────────────────────────────────────────────────┘
    with tab_precios:
        st.caption("Ajusta «Mi Precio CLP» por carta (parte del sugerido del mercado). "
                   "El neto descuenta la comisión de la plataforma.")
        cols_ro = ["Nombre Original", "Set", "Número Carta", "Estado", "Cantidad", "Precio CLP Sugerido"]
        edf = df_result[cols_ro].copy()
        edf["Mi Precio CLP"] = pd.to_numeric(df_result["Precio CLP Sugerido"], errors="coerce").fillna(0).astype(int)
        edited = st.data_editor(
            edf, hide_index=True, use_container_width=True, height=430,
            disabled=cols_ro,
            column_config={
                "Nombre Original": st.column_config.TextColumn("Carta", width="medium"),
                "Número Carta": st.column_config.TextColumn("N°", width="small"),
                "Estado": st.column_config.TextColumn("Estado", width="small"),
                "Cantidad": st.column_config.NumberColumn("Cant.", format="%d", width="small"),
                "Precio CLP Sugerido": st.column_config.NumberColumn("Sugerido CLP", format="$%d"),
                "Mi Precio CLP": st.column_config.NumberColumn("Mi Precio CLP", format="$%d", min_value=0, step=500),
            },
            key="editor_precios",
        )
        com = float(comision or 0)
        mip = pd.to_numeric(edited["Mi Precio CLP"], errors="coerce").fillna(0)
        cant = pd.to_numeric(edited["Cantidad"], errors="coerce").fillna(1)
        neto_unit = (mip * (1 - com / 100)).round().astype(int)
        total_bruto = int((mip * cant).sum())
        total_neto = int((neto_unit * cant).sum())
        cc1, cc2 = st.columns(2)
        cc1.metric("💵 Total a precio de venta", _fmt_clp(total_bruto))
        cc2.metric(f"💰 Neto tras comisión ({com:.1f}%)", _fmt_clp(total_neto))

        venta = df_result.copy()
        venta["Mi Precio CLP"] = mip.values
        venta["Neto CLP"] = neto_unit.values
        st.download_button(
            "📥 Descargar lista de venta (.xlsx)",
            data=exportar_excel(venta),
            file_name="lista_venta_tcg.xlsx",
            use_container_width=True, type="primary", key="dl_venta",
        )

    # ── Descarga Excel ────────────────────────────────────────────────────────
    st.markdown("---")
    bytes_excel = exportar_excel(df_result)
    st.download_button(
        label="📥 Descargar catálogo completo (.xlsx)",
        data=bytes_excel,
        file_name="catalogo_pokemon_tcg_fase6.xlsx",
        use_container_width=True,
        type="secondary",
    )


# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

def _agregar_resultado_al_dashboard(res: dict) -> int:
    """Añade un resultado (de procesar_carta) al df_result en sesión. Devuelve su índice."""
    cand = res.pop("_candidatos", []) if isinstance(res, dict) else []
    df_new = pd.DataFrame([res])
    if "df_result" in st.session_state and not st.session_state["df_result"].empty:
        df_comb = pd.concat([st.session_state["df_result"], df_new], ignore_index=True)
    else:
        df_comb = df_new
    st.session_state["df_result"] = df_comb
    idx = len(df_comb) - 1
    st.session_state.setdefault("candidatos", {})[idx] = cand
    return idx


def main():
    st.set_page_config(
        page_title="Catalogador Pokémon TCG",
        page_icon="⚡",
        layout="wide",
        initial_sidebar_state="expanded",
    )

    st.markdown(DARK_CSS, unsafe_allow_html=True)

    # Header
    st.markdown("""
    <div style="
        background:linear-gradient(135deg,#1A1A2E 0%,#16213E 50%,#0F3460 100%);
        padding:2rem 2.5rem;border-radius:12px;margin-bottom:1.5rem;
    ">
        <span style="
            display:inline-block;background:#2B6CB0;color:white;
            font-size:0.75rem;font-weight:600;padding:3px 12px;
            border-radius:20px;margin-bottom:0.75rem;letter-spacing:0.05em;
        ">BETA · PROTOTIPO</span>
        <h1 style="color:white;margin:0;font-size:2rem;">
            ⚡ Catalogador Inteligente — Pokémon TCG
        </h1>
        <p style="color:#A0AEC0;margin:0.5rem 0 0;font-size:1rem;">
            Sube la lista de tus cartas y te las dejo identificadas, valorizadas y listas para vender.
        </p>
    </div>
    """, unsafe_allow_html=True)

    # ── Pantalla de bienvenida (solo si aún no hay resultados) ────────────────
    if "df_result" not in st.session_state:
        st.markdown("""
        <div style="background:#161B22;border:1px solid #2D3748;border-radius:12px;
                    padding:1.5rem 1.75rem;margin-bottom:1.25rem;">
            <p style="color:#FFFFFF;font-size:1.05rem;margin:0 0 1rem;font-weight:600;">
                🎯 ¿Qué hace esta herramienta?
            </p>
            <p style="color:#CBD5E0;font-size:0.95rem;margin:0 0 1.25rem;line-height:1.6;">
                Catalogar cartas Pokémon a mano es lento: hay que buscar cada versión, su set, su
                rareza y su precio una por una. Esta app lo hace por ti en lote: subes una lista
                simple y te devuelve cada carta identificada con su arte exacto, su precio de
                referencia y lista para publicar.
            </p>
            <div style="display:flex;gap:1rem;flex-wrap:wrap;">
                <div style="flex:1;min-width:180px;background:#1E2530;border-radius:10px;padding:1rem;">
                    <div style="font-size:1.5rem;">1️⃣</div>
                    <p style="color:#90CDF4;font-weight:700;margin:0.4rem 0 0.2rem;">Sube tu lista</p>
                    <p style="color:#A0AEC0;font-size:0.85rem;margin:0;">Un Excel con nombre, número y estado. O usa los datos de ejemplo.</p>
                </div>
                <div style="flex:1;min-width:180px;background:#1E2530;border-radius:10px;padding:1rem;">
                    <div style="font-size:1.5rem;">2️⃣</div>
                    <p style="color:#9AE6B4;font-weight:700;margin:0.4rem 0 0.2rem;">La app identifica</p>
                    <p style="color:#A0AEC0;font-size:0.85rem;margin:0;">Busca cada carta en la base oficial y encuentra el arte exacto y su precio.</p>
                </div>
                <div style="flex:1;min-width:180px;background:#1E2530;border-radius:10px;padding:1rem;">
                    <div style="font-size:1.5rem;">3️⃣</div>
                    <p style="color:#FBD38D;font-weight:700;margin:0.4rem 0 0.2rem;">Revisa y vende</p>
                    <p style="color:#A0AEC0;font-size:0.85rem;margin:0;">Ajustas precios, revisas dudosas y descargas tu lista lista para publicar.</p>
                </div>
            </div>
            <p style="color:#F6E05E;font-size:0.9rem;margin:1.1rem 0 0;">
                👇 ¿Primera vez? Más abajo deja marcado <b>“Usar datos de prueba”</b> y pulsa
                <b>⚡ Iniciar búsqueda</b> para ver una demo al instante.
            </p>
        </div>
        """, unsafe_allow_html=True)

    # ── Sidebar ───────────────────────────────────────────────────────────────
    with st.sidebar:
        st.header("⚙️ Configuración")

        # API key permanente: si existe en .streamlit/secrets.toml la usamos
        # como valor por defecto, así no hay que pegarla en cada recarga.
        def _api_key_de_secrets():
            try:
                return st.secrets.get("pokemontcg_api_key", "") or ""
            except Exception:
                return ""

        if "api_key_guardada" not in st.session_state:
            st.session_state["api_key_guardada"] = _api_key_de_secrets()

        api_key_input = st.text_input(
            "API Key (opcional)", type="password",
            placeholder="pokemontcg.io key",
            value=st.session_state["api_key_guardada"],
            help="Clave gratuita en pokemontcg.io. Para dejarla fija, ponla en "
                 ".streamlit/secrets.toml como pokemontcg_api_key = \"tu-key\".",
        )
        if api_key_input != st.session_state["api_key_guardada"]:
            st.session_state["api_key_guardada"] = api_key_input

        api_key = st.session_state["api_key_guardada"] or None

        if api_key:
            origen = " (desde secrets.toml)" if api_key == _api_key_de_secrets() else ""
            st.success(f"🔑 API Key activa — velocidad óptima (4 workers){origen}")
        else:
            st.info("💡 Sin API key: 3 workers con throttle. Obtén una gratis en pokemontcg.io")
        clp_rate = st.number_input(
            "Tipo de cambio USD → CLP", min_value=0, value=950, step=10,
            help="Para sugerir el precio en pesos a partir del precio de mercado. "
                 "Pon 0 si no quieres convertir.",
        )
        comision = st.number_input(
            "Comisión plataforma (%)", min_value=0.0, max_value=50.0, value=0.0, step=0.5,
            help="Se descuenta del precio para calcular tu neto en la pestaña «Precios y venta».",
        )
        st.markdown("---")
        st.subheader("⚡ Velocidad")
        cfg_workers = st.slider(
            "Workers en paralelo", min_value=1, max_value=8, value=4,
            help="Más workers = más rápido, pero si la API te limita (429) súbelo poco.",
        )
        cfg_throttle = st.slider(
            "Espera entre peticiones (s)", min_value=0.0, max_value=2.0, value=0.2, step=0.1,
            help="Si ves muchos 429 en el diagnóstico, sube esto a 0.5–1.0.",
        )
        _CFG["max_workers"] = cfg_workers
        _CFG["throttle"] = cfg_throttle

        st.markdown("---")
        st.subheader("📂 Base de datos local")
        if not _DB_LOADED:
            for cp in ("card_data", os.path.join("pokemon-tcg-data", "cards", "en"),
                       os.path.join("pokemon-tcg-data-master", "cards", "en")):
                if os.path.isdir(cp) and cargar_base_local(cp):
                    break
        if _DB_LOADED:
            st.success(f"✅ Base local activa — {len(_DB_CARDS):,} cartas. "
                       "Búsqueda instantánea, sin depender de la API.")
            st.caption("Nota: los precios de mercado vienen de la API en vivo; en modo "
                       "local pueden no aparecer si los datos estáticos no los traen.")
        else:
            st.info("Usando la API en vivo. Para que NO dependa de la API (instantáneo y "
                    "estable aunque la API esté caída), descarga la base local — ver README.")
        st.markdown("---")
        st.subheader("📋 Columnas del archivo")
        st.markdown("""
| Columna | Ejemplo | Notas |
|---|---|---|
| `nombre` | Charizard ex | ✅ Obligatoria |
| `tipo` | Pokémon / Trainer | ✅ Obligatoria |
| `regulation_mark` | G | Opcional |
| `numero` | 234 · 125 · TG30 | ⭐ Recomendada |
| `estado` | NM/LP/MP/HP/DMG | Opcional (def. NM) |
| `cantidad` | 4 | Opcional (def. 1) |
| `es_de_liga` | Sí / No | Opcional |
| `set_forzado` | Ascended Heroes | Opcional · fuerza el set |
        """)
        st.markdown("---")
        st.markdown("""
**⭐ Columna `numero`**
El número impreso en la esquina inferior de la carta.
Permite identificar el **arte exacto** (Common, Full Art, SIR…).

**Cascada automática:**
🎯 `nombre + número` → arte exacto
📦 `nombre + bloque` → fallback estándar
🔤 `nombre + tipo` → sin bloque
🔍 `solo nombre` → salvavidas

**🟢 Confianza del match:**
Alta = N° encontrado exacto. Baja = se pidió un N°
pero la API trajo otra versión → **revisar**.

**🏷️ Estado:** NM/LP/MP/HP/DMG ajusta el precio sugerido.
        """)
        st.markdown("---")
        st.caption("pokemontcg.io · Fase 6 · Herramienta de venta")

    # ── Upload + Preview ──────────────────────────────────────────────────────
    col_izq, col_der = st.columns([1, 1], gap="large")

    with col_izq:
        st.subheader("1. Sube tu archivo")
        archivo = st.file_uploader(
            "Arrastra tu archivo aquí",
            type=["xlsx", "xls", "csv"],
            label_visibility="collapsed",
        )
        df_ej = pd.DataFrame([
            {"nombre": "Charizard ex",  "tipo": "Pokémon", "regulation_mark": "G",
             "numero": "234", "estado": "NM", "cantidad": 2, "es_de_liga": "No"},
            {"nombre": "Charizard ex",  "tipo": "Pokémon", "regulation_mark": "G",
             "numero": "125", "estado": "LP", "cantidad": 1, "es_de_liga": "No"},
            {"nombre": "Boss's Orders", "tipo": "Trainer", "regulation_mark": "G",
             "numero": "172", "estado": "NM", "cantidad": 4, "es_de_liga": "No"},
            {"nombre": "Iono",          "tipo": "Trainer", "regulation_mark": "G",
             "numero": "",    "estado": "MP", "cantidad": 4, "es_de_liga": "No"},
            {"nombre": "Pikachu ex",    "tipo": "Pokémon", "regulation_mark": "H",
             "numero": "241", "estado": "NM", "cantidad": 2, "es_de_liga": "No"},
        ])
        buf = io.BytesIO()
        df_ej.to_excel(buf, index=False)
        buf.seek(0)
        st.download_button(
            "📥 Descargar archivo de ejemplo (.xlsx)",
            data=buf,
            file_name="lista_ejemplo_fase6.xlsx",
            use_container_width=True,
        )

    with col_der:
        st.subheader("2. Vista previa")
        df_input = None
        if archivo is not None:
            try:
                df_raw = (
                    pd.read_csv(archivo)
                    if archivo.name.endswith(".csv")
                    else pd.read_excel(archivo)
                )
                df_raw.columns = [
                    c.strip().lower()
                     .replace(" ", "_")
                     .replace("número", "numero")
                     .replace("ú", "u")
                    for c in df_raw.columns
                ]
                if "numero" in df_raw.columns:
                    df_raw["numero"] = df_raw["numero"].fillna("").astype(str).str.strip()
                df_input = df_raw
                # Si se subió un archivo distinto, descartamos resultados viejos
                # para que el dashboard no muestre datos del procesamiento anterior.
                sig = f"{archivo.name}-{getattr(archivo, 'size', len(df_raw))}"
                if st.session_state.get("last_file_sig") != sig:
                    st.session_state["last_file_sig"] = sig
                    st.session_state.pop("df_result", None)
                    st.session_state.pop("candidatos", None)
                st.dataframe(df_input, use_container_width=True, height=240)
            except Exception as e:
                st.error(f"Error al leer el archivo: {e}")
        else:
            st.markdown("""
            <div style="background:#1E2530;border-left:4px solid #D69E2E;
                        border-radius:6px;padding:0.75rem 1rem;
                        color:#F6E05E;font-size:0.875rem;">
                📂 Sube un archivo para comenzar — o activa los datos de prueba abajo.
            </div>
            """, unsafe_allow_html=True)

    # ── Carga manual de una carta (sin Excel) ─────────────────────────────────
    st.markdown("---")
    st.markdown("""
    <div style="display:flex;align-items:center;gap:10px;margin-bottom:2px;">
        <span style="font-size:1.15rem;font-weight:700;color:#FFFFFF;
              font-family:inherit;">✍️ ¿Solo unas pocas cartas?</span>
        <span style="background:#234E52;color:#9DECF9;font-size:0.68rem;font-weight:700;
              padding:2px 9px;border-radius:999px;letter-spacing:.04em;">SIN EXCEL</span>
    </div>
    <p style="color:#A0AEC0;font-size:0.9rem;margin:0 0 4px;">
        Agrégalas una por una acá abajo. Se procesan al instante y aparecen en el dashboard.
    </p>
    """, unsafe_allow_html=True)

    with st.expander("➕ Agregar una carta a mano", expanded=False):
        with st.form("form_carta_manual", clear_on_submit=True):
            mc1, mc2 = st.columns([2, 1])
            m_nombre = mc1.text_input("Nombre de la carta *", placeholder="Ej: Charizard ex")
            m_tipo = mc2.selectbox("Tipo", ["Pokémon", "Trainer", "Energy"])
            mc3, mc4, mc5 = st.columns(3)
            m_numero = mc3.text_input("N° de carta", placeholder="Ej: 234")
            m_bloque = mc4.text_input("Bloque", placeholder="Ej: G / H")
            m_estado = mc5.selectbox("Estado", ["NM", "LP", "MP", "HP", "DMG"])
            mc6, mc7 = st.columns([1, 2])
            m_cantidad = mc6.number_input("Cantidad", min_value=1, max_value=99, value=1, step=1)
            m_liga = mc7.checkbox("Es versión de Liga / Promo")
            m_enviar = st.form_submit_button("➕ Agregar y procesar carta", type="primary",
                                             use_container_width=True)

        if m_enviar:
            if not m_nombre.strip():
                st.error("⛔ Escribe el nombre de la carta.")
            else:
                fila_manual = {
                    "nombre": m_nombre, "tipo": m_tipo, "regulation_mark": m_bloque,
                    "numero": str(m_numero).strip(), "estado": m_estado,
                    "cantidad": m_cantidad, "es_de_liga": "Sí" if m_liga else "No",
                    "set_forzado": "",
                }
                with st.spinner(f"Buscando «{m_nombre}»…"):
                    res = procesar_carta(fila_manual, api_key or None, clp_rate)
                if res.get("Set") == "No encontrado":
                    # No encontrada: en vez de agregarla a ciegas, ofrecemos sugerencias
                    sugerencias = sugerir_nombres(m_nombre, api_key or None)
                    st.session_state["manual_no_encontrada"] = {
                        "fila": fila_manual, "sugerencias": sugerencias,
                    }
                    st.rerun()
                else:
                    _agregar_resultado_al_dashboard(res)
                    st.success(f"✅ «{m_nombre}» agregada al dashboard.")
                    st.rerun()

    # ── Sugerencia «¿quisiste decir…?» cuando la carta no se encontró ─────────
    pendiente = st.session_state.get("manual_no_encontrada")
    if pendiente:
        fila_p = pendiente["fila"]
        sugs = pendiente["sugerencias"]
        nombre_p = fila_p["nombre"]
        st.markdown(f"""
        <div style="background:#2D2018;border:1px solid #D69E2E;border-radius:12px;
                    padding:1rem 1.25rem;margin-top:6px;">
            <p style="color:#F6E05E;font-weight:700;margin:0 0 2px;">
                🔎 No encontré «{nombre_p}»
            </p>
            <p style="color:#CBD5E0;font-size:0.9rem;margin:0;">
                {"¿Quisiste decir alguna de estas? Toca para corregir y reprocesar:"
                 if sugs else "No hay nombres parecidos en la base. Revisa la ortografía o agrégala igual."}
            </p>
        </div>
        """, unsafe_allow_html=True)

        if sugs:
            cols_s = st.columns(min(len(sugs), 4))
            for i, s in enumerate(sugs):
                if cols_s[i % len(cols_s)].button(f"✓ {s}", key=f"sug_{i}", use_container_width=True):
                    fila_corr = dict(fila_p, nombre=s)
                    with st.spinner(f"Buscando «{s}»…"):
                        res2 = procesar_carta(fila_corr, api_key or None, clp_rate)
                    _agregar_resultado_al_dashboard(res2)
                    st.session_state.pop("manual_no_encontrada", None)
                    st.success(f"✅ «{s}» agregada al dashboard.")
                    st.rerun()

        c_ig, c_ca = st.columns(2)
        if c_ig.button("➕ Agregar igual (como no encontrada)", use_container_width=True):
            with st.spinner("Agregando…"):
                res3 = procesar_carta(fila_p, api_key or None, clp_rate)
            _agregar_resultado_al_dashboard(res3)
            st.session_state.pop("manual_no_encontrada", None)
            st.warning(f"Se agregó «{nombre_p}» como no encontrada.")
            st.rerun()
        if c_ca.button("✕ Cancelar", use_container_width=True):
            st.session_state.pop("manual_no_encontrada", None)
            st.rerun()

    # ── Procesamiento ─────────────────────────────────────────────────────────
    st.markdown("---")
    st.subheader("3. Procesar y enriquecer (desde archivo)")

    usar_demo = st.checkbox("Usar datos de prueba internos", value=(archivo is None))
    if usar_demo:
        df_input = pd.DataFrame([
            {"nombre": "Charizard ex",  "tipo": "Pokémon", "regulation_mark": "G",
             "numero": "234", "estado": "NM", "cantidad": 2, "es_de_liga": "No"},
            {"nombre": "Iono",          "tipo": "Trainer", "regulation_mark": "G",
             "numero": "",    "estado": "LP", "cantidad": 4, "es_de_liga": "No"},
            {"nombre": "Boss's Orders", "tipo": "Trainer", "regulation_mark": "G",
             "numero": "172", "estado": "NM", "cantidad": 4, "es_de_liga": "No"},
            {"nombre": "Pikachu ex",    "tipo": "Pokémon", "regulation_mark": "H",
             "numero": "", "estado": "MP", "cantidad": 2, "es_de_liga": "No"},
            {"nombre": "Gardevoir ex",  "tipo": "Pokémon", "regulation_mark": "G",
             "numero": "",    "estado": "NM", "cantidad": 3, "es_de_liga": "No"},
            {"nombre": "Arven",         "tipo": "Trainer", "regulation_mark": "G",
             "numero": "",    "estado": "LP", "cantidad": 4, "es_de_liga": "No"},
        ])

    # ── Validación del archivo de entrada ─────────────────────────────────────
    errores, advertencias = ([], [])
    if df_input is not None:
        errores, advertencias = validar_entrada(df_input)
        for e in errores:
            st.error("⛔ " + e)
        for a in advertencias:
            st.warning("⚠️ " + a)

    boton = st.button(
        "⚡ Iniciar búsqueda en lote",
        type="primary",
        use_container_width=True,
        disabled=(df_input is None or bool(errores)),
    )

    if "df_result" in st.session_state:
        if st.button("🗑️ Limpiar resultados", use_container_width=True, key="limpiar"):
            st.session_state.pop("df_result", None)
            st.session_state.pop("candidatos", None)
            st.rerun()

    if boton and df_input is not None:
        total      = len(df_input)
        progress   = st.progress(0)
        status_box = st.empty()
        resultados = [None] * total

        # ── Paralelismo (configurable desde el sidebar) ───────────────────────
        max_workers = _CFG.get("max_workers", 4)
        _reset_stats()
        t_inicio = time.time()
        completadas = [0]  # lista para mutación dentro del closure

        filas = []
        for row in df_input.itertuples(index=False):
            filas.append({
                "nombre":          getattr(row, "nombre", ""),
                "tipo":            getattr(row, "tipo", ""),
                "regulation_mark": getattr(row, "regulation_mark", ""),
                "numero":          str(getattr(row, "numero", "")).strip(),
                "estado":          getattr(row, "estado", ""),
                "cantidad":        getattr(row, "cantidad", 1),
                "es_de_liga":      getattr(row, "es_de_liga", ""),
                "set_forzado":     getattr(row, "set_forzado", ""),
            })

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_to_idx = {
                executor.submit(procesar_carta, fila, api_key or None, clp_rate): idx
                for idx, fila in enumerate(filas)
            }
            for future in as_completed(future_to_idx):
                idx = future_to_idx[future]
                try:
                    resultados[idx] = future.result()
                except Exception as e:
                    # Si una carta falla, insertar fila de error para no romper todo
                    resultados[idx] = {
                        "Nombre Original": filas[idx].get("nombre", "?"),
                        "Error": str(e),
                    }
                completadas[0] += 1
                nombre = filas[idx].get("nombre", "")
                status_box.markdown(
                    f"✅ **{completadas[0]}/{total}** procesadas — última: **{nombre}**"
                )
                progress.progress(completadas[0] / total)

        status_box.success(f"✅ Completado — {total} cartas procesadas.")

        # ── Panel de diagnóstico ──────────────────────────────────────────────
        dur = time.time() - t_inicio
        with _STATS_LOCK:
            s = dict(_STATS)
        reqs = s["requests"]
        prom = (s["tiempo_red"] / reqs) if reqs else 0
        with st.expander("🔍 Diagnóstico de velocidad (ver por qué tardó lo que tardó)", expanded=True):
            d1, d2, d3, d4, d5 = st.columns(5)
            d1.metric("⏱️ Tiempo total", f"{dur:.0f} s")
            d2.metric("🌐 Peticiones reales", reqs)
            d3.metric("⚡ Aciertos de caché", s["cache_hits"])
            d4.metric("🚫 Rate limit (429)", s["rate_limited"])
            d5.metric("⏳ Prom. por petición", f"{prom:.2f} s")
            if s["rate_limited"] > 0:
                st.warning(f"La API te limitó {s['rate_limited']} vez(es) (429). "
                           "Sube la «Espera entre peticiones» a 0.5–1.0 y/o baja los workers en el sidebar.")
            elif prom > 1.5:
                st.warning(f"Cada petición tardó en promedio {prom:.1f}s — la API está lenta ahora mismo "
                           "(no es tu PC). Reintenta más tarde o baja los workers.")
            else:
                st.info("Sin rate limit y respuesta rápida. Si reprocesas, la caché lo hará casi instantáneo.")

        df_final = pd.DataFrame(resultados)
        # Separamos las variantes candidatas a session_state (no van en la tabla
        # ni en el Excel) para poder ofrecer la corrección manual de versión.
        if "_candidatos" in df_final.columns:
            st.session_state["candidatos"] = {
                i: (df_final.at[i, "_candidatos"] or []) for i in df_final.index
            }
            df_final = df_final.drop(columns=["_candidatos"])
        else:
            st.session_state["candidatos"] = {}
        st.session_state["df_result"] = df_final

    # ── Segundo paso: enriquecer precios vía API ───────────────────────────────
    # Siempre visible si hay resultados con cartas sin precio, independiente
    # de si la base local está cargada o no.
    if "df_result" in st.session_state:
        df_cur = st.session_state["df_result"]
        # Verificar columnas necesarias
        tiene_card_id   = "Card ID" in df_cur.columns
        tiene_col_precio = "Precio USD Mercado" in df_cur.columns
        # Hay al menos una carta sin precio Y con Card ID válido para consultarla
        if tiene_card_id and tiene_col_precio:
            mask_sin_precio = df_cur["Precio USD Mercado"].isna()
            mask_con_id = (
                df_cur["Card ID"].notna() &
                (df_cur["Card ID"] != "-") &
                (df_cur["Card ID"] != "")
            )
            n_sin = int((mask_sin_precio & mask_con_id).sum())
        else:
            n_sin = 0

        if n_sin > 0:
            st.markdown("---")
            st.markdown(f"""
            <div style="background:#1A2A1A;border:1px solid #48BB78;border-radius:12px;
                        padding:1rem 1.25rem;margin-bottom:0.5rem;">
                <p style="color:#9AE6B4;font-weight:700;margin:0 0 4px;font-size:1.05rem;">
                    💰 Paso 2 — obtener precios de mercado
                </p>
                <p style="color:#A0AEC0;font-size:0.9rem;margin:0;">
                    <b style="color:#F6AD55;">{n_sin} carta(s)</b> identificadas aún no tienen precio.
                    Pulsa el botón para consultarlos: cada carta ya tiene su ID exacto,
                    así que es una petición directa por carta, sin búsqueda de texto.
                    Tarda lo que la API tarde (segundos, no minutos).
                </p>
            </div>
            """, unsafe_allow_html=True)
            if st.button(
                f"💰 Obtener precios ({n_sin} carta(s))",
                type="primary",
                use_container_width=True,
                key="btn_precios",
            ):
                _reset_stats()
                prog2    = st.progress(0)
                status2  = st.empty()
                t2       = time.time()
                df_enriq = enriquecer_precios_en_lote(
                    st.session_state["df_result"],
                    api_key or None,
                    clp_rate,
                    progress_bar=prog2,
                    status_box=status2,
                )
                dur2 = time.time() - t2
                with _STATS_LOCK:
                    s2 = dict(_STATS)
                n_con_precio = int(df_enriq["Precio USD Mercado"].notna().sum())
                status2.success(
                    f"✅ Precios obtenidos en {dur2:.0f}s — "
                    f"{s2['requests']} peticiones | {n_con_precio} cartas con precio | "
                    f"{s2['rate_limited']} rate-limits."
                )
                st.session_state["df_result"] = df_enriq
                st.rerun()


    if "df_result" in st.session_state:
        render_dashboard(st.session_state["df_result"], clp_rate=clp_rate, comision=comision)

    # ── Pie de página / feedback ──────────────────────────────────────────────
    st.markdown("---")
    st.markdown("""
    <div style="text-align:center;color:#718096;font-size:0.85rem;padding:0.5rem 0 1.5rem;">
        🧪 Versión beta · Prototipo de un proyecto en desarrollo.<br>
        ¿Te sirvió o tienes ideas? Tu feedback ayuda a mejorarlo —
        <a href="mailto:tucorreo@ejemplo.com" style="color:#63B3ED;">escríbeme aquí</a>.
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    main()