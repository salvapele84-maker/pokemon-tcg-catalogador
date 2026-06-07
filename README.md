# ⚡ Catalogador Inteligente — Pokémon TCG

App en Streamlit para catalogar y preparar la venta de cartas Pokémon TCG.

## 🚀 Cómo dejarla ONLINE (Streamlit Community Cloud — gratis)

### Paso 1 — Crear cuenta en GitHub
Si no tienes, créala en https://github.com (gratis).

### Paso 2 — Subir el proyecto a un repositorio
Sube estos archivos a un repo nuevo (puede ser privado):
- `salva.py`
- `requirements.txt`
- `.gitignore`
- carpeta `.streamlit/` con `config.toml`

⚠️ **NO subas** `secrets.toml` (tu API key). El `.gitignore` ya lo bloquea.

La forma más simple sin usar la consola: en GitHub, botón "Add file" → "Upload files",
arrastra los archivos y haz commit.

### Paso 3 — Conectar a Streamlit Cloud
1. Entra a https://share.streamlit.io e inicia sesión con GitHub.
2. "Create app" → "Deploy a public app from a repository".
3. Elige tu repositorio, la rama (main) y el archivo principal: `salva.py`.
4. Deploy. En 1-2 minutos queda con una URL pública tipo
   `https://tu-app.streamlit.app`.

### Paso 4 — Poner la API key en la nube (permanente y segura)
En la página de tu app en Streamlit Cloud:
- Menú "⋮" → "Settings" → "Secrets".
- Pega:  `pokemontcg_api_key = "tu-key-aqui"`
- Guarda. La app la lee sola al arrancar.

¡Listo! Cualquiera con el link puede usarla.

---

## 💻 Cómo correrla LOCAL
```
pip install -r requirements.txt
streamlit run salva.py
```
Para fijar tu API key local, copia `.streamlit/secrets.toml.example`
a `.streamlit/secrets.toml` y pon tu key.

## 📋 Columnas del Excel de entrada
| Columna | Obligatoria | Ejemplo |
|---|---|---|
| nombre | Sí | Charizard ex |
| tipo | Sí | Pokémon / Trainer / Energy |
| regulation_mark | No | G |
| numero | Recomendada | 234 |
| estado | No | NM / LP / MP / HP / DMG |
| cantidad | No | 4 |
| es_de_liga | No | Sí / No |
| set_forzado | No | Ascended Heroes |
