#!/usr/bin/env bash
# Deploy the published ontology site to a Wikimedia Toolforge tool account.
#
# Run this while `become`-ing the tool on `login.toolforge.org`:
#
#   ssh you@login.toolforge.org
#   become wikidata-ontology
#   bash $HOME/repo/toolforge/deploy.sh
#
# It expects the repository checked out at $TOOL_REPO (default ~/repo), with the
# generated `site/` directory committed — the same directory GitHub Pages, Vercel,
# Cloudflare Pages and the Hugging Face Space serve.
set -euo pipefail

TOOL_REPO="${TOOL_REPO:-$HOME/repo}"
SRC="$HOME/www/python/src"

echo "→ updating $TOOL_REPO"
git -C "$TOOL_REPO" pull --ff-only

echo "→ installing the web service into $SRC"
mkdir -p "$SRC"
cp -a "$TOOL_REPO/toolforge/www/python/src/." "$SRC/"
rm -rf "$SRC/site"
cp -a "$TOOL_REPO/site" "$SRC/site"
cp -a "$TOOL_REPO/scripts/verify_site.py" "$SRC/verify_site.py"

echo "→ checking the copy against the manifest"
python3 "$SRC/verify_site.py" "$SRC/site"

echo "→ (re)creating the virtualenv"
webservice --backend=kubernetes python3.11 shell -- \
  bash -c "python3 -m venv \$HOME/www/python/venv && \
           \$HOME/www/python/venv/bin/pip install --upgrade pip && \
           \$HOME/www/python/venv/bin/pip install -r \$HOME/www/python/src/requirements.txt"

echo "→ restarting the web service"
toolforge webservice python3.11 restart

echo "done: https://${TOOL_NAME:-wikidata-ontology}.toolforge.org/"
