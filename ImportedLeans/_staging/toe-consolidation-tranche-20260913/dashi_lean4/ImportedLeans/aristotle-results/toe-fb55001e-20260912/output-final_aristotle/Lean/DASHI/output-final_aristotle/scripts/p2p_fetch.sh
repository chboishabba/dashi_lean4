#!/usr/bin/env bash
# Fetch the published ontology from a peer, and check what the peer served.
#
#   bash scripts/p2p_fetch.sh https://<mirror>/            # any HTTP mirror
#   bash scripts/p2p_fetch.sh ipfs://<cid>                 # an IPFS copy
#   bash scripts/p2p_fetch.sh magnet:?xt=...               # a BitTorrent copy
#
# Whatever the transport, the files are checked against the digests in the
# manifest before anything is trusted, and then re-checked by the verified tool.
set -euo pipefail

SOURCE="${1:-}"
OUT="${2:-peer}"
[ -n "$SOURCE" ] || { echo "usage: scripts/p2p_fetch.sh (URL | ipfs://CID | magnet:?…) [DIR]" >&2; exit 1; }

mkdir -p "$OUT"

list_paths() {   # the files the manifest lists, one per line
  python3 -c 'import json,sys; print("\n".join(f["path"] for f in json.load(open(sys.argv[1], encoding="utf-8"))["files"]))' "$1"
}

fetch_http() {   # $1 = base URL
  curl -sSL "$1/manifest.json" -o "$OUT/manifest.json"
  while read -r p; do
    [ -n "$p" ] || continue
    mkdir -p "$OUT/$(dirname "$p")"
    curl -sSL "$1/$p" -o "$OUT/$p"
  done < <(list_paths "$OUT/manifest.json")
}

case "$SOURCE" in
  ipfs://*)
    CID="${SOURCE#ipfs://}"
    if command -v ipfs >/dev/null 2>&1; then
      ipfs get -o "$OUT" "$CID"
    else
      echo "→ no local IPFS node, falling back to a public gateway"
      fetch_http "https://ipfs.io/ipfs/$CID"
    fi
    ;;
  magnet:*)
    command -v webtorrent >/dev/null 2>&1 || { echo "webtorrent-cli is required for magnet links" >&2; exit 1; }
    webtorrent download "$SOURCE" --out "$OUT"
    ;;
  *)
    fetch_http "${SOURCE%/}"
    ;;
esac

echo "→ checking what the peer served"
python3 scripts/verify_site.py "$OUT"

WIKIDATA=./.lake/build/bin/wikidata
if [ -x "$WIKIDATA" ]; then
  echo "→ re-checking the copies with the verified tool"
  for f in "$OUT"/data/*.wdkb; do
    [ -e "$f" ] || continue
    "$WIKIDATA" check "$f"
  done
fi
