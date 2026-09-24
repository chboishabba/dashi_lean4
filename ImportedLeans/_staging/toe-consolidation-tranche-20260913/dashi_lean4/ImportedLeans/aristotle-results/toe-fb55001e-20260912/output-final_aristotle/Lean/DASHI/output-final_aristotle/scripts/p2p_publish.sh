#!/usr/bin/env bash
# Publish the site to the peer-to-peer mirrors and record where it landed.
#
#   bash scripts/p2p_publish.sh [site]
#
# Three transports, each optional — whatever is installed is used:
#
#   ipfs            `ipfs add -r site`, then the CID is written into manifest.json
#   IPFS_PIN_TOKEN  a web3.storage-compatible pinning service, for CI
#   webtorrent      `webtorrent-cli` seeds the archive and prints a magnet link
#
# The digests in `site/manifest.json` are what a peer checks the data against
# (`scripts/verify_site.py`, and `js/p2p.js` in the browser), so an untrusted peer
# can serve the files without being trusted with their contents.
set -euo pipefail

SITE="${1:-site}"
MANIFEST="$SITE/manifest.json"
[ -f "$MANIFEST" ] || { echo "no $MANIFEST — run: wikidata publish data/*.wdkb --out $SITE" >&2; exit 1; }

python3 scripts/verify_site.py "$SITE"

CID=""
if command -v ipfs >/dev/null 2>&1; then
  echo "→ adding to the local IPFS node"
  CID="$(ipfs add -r -Q "$SITE")"
  echo "   ipfs://$CID"
elif [ -n "${IPFS_PIN_TOKEN:-}" ]; then
  echo "→ uploading to the pinning service"
  TAR="$(mktemp -u).car"
  tar -cf "$TAR" -C "$SITE" .
  CID="$(curl -sS -X POST https://api.web3.storage/upload \
        -H "Authorization: Bearer $IPFS_PIN_TOKEN" \
        --data-binary @"$TAR" | python3 -c 'import json,sys; print(json.load(sys.stdin).get("cid",""))')"
  [ -n "$CID" ] && echo "   ipfs://$CID"
else
  echo "→ no IPFS client and no pinning token: skipping IPFS"
fi

MAGNET=""
if command -v webtorrent >/dev/null 2>&1; then
  echo "→ seeding over BitTorrent"
  TARBALL="$(mktemp -d)/wikidata-ontology.tar.gz"
  tar -czf "$TARBALL" -C "$SITE" .
  MAGNET="$(webtorrent seed "$TARBALL" --quiet --keep-seeding 2>/dev/null | grep -m1 '^magnet:' || true)"
  [ -n "$MAGNET" ] && echo "   $MAGNET"
else
  echo "→ webtorrent not installed: skipping BitTorrent"
fi

python3 - "$MANIFEST" "$CID" "$MAGNET" <<'PY'
import json, sys
path, cid, magnet = sys.argv[1], sys.argv[2], sys.argv[3]
m = json.load(open(path, encoding="utf-8"))
if cid:
    m.setdefault("ipfs", {})["cid"] = cid
if magnet:
    m.setdefault("bittorrent", {})["magnet"] = magnet
json.dump(m, open(path, "w", encoding="utf-8"), indent=2, ensure_ascii=False)
print(f"recorded in {path}: ipfs={cid or 'none'} bittorrent={'yes' if magnet else 'none'}")
PY

echo "note: manifest.json changed, so its own digest moved — the digests it lists"
echo "      are of the data files, which did not change."
