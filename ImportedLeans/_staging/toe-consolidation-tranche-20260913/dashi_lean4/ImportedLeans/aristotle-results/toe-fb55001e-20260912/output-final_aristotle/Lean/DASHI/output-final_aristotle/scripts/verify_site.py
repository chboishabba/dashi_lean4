#!/usr/bin/env python3
"""Check a published site against the manifest the verified tool wrote.

Every file listed in ``site/manifest.json`` carries the length and the 64-bit
FNV-1a digest that ``wikidata publish`` computed for it (``Wikidata.Publish.fnv1a``,
folded over Unicode code points).  This script recomputes both, so a mirror — a
Pages deployment, a Vercel build, a Cloudflare edge, a Hugging Face dataset, an
IPFS copy or an archive.org deposit — can be checked against the original without
trusting the transport.

    python3 scripts/verify_site.py site

Exit status 0 when every file matches, 1 otherwise.
"""
import json
import os
import sys

OFFSET = 0xCBF29CE484222325
PRIME = 0x100000001B3
M64 = (1 << 64) - 1


def fnv1a(text: str) -> str:
    h = OFFSET
    for ch in text:
        h = ((h ^ ord(ch)) * PRIME) & M64
    return f"{h:016x}"


def main(root: str) -> int:
    manifest_path = os.path.join(root, "manifest.json")
    if not os.path.exists(manifest_path):
        print(f"{manifest_path}: missing", file=sys.stderr)
        return 1
    with open(manifest_path, encoding="utf-8") as fh:
        manifest = json.load(fh)

    bad = 0
    for entry in manifest["files"]:
        path = os.path.join(root, entry["path"])
        if not os.path.exists(path):
            print(f"  ✗ {entry['path']}: missing")
            bad += 1
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        if len(text) != entry["bytes"]:
            print(f"  ✗ {entry['path']}: {len(text)} code points, manifest says {entry['bytes']}")
            bad += 1
            continue
        digest = fnv1a(text)
        if digest != entry["fnv1a64"]:
            print(f"  ✗ {entry['path']}: digest {digest}, manifest says {entry['fnv1a64']}")
            bad += 1
            continue
        print(f"  ✓ {entry['path']}  {entry['bytes']} code points  {digest}")

    for ds in manifest.get("datasets", []):
        print(f"  · {ds['name']}: {ds['items']} items, {ds['rows']} rows, {ds['cid']}")

    if bad:
        print(f"{bad} file(s) do not match the manifest", file=sys.stderr)
        return 1
    print(f"{len(manifest['files'])} file(s) verified against the manifest")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "site"))
