#!/usr/bin/env bash
# Deposit the ontology snapshots on archive.org.
#
#   bash scripts/archive_upload.sh [archive-dir]
#
# The deposits themselves are built by the verified tool:
#
#   wikidata archive data/upper.wdkb --out archive
#
# which writes, per ontology, a directory named after its content address holding
# `ontology.wdkb`, `ontology.jsonl`, `manifest.tsv` and `<identifier>_meta.xml`,
# and reports that the deposit re-imports to the base it was made from
# (`Archive.importKB?_bundleOf`) and that its manifest is honest
# (`Archive.checkManifest_bundleOf`).
#
# Credentials: `ia configure`, or IA_ACCESS_KEY / IA_SECRET_KEY in the environment.
set -euo pipefail

DIR="${1:-archive}"
command -v ia >/dev/null 2>&1 || { echo "the `internetarchive` client is required: pip install internetarchive" >&2; exit 1; }
[ -d "$DIR" ] || { echo "no $DIR — run: wikidata archive data/*.wdkb --out $DIR" >&2; exit 1; }

for item in "$DIR"/*/; do
  id="$(basename "$item")"
  meta="$item/${id}_meta.xml"
  [ -f "$meta" ] || { echo "skipping $id: no metadata"; continue; }

  # read the metadata the tool generated, so the deposit says the same as the file
  title="$(python3 -c 'import re,sys; print(re.search(r"<title>(.*?)</title>", open(sys.argv[1], encoding="utf-8").read(), re.S).group(1))' "$meta")"
  desc="$(python3 -c 'import re,sys; print(re.search(r"<description>(.*?)</description>", open(sys.argv[1], encoding="utf-8").read(), re.S).group(1))' "$meta")"

  echo "→ uploading $id"
  ia upload "$id" "$item"ontology.wdkb "$item"ontology.jsonl "$item"manifest.tsv "$meta" \
    --metadata="title:$title" \
    --metadata="description:$desc" \
    --metadata="mediatype:data" \
    --metadata="collection:opensource" \
    --metadata="licenseurl:https://creativecommons.org/publicdomain/zero/1.0/" \
    --metadata="subject:wikidata" \
    --metadata="subject:ontology" \
    --metadata="subject:lean4" \
    --retries 5
  echo "   https://archive.org/details/$id"
done
