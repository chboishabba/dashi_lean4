#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
: "${GWB_RELATION_BIN:?set path to SLR #5 expanded-cert executable}"
source_dir="${GWB_SOURCE_DIR:-.dashi/gwb-source}"
mkdir -p .dashi/gwb-relation
python3 tools/replay_gwb_relation_rows.py "$source_dir" "$GWB_RELATION_BIN" .dashi/gwb-relation/rows.json
lake env lean --run tools/GwbProofRunner.lean relation-check "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" .dashi/gwb-relation/rows.json

# Check rejection reason, not merely a failed Lean invocation.
stage="$(mktemp -d .dashi/gwb-relation/negative.XXXXXX)"
trap 'rm -rf "$stage"' EXIT
for label in forged-head missing-row duplicate-row promoted-row; do
  python3 - "$label" .dashi/gwb-relation/rows.json "$stage/$label.json" <<'PY'
import sys,json
label,src,dst=sys.argv[1:]
j=json.load(open(src)); r=j["relations"]
if label=="forged-head": r[0]["head_i"]+=1000000
elif label=="missing-row": r.pop()
elif label=="duplicate-row": r[1]=r[0]
elif label=="promoted-row": r[0]["candidate_only"]=False
with open(dst,"w") as f: json.dump(j,f)
PY
  if lake env lean --run tools/GwbProofRunner.lean relation-check "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" "$stage/$label.json" > "$stage/$label.log" 2>&1; then
    echo "UNSOUND: accepted $label" >&2; exit 1
  fi
  grep -q '^GWB_RELATION_TRANSPORT_REJECTED$' "$stage/$label.log"
  echo "GWB_RELATION_NEGATIVE_REJECTED $label"
done
python3 tools/inspect_gwb_relation_mentions.py "$source_dir" .dashi/gwb-relation/rows.json .dashi/gwb-relation/mention-inspection.json
