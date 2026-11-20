#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
: "${GWB_RELATION_BIN:?set path to SLR #5 expanded-cert executable}"
source_dir="${GWB_SOURCE_DIR:-.dashi/gwb-source}"
mkdir -p .dashi/gwb-relation
python3 tools/replay_gwb_relation_rows.py "$source_dir" "$GWB_RELATION_BIN" .dashi/gwb-relation/rows.json
lake env lean --run tools/GwbProofRunner.lean relation-check "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" .dashi/gwb-relation/rows.json
