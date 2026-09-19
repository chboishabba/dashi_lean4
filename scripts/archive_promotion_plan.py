#!/usr/bin/env python3
"""Turn a comparison CSV into a review-only promotion plan."""
import argparse,csv
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("comparison",type=Path);p.add_argument("--title",required=True);p.add_argument("--output",type=Path,required=True);a=p.parse_args();a.output.parent.mkdir(parents=True,exist_ok=True)
actions={"identical":"retain_active_no_copy","staged_only":"review_for_promotion","divergent":"preserve_donor_and_review_diff"}
with a.comparison.open(newline="",encoding="utf8") as src,a.output.open("w",newline="",encoding="utf8") as dst:
 w=csv.DictWriter(dst,fieldnames=("tranche_title","relative_path","comparison_status","recommended_action"));w.writeheader()
 for r in csv.DictReader(src):w.writerow(dict(tranche_title=a.title,relative_path=r["relative_path"],comparison_status=r["status"],recommended_action=actions[r["status"]]))
