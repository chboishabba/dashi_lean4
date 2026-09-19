#!/usr/bin/env python3
"""Compare staged Lean modules with active modules by relative path and hash."""
import argparse,csv,hashlib,os
from pathlib import Path
def sha(p):
 h=hashlib.sha256()
 with p.open("rb") as f:
  for b in iter(lambda:f.read(1048576),b""):h.update(b)
 return h.hexdigest()
p=argparse.ArgumentParser();p.add_argument("--staged",type=Path,required=True);p.add_argument("--active",type=Path,required=True);p.add_argument("--output",type=Path,required=True);a=p.parse_args()
s={str(x.relative_to(a.staged)):x for x in a.staged.rglob("*.lean")}; active={str(x.relative_to(a.active)):x for x in a.active.rglob("*.lean")};tmp=a.output.with_suffix(a.output.suffix+".tmp");tmp.parent.mkdir(parents=True,exist_ok=True)
with tmp.open("w",newline="",encoding="utf8") as f:
 w=csv.DictWriter(f,fieldnames=("relative_path","status","staged_sha256","active_sha256"));w.writeheader()
 for rel,x in sorted(s.items()):
  sh=sha(x); ah=sha(active[rel]) if rel in active else ""; w.writerow(dict(relative_path=rel,status="staged_only" if not ah else ("identical" if sh==ah else "divergent"),staged_sha256=sh,active_sha256=ah))
os.replace(tmp,a.output)
