#!/usr/bin/env python3
"""Inventory archive provenance without unpacking archives."""
import argparse, csv, hashlib, os, re, tarfile
from pathlib import Path
EXT = (".tar.gz", ".tgz", ".tar.xz", ".tar")
NAMES = {"TOE_DASHI_HANDOFF_README.md", "HANDOFF.md", "ARISTOTLE_SUMMARY.md", "README.md"}
def sha(p):
 h=hashlib.sha256()
 with p.open("rb") as f:
  for b in iter(lambda:f.read(1048576),b""): h.update(b)
 return h.hexdigest()
def meta(p):
 try:
  with tarfile.open(p,"r:*") as t:
   ms=t.getmembers(); roots=";".join(sorted({m.name.split("/",1)[0] for m in ms if m.name}))
   for m in ms:
    if Path(m.name).name in NAMES and m.isfile():
     s=t.extractfile(m)
     if s:
      hit=re.search(r"^#\s+(.+?)\s*$",s.read(1048576).decode("utf8","replace"),re.M)
      if hit:return roots,hit.group(1)
   return roots,""
 except (tarfile.TarError,OSError): return "",""
p=argparse.ArgumentParser(); p.add_argument("roots",nargs="+",type=Path);p.add_argument("--output",required=True,type=Path);a=p.parse_args()
paths=sorted({x for r in a.roots for x in r.rglob("*") if x.is_file() and x.name.lower().endswith(EXT)})
tmp=a.output.with_suffix(a.output.suffix+".tmp");tmp.parent.mkdir(parents=True,exist_ok=True)
with tmp.open("w",newline="",encoding="utf8") as f:
 w=csv.DictWriter(f,fieldnames=("archive_filename","tranche_title","sha256","bytes","source_path","top_level_roots","integration_state"));w.writeheader()
 for x in paths:
  roots,title=meta(x);w.writerow(dict(archive_filename=x.name,tranche_title=title,sha256=sha(x),bytes=x.stat().st_size,source_path=x,top_level_roots=roots,integration_state="untriaged"))
os.replace(tmp,a.output)
