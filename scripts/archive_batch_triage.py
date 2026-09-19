#!/usr/bin/env python3
"""Batch-triage archive Lean surfaces without unpacking or modifying a tree."""
from __future__ import annotations
import argparse, csv, hashlib, re, tarfile
from pathlib import Path

EXT=(".tar.gz", ".tgz", ".tar.xz", ".tar")
TITLE={"TOE_DASHI_HANDOFF_README.md","TOE_CONSOLIDATION_BRIEF.md","HANDOFF.md","ARISTOTLE_SUMMARY.md","README.md"}

def hstream(s):
 h=hashlib.sha256()
 for b in iter(lambda:s.read(1048576),b""): h.update(b)
 return h.hexdigest()
def hfile(p):
 with p.open("rb") as s:return hstream(s)
def mapped(name):
 for marker, root in (("/Lean/Spine/","Spine"),("/DASHI/output-final_aristotle/RequestProject/","DASHI/output-final_aristotle/RequestProject")):
  if marker in name:return root, name.split(marker,1)[1]
 return None
def main():
 p=argparse.ArgumentParser();p.add_argument("archives",nargs="+",type=Path);p.add_argument("--active",required=True,type=Path);p.add_argument("--summary",required=True,type=Path);p.add_argument("--candidates",required=True,type=Path);p.add_argument("--limit",type=int);a=p.parse_args()
 files=sorted({x for r in a.archives for x in r.rglob("*") if x.is_file() and x.name.lower().endswith(EXT)})
 if a.limit: files=files[:a.limit]
 a.summary.parent.mkdir(parents=True,exist_ok=True); a.candidates.parent.mkdir(parents=True,exist_ok=True)
 with a.summary.open("w",newline="",encoding="utf8") as so,a.candidates.open("w",newline="",encoding="utf8") as co:
  sw=csv.DictWriter(so,fieldnames=("archive_filename","tranche_title","sha256","spine_identical","spine_divergent","spine_staged_only","request_identical","request_divergent","request_staged_only"));sw.writeheader()
  cw=csv.DictWriter(co,fieldnames=("archive_filename","tranche_title","surface","relative_path","status","archive_sha256","active_sha256"));cw.writeheader()
  for path in files:
   title=""; counts={k:0 for k in ("spine_identical","spine_divergent","spine_staged_only","request_identical","request_divergent","request_staged_only")}
   ah=hfile(path)
   try:
    with tarfile.open(path,"r:*") as t:
     for m in t:
      if not m.isfile(): continue
      if Path(m.name).name in TITLE and not title:
       s=t.extractfile(m); text=s.read(1048576).decode("utf8","replace") if s else ""; hit=re.search(r"^#\s+(.+?)\s*$",text,re.M); title=hit.group(1) if hit else title
      hit=mapped(m.name)
      if not hit: continue
      surface, rel=hit; s=t.extractfile(m)
      if s is None: continue
      donor=hstream(s); active=a.active/surface/rel; current=hfile(active) if active.exists() else ""
      status="staged_only" if not current else ("identical" if donor==current else "divergent")
      key=("spine" if surface=="Spine" else "request")+"_"+status; counts[key]+=1
      if status!="identical":cw.writerow(dict(archive_filename=path.name,tranche_title=title,surface=surface,relative_path=rel,status=status,archive_sha256=donor,active_sha256=current))
   except tarfile.TarError: pass
   sw.writerow(dict(archive_filename=path.name,tranche_title=title,sha256=ah,**counts))
if __name__=="__main__":main()
