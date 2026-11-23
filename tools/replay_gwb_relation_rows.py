#!/usr/bin/env python3
"""Replay archived SLR tokens through original #5 relation producer; no parser."""
import argparse
import json
import subprocess
from pathlib import Path

def replay(slr, article, executable):
    lines = ["C\tparity=1", "D\t1"]
    coordinates = {}
    def esc(s):
        return str(s).replace("\\", "\\\\").replace("\t", "\\t").replace("\n", "\\n")
    for sentence in slr["pnf_candidates"]:
        sid = sentence["sentence_index"]
        rows = sentence["dependency_rows"]
        local = {t["i"]: i for i,t in enumerate(rows)}
        if len(local) != len(rows):
            raise ValueError("duplicate parser token")
        lines.append(f"S\t{sid}")
        for i,t in enumerate(rows):
            a,b = t["idx"],t["idx"]+len(t["text"])
            if not (0 <= a < b <= len(article)) or article[a:b] != t["text"]:
                raise ValueError("source literal mismatch")
            head = local[t["head_i"]]
            coordinates[sid,i] = (t,a,b,head)
            lines.append("\t".join(map(str,["T",i,a,b,head,esc(t["text"]),esc(t.get("lemma","-")),t.get("pos","-"),t.get("tag","-"),t["dep"]])))
        lines.append("E")
    p = subprocess.run([str(executable),"--export-relations"],input="\n".join(lines)+"\n",text=True,capture_output=True,check=True)
    metrics = [x for x in p.stderr.splitlines() if x.startswith("SL_RELATION_ATTACHMENT_METRIC ")]
    if len(metrics)!=1:
        raise ValueError("missing producer parity receipt")
    metric = dict(x.split("=",1) for x in metrics[0].split()[1:])
    if metric["parity_mode"]!="1" or metric["parity_failed"]!="0" or int(metric["parity_checked"])!=len(slr["pnf_candidates"]):
        raise ValueError("relation parity failed")
    out=[]; seen=set()
    for line in p.stdout.splitlines():
        mark,rev,sid,ordinal,a,b,kind,head,candidate,context=line.split("\t")
        sid,ordinal,a,b=map(int,(sid,ordinal,a,b))
        t,start,end,h=coordinates[sid,ordinal]
        if mark!="R" or rev!="1" or (sid,ordinal) in seen or (a,b)!=(start,end) or head!=("root" if h==ordinal else str(h)) or candidate!="true" or context!="true":
            raise ValueError("invalid relation coordinate")
        seen.add((sid,ordinal))
        out.append(dict(sentence_index=sid,token_i=t["i"],head_i=t["head_i"],start_char=a,end_char=b,kind=kind,candidate_only=True,context_resolution_required=True))
    if len(out)!=int(metric["candidates"]):
        raise ValueError("incomplete producer output")
    return dict(source_revision=slr["revision_ref"],source_unit_ref=slr["source_unit_ref"],relations=out)

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("source",type=Path)
    p.add_argument("executable",type=Path)
    p.add_argument("output",type=Path)
    a=p.parse_args()
    result=replay(json.loads((a.source/"slr-record.json").read_text()),(a.source/"article.txt").read_text(),a.executable.resolve())
    a.output.write_text(json.dumps(result,indent=2)+"\n")
    print("GWB_ORIGINAL_RELATION_ROWS",len(result["relations"]))
