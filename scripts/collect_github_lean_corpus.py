#!/usr/bin/env python3
"""Collect the independent GitHub-wide ``language:Lean`` repository corpus.

The collector partitions by inclusive creation-date windows because GitHub
Search exposes at most 1,000 results for one query.  State and raw responses
are written as each partition/page completes, so an interrupted run can be
resumed with the same --out directory.
"""
import argparse, csv, datetime as dt, json, os, time, urllib.error, urllib.parse, urllib.request
from pathlib import Path

FIELDS = ["github_id", "full_name", "html_url", "description", "language",
          "default_branch", "license_spdx", "archived", "fork",
          "stargazers_count", "created_at", "updated_at", "pushed_at",
          "source_query", "source_partition"]

def day(s): return dt.date.fromisoformat(s)
def next_day(d): return d + dt.timedelta(days=1)

class Client:
    def __init__(self):
        self.token = os.environ.get("GITHUB_TOKEN") or os.popen("gh auth token 2>/dev/null").read().strip()
        self.root = "https://api.github.com/search/repositories"
        self.last_request = 0.0
    def get(self, query, page=1, per_page=100):
        wait = 2.25 - (time.monotonic() - self.last_request)
        if wait > 0:
            time.sleep(wait)
        qs = urllib.parse.urlencode({"q": query, "sort": "updated", "order": "desc",
                                     "per_page": per_page, "page": page})
        req = urllib.request.Request(self.root + "?" + qs,
          headers={"Accept":"application/vnd.github+json", "User-Agent":"dashi-jmd-lean-corpus/1.0",
                   "X-GitHub-Api-Version":"2022-11-28", **({"Authorization":"Bearer "+self.token} if self.token else {})})
        while True:
            self.last_request = time.monotonic()
            try:
                with urllib.request.urlopen(req, timeout=60) as r:
                    return json.load(r)
            except urllib.error.HTTPError as exc:
                if exc.code != 403:
                    raise
                retry = int(exc.headers.get("Retry-After", "60"))
                reset = exc.headers.get("X-RateLimit-Reset")
                if reset:
                    retry = max(retry, int(reset) - int(time.time()) + 2)
                print(f"GitHub Search API limited; waiting {retry}s", flush=True)
                time.sleep(retry)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("docs/roadmap/jmd_lean_corpus"))
    ap.add_argument("--start", default="2008-01-01")
    ap.add_argument("--end", default=dt.date.today().isoformat())
    args = ap.parse_args(); args.out.mkdir(parents=True, exist_ok=True)
    raw = args.out / "raw"; raw.mkdir(exist_ok=True)
    state_path = args.out / "checkpoint.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {"partitions":{},"repos":{}}
    client = Client()
    def save(): state_path.write_text(json.dumps(state, indent=2, sort_keys=True)+"\n")
    def count(a,b):
        q=f"language:Lean created:{a.isoformat()}..{b.isoformat()}"
        key=f"{a}_{b}"; p=raw/(key+"_count.json")
        if p.exists(): return json.loads(p.read_text())["total_count"]
        data=client.get(q,1,1); p.write_text(json.dumps(data,indent=2)+"\n")
        return data["total_count"]
    windows=[]
    def split(a,b):
        n=count(a,b)
        if n <= 900 or a >= b: windows.append((a,b,n)); return
        mid=a+(b-a)//2; split(a,mid); split(next_day(mid),b)
    split(day(args.start),day(args.end))
    for a,b,n in windows:
        key=f"{a}_{b}"; part=state["partitions"].setdefault(key,{"start":str(a),"end":str(b),"count":n,"pages":0})
        q=f"language:Lean created:{a.isoformat()}..{b.isoformat()}"
        for page in range(part["pages"]+1, (n+99)//100+1):
            data=client.get(q,page,100)
            (raw/f"{key}_page_{page:03d}.json").write_text(json.dumps(data,indent=2)+"\n")
            for repo in data.get("items",[]):
                lic=repo.get("license") or {}
                state["repos"][str(repo["id"])]={"github_id":repo["id"],"full_name":repo["full_name"],"html_url":repo["html_url"],"description":repo.get("description") or "","language":repo.get("language") or "","default_branch":repo.get("default_branch") or "","license_spdx":lic.get("spdx_id") or "","archived":repo.get("archived"),"fork":repo.get("fork"),"stargazers_count":repo.get("stargazers_count"),"created_at":repo.get("created_at"),"updated_at":repo.get("updated_at"),"pushed_at":repo.get("pushed_at"),"source_query":q,"source_partition":key}
            part["pages"]=page; save(); print(f"{key} page {page}: {len(data.get('items',[]))}; unique {len(state['repos'])}", flush=True)
    rows=[state["repos"][k] for k in sorted(state["repos"], key=int)]
    with (args.out/"github_lean_repositories.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=FIELDS); w.writeheader(); w.writerows(rows)
    summary={"query":"language:Lean","retrieval_date_utc":dt.datetime.now(dt.timezone.utc).isoformat(),"repository_count":len(rows),"partitions":len(windows),"source":"https://github.com/search?q=lang%3Alean&type=repositories&s=updated&o=desc","search_cap_note":"Partitions are bounded to <=900 results; deduplicated by GitHub numeric id."}
    (args.out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps(summary,indent=2))
if __name__ == "__main__": main()
