#!/usr/bin/env python3
"""Export jmikedupont2's public GitHub stars without altering any repository.

Usage: GITHUB_TOKEN=... python export_jmd_stars.py
Output: jmd_starred_all.csv, jmd_starred_primary_lean.csv, jmd_starred_summary.json
Primary language is a GitHub heuristic, NOT proof that a repo contains Lean files.
"""
import csv
import json
import os
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

USER = "jmikedupont2"
BASE = f"https://api.github.com/users/{USER}/starred"
OUT = Path(__file__).resolve().parent
FIELDS = ["full_name", "html_url", "description", "language", "default_branch", "archived", "fork", "stargazers_count", "updated_at", "pushed_at", "license_spdx", "github_id"]

def get_page(page):
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "jmd-star-audit/0.1", "X-GitHub-Api-Version":"2022-11-28"}
    if os.getenv("GITHUB_TOKEN"):
        headers["Authorization"] = "Bearer " + os.environ["GITHUB_TOKEN"]
    req = urllib.request.Request(BASE + f"?per_page=100&page={page}&sort=created&direction=desc", headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=30) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")[:500]
        raise RuntimeError(f"GitHub HTTP {exc.code}, page {page}: {detail}") from exc

def write_csv(path, rows):
    with path.open("w", newline="", encoding="utf-8") as f:
        writer=csv.DictWriter(f, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)

def main():
    all_rows=[]
    page=1
    while True:
        raw=get_page(page)
        if not isinstance(raw,list):
            raise RuntimeError(f"Unexpected API response on page {page}: {repr(raw)[:250]}")
        for repo in raw:
            all_rows.append({
                "full_name":repo.get("full_name"), "html_url":repo.get("html_url"),
                "description":repo.get("description") or "", "language":repo.get("language") or "",
                "default_branch":repo.get("default_branch") or "", "archived":repo.get("archived"),
                "fork":repo.get("fork"), "stargazers_count":repo.get("stargazers_count"),
                "updated_at":repo.get("updated_at"), "pushed_at":repo.get("pushed_at"),
                "license_spdx":(repo.get("license") or {}).get("spdx_id") or "",
                "github_id":repo.get("id"),
            })
        print(f"page {page}: {len(raw)} repos; total {len(all_rows)}", file=sys.stderr)
        if len(raw)<100: break
        page+=1
        if page>1000: raise RuntimeError("Safety page limit reached")
    seen=set()
    uniq=[]
    for row in all_rows:
        if row["github_id"] not in seen:
            seen.add(row["github_id"])
            uniq.append(row)
    lean=[row for row in uniq if row["language"]=="Lean"]
    write_csv(OUT/"jmd_starred_all.csv", uniq)
    write_csv(OUT/"jmd_starred_primary_lean.csv", lean)
    summary={"github_user":USER,"retrieval_date_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),
             "total_public_starred":len(uniq),"primary_language_lean":len(lean),
             "meaning":"Includes public stars only. 'Lean' is the repository's primary language, not a file-content census.",
             "source_api":BASE,"pages_fetched":page}
    (OUT/"jmd_starred_summary.json").write_text(json.dumps(summary,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(summary,indent=2))

if __name__=="__main__":
    main()
