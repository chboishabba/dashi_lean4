#!/usr/bin/env python3
"""Push the published ontology to a Hugging Face dataset repository and Space.

Both repositories are assembled from the *same* files the static site serves, so
the dataset, the Space, the web mirrors and the archive deposits are byte for byte
the same replica:

    dataset repo   hf/README.md (the dataset card)
                   site/data/*.jsonl, site/data/*.wdkb
                   site/manifest.json

    Space repo     hf/space/* (app.py, requirements.txt, the Space card)
                   site/data/*.jsonl, site/manifest.json

Before uploading, every file is re-checked against the manifest digests written by
the verified tool (`scripts/verify_site.py`).

    HF_TOKEN=... python3 scripts/hf_sync.py \
        --dataset wikidata-ontology-lean/wikidata-ontology \
        --space   wikidata-ontology-lean/wikidata-ontology-browser
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def staged(kind: str, site: str) -> str:
    """Assemble a temporary directory holding exactly what the repo should carry."""
    out = tempfile.mkdtemp(prefix=f"hf-{kind}-")
    os.makedirs(os.path.join(out, "data"), exist_ok=True)
    for name in sorted(os.listdir(os.path.join(site, "data"))):
        if kind == "space" and not name.endswith(".jsonl"):
            continue
        shutil.copy2(os.path.join(site, "data", name), os.path.join(out, "data", name))
    shutil.copy2(os.path.join(site, "manifest.json"), os.path.join(out, "manifest.json"))
    if kind == "dataset":
        shutil.copy2(os.path.join(ROOT, "hf", "README.md"), os.path.join(out, "README.md"))
    else:
        for name in ("README.md", "app.py", "requirements.txt"):
            shutil.copy2(os.path.join(ROOT, "hf", "space", name), os.path.join(out, name))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--site", default=os.path.join(ROOT, "site"))
    ap.add_argument("--dataset", default=None, help="e.g. user/wikidata-ontology")
    ap.add_argument("--space", default=None, help="e.g. user/wikidata-ontology-browser")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    check = subprocess.run(
        [sys.executable, os.path.join(ROOT, "scripts", "verify_site.py"), args.site])
    if check.returncode != 0:
        print("refusing to upload: the site does not match its manifest", file=sys.stderr)
        return 1

    if args.dry_run:
        for kind, repo in (("dataset", args.dataset), ("space", args.space)):
            if repo:
                print(f"would upload {staged(kind, args.site)} → {kind} {repo}")
        return 0

    from huggingface_hub import HfApi  # imported late so --dry-run needs no dependency

    api = HfApi(token=os.environ.get("HF_TOKEN"))
    for kind, repo in (("dataset", args.dataset), ("space", args.space)):
        if not repo:
            continue
        repo_type = "dataset" if kind == "dataset" else "space"
        api.create_repo(repo_id=repo, repo_type=repo_type, exist_ok=True,
                        space_sdk="gradio" if repo_type == "space" else None)
        api.upload_folder(folder_path=staged(kind, args.site), repo_id=repo,
                          repo_type=repo_type,
                          commit_message="sync the published ontology snapshots")
        print(f"pushed {repo_type} {repo}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
