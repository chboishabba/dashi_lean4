#!/usr/bin/env python3
"""Print what Wikidata says about the given entity identifiers.

    python3 scripts/wd_show.py Q5 P31 …
"""

from __future__ import annotations

import json
import sys
import time
import urllib.parse
import urllib.request

API = "https://www.wikidata.org/w/api.php"
UA = "wikidata-lean-formalisation/1.0 (vocabulary grounding script)"


def get(ids):
    params = {
        "action": "wbgetentities",
        "ids": "|".join(ids),
        "props": "labels|descriptions",
        "languages": "en",
        "format": "json",
    }
    url = API + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    for attempt in range(6):
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                return json.loads(resp.read().decode("utf-8")).get("entities", {})
        except Exception as exc:
            print(f"  retry {attempt + 1}: {exc}", file=sys.stderr)
            time.sleep(10 * (attempt + 1))
    raise SystemExit("could not reach the Wikidata API")


def main() -> None:
    ids = sys.argv[1:]
    for i in range(0, len(ids), 50):
        ents = get(ids[i : i + 50])
        for eid in ids[i : i + 50]:
            e = ents.get(eid, {})
            if e.get("missing") is not None:
                print(f"{eid:12} MISSING")
                continue
            print(
                "{:12} {:45} {}".format(
                    eid,
                    e.get("labels", {}).get("en", {}).get("value", "")[:45],
                    e.get("descriptions", {}).get("en", {}).get("value", "")[:100],
                )
            )
        time.sleep(1.0)


if __name__ == "__main__":
    main()
