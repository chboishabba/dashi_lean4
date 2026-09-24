#!/usr/bin/env python3
"""Search Wikidata for the entity behind a phrase.

Used while grounding the vocabulary of the formalisation: for each notion the
development names, this prints the candidate Wikidata entities so that the right
one can be recorded in `RequestProject/Vocabulary.lean`.

    python3 scripts/wd_search.py "transitive relation" "partial order" …
"""

from __future__ import annotations

import json
import sys
import time
import urllib.parse
import urllib.request

API = "https://www.wikidata.org/w/api.php"
UA = "wikidata-lean-formalisation/1.0 (vocabulary grounding script)"


def search(phrase: str, kind: str = "item", limit: int = 4):
    params = {
        "action": "wbsearchentities",
        "search": phrase,
        "language": "en",
        "uselang": "en",
        "type": kind,
        "limit": str(limit),
        "format": "json",
    }
    url = API + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    for attempt in range(6):
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                return json.loads(resp.read().decode("utf-8")).get("search", [])
        except Exception as exc:
            print(f"  retry {attempt + 1}: {exc}", file=sys.stderr)
            time.sleep(10 * (attempt + 1))
    raise SystemExit("could not reach the Wikidata API")


def main() -> None:
    args = sys.argv[1:]
    kind = "item"
    if args and args[0] in ("--property", "--item"):
        kind = args[0][2:]
        args = args[1:]
    for phrase in args:
        print(f"# {phrase}")
        for hit in search(phrase, kind):
            print(
                "   {:12} {:40} {}".format(
                    hit.get("id", ""),
                    hit.get("label", "")[:40],
                    hit.get("description", "")[:90],
                )
            )
        time.sleep(1.0)


if __name__ == "__main__":
    main()
