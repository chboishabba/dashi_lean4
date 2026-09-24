# Wikimedia Toolforge deployment

Toolforge (the successor of the old toolserver) is the natural home for a tool
about Wikidata: it sits inside the Wikimedia infrastructure, and its copy of the
data can be compared against every other mirror with the manifest digests.

## One-off setup

```bash
ssh you@login.toolforge.org
become wikidata-ontology                      # your tool account
git clone https://github.com/YOU/wikidata-ontology-lean.git $HOME/repo
cp $HOME/repo/toolforge/service.template $HOME/service.template
bash $HOME/repo/toolforge/deploy.sh
toolforge webservice python3.11 start
```

## Updating

```bash
become wikidata-ontology
bash $HOME/repo/toolforge/deploy.sh           # pulls, copies site/, verifies, restarts
```

The `toolforge` job of `.github/workflows/mirrors.yml` does the same over SSH when
`TOOLFORGE_SSH_KEY`, `TOOLFORGE_USER` and `TOOLFORGE_TOOL` are configured.

## What the service adds

The static files (`site/`) are served as they are, so the Toolforge copy is
byte-for-byte the GitHub Pages / Vercel / Cloudflare / Hugging Face copy. On top
of that:

| route | answer |
|-------|--------|
| `/api/ask/<ontology>/subclass/<a>/<b>` | is `a` a subclass of `b`? (reflexive–transitive closure of P279) |
| `/api/ask/<ontology>/instance/<a>/<c>` | is `a` an instance of `c`? (P31 then P279\*) |
| `/api/verify` | recompute every digest in `manifest.json` on the server |

The two query routes implement the relations the Lean development defines
(`Wikidata.KB.isSubclassOf`, `Wikidata.KB.isInstanceOf`, proved to agree with the
abstract semantics in `RequestProject/Engine.lean`); for an answer that comes with
a proof, use the tool itself:

```bash
wikidata ask site/data/upper-ontology.wdkb subclass Q5 Q35120
wikidata why site/data/upper-ontology.wdkb Q5 Q35120
```
