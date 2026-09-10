# Publishing, mirroring, syncing and archiving

The ontology is not only formalised, it is *published*: the same bytes are served
from a static site, from three commercial hosts, from a Wikimedia tool account,
from a Hugging Face dataset and Space, from peer-to-peer networks and from a long
term archive. This page describes how, and what is guaranteed about each hop.

Everything starts from one command:

```bash
lake build wikidata
./.lake/build/bin/wikidata publish data/*.wdkb --out site
```

which writes the whole site — pages, data, a small JSON API, and a manifest — and
prints, for each ontology, the number of published rows, its content address, and
whether reading the published file back returns the base it was written from.

## What the site contains

```
site/
  index.html            the overview: one row per ontology, with counts and links
  d/NAME.html           a page per ontology
  data/NAME.jsonl       the published rows (JSON Lines)
  data/NAME.wdkb        the same ontology in the project's own tab separated format
  api/index.json        the summaries, as JSON
  api/NAME.json         the full ontology, as JSON
  manifest.json         every file with its length, digest and content address
  js/p2p.js             mirror selection and integrity checking in the browser
  style.css  robots.txt  _headers  _redirects  .nojekyll
```

`_headers` and `_redirects` are the Cloudflare Pages conventions; `vercel.json`
carries the same rules for Vercel; GitHub Pages needs neither. So one directory
deploys unchanged everywhere.

## The guarantees

| what | theorem |
|------|---------|
| the published rows *are* the ontology — a round trip returns exactly what was published | `Wikidata.Publish.parseJsonl?_jsonlOfKB` |
| one header row plus one row per item, level and statement, nothing more | `Wikidata.Publish.length_kbRecs` |
| the `.wdkb` copy round-trips too | `Wikidata.Cli.parseKB?_renderKB` |
| the content address names the ontology: same canonical text ⟹ same base | `Wikidata.Publish.eq_of_renderKB_eq` |
| replicas converge after one round of gossip | `Wikidata.KB.gossip_pairwise_equiv` |
| and no replica loses anything | `Wikidata.KB.gossip_entails_all`, `Wikidata.KB.pool_entails_mem` |
| syncing invents nothing (it is the least upper bound for entailment) | `Wikidata.KB.sync_least` |
| sync is commutative, associative and idempotent up to agreement | `Wikidata.KB.sync_comm_equiv`, `sync_assoc_equiv`, `sync_idem_equiv` |
| an archive deposit re-imports to the base it was made from | `Wikidata.Archive.importKB?_bundleOf` |
| the JSON Lines copy alone suffices to restore it | `Wikidata.Archive.importKB?_rows_only` |
| the deposit's manifest is honest | `Wikidata.Archive.checkManifest_bundleOf` |

`RequestProject/PublishExamples.lean` exhibits all of this on the downloaded
fragment about Douglas Adams, including two replicas that drift apart and come
back together.

## The mirrors

| target | configuration | how it deploys |
|--------|---------------|----------------|
| GitHub Pages | `.github/workflows/pages.yml` | verifies `site/` against the manifest, then uploads it as the Pages artifact |
| Vercel | `vercel.json` | `outputDirectory: site`; the build command is the manifest check |
| Cloudflare Pages | `wrangler.toml`, `site/_headers`, `site/_redirects` | `wrangler pages deploy site` |
| Hugging Face dataset | `hf/README.md`, `scripts/hf_sync.py` | uploads the dataset card plus `site/data` and `site/manifest.json` |
| Hugging Face Space | `hf/space/` | a Gradio browser over the same files, which verifies them on start-up |
| Wikimedia Toolforge | `toolforge/` | `toolforge/deploy.sh`, or the `toolforge` job of the mirrors workflow |
| IPFS / BitTorrent | `scripts/p2p_publish.sh` | records the CID and magnet link back into `manifest.json` |
| archive.org | `scripts/archive_upload.sh` | uploads the deposits built by `wikidata archive` |

`.github/workflows/mirrors.yml` runs all of them on a push to `site/` and weekly;
each job is skipped unless its credentials are configured, so a fork can turn the
mirrors on one at a time.

Every mirror is checked the same way:

```bash
python3 scripts/verify_site.py site           # or any downloaded copy
```

which recomputes the length and the 64-bit FNV-1a digest of every file listed in
`manifest.json`. That digest is `Wikidata.Publish.fnv1a`, the same function the
tool used when it wrote the manifest, reimplemented in the checker, in the browser
(`site/js/p2p.js`) and in the Toolforge service (`/api/verify`).

## Peer-to-peer

```bash
bash scripts/p2p_publish.sh site              # ipfs add / pin, webtorrent seed
bash scripts/p2p_fetch.sh ipfs://<cid> peer   # or an https mirror, or a magnet link
```

A peer is never trusted: whatever it serves is checked against the manifest before
it is used, and the resulting `.wdkb` files are re-checked by `wikidata check`.
The browser does the same — `site/js/p2p.js` walks the list of mirrors (this
origin, then the IPFS gateways, then whatever `manifest.json` lists) and accepts
the first copy whose digest matches.

When several peers have *different* ontologies rather than different copies of the
same one, `wikidata sync` is the protocol:

```bash
wikidata sync peerA.wdkb peerB.wdkb peerC.wdkb --out pooled.wdkb
```

It reports that each replica is kept in the pool, and that after one round every
replica agrees with every other — the executable counterpart of
`KB.gossip_pairwise_equiv` and `KB.gossip_entails_all`.

## Archives

```bash
wikidata archive data/upper.wdkb --out archive     # build the deposit
bash scripts/archive_upload.sh archive             # send it to archive.org
bash scripts/archive_download.sh wikidata-ontology-wdkb1-…   # bring it back
```

A deposit is a directory named after the content address, holding
`ontology.wdkb`, `ontology.jsonl`, `manifest.tsv` and `<identifier>_meta.xml`
(the Dublin Core style metadata archive.org expects). `wikidata archive` prints
whether the deposit re-imports to the base it was made from and whether its
manifest checks out; both are theorems, so the answer is always yes for anything
the tool produced.

`wikidata unarchive DIR` reads a deposit back — from an `ia download`, from a
mirror, or from a tarball found in twenty years' time — and reports whether the
two copies inside it agree.
