# Peer-to-peer mirroring

The published site is a plain directory of files with a manifest, which is all a
peer-to-peer network needs. There is nothing to run here: the two scripts do the
work.

```bash
bash scripts/p2p_publish.sh site               # add to IPFS, seed over BitTorrent,
                                               # record the CID / magnet in manifest.json
bash scripts/p2p_fetch.sh ipfs://<cid> peer    # fetch from a peer and check what it served
bash scripts/p2p_fetch.sh https://<mirror>/ peer
bash scripts/p2p_fetch.sh 'magnet:?xt=…' peer
```

## Why an untrusted peer is safe to use

`site/manifest.json` lists, for every published file, its length in code points
and a 64-bit FNV-1a digest. Those numbers are computed by the verified tool
(`Wikidata.Publish.fnv1a`), and re-computed by whoever receives the data:

* `scripts/verify_site.py` — on the command line, and in every deployment
  workflow before anything is uploaded;
* `site/js/p2p.js` — in the browser, which walks the mirror list (this origin,
  then the IPFS gateways, then whatever `manifest.json` names) and accepts the
  first copy whose digest matches;
* `/api/verify` — on the Toolforge service, so the Wikimedia copy can be compared
  with the others.

Each ontology also carries a **content address** (`Wikidata.Publish.cid`),
computed from its canonical text. Two clean bases with the same canonical text
are equal (`Publish.eq_of_renderKB_eq`), so quoting the content address is
quoting the ontology, not just a file.

## When peers disagree rather than differ

Digests catch a *corrupted* copy. A peer that has genuinely learnt something else
is a different matter, and that is what `wikidata sync` is for:

```bash
wikidata sync peerA.wdkb peerB.wdkb peerC.wdkb --out pooled.wdkb
```

Each peer imports the pooled state. This is a join-semilattice operation up to
agreement — commutative, associative, idempotent (`KB.sync_comm_equiv`,
`KB.sync_assoc_equiv`, `KB.sync_idem_equiv`) — so the replicas converge whatever
order the messages arrive in (`KB.gossip_pairwise_equiv`), none of them loses
anything (`KB.gossip_entails_all`), and none of them gains anything that was not
in some peer (`KB.sync_least`).
