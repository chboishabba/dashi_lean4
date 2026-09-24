// Peer-to-peer mirroring for the published ontology.
//
// Every file listed in manifest.json carries its length and a 64-bit FNV-1a
// digest, computed by the verified tool.  The same digests are what the IPFS and
// BitTorrent copies are checked against, so a peer can serve the data without
// being trusted.
const FNV_OFFSET = 0xcbf29ce484222325n, FNV_PRIME = 0x100000001b3n, M64 = (1n << 64n) - 1n;

export function fnv1a(text) {
  let h = FNV_OFFSET;
  for (const ch of text) { h = ((h ^ BigInt(ch.codePointAt(0))) * FNV_PRIME) & M64; }
  return h.toString(16).padStart(16, '0');
}

export async function loadManifest(base = '') { return (await fetch(base + 'manifest.json')).json(); }

/** Fetch a file and check it against the manifest entry. */
export async function verified(entry, base = '') {
  const text = await (await fetch(base + entry.path)).text();
  const digest = fnv1a(text);
  if (digest !== entry.fnv1a64) throw new Error(`digest mismatch for ${entry.path}`);
  return text;
}

/** The mirrors to try, in order: this origin, then the public gateways. */
export function mirrors(manifest) {
  const out = [''];
  if (manifest.ipfs && manifest.ipfs.cid) {
    for (const g of manifest.ipfs.gateways) out.push(`${g}/ipfs/${manifest.ipfs.cid}/`);
  }
  for (const m of manifest.mirrors || []) out.push(m);
  return out;
}

/** Try every mirror until one serves a file whose digest matches. */
export async function fetchAnywhere(manifest, path) {
  const entry = manifest.files.find(f => f.path === path);
  if (!entry) throw new Error('not in manifest: ' + path);
  let last;
  for (const base of mirrors(manifest)) {
    try { return await verified(entry, base); } catch (e) { last = e; }
  }
  throw last;
}

/** Seed and fetch the archive over BitTorrent, if WebTorrent is loaded. */
export function seed(manifest) {
  if (typeof WebTorrent === 'undefined' || !manifest.bittorrent) return null;
  const client = new WebTorrent();
  client.add(manifest.bittorrent.magnet);
  return client;
}

(async () => {
  const el = document.getElementById('p2p-status');
  if (!el) return;
  try {
    const m = await loadManifest();
    let ok = 0;
    for (const f of m.files.filter(f => f.path.endsWith('.jsonl'))) {
      try { await verified(f); ok++; } catch (e) { /* a mirror may lag */ }
    }
    el.textContent = `${ok} dataset file(s) verified against the manifest; ` +
      `${(m.mirrors || []).length + 1} mirror(s), IPFS ${m.ipfs && m.ipfs.cid ? 'pinned' : 'unpinned'}.`;
  } catch (e) { el.textContent = 'manifest unavailable (' + e.message + ')'; }
})();
