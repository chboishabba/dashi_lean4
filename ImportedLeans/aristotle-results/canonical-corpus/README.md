# Canonical Aristotle source corpus

`manifest.json` inventories every in-scope archive and the generated-content exclusions. The `records/` JSON Lines shards map every original archive member to one content-addressed file under `blobs/sha256/`. This preserves request/version provenance without silently overwriting older results. Raw archives are intentionally not committed.
