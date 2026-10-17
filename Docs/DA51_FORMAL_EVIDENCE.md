# DA51 formal-evidence linkage

Date: 2026-10-17

`DA51.EvidenceRef` remains the minimal producer/artifact provenance edge. `DA51.EvidenceRevisionRef` is an additive companion for binding one concrete artifact revision and formal statement digest to that edge without changing the DA51 wire ABI or existing constructors.

```text
EvidenceRef
  address
  producer
  artifact
  kind

EvidenceRevisionRef
  evidence
  artifactRevision
  artifactDigest
  statementDigest
  demandRef?
  obligationRef?
```

The same DA51 semantic address may legitimately have multiple evidence revisions or statement digests. Therefore DA51 identity cannot substitute for exact statement identity.

The formal boundary is explicit:

```text
EvidenceRevisionRef.EstablishesProof = False
```

A revision/digest binding is provenance, not a proof term. A real formal certificate still belongs to the checker/theorem object that produced it and downstream consumers must bind it to the exact statement/obligation they intend to pay.

The following implications remain forbidden:

```text
DA51 address/status != theorem proof
EvidenceRef != theorem proof
EvidenceRevisionRef != theorem proof
artifact digest != theorem proof
statement digest != theorem proof
demand/obligation ref != theorem proof
```

Type 8 remains the frozen atlas-entry payload. No type 9 allocation or ABI reinterpretation is introduced by this linkage.
