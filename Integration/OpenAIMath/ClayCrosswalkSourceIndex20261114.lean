import Integration.OpenAIMath.FullUpstreamMainResultsCatalogue

/-!
# 14 November 2026 — OAI math 208 declaration source index in consolidated Clay Lean.

Source: OpenAI openai/math (Apache-2.0), and the source-qualified index
written first on chboishabba/dashi_lean4 #78, head 32a7c06f2795427680173a3e61ec00c55e2e21fe.
Original formal mathematical authors retain source credit; this is metadata.

Vendor PIN: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a
  (719 manuscripts / 372 families / 200 original catalogue references).
Newer INDEX SOURCE: openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
  (721 manuscripts / 373 families / 208 main-result declarations).
The index is later than the vendor: never claim every entry is available from
the older submodule. No upstream 4.34.1 theorem is imported by this module.
The independent OpenAI Yang--Mills 4.32 source is another repository.

Golden inventory and six source-read relationships:
chboishabba/dashi_agda #1499
Docs/roadmaps/OpenAIMathCorpusCrosswalk20261114.md
No same-object bridge, local upstream-kernel acceptance, or Agda theorem
follows from an index size proof.
-/

namespace Integration.OpenAIMath

def indexedOpenAIMathRevision : String :=
  "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"

def indexedOpenAIMathCatalogueBlob : String :=
  "372bcd714cd3a186a9139ac8e0f3318961fb2df1"

def earlierVendorCatalogueBlob : String :=
  "275eee8cfab7ce49d3a5e88f02cbb8f28fe6fee6"

def originalCorpusHeadlinesLocalKernelAccepted : Bool := false

def originalCorpusSameObjectToAgdaPaid : Bool := false

theorem sourceIndexHas208Declarations :
    mainResultDeclarations.length = 208 :=
  catalogueEntryCount

theorem notAllIndexedProofsImportedIntoDASHI :
    allCatalogueDeclarationsImportedIntoDASHI = false := rfl

theorem noSourceMetadataCreatesAgdaTheorem :
    originalCorpusSameObjectToAgdaPaid = false := rfl

theorem sourceIndexNotLocallyKernelAccepted :
    originalCorpusHeadlinesLocalKernelAccepted = false := rfl

end Integration.OpenAIMath
