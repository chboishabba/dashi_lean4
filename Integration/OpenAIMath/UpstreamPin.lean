namespace Integration.OpenAIMath

/-- Immutable upstream repository identity for the October 2026 OpenAI mathematics corpus. -/
def upstreamRepository : String := "https://github.com/openai/math"

/-- Exact upstream commit consumed by this DASHI receipt. -/
def upstreamCommit : String := "1581d4cbdd69a0faf34b2089614fe2a814316a6a"

/-- Upstream license identifier. The vendored/materialized checkout must retain the upstream license. -/
def upstreamLicense : String := "Apache-2.0"

/-- Lean toolchain declared by the pinned upstream corpus. -/
def upstreamLeanToolchain : String := "leanprover/lean4:v4.34.1"

/-- Upstream machine-readable formalization catalogue. -/
def upstreamFormalizationCatalogue : String := "lean/formalization.yaml"

/-- Upstream Lean umbrella module. -/
def upstreamLeanRoot : String := "lean/OAI.lean"

/-- Hermetic upstream gitlink checkout relative to the DASHI Lean repository. -/
def upstreamVendorPath : String := "vendor/openai-math-src"

/-- Metadata never turns a manuscript claim into a Lean theorem. -/
def manuscriptClaimIsLeanTheorem : Bool := false

/-- Catalogue indexing is not itself a kernel receipt. -/
def catalogueEntryIsKernelReceipt : Bool := false

/-- An upstream Lean theorem is not automatically a DASHI same-object port. -/
def upstreamLeanTheoremIsDASHIPort : Bool := false

/-- A Lean theorem is not an Agda theorem merely because Agda records its existence. -/
def upstreamLeanTheoremIsAgdaTheorem : Bool := false

/-- Subject/relevance matching is not same-object theorem transport. -/
def topicalRelevanceIsSameObjectTransport : Bool := false

end Integration.OpenAIMath
