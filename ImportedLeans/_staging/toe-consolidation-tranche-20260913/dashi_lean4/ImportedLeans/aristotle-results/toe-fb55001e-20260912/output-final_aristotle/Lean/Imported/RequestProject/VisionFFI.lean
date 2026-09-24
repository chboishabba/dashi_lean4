

/-!
# VisionFFI — a C-ABI surface for the dual-atlas per-declaration embedding

This module exposes the deterministic, per-declaration *vision embedding* of the
dual atlas (`cog`, `triad`, `harm`) through a flat **C ABI**, so the very same
projections that `RequestProject.VisionAtlas` rasterised and
`RequestProject.VisionPatterns` certified can be called from Python / Rust / C++
over FFI.

The pipeline is:

```
decl ──fingerprint──▶ h : UInt64 ──┬──▶ aristo_cog  h ∈ 1..92   (one-hot, dim 92)
                                   ├──▶ aristo_triad h ∈ 0..19   (one-hot, dim 20)
                                   └──▶ aristo_harm  h ∈ {0,5,7,11,13} → idx 0..4 (one-hot, dim 5)
                                                                  ──▶ 117-dim embedding
```

## Why a separate, dependency-light module?

The exported functions operate purely on `UInt64` and allocate no Lean heap
objects, so the emitted C is a handful of unboxed scalar functions.  Keeping this
file free of heavy imports (no `Mathlib`) means the shared library produced from
it (`libaristovision.so`) is tiny and links only against the Lean runtime — see
`vision/ffi/build_so.sh` and `vision/ffi/aristo_vision.py`.

The formal link to the *already certified* projections of `DualAtlas`
(`cogProj` / `triadProj` / `harmCode`) is established separately, in
`RequestProject.VisionFFICert`, so that the certification can use Mathlib while
this runtime surface stays light.

## Concrete `@[export]` setup

Each `@[export c_name] def leanName ...` emits a C function `c_name` with the
matching unboxed signature (`UInt64 → UInt64` becomes
`uint64_t c_name(uint64_t)`).  The harness loads `libleanshared.so`, then this
library, runs the module initialiser `initialize_RequestProject_VisionFFI`, and
calls the symbols directly.
-/

namespace VisionFFI

/-! ## §1  The pure projections (mirrors of `DualAtlas.cogProj/triadProj/harmCode`) -/

/-- Cognitive grid projection on the C-ABI scalar type: maps a 64-bit
declaration fingerprint into the `46×2 = 92`-cell grid, value in `1..92`. -/
@[inline] def cogU (h : UInt64) : UInt64 := (h % 92) + 1

/-- Semantic triad projection: maps a fingerprint into the `20×3` recursion,
value in `0..19`. -/
@[inline] def triadU (h : UInt64) : UInt64 := (h % 60) / 3

/-- Harmonic cell code, priority `13 > 11 > 7 > 5 > default`, value in
`{0,5,7,11,13}`. -/
@[inline] def harmU (h : UInt64) : UInt64 :=
  if h % 13 == 0 then 13
  else if h % 11 == 0 then 11
  else if h % 7 == 0 then 7
  else if h % 5 == 0 then 5
  else 0

/-- Harmonic *bucket index* in `0..4` for the one-hot block, mapping the code
`0,5,7,11,13 ↦ 0,1,2,3,4`. -/
@[inline] def harmIndexU (h : UInt64) : UInt64 :=
  if h % 13 == 0 then 4
  else if h % 11 == 0 then 3
  else if h % 7 == 0 then 2
  else if h % 5 == 0 then 1
  else 0

/-- The dimension of the assembled per-declaration embedding:
`92 (cog) + 20 (triad) + 5 (harm) = 117`. -/
def embeddingDimU : UInt64 := 117

/-! ## §2  The exported C ABI

Each function below is exported under a stable C name.  The Lean compiler emits,
e.g., `uint64_t aristo_cog(uint64_t)` for `aristo_cog`. -/

/-- C entry point `uint64_t aristo_cog(uint64_t h)` — the cognitive index `1..92`. -/
@[export aristo_cog] def aristo_cog (h : UInt64) : UInt64 := cogU h

/-- C entry point `uint64_t aristo_triad(uint64_t h)` — the semantic triad `0..19`. -/
@[export aristo_triad] def aristo_triad (h : UInt64) : UInt64 := triadU h

/-- C entry point `uint64_t aristo_harm(uint64_t h)` — the harmonic code in
`{0,5,7,11,13}`. -/
@[export aristo_harm] def aristo_harm (h : UInt64) : UInt64 := harmU h

/-- C entry point `uint64_t aristo_harm_index(uint64_t h)` — the harmonic bucket
index `0..4`. -/
@[export aristo_harm_index] def aristo_harm_index (h : UInt64) : UInt64 := harmIndexU h

/-- C entry point `uint64_t aristo_embedding_dim(uint64_t)` — the embedding
dimension `117` (argument ignored). -/
@[export aristo_embedding_dim] def aristo_embedding_dim (_h : UInt64) : UInt64 := embeddingDimU

/-! ## §3  Self-contained range certification (no Mathlib)

These guarantee that the values handed across the FFI boundary are exactly the
documented ranges, so the Python side can safely allocate fixed one-hot blocks.
-/

/-
`cogU` reduced through `toNat` is the textbook cognitive projection.
-/
theorem cogU_toNat (h : UInt64) : (cogU h).toNat = h.toNat % 92 + 1 := by
  simp [cogU];
  omega

/-
The cognitive index is always in `1..92`.
-/
theorem cogU_range (h : UInt64) : 1 ≤ (cogU h).toNat ∧ (cogU h).toNat ≤ 92 := by
  rw [ cogU_toNat, Nat.add_comm ];
  omega

/-
`triadU` reduced through `toNat` is the textbook semantic-triad projection.
-/
theorem triadU_toNat (h : UInt64) : (triadU h).toNat = h.toNat % 60 / 3 := by
  simp [triadU]

/-
The semantic triad is always in `0..19`.
-/
theorem triadU_range (h : UInt64) : (triadU h).toNat ≤ 19 := by
  rw [ triadU_toNat ] ; omega

/-
The harmonic code is always one of the five legal codes.
-/
theorem harmU_mem (h : UInt64) :
    harmU h = 0 ∨ harmU h = 5 ∨ harmU h = 7 ∨ harmU h = 11 ∨ harmU h = 13 := by
  grind +locals

/-
The harmonic bucket index is always in `0..4`.
-/
theorem harmIndexU_range (h : UInt64) : (harmIndexU h).toNat ≤ 4 := by
  unfold harmIndexU
  repeat' split
  all_goals decide

/-- The exported entry points are definitionally the projections (sanity). -/
theorem export_agrees (h : UInt64) :
    aristo_cog h = cogU h ∧ aristo_triad h = triadU h ∧
    aristo_harm h = harmU h ∧ aristo_harm_index h = harmIndexU h := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end VisionFFI