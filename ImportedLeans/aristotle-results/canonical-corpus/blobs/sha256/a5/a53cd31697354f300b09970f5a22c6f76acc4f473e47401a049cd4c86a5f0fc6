import RequestProject.DualAtlas
import RequestProject.VisionFFI

/-!
# VisionFFICert — the FFI surface equals the certified dual-atlas projections

`RequestProject.VisionFFI` exposes `cogU` / `triadU` / `harmU` over a flat C ABI,
keeping itself free of `Mathlib` so the produced shared library stays light.

This module (which *may* use `Mathlib`) closes the loop: it proves that, read
through `UInt64.toNat`, the FFI scalar projections coincide **exactly** with the
already-certified `DualAtlas.cogProj` / `DualAtlas.triadProj` / `DualAtlas.harmCode`
— the very projections whose rasters `RequestProject.VisionPatterns` proves the
harmonic-dominance and argmax findings about.

Hence a vector assembled on the Python side from the FFI outputs is, provably,
the same dual-atlas embedding the in-Lean analysis is built on.
-/

namespace VisionFFICert

open VisionFFI

/-
The FFI cognitive projection equals the certified `DualAtlas.cogProj`.
-/
theorem cogU_eq_cogProj (h : UInt64) :
    (cogU h).toNat = DualAtlas.cogProj h.toNat := by
  rw [cogU_toNat]; rfl

/-
The FFI semantic-triad projection equals the certified `DualAtlas.triadProj`.
-/
theorem triadU_eq_triadProj (h : UInt64) :
    (triadU h).toNat = DualAtlas.triadProj h.toNat := by
  simp [triadU, DualAtlas.triadProj]

/-
The FFI harmonic code equals the certified `DualAtlas.harmCode`.
-/
theorem harmU_eq_harmCode (h : UInt64) :
    (harmU h).toNat = DualAtlas.harmCode h.toNat := by
  unfold harmU DualAtlas.harmCode;
  split_ifs <;> simp_all +decide [ ← UInt64.toNat_inj ]

/-- Consequently the FFI cognitive index satisfies the dual-atlas range guarantee
`DualAtlas.cogProj_mem`. -/
theorem cogU_mem (h : UInt64) : 1 ≤ (cogU h).toNat ∧ (cogU h).toNat ≤ 92 := by
  rw [cogU_eq_cogProj]; exact DualAtlas.cogProj_mem _

/-- Consequently the FFI semantic triad satisfies the dual-atlas range guarantee
`DualAtlas.triadProj_le`. -/
theorem triadU_le (h : UInt64) : (triadU h).toNat ≤ 19 := by
  rw [triadU_eq_triadProj]; exact DualAtlas.triadProj_le _

end VisionFFICert