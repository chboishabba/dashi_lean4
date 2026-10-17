import Mathlib.LinearAlgebra.Dimension.Finite
import Integration.OggSSP2BUniqueInvariant24Range

/-!
# Frobenius socle rigidity forces the unique invariant 24-submodule

The executed Co1 Sym2(24) screen gives the stronger target-side statement that
the ambient socle is exactly the explicit Frobenius-square 24.  At theorem
level the useful consequence is simple: if the Frobenius range is contained in
every nonzero invariant submodule, then every invariant 24-dimensional
submodule equals the Frobenius range by finite-dimensional rigidity.

The runtime-to-proof bridge remains explicit: this file does not turn a GAP or
Agda receipt into Lean kernel authority.  It only removes a redundant second
"enumerate every 24-submodule" obligation once the socle containment theorem
is supplied on the same Co1 module.
-/

namespace Integration.OggSSP2BSocleForcesUnique24

namespace U := Integration.OggSSP2BUniqueInvariant24Range

variable {K S V : Type*}
  [DivisionRing K]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Proof-relevant form of "the ambient socle is the Frobenius 24" sufficient
for the target uniqueness compiler. -/
structure FrobeniusSocleReceipt
    (frobenius : V →ₗ[K] S)
    (IsInvariant : Submodule K S → Prop) : Prop where
  frobenius_finrank : Module.finrank K frobenius.range = 24
  frobenius_invariant : IsInvariant frobenius.range
  frobenius_contained_in_every_nonzero_invariant :
    ∀ W : Submodule K S, IsInvariant W → W ≠ ⊥ → frobenius.range ≤ W

namespace FrobeniusSocleReceipt

variable {frobenius : V →ₗ[K] S}
variable {IsInvariant : Submodule K S → Prop}
variable (r : FrobeniusSocleReceipt frobenius IsInvariant)

/-- The socle statement already implies uniqueness of the invariant 24-range. -/
theorem unique_invariant_24
    (W : Submodule K S)
    (hWdim : Module.finrank K W = 24)
    (hWinv : IsInvariant W) :
    W = frobenius.range := by
  have hWne : W ≠ ⊥ := by
    intro hbot
    subst W
    simp at hWdim
  have hle : frobenius.range ≤ W :=
    r.frobenius_contained_in_every_nonzero_invariant W hWinv hWne
  exact (Submodule.eq_of_le_of_finrank_eq hle (r.frobenius_finrank.trans hWdim.symm)).symm

/-- Adapter into the already-existing unique-range norm-weld compiler. -/
def toUniqueInvariant24SubmoduleReceipt :
    U.UniqueInvariant24SubmoduleReceipt frobenius IsInvariant where
  frobenius_range_finrank_eq_24 := r.frobenius_finrank
  frobenius_invariant := r.frobenius_invariant
  unique_invariant_24 := by
    intro W hdim hinv
    exact r.unique_invariant_24 W hdim hinv

end FrobeniusSocleReceipt

end Integration.OggSSP2BSocleForcesUnique24
