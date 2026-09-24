import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Quantum/UVFiniteness.agda` (genuine theorem)

Faithful transcription of the abstract UV-finiteness bundle:

* `UVBounded` — a family of "levels" `L` each carrying a Hilbert dimension
  `dimH` bounded by `bound` (`dimH l ≤ bound l`),
* `UVFinite B` — every level has *finite* modes.

The genuine content (`uvFiniteness`) is that any bounded family is finite-mode:
the bound itself witnesses finiteness.  This is a real, fully-proved construction
(not a postulate).  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.UVFiniteness

/-- A bounded-dimension family (Agda `record UVBounded`). -/
structure UVBounded where
  L : Type
  dimH : L → Nat
  bound : L → Nat
  dimH_le_bound : ∀ l, dimH l ≤ bound l

/-- Finiteness of modes: every level admits an `N` bounding its dimension
(Agda `record UVFinite`). -/
structure UVFinite (B : UVBounded) where
  finiteModes : ∀ l, ∃ N, B.dimH l ≤ N

/-- Genuine theorem: every bounded family is finite-mode, with the supplied
bound as witness (Agda `uvFiniteness`). -/
def uvFiniteness (B : UVBounded) : UVFinite B where
  finiteModes := fun l => ⟨B.bound l, B.dimH_le_bound l⟩

end AgdaMirror.UVFiniteness
