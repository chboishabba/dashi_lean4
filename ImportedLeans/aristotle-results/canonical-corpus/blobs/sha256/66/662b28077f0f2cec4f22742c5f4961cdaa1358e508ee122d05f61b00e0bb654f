import Mathlib
import AgdaMirror.Ultrametric
import AgdaMirror.Contraction

/-!
# Lean mirror of `FixedPoint.agda` (scaffolding + a genuine theorem)

Faithful transcription of `FixedPoint.agda`: the `Fixed` predicate and the
`UniqueFixed` record.  The Agda module leaves uniqueness as an *assumed* record
field.  Here, in addition to mirroring that record, we *prove* it genuinely:
strict contraction on distinct points really does force fixed points to coincide
(if `x ≠ y` were two fixed points, `d x y < d x y`, absurd).
-/

namespace AgdaMirror

/-- `x` is a fixed point of `K`. -/
def Fixed {S : Type} (K : S → S) (x : S) : Prop := K x = x

/-- Faithful mirror of the Agda `UniqueFixed` record (uniqueness as a field). -/
structure UniqueFixed {S : Type} (U : Ultrametric S) (K : S → S)
    (C : Contractive U K) where
  unique : ∀ x y, Fixed K x → Fixed K y → x = y

/-- Genuine theorem: a strictly contracting map (on distinct points) has at most
one fixed point.  This discharges, rather than assumes, the uniqueness claim. -/
theorem contractiveNe_unique_fixed {S : Type} {U : Ultrametric S} {K : S → S}
    (C : ContractiveNe U K) :
    ∀ x y, Fixed K x → Fixed K y → x = y := by
  intro x y hx hy
  by_contra hne
  have h := C.contractionNe hne
  rw [hx, hy] at h
  exact (lt_irrefl _ h)

end AgdaMirror
