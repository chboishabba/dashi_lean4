import Integration.PolarResidual
import Integration.ObserverQuotient

/-!
# Residual-bearing quotients as one structure, with its instances

Several places in the corpus follow the same pattern: a rich state is projected
to a coarse one, and what the projection would lose is retained as a typed
*residual*, so that the pair reopens the original exactly.  The corpus writes the
pattern out separately each time (`FibreRestrictionCore` /
`ProvenanceBearingQuotient` for the polar wheel; the Boolean support/magnitude
observers for the hyperfabric).  Here it is one structure with proved instances,
which is the honest form of the "instantiate the general structure, do not assert
semantic identity" discipline:

* `ResidualQuotient Rich Coarse Res` — a projection, a residual and a reopening
  with `reopen_project`;
* `injective_pair`, `card_le` — the pair `(project, residual)` is injective, so
  `|Rich| ≤ |Coarse| · |Res|`.  This is the general reason a residual cannot be
  dropped;
* `residual_not_subsingleton` — if the coarse layer is strictly smaller than the
  rich one, the residual carrier has at least two elements.

Two instances, both from material proved elsewhere in this spine:

* `polarQuotient` — the `9 → 6` polar projection of
  `Integration.PolarResidual`, with the Boolean "was this the zero branch"
  residual.  `polar_residual_needed` is `no_retraction_to_polar` re-derived from
  the general lemma.
* `signQuotient` — the polarity-invariant Boolean observer of
  `Integration.ObserverQuotient`, whose residual is exactly the sign that
  `no_equivariant_section` shows cannot be chosen equivariantly.

Nothing here is new mathematics; the point is that the two constructions are one
structure, and that the "residual is not removable" statements are one lemma.
-/

namespace Integration.Residual

open Integration.PolarResidual
open Integration.ObserverQuotient
open AgdaMirror.DASHIAlgebra (Trit)

/-- A projection that retains, in a typed residual, exactly what it would
otherwise lose. -/
structure ResidualQuotient (Rich Coarse Res : Type) where
  /-- The coarse observation. -/
  project : Rich → Coarse
  /-- The retained residual. -/
  residual : Rich → Res
  /-- Reassembly of the rich state from the two. -/
  reopen : Coarse → Res → Rich
  /-- Reassembly is exact. -/
  reopen_project : ∀ x, reopen (project x) (residual x) = x

variable {Rich Coarse Res : Type}

/-- The coarse observation together with the residual determines the rich
state. -/
theorem injective_pair (q : ResidualQuotient Rich Coarse Res) :
    Function.Injective (fun x => (q.project x, q.residual x)) := by
  intro x y h
  have hx := q.reopen_project x
  have hy := q.reopen_project y
  rw [← hx, ← hy]
  simp only [Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- Hence the rich carrier is no larger than the product. -/
theorem card_le [Fintype Rich] [Fintype Coarse] [Fintype Res]
    (q : ResidualQuotient Rich Coarse Res) :
    Fintype.card Rich ≤ Fintype.card Coarse * Fintype.card Res := by
  have h := Fintype.card_le_of_injective _ (injective_pair q)
  simpa [Fintype.card_prod] using h

/-- **The residual is not removable** when the coarse layer is strictly
smaller: it must carry at least two states. -/
theorem residual_not_subsingleton [Fintype Rich] [Fintype Coarse] [Fintype Res]
    (q : ResidualQuotient Rich Coarse Res)
    (h : Fintype.card Coarse < Fintype.card Rich) : 2 ≤ Fintype.card Res := by
  by_contra hcon
  push_neg at hcon
  have hle := card_le q
  have h1 : Fintype.card Res ≤ 1 := by omega
  have h2 : Fintype.card Coarse * Fintype.card Res ≤ Fintype.card Coarse * 1 :=
    Nat.mul_le_mul_left _ h1
  rw [Nat.mul_one] at h2
  omega

/-! ## Instance 1: the polar `9 → 6` projection -/

/-- The coarse polar cell, with the zero branch sent to the negative sheet. -/
def polarCoarse : FullPhaseCell → PolarPhaseCell
  | (.negativeTrit, ph) => (.polarNegative, ph)
  | (.zeroTrit, ph) => (.polarNegative, ph)
  | (.positiveTrit, ph) => (.polarPositive, ph)

/-- The residual: whether this was the zero branch. -/
def wasZero : FullPhaseCell → Bool
  | (.zeroTrit, _) => true
  | _ => false

/-- The polar projection as a residual-bearing quotient. -/
def polarQuotient : ResidualQuotient FullPhaseCell PolarPhaseCell Bool where
  project := polarCoarse
  residual := wasZero
  reopen := fun (p, ph) b => if b then (.zeroTrit, ph) else (polarToTrit p, ph)
  reopen_project := by rintro ⟨t, ph⟩; cases t <;> rfl

/-- `no_retraction_to_polar`, re-derived from the general lemma: the six polar
cells cannot carry the nine full cells alone. -/
theorem polar_residual_needed : 2 ≤ Fintype.card Bool :=
  residual_not_subsingleton polarQuotient (by decide)

/-! ## Instance 2: the sign residual of the magnitude observer -/

/-- The sign residual of a digit: `true` on the positive sheet. -/
def signBit (t : Trit) : Bool := decide (t = Trit.pos)

/-- The polarity-invariant Boolean observer as a residual-bearing quotient: the
coarse datum is the magnitude, the residual is the sign. -/
def signQuotient : ResidualQuotient Trit Bool Bool where
  project := polarPresence
  residual := signBit
  reopen := fun b s => if b then (if s then .pos else .neg) else .zer
  reopen_project := by decide

/-- The corresponding fact for the observer layer: the magnitude alone does not
determine the digit, so the sign residual is needed.  (What
`no_equivariant_section` adds is that the residual cannot be chosen
equivariantly.) -/
theorem sign_residual_needed : 2 ≤ Fintype.card Bool :=
  residual_not_subsingleton signQuotient (by decide)

/-- The two instances share the shape the corpus states informally as
"hot/coarse state + cold residual ↔ full state". -/
theorem residual_quotient_instances :
    (∀ c : FullPhaseCell,
        polarQuotient.reopen (polarQuotient.project c) (polarQuotient.residual c) = c) ∧
      (∀ t : Trit,
        signQuotient.reopen (signQuotient.project t) (signQuotient.residual t) = t) :=
  ⟨polarQuotient.reopen_project, signQuotient.reopen_project⟩

end Integration.Residual
