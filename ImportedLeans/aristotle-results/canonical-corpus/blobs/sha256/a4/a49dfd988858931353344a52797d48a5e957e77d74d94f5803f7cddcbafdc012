import Integration.Base369Group

/-!
# The nine-state phase quotient, and the two algebras on one nine-element chart

`Integration.Base369Group` proves that the `Base369` nonary layer is *not* two
ternary layers: `nonary_not_ternary_square` says no bijection carries the cyclic
`nonaryXor` to the componentwise `triXor`.  Read as a global statement — "nine
states are never two independent ternary coordinates" — that is too strong, and
this file makes the correction precise rather than retracting it.

The corpus builds a nine-state carrier by *symmetry reduction*, in
`DASHI/Foundations/TernaryEndomorphismPhaseQuotientExact.agda`: the level-two
ternary endomorphism code carrier `T³` (27 states) modulo the free order-three
output phase.  Mirrored and completed here:

* `rotateOutputCode_orderThree`, `rotateOutputCode_ne` — the `C₃` action is free
  (order three, no fixed point);
* `phaseEquiv : LevelTwoCode ≃ Phase3 × PhaseQuotient9` — the action is a
  product decomposition, so `27 = 3 × 9` on the nose;
* `quotient_eq_iff_orbit` — two codes have the same `PhaseQuotient9` coordinate
  **iff** they lie in the same `C₃` orbit.  This is what makes
  `PhaseQuotient9 = T × T` the orbit space `T³/C₃` rather than merely a nine-element
  set of the right size.

`DASHI/Foundations/PhaseQuotientNonaryGroupSeparationExact.agda` then gives a
two-sided chart `PhaseQuotient9 ↔ NonaryTruth`, mirrored here as `nonaryChart`.
Transporting the quotient's componentwise addition along that chart produces a
*second* algebra on the corpus's own nine labels, which the Agda constructs the
ingredients for but never packages:

* `nonaryPhaseAdd` with `nonaryPhaseAdd_hom`: the chart carries
  `q9Add` to `nonaryPhaseAdd` by construction;
* `phaseZModEquiv_add` — `(NonaryTruth, nonaryPhaseAdd) ≅ ℤ/3 × ℤ/3` additively;
* `nonaryPhaseAdd_exponent_three` versus `nonaryXor_order_nine` — the two
  algebras on the same carrier have different exponents, hence
* `nonary_two_algebras`: the nine labels support both `C₉` and `C₃ × C₃`, and
  (`q9_nonary_group_iso_impossible`) no bijection identifies the two.

The honest form of the boundary is therefore *the address carrier does not
determine the algebra*, not "nine is not three times three".

## The same phenomenon one level down: two origins on the ternary carrier

`triIdx_xor` (in `Integration.Base369Group`) says `triXor` **is** addition in the
native `Base369` index chart, whose zero is `tri-low`; `balTone_triXor_affine`
(in `Integration.TernaryHub`) says it is the affine law `x + y + 1` in the
balanced chart, whose zero is `tri-mid`.  Both are true, and the charts differ by
the translation `balTone_eq_triIdx_sub_one`.  The choice is not free:

* `triReflect_fixed_point_unique` — `tri-mid` is the unique fixed point of the
  corpus's polarity involution;
* `triIdx_not_polarity_compatible` — hence the native chart is *not* compatible
  with polarity, while the balanced one is (`balTone_reflect`), and by
  `Integration.TernaryHub.bal_unique_up_to_sign` the balanced chart is the only
  polarity-compatible one up to sign.

So `triXor` is additive exactly in the chart that ignores polarity, and affine
in the chart that respects it (`triXor_chart_dichotomy`).

Nothing here is a claim about the Monster, about physics, or about "nine states"
outside these finite carriers.
-/

namespace Integration.PhaseQuotient

open Integration.Levels
open Integration.TernaryHub
open Integration.Base369Group
open AgdaMirror.Base369 (TriTruth NonaryTruth triXor rotateTri nonaryXor)
open Synthesis.ToneCore (triReflect)

/-! ## The free `C₃` output phase on the 27-element code carrier -/

/-- Mirror of `DASHI.Cognition.RecursiveFibreTower.LevelTwoCode`: the three
outputs of a ternary endomorphism, listed at `tri-low`, `tri-mid`, `tri-high`. -/
abbrev LevelTwoCode := TriTruth × TriTruth × TriTruth

/-- Mirror of `DASHI.Cognition.PhaseEnrichedTrit.Phase3`. -/
inductive Phase3 | p0 | p1 | p2
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `TernaryEndomorphismPhaseQuotientExact.rotateOutputCode`: the
order-three output phase acting by postcomposition with `rotateTri`. -/
def rotateOutputCode : LevelTwoCode → LevelTwoCode
  | (a, b, c) => (rotateTri a, rotateTri b, rotateTri c)

/-- The action of a phase. -/
def rotateByPhase : Phase3 → LevelTwoCode → LevelTwoCode
  | .p0, c => c
  | .p1, c => rotateOutputCode c
  | .p2, c => rotateOutputCode (rotateOutputCode c)

theorem rotateOutputCode_orderThree (c : LevelTwoCode) :
    rotateOutputCode (rotateOutputCode (rotateOutputCode c)) = c := by
  obtain ⟨a, b, d⟩ := c; revert a b d; decide

/-- The action is **free**: no code is fixed by the phase rotation. -/
theorem rotateOutputCode_ne (c : LevelTwoCode) : rotateOutputCode c ≠ c := by
  obtain ⟨a, b, d⟩ := c; revert a b d; decide

/-- Mirror of `TernaryEndomorphismPhaseQuotientExact.PhaseQuotient9`. -/
abbrev PhaseQuotient9 := TriTruth × TriTruth

/-- Mirror of `phaseEncode`: normalise a code so that its `tri-low` output is
`tri-low`, and record which phase was undone. -/
def phaseEncode : LevelTwoCode → Phase3 × PhaseQuotient9
  | (.low, b, c) => (.p0, (b, c))
  | (.mid, b, c) => (.p1, (rotateTri (rotateTri b), rotateTri (rotateTri c)))
  | (.high, b, c) => (.p2, (rotateTri b, rotateTri c))

/-- Mirror of `phaseDecode`. -/
def phaseDecode : Phase3 × PhaseQuotient9 → LevelTwoCode
  | (.p0, (b, c)) => (.low, b, c)
  | (.p1, (b, c)) => (.mid, rotateTri b, rotateTri c)
  | (.p2, (b, c)) => (.high, rotateTri (rotateTri b), rotateTri (rotateTri c))

/-- **`27 = 3 × 9` on the nose**: the free `C₃` action splits the code carrier as
phase × normalised representative. -/
def phaseEquiv : LevelTwoCode ≃ Phase3 × PhaseQuotient9 where
  toFun := phaseEncode
  invFun := phaseDecode
  left_inv := by rintro ⟨a, b, c⟩; revert a b c; decide
  right_inv := by rintro ⟨p, b, c⟩; revert p b c; decide

/-- The quotient coordinate is `C₃`-invariant. -/
theorem phaseEncode_rotate_snd (c : LevelTwoCode) :
    (phaseEncode (rotateOutputCode c)).2 = (phaseEncode c).2 := by
  obtain ⟨a, b, d⟩ := c; revert a b d; decide

/-- …and it separates the orbits: two codes agree in the quotient coordinate
**iff** one is a phase rotation of the other.  This is the statement that
`PhaseQuotient9` is the orbit space `T³/C₃`, not just a nine-element set. -/
theorem quotient_eq_iff_orbit (c d : LevelTwoCode) :
    (phaseEncode c).2 = (phaseEncode d).2 ↔ ∃ k : Phase3, d = rotateByPhase k c := by
  obtain ⟨a₁, b₁, e₁⟩ := c
  obtain ⟨a₂, b₂, e₂⟩ := d
  revert a₁ b₁ e₁ a₂ b₂ e₂
  decide

/-- The cardinal ledger of the Agda module, as a theorem. -/
theorem phase_cardinalities :
    Fintype.card LevelTwoCode = 27 ∧ Fintype.card Phase3 = 3 ∧
      Fintype.card PhaseQuotient9 = 9 ∧ 3 * (2 + 7) = 27 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## The nonary chart of the phase quotient -/

/-- Mirror of `PhaseQuotientNonaryGroupSeparationExact.phasePairToNonary`
(row-major). -/
def phasePairToNonary : PhaseQuotient9 → NonaryTruth
  | (.low, .low) => .n0   | (.low, .mid) => .n1   | (.low, .high) => .n2
  | (.mid, .low) => .n3   | (.mid, .mid) => .n4   | (.mid, .high) => .n5
  | (.high, .low) => .n6  | (.high, .mid) => .n7  | (.high, .high) => .n8

/-- Mirror of `nonaryToPhasePair`. -/
def nonaryToPhasePair : NonaryTruth → PhaseQuotient9
  | .n0 => (.low, .low)   | .n1 => (.low, .mid)   | .n2 => (.low, .high)
  | .n3 => (.mid, .low)   | .n4 => (.mid, .mid)   | .n5 => (.mid, .high)
  | .n6 => (.high, .low)  | .n7 => (.high, .mid)  | .n8 => (.high, .high)

/-- The two-sided chart of the Agda module. -/
def nonaryChart : PhaseQuotient9 ≃ NonaryTruth where
  toFun := phasePairToNonary
  invFun := nonaryToPhasePair
  left_inv := by rintro ⟨a, b⟩; revert a b; decide
  right_inv := by decide

/-- Mirror of `q9Add`: componentwise `triXor` on the phase quotient. -/
def q9Add : PhaseQuotient9 → PhaseQuotient9 → PhaseQuotient9
  | (a₁, a₂), (b₁, b₂) => (triXor a₁ b₁, triXor a₂ b₂)

/-- The quotient's own addition, **transported to the nonary labels** along the
chart.  This is the operation the corpus has the ingredients for and never
packages: a second, genuinely different algebra on `NonaryTruth`. -/
def nonaryPhaseAdd (x y : NonaryTruth) : NonaryTruth :=
  nonaryChart (q9Add (nonaryChart.symm x) (nonaryChart.symm y))

/-- By construction the chart is an isomorphism onto the transported law. -/
theorem nonaryPhaseAdd_hom (x y : PhaseQuotient9) :
    nonaryChart (q9Add x y) = nonaryPhaseAdd (nonaryChart x) (nonaryChart y) := by
  simp [nonaryPhaseAdd]

/-! ### `(NonaryTruth, nonaryPhaseAdd) ≅ ℤ/3 × ℤ/3` -/

/-- The nonary labels in phase-quotient coordinates. -/
def phaseZModEquiv : NonaryTruth ≃ ZMod 3 × ZMod 3 :=
  nonaryChart.symm.trans ((triEquiv).prodCongr (triEquiv))

/-- **The transported law is componentwise `ℤ/3` addition.** -/
theorem phaseZModEquiv_add (x y : NonaryTruth) :
    phaseZModEquiv (nonaryPhaseAdd x y) = phaseZModEquiv x + phaseZModEquiv y := by
  revert x y; decide

/-- The transported law has exponent three. -/
theorem nonaryPhaseAdd_exponent_three (x : NonaryTruth) :
    nonaryPhaseAdd (nonaryPhaseAdd x x) x = .n0 := by
  revert x; decide

/-- `.n0` is its neutral element. -/
theorem nonaryPhaseAdd_zero (x : NonaryTruth) : nonaryPhaseAdd .n0 x = x := by
  revert x; decide

/-- The native cyclic law does not: `1 + 1 + 1 = 3 ≠ 0` in `ℤ/9`. -/
theorem nonaryXor_order_nine :
    nonaryXor (nonaryXor NonaryTruth.n1 .n1) .n1 = .n3 ∧ (NonaryTruth.n3 ≠ .n0) := by
  exact ⟨by decide, by decide⟩

/-- The two operations are different operations, not two presentations of one. -/
theorem nonaryPhaseAdd_ne_nonaryXor : ∃ x y : NonaryTruth, nonaryPhaseAdd x y ≠ nonaryXor x y :=
  ⟨.n1, .n2, by decide⟩

/-- **The separation theorem of the Agda module**, in its Lean form: no bijection
of the nine labels carries the phase-quotient addition to the cyclic `nonaryXor`.
Equivalent to `Integration.Base369Group.nonary_not_ternary_square`, read through
the chart. -/
theorem q9_nonary_group_iso_impossible :
    ¬ ∃ e : PhaseQuotient9 ≃ NonaryTruth, ∀ x y, e (q9Add x y) = nonaryXor (e x) (e y) := by
  rintro ⟨e, he⟩
  refine nonary_not_ternary_square ⟨e.symm, fun a b => ?_⟩
  have h : e (q9Add (e.symm a) (e.symm b)) = nonaryXor a b := by
    simpa using he (e.symm a) (e.symm b)
  have := congrArg e.symm h
  rw [e.symm_apply_apply] at this
  rw [← this]
  rfl

/-- **The corrected boundary.**  The nine labels carry two algebras — the cyclic
one they are defined with, and the phase-quotient one transported along the
corpus's own chart — they are genuinely different, and no relabelling identifies
them.  What fails is the identification of the *operations*; the identification
of the *carriers* is a theorem (`nonaryChart`). -/
theorem nonary_two_algebras :
    (∀ x y : NonaryTruth, phaseZModEquiv (nonaryPhaseAdd x y) = phaseZModEquiv x + phaseZModEquiv y) ∧
      (∀ x y : NonaryTruth, nonIdx (nonaryXor x y) = nonIdx x + nonIdx y) ∧
      (∃ x y : NonaryTruth, nonaryPhaseAdd x y ≠ nonaryXor x y) ∧
      ¬ ∃ e : PhaseQuotient9 ≃ NonaryTruth,
          ∀ x y, e (q9Add x y) = nonaryXor (e x) (e y) :=
  ⟨phaseZModEquiv_add, nonIdx_xor, nonaryPhaseAdd_ne_nonaryXor,
    q9_nonary_group_iso_impossible⟩

/-! ## Two origins on the ternary carrier -/

/-- The two charts differ by a translation by one. -/
theorem balTone_eq_triIdx_sub_one (t : TriTruth) : balTone t = triIdx t - 1 := by
  cases t <;> decide

/-- The native chart's origin is the `triXor` identity. -/
theorem triIdx_zero_iff (t : TriTruth) : triIdx t = 0 ↔ t = .low := by
  cases t <;> decide

/-- The balanced chart's origin is the polarity-fixed state. -/
theorem balTone_zero_iff (t : TriTruth) : balTone t = 0 ↔ t = .mid := by
  cases t <;> decide

/-- `tri-mid` is the unique fixed point of the corpus's polarity involution. -/
theorem triReflect_fixed_point_unique (t : TriTruth) : triReflect t = t ↔ t = .mid := by
  cases t <;> decide

/-- Hence the native index chart is **not** polarity-compatible. -/
theorem triIdx_not_polarity_compatible : ¬ ∀ t : TriTruth, triIdx (triReflect t) = - triIdx t := by
  intro h; exact absurd (h .low) (by decide)

/-- **The chart dichotomy**, stated as one theorem: the same `triXor` is the
group law in the native chart and the affine law `x + y + 1` in the
polarity-compatible chart, and the two charts are the two named origins. -/
theorem triXor_chart_dichotomy :
    (∀ a b, triIdx (triXor a b) = triIdx a + triIdx b) ∧
      (∀ a b, balTone (triXor a b) = balTone a + balTone b + 1) ∧
      (∀ t, balTone t = triIdx t - 1) ∧
      (∀ t : TriTruth, balTone (triReflect t) = - balTone t) ∧
      ¬ (∀ t : TriTruth, triIdx (triReflect t) = - triIdx t) :=
  ⟨triIdx_xor, balTone_triXor_affine, balTone_eq_triIdx_sub_one, balTone_reflect,
    triIdx_not_polarity_compatible⟩

end Integration.PhaseQuotient
