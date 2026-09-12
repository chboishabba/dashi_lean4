/-
# The NS Gram consumer, under TOE's factor-through discipline

The 2026-09-12 TOE overlay ships `Lean/Proposed/FibreRoutingProjectionAdapter.lean`,
a Mathlib-free prototype of the corpus' consumer-relative projection vocabulary:
`FactorsThrough`, `Determines`, `ProjectionCollision`, together with
`determines_of_factorsThrough` and `collision_blocks_factorisation`.  The donor
ships it as *proposed*, explicitly outside every build target, and records that
no Lean consumer of the fibre-routing material exists.

This file names such a consumer — not in the Fly/MoE/brain lane, where the donor
looked for one, but in Navier–Stokes, where the vocabulary answers a question the
lane actually asks: **what information about the outer cells does the Gram
consumer read?**

* `gramConsumer_factorsThrough_gramProfile` — the literal consumer
  `GramOperatorBound nu modes G k A` factors through the *Gram profile* of the
  cell family, i.e. through the pair (signed Gram entries `Re⟪G p, G q⟫`,
  masses `‖G p‖²`).  The factorisation datum is the record itself; the
  interpretation is the explicit inequality on profiles.
* `gramConsumer_determined_by_gramProfile` — hence any two cell families with
  the same Gram profile are indistinguishable to the consumer.  A producer is
  therefore free to replace the physical cells by anything with the same
  profile, and *only* the profile has to be estimated.
* `massProfile_collision` / `massProfile_not_determines` — the strictly coarser
  *mass profile* `p ↦ ‖G p‖²` does **not** determine even the Gram form: an
  explicit two-mode pair of families, one coherent and one signed, has identical
  masses and Gram forms `1` and `0`.  So the signed off-diagonal entries are not
  recoverable from the masses, and no mass-only producer can pay the consumer.

That is the exact reuse the donor asked for: the prototype's generic layer is
used verbatim, at a named current NS consumer, with the hypotheses matched.  It
is a statement about what the consumer reads, not a bound: nothing here closes
any Clay obligation and none is claimed.
-/
import Proposed.FibreRoutingProjectionAdapter
import RequestProject.NavierStokes.RateBlockGramBound

noncomputable section

namespace ClayNS.GramConsumer

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.Schur
open Proposed.FibreRoutingProjectionAdapter

/-- A family of outer cells at a fixed retained output. -/
abbrev CellFamily := Wave → Fin 3 → ℂ

/-! ## 1.  The profile the consumer reads -/

/-- The **Gram profile** of a cell family: its signed Gram entries together with
its masses. -/
def gramProfile (G : CellFamily) : (Wave → Wave → ℝ) × (Wave → ℝ) :=
  (fun p q => (herm (G p) (G q)).re, fun p => nsq (G p))

/-- The **mass profile**: the masses alone. -/
def massProfile (G : CellFamily) : Wave → ℝ := fun p => nsq (G p)

/-- The literal consumer of the remainder lane, as a predicate on cell
families. -/
def gramConsumer (nu : ℝ) (modes : Finset Wave) (k : Wave) (A : ℝ) : CellFamily → Prop :=
  fun G => GramOperatorBound nu modes G k A

/-- The signed resolvent Gram form itself, as a real-valued consumer. -/
def gramForm (nu : ℝ) (modes : Finset Wave) (k : Wave) (G : CellFamily) : ℝ :=
  ∑ p ∈ modes, ∑ q ∈ modes,
    (herm (G p) (G q)).re
      / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))

/-! ## 2.  The consumer factors through the Gram profile -/

/-- **The factorisation.**  `GramOperatorBound` is a reading of the Gram profile:
the interpretation is the same inequality written on profiles. -/
def gramConsumer_factorsThrough_gramProfile (nu : ℝ) (modes : Finset Wave) (k : Wave) (A : ℝ) :
    FactorsThrough gramProfile (gramConsumer nu modes k A) where
  interpret := fun pr =>
    ∑ p ∈ modes, ∑ q ∈ modes,
        pr.1 p q / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ A * (∑ p ∈ modes, pr.2 p / wsq p) / (2 * nu)
  factorisation := fun _ => rfl

/-- Hence the profile determines the consumer. -/
theorem gramConsumer_determined_by_gramProfile (nu : ℝ) (modes : Finset Wave) (k : Wave)
    (A : ℝ) : Determines gramProfile (gramConsumer nu modes k A) :=
  determines_of_factorsThrough (gramConsumer_factorsThrough_gramProfile nu modes k A)

/-- The same for the Gram form itself. -/
def gramForm_factorsThrough_gramProfile (nu : ℝ) (modes : Finset Wave) (k : Wave) :
    FactorsThrough gramProfile (gramForm nu modes k) where
  interpret := fun pr =>
    ∑ p ∈ modes, ∑ q ∈ modes,
      pr.1 p q / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
  factorisation := fun _ => rfl

/-! ## 3.  The mass profile is too coarse

Two cell families on the same two modes, with the same masses, whose Gram forms
differ.  The collision is the `ProjectionCollision` of the prototype, so it
refutes *every* decoder from masses to the Gram form. -/

/-- First retained mode of the witness. -/
def wE0 : Wave := ![1, 0, 0]

/-- Second retained mode of the witness. -/
def wE1 : Wave := ![0, 1, 0]

/-- The unit cell value of the witness. -/
def cellV : Fin 3 → ℂ := ![1, 0, 0]

/-- The coherent family: the same cell at both modes. -/
def famPlus : CellFamily := fun _ => cellV

/-- The signed family: the cell is reversed at the second mode. -/
def famMinus : CellFamily := fun p => if p = wE1 then -cellV else cellV

theorem wE0_ne_wE1 : wE0 ≠ wE1 := by
  intro h
  have := congrFun h 0
  simp [wE0, wE1] at this

theorem wsq_wE0 : wsq wE0 = 1 := by
  simp [wsq, wE0, Fin.sum_univ_three]

theorem wsq_wE1 : wsq wE1 = 1 := by
  simp [wsq, wE1, Fin.sum_univ_three]

theorem wsq_zero_sub_wE0 : wsq (0 - wE0) = 1 := by
  simp [wsq, wE0, Fin.sum_univ_three]

theorem wsq_zero_sub_wE1 : wsq (0 - wE1) = 1 := by
  simp [wsq, wE1, Fin.sum_univ_three]

theorem rate_wE0 : viscousPairRate 1 wE0 (0 - wE0) = 2 := by
  rw [viscousPairRate, wsq_wE0, wsq_zero_sub_wE0]; norm_num

theorem rate_wE1 : viscousPairRate 1 wE1 (0 - wE1) = 2 := by
  rw [viscousPairRate, wsq_wE1, wsq_zero_sub_wE1]; norm_num

theorem massProfile_famPlus_eq_famMinus : massProfile famPlus = massProfile famMinus := by
  funext p
  by_cases h : p = wE1
  · simp [massProfile, famPlus, famMinus, h, nsq, Fin.sum_univ_three]
  · simp [massProfile, famPlus, famMinus, h]

theorem gramForm_famPlus : gramForm 1 {wE0, wE1} 0 famPlus = 1 := by
  rw [gramForm, Finset.sum_pair wE0_ne_wE1]
  rw [Finset.sum_pair wE0_ne_wE1, Finset.sum_pair wE0_ne_wE1]
  rw [rate_wE0, rate_wE1]
  simp [famPlus, cellV, herm, Fin.sum_univ_three]
  norm_num

theorem gramForm_famMinus : gramForm 1 {wE0, wE1} 0 famMinus = 0 := by
  rw [gramForm, Finset.sum_pair wE0_ne_wE1]
  rw [Finset.sum_pair wE0_ne_wE1, Finset.sum_pair wE0_ne_wE1]
  rw [rate_wE0, rate_wE1]
  simp [famMinus, cellV, herm, Fin.sum_univ_three, wE0_ne_wE1]
  norm_num

/-- **The collision.**  Equal masses, different Gram forms. -/
def massProfile_collision : ProjectionCollision massProfile (gramForm 1 {wE0, wE1} 0) where
  left := famPlus
  right := famMinus
  sameProjection := massProfile_famPlus_eq_famMinus
  consumersDiffer := by
    rw [gramForm_famPlus, gramForm_famMinus]
    norm_num

/-- Hence no decoder from masses to the Gram form exists. -/
theorem massProfile_not_factorising :
    FactorsThrough massProfile (gramForm 1 {wE0, wE1} 0) → False :=
  collision_blocks_factorisation massProfile_collision

theorem massProfile_not_determines :
    ¬ Determines massProfile (gramForm 1 {wE0, wE1} 0) :=
  not_determines_of_collision massProfile_collision

end ClayNS.GramConsumer
