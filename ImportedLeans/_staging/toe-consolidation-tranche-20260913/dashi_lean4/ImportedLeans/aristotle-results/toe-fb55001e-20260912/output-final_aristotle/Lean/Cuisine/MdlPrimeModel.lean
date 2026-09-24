import Cuisine.UmamiTransport

/-!
# MDL: the cuisine transport read as a two-part code over the Monster primes

`Agda/MDL/Core.agda` supplies a two-part-code interface (`Dataset`, `Model`,
`modelTotalLength`, `better`, `Lyapunov`) and `Agda/MDL/PrimeSubsetModel.agda`
specialises it to "models parameterised by a subset of primes", with a subset
cost and a bound `limit71 = 71`.  Both files are *interfaces*: their two
declared theorems (`restrictSafe`, `subsetBoundedCost`) are the identity
function on their hypothesis, so they carry no content.

This file instantiates that interface concretely, on the cuisine transport, and
proves the optimality statement the interface is for.

* `MdlModel`, `modelTotalLength`, `Better`, `Lyapunov` — Lean mirrors of the
  Agda interface.
* `primeSubsetModel` — the concrete prime-subset model: the parameter is a
  Monster mask (a subset of the fifteen supersingular primes), the parameter
  cost is the number of primes kept, and the data cost is twice the number of
  non-neutral base points the mask fails to cover.
* `mdl_lower_bound`, `mdl_optimal_iff` — **the MDL theorem**: the support mask of
  the observed hyperfabric section is the *unique* minimiser of the total code
  length.
* `mdl_optimal_of_maskIntensity` — applied to the cuisine side: for the intensity
  of a mask (`Cuisine.UmamiTransport.maskIntensity`), the MDL-optimal
  supersingular prime subset is exactly that mask.  So the "which primes does
  this dish's intensity use" question has a well-posed, proved answer.
* `ssp_le_limit71` — the MDL bound `limit71 = 71` is exactly the largest
  supersingular prime of the base; every base prime satisfies it, and `71` is
  attained.  (A numeral identification, stated as such.)

Boundary: `CodeLength` is `ℕ`, the "dataset" is a finite function, and no
statistical claim of any kind is made.
-/

namespace Cuisine.MdlPrimeModel

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Cuisine.UmamiTransport

/-! ## Mirror of the Agda MDL interface -/

/-- Mirror of `MDL.Core.CodeLength`. -/
abbrev CodeLength := ℕ

/-- Mirror of `MDL.Core.Model` together with `MDL.Core.Dataset`: a two-part code
for a fixed sample. -/
structure MdlModel (Data : Type) where
  Param : Type
  param : Param
  encodeM : Param → CodeLength
  encodeData : Param → Data → CodeLength

/-- Mirror of `MDL.Core.modelTotalLength`. -/
def modelTotalLength {Data : Type} (M : MdlModel Data) (sample : Data) : CodeLength :=
  M.encodeM M.param + M.encodeData M.param sample

/-- Mirror of `MDL.Core.better`. -/
def Better {Data : Type} (M₁ M₂ : MdlModel Data) (sample : Data) : Prop :=
  modelTotalLength M₁ sample ≤ modelTotalLength M₂ sample

/-- Mirror of `MDL.Core.Lyapunov`. -/
structure Lyapunov {S : Type} (T : S → S) where
  L : S → CodeLength
  descent : ∀ s, L (T s) ≤ L s

/-! ## The concrete prime-subset model -/

/-- The base points a mask keeps. -/
def keep (m : MaskSSP) : Finset SSP := Finset.univ.filter (fun p => m p = true)

/-- The non-neutral base points of a section: its support. -/
def supp (F : Fabric) : Finset SSP := Finset.univ.filter (fun p => F p ≠ Trit.neg)

theorem keep_supportMask (F : Fabric) : keep (supportMask F) = supp F := by
  ext p
  simp [keep, supp, supportMask, support]

/-- Parameter cost: one unit per prime kept. -/
def paramCost (m : MaskSSP) : CodeLength := ∑ p : SSP, if m p = true then 1 else 0

/-- Data cost: two units per non-neutral base point the mask does not cover.
(The weight `2 > 1` is what makes leaving an observation unexplained more
expensive than paying for the parameter that would explain it.) -/
def dataCost (m : MaskSSP) (F : Fabric) : CodeLength :=
  ∑ p : SSP, if F p ≠ Trit.neg ∧ m p = false then 2 else 0

/-- The irreducible cost of the data: one unit per non-neutral base point. -/
def suppCost (F : Fabric) : CodeLength := ∑ p : SSP, if F p ≠ Trit.neg then 1 else 0

theorem suppCost_eq_card (F : Fabric) : suppCost F = (supp F).card := by
  rw [suppCost, supp, Finset.card_filter]

theorem paramCost_eq_card (m : MaskSSP) : paramCost m = (keep m).card := by
  rw [paramCost, keep, Finset.card_filter]

/-- The prime-subset model of `MDL.PrimeSubsetModel`, made concrete on the
fifteen supersingular primes. -/
def primeSubsetModel (m : MaskSSP) : MdlModel Fabric where
  Param := MaskSSP
  param := m
  encodeM := paramCost
  encodeData := dataCost

@[simp] theorem total_primeSubsetModel (m : MaskSSP) (F : Fabric) :
    modelTotalLength (primeSubsetModel m) F = paramCost m + dataCost m F := rfl

/-! ## The MDL optimality theorem -/

/-- The code length paid at one base point. -/
def pointCost (b : Bool) (t : Trit) : CodeLength :=
  (if b = true then 1 else 0) + (if t ≠ Trit.neg ∧ b = false then 2 else 0)

theorem total_eq_sum (m : MaskSSP) (F : Fabric) :
    modelTotalLength (primeSubsetModel m) F = ∑ p : SSP, pointCost (m p) (F p) := by
  simp only [total_primeSubsetModel, paramCost, dataCost, pointCost, Finset.sum_add_distrib]

/-- **Pointwise bound.**  Each base point costs at least its irreducible cost,
with equality exactly when the mask agrees with the support there. -/
theorem pointCost_ge (b : Bool) (t : Trit) :
    (if t ≠ Trit.neg then 1 else 0) ≤ pointCost b t := by
  cases b <;> cases t <;> simp [pointCost]

theorem pointCost_eq_iff (b : Bool) (t : Trit) :
    pointCost b t = (if t ≠ Trit.neg then 1 else 0) ↔ b = support t := by
  cases b <;> cases t <;> simp [pointCost, support]

/-- **Lower bound.**  No prime subset codes the section more cheaply than its
support does. -/
theorem mdl_lower_bound (m : MaskSSP) (F : Fabric) :
    suppCost F ≤ modelTotalLength (primeSubsetModel m) F := by
  rw [total_eq_sum, suppCost]
  exact Finset.sum_le_sum fun p _ => pointCost_ge (m p) (F p)

/-- **The support mask pays exactly the irreducible cost.** -/
theorem total_supportMask (F : Fabric) :
    modelTotalLength (primeSubsetModel (supportMask F)) F = suppCost F := by
  rw [total_eq_sum, suppCost]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (pointCost_eq_iff _ _).2 rfl

/-- **Uniqueness.**  The bound is attained exactly at the support mask, so the
MDL-optimal prime subset of a hyperfabric section is its support. -/
theorem mdl_optimal_iff (m : MaskSSP) (F : Fabric) :
    modelTotalLength (primeSubsetModel m) F = suppCost F ↔ m = supportMask F := by
  constructor
  · intro h
    rw [total_eq_sum, suppCost] at h
    have hle : ∀ p ∈ (Finset.univ : Finset SSP),
        (if F p ≠ Trit.neg then 1 else 0) ≤ pointCost (m p) (F p) :=
      fun p _ => pointCost_ge (m p) (F p)
    have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp h.symm
    funext p
    exact (pointCost_eq_iff (m p) (F p)).1 (hpt p (Finset.mem_univ p)).symm
  · rintro rfl
    exact total_supportMask F

/-- **The cuisine instance.**  For the intensity that `Cuisine.UmamiTransport`
assigns to a Monster mask, the MDL-optimal prime subset is that very mask. -/
theorem mdl_optimal_of_maskIntensity (m m' : MaskSSP) :
    modelTotalLength (primeSubsetModel m') (umamiFabric (maskIntensity m)) =
        suppCost (umamiFabric (maskIntensity m)) ↔ m' = m := by
  rw [mdl_optimal_iff, supportMask_umamiFabric_maskIntensity]

/-- ... and the optimal code length is the number of primes in the mask. -/
theorem mdl_optimal_length (m : MaskSSP) :
    modelTotalLength (primeSubsetModel m) (umamiFabric (maskIntensity m)) = paramCost m := by
  have h : modelTotalLength (primeSubsetModel m) (umamiFabric (maskIntensity m)) =
      suppCost (umamiFabric (maskIntensity m)) :=
    (mdl_optimal_of_maskIntensity m m).2 rfl
  rw [h, suppCost_eq_card, ← keep_supportMask, supportMask_umamiFabric_maskIntensity,
    paramCost_eq_card]

/-! ## The MDL bound `71` -/

/-- Mirror of `MDL.Core.limit71`. -/
def limit71 : ℕ := 71

/-- Every prime of the Monster base satisfies the MDL bound, and the bound is
attained: `limit71` is the largest supersingular prime.  This is a numeral
identification, recorded as such. -/
theorem ssp_le_limit71 : (∀ p : SSP, prime p ≤ limit71) ∧ ∃ p : SSP, prime p = limit71 :=
  ⟨by decide, ⟨SSP.p71, rfl⟩⟩

end Cuisine.MdlPrimeModel
