import Mathlib
import Integration.Experiment.QuantityGraph
import Integration.PredictionEnvelope

/-!
# Lane 2 — uncertainty objects over prediction envelopes

An envelope (`Integration.PredictionEnvelope`) says which values the evidence
leaves open.  This file adds the *quantitative* layer: covariance objects,
first-order propagation `Σ_y = J Σ_x Jᵀ`, and a three-way budget that keeps

* measurement uncertainty,
* parameter uncertainty, and
* model discrepancy

as separate fields that are **proved** not to be recoverable from their sum.

## The results that matter

* `Cov.push` — first-order propagation is well defined: it returns a covariance
  object, i.e. symmetry and positive semidefiniteness are *proved preserved*,
  not assumed (`push_symm`, `push_psd`).
* `scalar_variance_diagonal` — with independent inputs the propagation formula
  is the familiar `σ_y² = Σ (∂y/∂xᵢ)² σᵢ²`, derived rather than posited.
* `total_does_not_determine_the_split` — a `Collision` of the existing
  factorisation owner: the one-number total is not a sufficient statistic for
  the question "where does the uncertainty come from?".
* `unquantified_discrepancy_blocks_the_ranking` — a budget whose model
  discrepancy is unquantified does not determine which source dominates, *even
  when the quantified part is overwhelmingly measurement noise*
  (`numerically_dominant_is_not_epistemically_dominant`).
* `interval_widens_with_discrepancy` — ignoring an unquantified discrepancy
  reports a strictly narrower interval, so silence is not neutrality.

Everything is over `ℚ`; no distributional assumption is made anywhere, and
"variance" here is just a nonnegative rational bookkeeping entry.
-/

namespace Integration.Experiment.Uncertainty

open Matrix
open Integration.CoordinateSufficiency
open Integration.FactorisationCollision

/-! ## §1 Covariance objects and first-order propagation -/

/-- A covariance object on `n` coordinates: a symmetric positive-semidefinite
rational matrix.  The two conditions are fields, so every covariance in the
calculus carries its own proof. -/
structure Cov (n : ℕ) where
  /-- The matrix of covariances. -/
  toMatrix : Matrix (Fin n) (Fin n) ℚ
  /-- Covariance matrices are symmetric. -/
  symm : toMatrix.transpose = toMatrix
  /-- Covariance matrices are positive semidefinite. -/
  psd : ∀ v : Fin n → ℚ, 0 ≤ v ⬝ᵥ (toMatrix *ᵥ v)

namespace Cov

/-- **First-order propagation.**  Given the Jacobian `J` of the map from inputs
to outputs, the output covariance is `J Σ Jᵀ`. -/
def push {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℚ) (S : Cov n) : Cov m where
  toMatrix := J * S.toMatrix * J.transpose
  symm := by
    simp [Matrix.transpose_mul, S.symm, Matrix.mul_assoc]
  psd := by
    intro v
    have h : (J * S.toMatrix * J.transpose) *ᵥ v = J *ᵥ (S.toMatrix *ᵥ (J.transpose *ᵥ v)) := by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact S.psd _

/-- Propagation really is `J Σ Jᵀ`. -/
@[simp] theorem push_toMatrix {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℚ) (S : Cov n) :
    (push J S).toMatrix = J * S.toMatrix * J.transpose := rfl

/-- Symmetry is preserved (restated from the field, for citation). -/
theorem push_symm {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℚ) (S : Cov n) :
    (push J S).toMatrix.transpose = (push J S).toMatrix := (push J S).symm

/-- Positive semidefiniteness is preserved. -/
theorem push_psd {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℚ) (S : Cov n) (v : Fin m → ℚ) :
    0 ≤ v ⬝ᵥ ((push J S).toMatrix *ᵥ v) := (push J S).psd v

/-- **Propagation composes**: pushing along `J₁` then `J₂` is pushing along
`J₂ J₁`, so a chain of laws in the quantity graph has one Jacobian. -/
theorem push_push {n m k : ℕ} (J₁ : Matrix (Fin m) (Fin n) ℚ)
    (J₂ : Matrix (Fin k) (Fin m) ℚ) (S : Cov n) :
    (push J₂ (push J₁ S)).toMatrix = (push (J₂ * J₁) S).toMatrix := by
  simp [push, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The covariance of independent inputs with variances `d`. -/
def diag {n : ℕ} (d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) : Cov n where
  toMatrix := Matrix.diagonal d
  symm := Matrix.diagonal_transpose d
  psd := by
    intro v
    rw [Matrix.dotProduct_mulVec]
    simp [Matrix.vecMul_diagonal, dotProduct]
    exact Finset.sum_nonneg fun i _ => by nlinarith [hd i, sq_nonneg (v i)]

end Cov

/-- **The familiar scalar formula, derived.**  For a scalar output with
sensitivity row `J` and independent inputs of variances `d`, first-order
propagation gives `σ_y² = Σᵢ (∂y/∂xᵢ)² σᵢ²`. -/
theorem scalar_variance_diagonal {n : ℕ} (J : Matrix (Fin 1) (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) :
    (Cov.push J (Cov.diag d hd)).toMatrix 0 0 = ∑ i, (J 0 i) ^ 2 * d i := by
  simp [Cov.push, Cov.diag, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply]
  ring_nf

/-- Worked instance for the coulomb-counting edge `Q = I t`: with sensitivities
`(∂Q/∂I, ∂Q/∂t) = (t, I)` and independent input variances, the propagated
variance is `t² σ_I² + I² σ_t²`. -/
theorem charge_variance (I t sI st : ℚ) (hI : 0 ≤ sI) (ht : 0 ≤ st) :
    (Cov.push (Matrix.of ![![t, I]]) (Cov.diag ![sI, st] (by
      intro i; fin_cases i <;> simpa))).toMatrix 0 0 = t ^ 2 * sI + I ^ 2 * st := by
  rw [scalar_variance_diagonal]
  simp [Fin.sum_univ_two]

/-! ## §2 The three-way budget -/

/-- Where a contribution to the uncertainty comes from.  These are not
interchangeable: the first two are quantified noise, the third is a statement
about the model itself. -/
inductive Source
  /-- Noise in the instruments. -/
  | measurement
  /-- Imprecision in the parameters of the model. -/
  | parameter
  /-- The model's own inadequacy. -/
  | modelDiscrepancy
  deriving DecidableEq, Repr, Fintype

/-- An uncertainty budget.  The model-discrepancy entry is an `Option`: `none`
records that the discrepancy has **not been quantified**, which is a different
state from having quantified it as zero. -/
structure Budget where
  /-- Variance attributed to measurement noise. -/
  measurement : ℚ
  /-- Variance attributed to parameter uncertainty. -/
  parameter : ℚ
  /-- Variance attributed to model discrepancy, when it has been quantified. -/
  modelDiscrepancy : Option ℚ
  deriving DecidableEq

namespace Budget

/-- The sum of the entries that have been quantified. -/
def quantifiedTotal (b : Budget) : ℚ :=
  b.measurement + b.parameter + b.modelDiscrepancy.getD 0

/-- Whether the model discrepancy has been quantified at all. -/
def isComplete (b : Budget) : Bool := b.modelDiscrepancy.isSome

/-- The source with the largest quantified entry, treating an unquantified
discrepancy as contributing nothing — which is exactly the reading the theorems
below show to be unsafe. -/
def dominantQuantified (b : Budget) : Source :=
  let m := b.measurement
  let p := b.parameter
  let d := b.modelDiscrepancy.getD 0
  if d ≥ m ∧ d ≥ p then .modelDiscrepancy
  else if m ≥ p then .measurement else .parameter

/-- The fraction of the quantified variance carried by measurement noise. -/
def measurementShare (b : Budget) : ℚ := b.measurement / b.quantifiedTotal

end Budget

/-- **The total is not a sufficient statistic.**  Two budgets with the same
total have different dominant sources: this is a `Collision` of the existing
owner, so no function of the total whatsoever recovers the attribution. -/
def totalCollision : Collision Budget.quantifiedTotal Budget.dominantQuantified where
  left := ⟨10, 0, some 0⟩
  right := ⟨0, 10, some 0⟩
  distinct := by
    intro h
    have := congrArg Budget.measurement h
    norm_num at this
  collide := by norm_num [Budget.quantifiedTotal]
  separate := by decide

theorem total_does_not_determine_the_split :
    ¬ Determines Budget.quantifiedTotal Budget.dominantQuantified :=
  totalCollision.not_determines

/-- **And no downstream reading of the total repairs it**: printing one number
loses the attribution permanently. -/
theorem no_reading_of_the_total_gives_the_attribution (f : ℚ → Source) :
    ¬ ∀ b : Budget, b.dominantQuantified = f b.quantifiedTotal :=
  totalCollision.no_reading f

/-! ## §3 Unquantified model discrepancy -/

/-- Forgetting the discrepancy entry: the map a report performs when it prints
only the quantified noise. -/
def eraseDiscrepancy (b : Budget) : ℚ × ℚ := (b.measurement, b.parameter)

/-- The true dominant source once the discrepancy *is* quantified. -/
def dominantOfCompletion (b : Budget) : Source := b.dominantQuantified

/-- **An unquantified discrepancy blocks the ranking.**  Two budgets with
identical measurement and parameter variances have different dominant sources,
so the quantified part does not determine where the dominant uncertainty
lies. -/
def discrepancyCollision : Collision eraseDiscrepancy dominantOfCompletion where
  left := ⟨10, 1, some 0⟩
  right := ⟨10, 1, some 100⟩
  distinct := by
    intro h
    have := congrArg Budget.modelDiscrepancy h
    norm_num at this
  collide := rfl
  separate := by decide

theorem unquantified_discrepancy_blocks_the_ranking :
    ¬ Determines eraseDiscrepancy dominantOfCompletion :=
  discrepancyCollision.not_determines

/-- **The sentence the lane asks the system to be able to say.**  There is a
budget in which measurement noise carries at least 95% of the *quantified*
variance — so the quantified ranking says "measurement" — while the model
discrepancy is unquantified, and a completion of that same budget in which the
discrepancy dominates.  The two facts are simultaneously true, which is why they
must be reported separately. -/
theorem numerically_dominant_is_not_epistemically_dominant :
    ∃ b : Budget,
      95 / 100 ≤ b.measurementShare ∧
      b.isComplete = false ∧
      b.dominantQuantified = .measurement ∧
      ∃ c : Budget,
        c.measurement = b.measurement ∧ c.parameter = b.parameter ∧
        c.isComplete = true ∧ c.dominantQuantified = .modelDiscrepancy := by
  refine ⟨⟨99, 1, none⟩, ?_, rfl, by decide, ⟨99, 1, some 1000⟩, rfl, rfl, rfl, by decide⟩
  norm_num [Budget.measurementShare, Budget.quantifiedTotal]

/-! ## §4 Intervals: a coverage rule, and what silence costs -/

/-- A coverage rule turns a variance into a reported half-width.  It is data,
supplied by the consumer of the prediction, and required to be monotone: more
variance never reports a narrower interval. -/
structure Coverage where
  /-- The half-width reported for a given variance. -/
  halfWidth : ℚ → ℚ
  /-- More variance, no narrower an interval. -/
  mono : Monotone halfWidth
  /-- Half-widths are nonnegative. -/
  nonneg : ∀ v, 0 ≤ halfWidth v

/-- The reported interval around a central value. -/
def interval (cov : Coverage) (centre : ℚ) (variance : ℚ) : Set ℚ :=
  Set.Icc (centre - cov.halfWidth variance) (centre + cov.halfWidth variance)

/-- The centre is always inside its own interval. -/
theorem centre_mem_interval (cov : Coverage) (c v : ℚ) : c ∈ interval cov c v := by
  have h := cov.nonneg v
  constructor <;> simp <;> linarith

/-- **Reported intervals are monotone in the variance.** -/
theorem interval_mono (cov : Coverage) (c : ℚ) {v w : ℚ} (h : v ≤ w) :
    interval cov c v ⊆ interval cov c w := by
  intro x hx
  have hm := cov.mono h
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **Silence is not neutrality.**  Suppressing an unquantified discrepancy
reports the interval of the quantified total; quantifying it can only widen
that interval, and for a strictly monotone coverage rule the widening is
strict. -/
theorem interval_widens_with_discrepancy (cov : Coverage) (c : ℚ) (b : Budget)
    (d : ℚ) (hd : 0 ≤ d) :
    interval cov c ({ b with modelDiscrepancy := none } : Budget).quantifiedTotal ⊆
      interval cov c ({ b with modelDiscrepancy := some d } : Budget).quantifiedTotal := by
  refine interval_mono cov c ?_
  simp [Budget.quantifiedTotal]
  linarith

/-- The plainest coverage rule: report the variance itself, clamped at zero. -/
def clampCoverage : Coverage where
  halfWidth := fun v => max v 0
  mono := fun _ _ h => by simpa using max_le_max h le_rfl
  nonneg := fun _ => le_max_right _ _

/-- With that rule the widening is strict as soon as the discrepancy is
positive: the two reports are different intervals, so a reader can tell whether
the discrepancy was counted. -/
theorem widening_is_strict :
    interval clampCoverage 0 ((⟨1, 0, none⟩ : Budget)).quantifiedTotal ≠
      interval clampCoverage 0 ((⟨1, 0, some 4⟩ : Budget)).quantifiedTotal := by
  intro h
  have h5 : (5 : ℚ) ∈ interval clampCoverage 0 ((⟨1, 0, some 4⟩ : Budget)).quantifiedTotal :=
    Set.mem_Icc.mpr (by norm_num [clampCoverage, Budget.quantifiedTotal])
  rw [← h] at h5
  have := (Set.mem_Icc.mp h5).2
  norm_num [clampCoverage, Budget.quantifiedTotal] at this

/-! ## §5 Attaching the budget to an envelope -/

/-- A quantitative prediction: a central value, an uncertainty budget, and the
coverage rule used to report it.  The budget is kept as a record, not
collapsed. -/
structure QuantPrediction where
  /-- The predicted central value. -/
  centre : ℚ
  /-- The three-way budget. -/
  budget : Budget
  /-- The reporting rule. -/
  coverage : Coverage

/-- The interval a quantitative prediction reports. -/
def QuantPrediction.reported (p : QuantPrediction) : Set ℚ :=
  interval p.coverage p.centre p.budget.quantifiedTotal

/-- **The report does not determine the budget.**  Two predictions can report
the same interval from different attributions, so the interval must travel with
its budget: this is again the factorisation owner, applied to the reporting
map. -/
theorem report_does_not_determine_the_budget :
    ∃ p q : QuantPrediction,
      p.reported = q.reported ∧ p.budget.dominantQuantified ≠ q.budget.dominantQuantified := by
  refine ⟨⟨0, ⟨10, 0, some 0⟩, clampCoverage⟩, ⟨0, ⟨0, 10, some 0⟩, clampCoverage⟩, ?_, by decide⟩
  simp [QuantPrediction.reported, interval, Budget.quantifiedTotal]

end Integration.Experiment.Uncertainty
