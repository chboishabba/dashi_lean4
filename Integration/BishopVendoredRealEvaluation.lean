import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Evaluation of DASHI's vendored Bishop reals into Lean Real

Source authority:
* dashi_agda git submodule vendor/bishop
* upstream viktorcsimma/bishop
* pinned source inspected at commit
  240e38c7f6938f20f865b1f956c5f084da48bd54
* source module Real.agda

The vendored representation is a regular rational sequence x_n satisfying,
for nonzero m,n,

  |x_m - x_n| <= 1/m + 1/n,

with setoid equality

  x ~= y  iff  |x_n - y_n| <= 2/n.

The source arithmetic is intentionally not replaced by pointwise arithmetic:
addition resamples at 2*n, while multiplication resamples at 2*K*n.  This
module evaluates the regular sequence in Lean Real and proves preservation
from those exact source sequence equations.

It does not yet identify DASHI's Bishop power-series exp/sin/cos/Machin-pi
with Lean's classical functions; those remain the transcendental same-object
leaves.
-/

namespace Integration.BishopVendoredRealEvaluation

open Filter
open scoped Topology

noncomputable section

/-- Semantic mirror of the actual vendored Bishop real representation.

The regularity statement is written after the canonical rational-to-real cast;
it is exactly the inequality supplied by Real.reg in the vendored Agda source.
-/
structure RegularRatReal where
  seq : ℕ → ℚ
  regular :
    ∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
      |((seq m : ℝ) - (seq n : ℝ))| ≤
        1 / (m : ℝ) + 1 / (n : ℝ)

/-- The exact Bishop setoid relation, after the canonical rational-to-real cast. -/
def Equiv (x y : RegularRatReal) : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    |((x.seq n : ℝ) - (y.seq n : ℝ))| ≤ 2 / (n : ℝ)

/-- Shift away Bishop's deliberately unconstrained index zero. -/
def shifted (x : RegularRatReal) (n : ℕ) : ℝ :=
  (x.seq (n + 1) : ℝ)

private theorem positive_cast_succ (n : ℕ) :
    (0 : ℝ) < (n + 1 : ℕ) := by
  exact_mod_cast Nat.succ_pos n

private theorem two_div_succ_tendsto_zero :
    Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have h :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1))
  simpa [div_eq_mul_inv] using h

/-- The shifted rational sequence is Cauchy in Lean Real. -/
theorem shifted_cauchy (x : RegularRatReal) :
    CauchySeq (shifted x) := by
  rw [cauchySeq_iff_le_tendsto_0]
  refine ⟨fun N : ℕ => (2 : ℝ) / (N + 1 : ℝ), ?_, ?_, two_div_succ_tendsto_zero⟩
  · intro N
    positivity
  · intro n m N hn hm
    rw [Real.dist_eq]
    have hreg :=
      x.regular (n + 1) (m + 1) (by omega) (by omega)
    have hncast : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hn 1
    have hmcast : (N + 1 : ℝ) ≤ (m + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hm 1
    have hninv :
        1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      exact one_div_le_one_div_of_le (positive_cast_succ N) hncast
    have hminv :
        1 / (m + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      exact one_div_le_one_div_of_le (positive_cast_succ N) hmcast
    exact hreg.trans (by linarith)

/-- Canonical classical value of one vendored Bishop regular real. -/
def eval (x : RegularRatReal) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete (shifted_cauchy x))

/-- The source sequence converges to its canonical Lean value. -/
theorem tendsto_eval (x : RegularRatReal) :
    Tendsto (shifted x) atTop (𝓝 (eval x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (shifted_cauchy x))

/-- Bishop-equivalent representatives have asymptotically zero distance. -/
theorem equiv_dist_tendsto_zero
    {x y : RegularRatReal}
    (hxy : Equiv x y) :
    Tendsto (fun n => dist (shifted x n) (shifted y n))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) two_div_succ_tendsto_zero
  rw [Real.dist_eq]
  simpa [shifted] using hxy (n + 1) (by omega)

/-- The evaluation descends through the actual Bishop setoid. -/
theorem eval_respects_equiv
    {x y : RegularRatReal}
    (hxy : Equiv x y) :
    eval x = eval y := by
  have hdist := equiv_dist_tendsto_zero hxy
  have hxDist :
      Tendsto (fun n => dist (shifted x n) (eval x)) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp (tendsto_eval x)
  have hyToX : Tendsto (shifted y) atTop (𝓝 (eval x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) ?_
    · calc
        dist (shifted y n) (eval x)
            ≤ dist (shifted y n) (shifted x n) +
                dist (shifted x n) (eval x) := dist_triangle _ _ _
    · exact (by simpa [dist_comm] using hdist).add hxDist
  exact tendsto_nhds_unique hyToX (tendsto_eval y)

/-- Index used to view the Bishop a*n resampling as a subsequence of shifted. -/
def resampleIndex (a : ℕ) (n : ℕ) : ℕ :=
  a * n + (a - 1)

theorem resampleIndex_strictMono
    {a : ℕ} (ha : 0 < a) :
    StrictMono (resampleIndex a) := by
  intro m n hmn
  unfold resampleIndex
  omega

theorem shifted_resampleIndex
    {a : ℕ} (ha : 0 < a)
    (x : RegularRatReal) (n : ℕ) :
    shifted x (resampleIndex a n) =
      (x.seq (a * (n + 1)) : ℝ) := by
  unfold shifted resampleIndex
  congr 1
  omega

/-- Every positive linear resampling used by the vendored arithmetic has the
same classical limit. -/
theorem tendsto_resample
    (x : RegularRatReal)
    {a : ℕ} (ha : 0 < a) :
    Tendsto (fun n => (x.seq (a * (n + 1)) : ℝ))
      atTop (𝓝 (eval x)) := by
  have h :=
    (tendsto_eval x).comp
      (StrictMono.tendsto_atTop (resampleIndex_strictMono ha))
  simpa only [shifted_resampleIndex ha x] using h

/-- Mirror only the source arithmetic equations that are needed for transport.

These equations are exactly the definitions in the vendored Real.agda:
* addition samples each operand at 2*n;
* negation is pointwise;
* multiplication samples both operands at 2*max(Kx,Ky)*n.
-/
structure VendoredArithmeticMirror where
  zero one : RegularRatReal
  add : RegularRatReal → RegularRatReal → RegularRatReal
  neg : RegularRatReal → RegularRatReal
  mul : RegularRatReal → RegularRatReal → RegularRatReal
  K : RegularRatReal → ℕ

  K_pos : ∀ x, 0 < K x

  seq_zero : ∀ n, zero.seq n = 0
  seq_one : ∀ n, one.seq n = 1

  seq_add :
    ∀ x y n,
      (add x y).seq n = x.seq (2 * n) + y.seq (2 * n)

  seq_neg :
    ∀ x n,
      (neg x).seq n = - x.seq n

  seq_mul :
    ∀ x y n,
      let k := max (K x) (K y)
      (mul x y).seq n =
        x.seq (2 * k * n) * y.seq (2 * k * n)

namespace VendoredArithmeticMirror

variable (A : VendoredArithmeticMirror)

/-- Constant-sequence zero evaluates to Lean zero. -/
theorem eval_zero :
    eval A.zero = 0 := by
  apply tendsto_nhds_unique (tendsto_eval A.zero)
  simpa [shifted, A.seq_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Constant-sequence one evaluates to Lean one. -/
theorem eval_one :
    eval A.one = 1 := by
  apply tendsto_nhds_unique (tendsto_eval A.one)
  simpa [shifted, A.seq_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- Vendored pointwise negation evaluates to ordinary negation. -/
theorem eval_neg (x : RegularRatReal) :
    eval (A.neg x) = - eval x := by
  apply tendsto_nhds_unique (tendsto_eval (A.neg x))
  have hx := (tendsto_eval x).neg
  simpa [shifted, A.seq_neg] using hx

/-- Vendored resampled addition evaluates to ordinary addition. -/
theorem eval_add (x y : RegularRatReal) :
    eval (A.add x y) = eval x + eval y := by
  apply tendsto_nhds_unique (tendsto_eval (A.add x y))
  have hx := tendsto_resample x (by norm_num : 0 < 2)
  have hy := tendsto_resample y (by norm_num : 0 < 2)
  have hsum := hx.add hy
  simpa [shifted, A.seq_add] using hsum

/-- The actual Bishop multiplication resampling factor is positive. -/
private theorem mulFactor_pos (x y : RegularRatReal) :
    0 < 2 * max (A.K x) (A.K y) := by
  have hk : 0 < max (A.K x) (A.K y) :=
    lt_of_lt_of_le (A.K_pos x) (le_max_left _ _)
  omega

/-- Vendored canonical-bound-resampled multiplication evaluates to ordinary
multiplication.  No pointwise-multiplication simplification is made. -/
theorem eval_mul (x y : RegularRatReal) :
    eval (A.mul x y) = eval x * eval y := by
  apply tendsto_nhds_unique (tendsto_eval (A.mul x y))
  let a := 2 * max (A.K x) (A.K y)
  have ha : 0 < a := by
    dsimp [a]
    exact mulFactor_pos A x y
  have hx := tendsto_resample x ha
  have hy := tendsto_resample y ha
  have hprod := hx.mul hy
  simpa [shifted, A.seq_mul, a] using hprod

end VendoredArithmeticMirror

/-- Machine-readable boundary for the reusable vendor bridge. -/
structure VendorEvaluationBoundary where
  vendorSubmoduleRecognized : Bool
  pinnedRegularSequenceFormulaMirrored : Bool
  bishopSetoidFormulaMirrored : Bool
  evaluatorIntoLeanRealOwned : Bool
  setoidRepresentativeIndependenceOwned : Bool
  positiveResamplingInvariantOwned : Bool
  vendoredZeroOneNegAddPreservationOwned : Bool
  vendoredCanonicalBoundMulPreservationOwned : Bool

  actualAgdaVendorMirrorInhabited : Bool
  bishopExpIdentifiedWithRealExp : Bool
  bishopSinIdentifiedWithRealSin : Bool
  bishopCosIdentifiedWithRealCos : Bool
  bishopMachinPiIdentifiedWithRealPi : Bool

def vendorEvaluationBoundary : VendorEvaluationBoundary where
  vendorSubmoduleRecognized := true
  pinnedRegularSequenceFormulaMirrored := true
  bishopSetoidFormulaMirrored := true
  evaluatorIntoLeanRealOwned := true
  setoidRepresentativeIndependenceOwned := true
  positiveResamplingInvariantOwned := true
  vendoredZeroOneNegAddPreservationOwned := true
  vendoredCanonicalBoundMulPreservationOwned := true

  actualAgdaVendorMirrorInhabited := false
  bishopExpIdentifiedWithRealExp := false
  bishopSinIdentifiedWithRealSin := false
  bishopCosIdentifiedWithRealCos := false
  bishopMachinPiIdentifiedWithRealPi := false

end

end Integration.BishopVendoredRealEvaluation
