import Integration.BishopVendoredRealEvaluation
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Concrete mirror of the vendored Bishop real arithmetic

This module reconstructs, in Lean, the exact arithmetic definitions from the
pinned DASHI Bishop submodule:

  viktorcsimma/bishop
  commit 240e38c7f6938f20f865b1f956c5f084da48bd54
  Real.agda

The mirror is intentionally definition-shaped rather than merely equivalent:

* rationals are constant regular sequences;
* zero/one are the constant 0/1 sequences;
* negation is pointwise;
* addition samples both inputs at 2*n;
* the canonical bound is the strict integer bound
    1 + floor(|x_1| + 2);
* multiplication samples both inputs at
    2 * max(K x, K y) * n.

This does NOT claim generated Agda replay.  It removes the abstract
VendoredArithmeticMirror input by giving a source-faithful Lean inhabitant
against the content-addressed vendored source.
-/

namespace Integration.BishopVendoredArithmeticConcrete

open Integration.BishopVendoredRealEvaluation

noncomputable section

/-- Source rational embedding: constant regular sequence. -/
def rationalReal (q : ℚ) : RegularRatReal where
  seq _ := q
  regular m n hm hn := by
    simp
    positivity

def zeroReal : RegularRatReal := rationalReal 0
def oneReal : RegularRatReal := rationalReal 1

/-- The exact source strict integer bound K.

For the pinned Bishop source the quotient of numerator by denominator in the
definition of K is the rational floor because |x_1|+2 is nonnegative.
-/
def bishopK (x : RegularRatReal) : ℕ :=
  Int.natAbs ⌊|x.seq 1| + 2⌋ + 1

theorem bishopK_pos (x : RegularRatReal) :
    0 < bishopK x := by
  unfold bishopK
  omega

private theorem one_div_nat_le_one
    {n : ℕ} (hn : n ≠ 0) :
    (1 : ℝ) / n ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1

/-- Every nonzero source sample is strictly bounded by the exact vendored K. -/
theorem sample_abs_lt_bishopK
    (x : RegularRatReal)
    (n : ℕ)
    (hn : n ≠ 0) :
    |(x.seq n : ℝ)| < bishopK x := by
  have hreg := x.regular n 1 hn (by omega)
  have hdiff :
      |(x.seq n : ℝ) - (x.seq 1 : ℝ)| ≤
        1 / (n : ℝ) + 1 := by
    simpa using hreg
  have htri :
      |(x.seq n : ℝ)| ≤
        |(x.seq 1 : ℝ)| +
          |(x.seq n : ℝ) - (x.seq 1 : ℝ)| := by
    calc
      |(x.seq n : ℝ)|
          = |(x.seq 1 : ℝ) +
              ((x.seq n : ℝ) - (x.seq 1 : ℝ))| := by ring_nf
      _ ≤ |(x.seq 1 : ℝ)| +
            |(x.seq n : ℝ) - (x.seq 1 : ℝ)| := abs_add _ _
  have hone : (1 : ℝ) / n ≤ 1 :=
    one_div_nat_le_one hn
  have hpre :
      |(x.seq n : ℝ)| ≤ |(x.seq 1 : ℝ)| + 2 := by
    linarith
  let q : ℚ := |x.seq 1| + 2
  have hq_nonneg : (0 : ℚ) ≤ q := by
    dsimp [q]
    positivity
  have hq_cast :
      (q : ℝ) = |(x.seq 1 : ℝ)| + 2 := by
    simp [q]
  have hfloor :
      (q : ℝ) < ((⌊q⌋ + 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.lt_floor_add_one q
  have hfloor_nonneg : (0 : ℤ) ≤ ⌊q⌋ := by
    exact Int.floor_nonneg.mpr hq_nonneg
  have hK :
      ((bishopK x : ℕ) : ℝ) =
        ((⌊q⌋ + 1 : ℤ) : ℝ) := by
    unfold bishopK
    have hfloorQ :
        ⌊q⌋ = ⌊(|x.seq 1| + 2 : ℚ)⌋ := rfl
    rw [hfloorQ]
    simp [Int.natAbs_of_nonneg hfloor_nonneg]
  rw [← hq_cast] at hpre
  rw [hK]
  exact lt_of_le_of_lt hpre hfloor

def negReal (x : RegularRatReal) : RegularRatReal where
  seq n := -x.seq n
  regular m n hm hn := by
    have h := x.regular m n hm hn
    simpa [sub_eq_add_neg, abs_neg] using h

/-- Exact source addition: resample at 2*n. -/
def addReal (x y : RegularRatReal) : RegularRatReal where
  seq n := x.seq (2 * n) + y.seq (2 * n)
  regular m n hm hn := by
    have hm2 : 2 * m ≠ 0 := by omega
    have hn2 : 2 * n ≠ 0 := by omega
    have hx := x.regular (2 * m) (2 * n) hm2 hn2
    have hy := y.regular (2 * m) (2 * n) hm2 hn2
    have htri :
        |(((x.seq (2 * m) : ℝ) + (y.seq (2 * m) : ℝ)) -
           ((x.seq (2 * n) : ℝ) + (y.seq (2 * n) : ℝ)))|
          ≤
        |(x.seq (2 * m) : ℝ) - (x.seq (2 * n) : ℝ)| +
        |(y.seq (2 * m) : ℝ) - (y.seq (2 * n) : ℝ)| := by
      have :=
        abs_add
          ((x.seq (2 * m) : ℝ) - (x.seq (2 * n) : ℝ))
          ((y.seq (2 * m) : ℝ) - (y.seq (2 * n) : ℝ))
      convert this using 1 <;> ring
    calc
      |((((x.seq (2 * m) + y.seq (2 * m) : ℚ) : ℝ)) -
         (((x.seq (2 * n) + y.seq (2 * n) : ℚ) : ℝ)))|
          ≤
        |(x.seq (2 * m) : ℝ) - (x.seq (2 * n) : ℝ)| +
        |(y.seq (2 * m) : ℝ) - (y.seq (2 * n) : ℝ)| := by
            simpa using htri
      _ ≤
        (1 / ((2 * m : ℕ) : ℝ) + 1 / ((2 * n : ℕ) : ℝ)) +
        (1 / ((2 * m : ℕ) : ℝ) + 1 / ((2 * n : ℕ) : ℝ)) := by
            gcongr
      _ = 1 / (m : ℝ) + 1 / (n : ℝ) := by
            field_simp
            ring

/-- Exact source multiplication: resample at 2*max(Kx,Ky)*n. -/
def mulReal (x y : RegularRatReal) : RegularRatReal where
  seq n :=
    let k := max (bishopK x) (bishopK y)
    x.seq (2 * k * n) * y.seq (2 * k * n)
  regular m n hm hn := by
    let k := max (bishopK x) (bishopK y)
    have hk : 0 < k := by
      exact lt_of_lt_of_le (bishopK_pos x) (le_max_left _ _)
    have hm' : 2 * k * m ≠ 0 := by omega
    have hn' : 2 * k * n ≠ 0 := by omega
    let xm : ℝ := x.seq (2 * k * m)
    let xn : ℝ := x.seq (2 * k * n)
    let ym : ℝ := y.seq (2 * k * m)
    let yn : ℝ := y.seq (2 * k * n)
    have hxreg := x.regular (2 * k * m) (2 * k * n) hm' hn'
    have hyreg := y.regular (2 * k * m) (2 * k * n) hm' hn'
    have hxbound : |xm| ≤ k := by
      exact (sample_abs_lt_bishopK x (2 * k * m) hm').le.trans
        (by exact_mod_cast le_max_left (bishopK x) (bishopK y))
    have hybound : |yn| ≤ k := by
      exact (sample_abs_lt_bishopK y (2 * k * n) hn').le.trans
        (by exact_mod_cast le_max_right (bishopK x) (bishopK y))
    have hsplit :
        |xm * ym - xn * yn|
          ≤ |xm| * |ym - yn| + |yn| * |xm - xn| := by
      calc
        |xm * ym - xn * yn|
            = |xm * (ym - yn) + yn * (xm - xn)| := by
                congr 1
                ring
        _ ≤ |xm * (ym - yn)| + |yn * (xm - xn)| := abs_add _ _
        _ = |xm| * |ym - yn| + |yn| * |xm - xn| := by
                simp [abs_mul]
    have hnonnegY : 0 ≤ |ym - yn| := abs_nonneg _
    have hnonnegX : 0 ≤ |xm - xn| := abs_nonneg _
    have h1 :
        |xm| * |ym - yn|
          ≤ (k : ℝ) *
            (1 / ((2 * k * m : ℕ) : ℝ) +
             1 / ((2 * k * n : ℕ) : ℝ)) := by
      exact mul_le_mul hxbound hyreg hnonnegY (by positivity)
    have h2 :
        |yn| * |xm - xn|
          ≤ (k : ℝ) *
            (1 / ((2 * k * m : ℕ) : ℝ) +
             1 / ((2 * k * n : ℕ) : ℝ)) := by
      exact mul_le_mul hybound hxreg hnonnegX (by positivity)
    have hmain :
        |xm * ym - xn * yn|
          ≤
        (k : ℝ) *
          (1 / ((2 * k * m : ℕ) : ℝ) +
           1 / ((2 * k * n : ℕ) : ℝ)) +
        (k : ℝ) *
          (1 / ((2 * k * m : ℕ) : ℝ) +
           1 / ((2 * k * n : ℕ) : ℝ)) :=
      hsplit.trans (add_le_add h1 h2)
    change
      |(((x.seq (2 * k * m) * y.seq (2 * k * m) : ℚ) : ℝ) -
        ((x.seq (2 * k * n) * y.seq (2 * k * n) : ℚ) : ℝ))|
        ≤ 1 / (m : ℝ) + 1 / (n : ℝ)
    change |xm * ym - xn * yn| ≤ _
    refine hmain.trans ?_
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    field_simp
    ring

/-- Concrete source-faithful inhabitant of the previously abstract arithmetic
mirror. -/
def concreteVendoredArithmeticMirror : VendoredArithmeticMirror where
  zero := zeroReal
  one := oneReal
  add := addReal
  neg := negReal
  mul := mulReal
  K := bishopK

  K_pos := bishopK_pos

  seq_zero n := rfl
  seq_one n := rfl
  seq_add x y n := rfl
  seq_neg x n := rfl
  seq_mul x y n := rfl

structure Boundary where
  pinnedBishopKMirrored : Bool
  strictSampleBoundOwned : Bool
  constantRationalEmbeddingOwned : Bool
  exact2nAdditionMirrored : Bool
  pointwiseNegationMirrored : Bool
  exact2MaxKMultiplicationMirrored : Bool
  concreteVendoredArithmeticMirrorOwned : Bool

  generatedAgdaReplayObserved : Bool
  exactHeadLeanKernelReceiptObserved : Bool

def boundary : Boundary where
  pinnedBishopKMirrored := true
  strictSampleBoundOwned := true
  constantRationalEmbeddingOwned := true
  exact2nAdditionMirrored := true
  pointwiseNegationMirrored := true
  exact2MaxKMultiplicationMirrored := true
  concreteVendoredArithmeticMirrorOwned := true

  generatedAgdaReplayObserved := false
  exactHeadLeanKernelReceiptObserved := false

end

end Integration.BishopVendoredArithmeticConcrete
