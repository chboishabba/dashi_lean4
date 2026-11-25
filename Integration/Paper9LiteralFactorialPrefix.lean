import Integration.Paper9HypergeometricSeriesODE

/-! SOURCE-WRITTEN, UNCOMPILED.
The literal integer recursion of BishopChudnovskyRationalMidpointExact,
with B_split = 1, is interpreted in Q and identified with the original
factorial terms. This is the Lean target of a source reflection, not
a claim of an Agda/Lean kernel translation. -/
namespace Integration.Paper9LiteralFactorialPrefix

open scoped BigOperators
open Integration.Paper9CuspOrderFactorial
open Integration.Paper9HypergeometricSeriesODE

def leafP : ℕ → ℤ
  | 0 => 1
  | n+1 => -(24*(2*(n : ℤ)+1)*(6*(n : ℤ)+1)*(6*(n : ℤ)+5))

def leafQ : ℕ → ℕ
  | 0 => 1
  | n+1 => 640320^3*(n+1)^3

def weight (n : ℕ) : ℤ := 13591409+545140134*(n : ℤ)

structure RawPrefix where
  p : ℤ
  q : ℕ
  t : ℤ

def prefix : ℕ → RawPrefix
  | 0 => ⟨1,1,0⟩
  | n+1 =>
    let u := prefix n
    let p := u.p * leafP n
    ⟨p, u.q * leafQ n, u.t * (leafQ n : ℤ) + p * weight n⟩

theorem leafQ_pos (n : ℕ) : 0 < leafQ n := by
  cases n <;> simp [leafQ] <;> positivity

theorem prefixQ_pos (n : ℕ) : 0 < (prefix n).q := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 0 < (prefix n).q * leafQ n
    exact Nat.mul_pos ih (leafQ_pos n)

def product (n : ℕ) : ℚ := (prefix n).p / ((prefix n).q : ℚ)
def sum (n : ℕ) : ℚ := (prefix n).t / ((prefix n).q : ℚ)
def leaf (n : ℕ) : ℚ := (leafP n : ℚ)/(leafQ n : ℚ)

theorem productStep (n : ℕ) :
    product (n+1) = product n * leaf n := by
  have hq : ((prefix n).q : ℚ) ≠ 0 := by exact_mod_cast (prefixQ_pos n).ne'
  have hl : (leafQ n : ℚ) ≠ 0 := by exact_mod_cast (leafQ_pos n).ne'
  unfold product leaf
  simp only [prefix,Int.cast_mul,Nat.cast_mul]
  field_simp [hq,hl] <;> ring

theorem sumStep (n : ℕ) :
    sum (n+1) = sum n + product (n+1)*(weight n : ℚ) := by
  have hq : ((prefix n).q : ℚ) ≠ 0 := by exact_mod_cast (prefixQ_pos n).ne'
  have hl : (leafQ n : ℚ) ≠ 0 := by exact_mod_cast (leafQ_pos n).ne'
  unfold sum product
  simp only [prefix,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp [hq,hl] <;> ring

theorem actualLeafSucc (n : ℕ) :
    leaf (n+1) = cmZ * ratio n := by
  rw [cmRatio]
  unfold leaf leafP leafQ C
  push_cast
  ring

-- The shift is essential: prefix 0 is empty, prefix 1 contains the
-- unweighted n=0 term equal to one.
theorem productFactorial (n : ℕ) :
    product (n+1) = coeff n * cmZ^n := by
  induction n with
  | zero => norm_num [product,prefix,leafP,leafQ,coeffZero]
  | succ n ih =>
    rw [show n+1+1=(n+1)+1 by rfl,productStep,ih,actualLeafSucc,
      coeffSucc,pow_succ]
    ring

theorem sumFactorial (N : ℕ) :
    sum N = ∑ n ∈ Finset.range N,
      (13591409+545140134*(n : ℚ))*(coeff n*cmZ^n) := by
  induction N with
  | zero => norm_num [sum,prefix]
  | succ N ih =>
    rw [sumStep,ih,productFactorial,Finset.sum_range_succ]
    unfold weight
    push_cast
    ring

-- This is a HasSum for the literal factorial weights at the selected CM
-- argument, not a claim that the CM j/period certificates were reflected.
theorem factorialHasSumCM :
    HasSum (fun n : ℕ => (13591409+545140134*(n : ℂ))*
      ((coeff n : ℂ)*(cmZ : ℂ)^n))
      (13591409*H (cmZ : ℂ)+545140134*jet 1 (cmZ : ℂ)) := by
  have hz : ‖(cmZ : ℂ)‖ < 1/2 := by
    rw [show (cmZ : ℂ) = ((cmZ : ℝ) : ℂ) by norm_cast,
      Complex.norm_real,Real.norm_eq_abs]
    norm_num [cmZ,C]
  have h0 := jetHasSum 0 (by decide) (cmZ : ℂ) hz
  have h1 := jetHasSum 1 (by decide) (cmZ : ℂ) hz
  have h := (h0.mul_left (13591409 : ℂ)).add (h1.mul_left (545140134 : ℂ))
  rw [jetZeroOrder] at h
  convert h using 1
  funext n
  simp [jetCoeff]
  ring

theorem literalPrefixTendsto :
    Filter.Tendsto (fun N => (sum N : ℂ)) Filter.atTop
      (nhds (13591409*H (cmZ : ℂ)+545140134*jet 1 (cmZ : ℂ))) := by
  have h := factorialHasSumCM.tendsto_sum_nat
  convert h using 1
  funext N
  rw [sumFactorial]
  push_cast
  rfl

end Integration.Paper9LiteralFactorialPrefix
