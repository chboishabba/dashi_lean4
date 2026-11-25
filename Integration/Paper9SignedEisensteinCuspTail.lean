import Integration.Paper9CMNormalizedCuspWindow
import Integration.Paper9SelectedCMDomain

/-! SOURCE-WRITTEN, UNCOMPILED. Specialize the existing original
Eisenstein HasSum owners to the two-prefix tail. Signed 240/-504
normalizations are the actual original coefficients, not Monster
representation hypotheses. No new Fourier series. -/
namespace Integration.Paper9SignedEisensteinCuspTail
open Complex Filter UpperHalfPlane ArithmeticFunction
open scoped BigOperators Topology ArithmeticFunction.sigma
open Integration.Paper9OriginalEisensteinCoeff
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9SelectedCMDomain

noncomputable section

theorem signedNormalization (a b : ℂ) :
    (a-b=744 ∧ 3*a-2*b=1728) ↔ (a=240 ∧ b= -504) := by
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · linear_combination h2-2*h1
    · linear_combination h2-3*h1
  · rintro ⟨rfl,rfl⟩
    norm_num

theorem shiftedIndexBound (n : ℕ) : n+3 ≤ 3*2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ 2^n := by positivity
    omega

-- The original sigma_le_pow_succ, at actual omitted index n+3.
theorem termBound (c k n : ℕ) (q : ℂ) (hk : k≤5)
    (hsmall : ‖q‖≤(1/2:ℝ)^36) :
    ‖((c*σ k (n+3):ℕ):ℂ)*q^(n+3)‖ ≤
      (c:ℝ)*3^(k+1)*‖q‖^3*(1/2:ℝ)^n := by
  have hσ : (σ k (n+3):ℝ) ≤ ((3:ℝ)*2^n)^(k+1) := by
    calc
      _ ≤ ((n+3:ℕ):ℝ)^(k+1) := by
        exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k (n+3)
      _ ≤ _ := by
        gcongr
        exact_mod_cast shiftedIndexBound n
  have hr : (2:ℝ)^(k+1)*‖q‖≤1/2 := by
    have hpow : (2:ℝ)^(k+1)≤2^6 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ (2:ℝ)^6*((1/2:ℝ)^36) := by gcongr
      _ ≤ _ := by norm_num
  rw [norm_mul,Complex.norm_natCast,norm_pow,Nat.cast_mul]
  calc
    _ ≤ (c:ℝ)*((3:ℝ)*2^n)^(k+1)*‖q‖^(n+3) := by gcongr
    _ = (c:ℝ)*3^(k+1)*‖q‖^3*((2:ℝ)^(k+1)*‖q‖)^n := by
      rw [mul_pow,pow_add,mul_pow,← pow_mul, Nat.mul_comm n (k+1),pow_mul]
      ring
    _ ≤ _ := by gcongr

theorem normTail (f : ℕ → ℂ) (C : ℝ) (hC : 0≤C)
    (hs : Summable f) (hb : ∀ n, ‖f n‖≤C*(1/2:ℝ)^n) :
    ‖∑' n, f n‖≤2*C := by
  have hg : HasSum (fun n : ℕ => C*(1/2:ℝ)^n) (2*C) := by
    convert (hasSum_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)).mul_left C using 1 <;> ring
  have hn : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hg.summable
  exact (norm_tsum_le_tsum_norm hn).trans
    ((tsum_le_tsum hb hn hg.summable).trans_eq hg.tsum_eq)

-- Reuse actual all-index original source HasSum, including the
-- signed E6 coefficient and q^0=1. Only split at index 3.
theorem e4TwoTailAt (τ : ℍ)
    (hq : ‖Periodic.qParam 1 (τ:ℂ)‖≤(1/2:ℝ)^36) :
    ‖x (Periodic.qParam 1 τ) -
      (1+240*Periodic.qParam 1 τ+2160*(Periodic.qParam 1 τ)^2)‖ ≤
      38880*‖Periodic.qParam 1 (τ:ℂ)‖^3 := by
  let q := Periodic.qParam 1 (τ:ℂ)
  let f : ℕ → ℂ := fun n => (e4Z n:ℂ)*q^n
  have hs : HasSum f (Integration.MoonshineEisensteinAnalytic.E4 τ) := by
    simpa [f,q,smul_eq_mul] using e4HasSum τ
  have ht : Summable (fun n => f (n+3)) :=
    (summable_nat_add_iff 3).mpr hs.summable
  have he := hs.unique ((hasSum_nat_add_iff' 3).mp ht.hasSum)
  have hp : (∑ n ∈ Finset.range 3, f n)=1+240*q+2160*q^2 := by
    norm_num [f,e4Z,Finset.sum_range_succ,ArithmeticFunction.sigma]
  have hb := normTail (fun n => f (n+3)) (19440*‖q‖^3)
    (by positivity) ht (fun n => by
      simpa [f,e4Z,show n+3≠0 by omega] using termBound 240 3 n q (by decide) hq)
  rw [xAtQ,he,hp]
  convert hb using 1 <;> ring

theorem e6TwoTailAt (τ : ℍ)
    (hq : ‖Periodic.qParam 1 (τ:ℂ)‖≤(1/2:ℝ)^36) :
    ‖y (Periodic.qParam 1 τ) -
      (1-504*Periodic.qParam 1 τ-16632*(Periodic.qParam 1 τ)^2)‖ ≤
      734832*‖Periodic.qParam 1 (τ:ℂ)‖^3 := by
  let q := Periodic.qParam 1 (τ:ℂ)
  let f : ℕ → ℂ := fun n => (e6Z n:ℂ)*q^n
  have hs : HasSum f (Integration.MoonshineEisensteinAnalytic.E6 τ) := by
    simpa [f,q,smul_eq_mul] using e6HasSum τ
  have ht : Summable (fun n => f (n+3)) :=
    (summable_nat_add_iff 3).mpr hs.summable
  have he := hs.unique ((hasSum_nat_add_iff' 3).mp ht.hasSum)
  have hp : (∑ n ∈ Finset.range 3, f n)=1-504*q-16632*q^2 := by
    norm_num [f,e6Z,Finset.sum_range_succ,ArithmeticFunction.sigma]
  have hb := normTail (fun n => f (n+3)) (367416*‖q‖^3)
    (by positivity) ht (fun n => by
      simpa [f,e6Z,show n+3≠0 by omega,neg_mul,norm_neg] using
        termBound 504 5 n q (by decide) hq)
  rw [yAtQ,he,hp]
  convert hb using 1 <;> ring

end
end Integration.Paper9SignedEisensteinCuspTail
