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

-- Stable normalized cusp quotient. Consume the two polynomial
-- remainders; no tiny discriminant division in the error estimate.
theorem cuspRemainder (q N D : ℂ)
    (hq : q≠0) (hr : ‖q‖≤(1/2:ℝ)^36)
    (hN : ‖N-(1+720*q+179280*q^2)‖≤20000000*‖q‖^3)
    (hD : ‖D-(1-24*q)‖≤24000*‖q‖^2) :
    ‖N/D/q-1/q-744‖≤500000*‖q‖ := by
  let r := ‖q‖
  have hpos : 0<r := norm_pos_iff.mpr hq
  have hr0 : 0≤r := hpos.le
  have hsmall : r≤(1/2:ℝ)^36 := hr
  have hδ : ‖D-1‖≤24000*r^2+24*r := by
    calc
      _ = ‖(D-(1-24*q))-24*q‖ := by congr 1 <;> ring
      _ ≤ ‖D-(1-24*q)‖+‖24*q‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul,norm_ofNat]; exact add_le_add_right hD _
  have hdsmall : 24000*r^2+24*r≤1/2 := by
    have hp : r^2≤((1/2:ℝ)^36)^2 := by gcongr
    linarith
  have hd : 1/2≤‖D‖ := by
    have hn := norm_add_le D (1-D)
    rw [show D+(1-D)=1 by ring,norm_one,norm_sub_rev] at hn
    linarith
  have hdne : D≠0 := by
    intro he
    rw [he,norm_zero] at hd
    norm_num at hd
  have hb : ‖1+744*q‖≤2 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖744*q‖ := norm_add_le _ _
      _ = 1+744*r := by simp [norm_mul,r]
      _ ≤ _ := by linarith
  have hex : N-(1+744*q)*D =
      (N-(1+720*q+179280*q^2))+197136*q^2-
        (1+744*q)*(D-(1-24*q)) := by ring
  have hn : ‖N-(1+744*q)*D‖≤250000*r^2 := by
    rw [hex]
    calc
      _ ≤ ‖(N-(1+720*q+179280*q^2))+197136*q^2‖+
            ‖(1+744*q)*(D-(1-24*q))‖ := norm_sub_le _ _
      _ ≤ ‖N-(1+720*q+179280*q^2)‖+‖197136*q^2‖+
            ‖(1+744*q)*(D-(1-24*q))‖ :=
        add_le_add_right (norm_add_le _ _) _
      _ ≤ 20000000*r^3+197136*r^2+2*(24000*r^2) := by
        rw [norm_mul,norm_ofNat,norm_pow,norm_mul]
        gcongr
      _ ≤ _ := by
        have hc : 20000000*r+197136+2*24000≤250000 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg r)]
  have he : N/D/q-1/q-744=(N-(1+744*q)*D)/(D*q) := by
    field_simp [hq,hdne] <;> ring
  rw [he,norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hdne) hpos)).2
  calc
    _ ≤ 250000*r^2 := hn
    _ ≤ 500000*r*(‖D‖*r) := by
      nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg r)]

end
end Integration.Paper9SignedEisensteinCuspTail
