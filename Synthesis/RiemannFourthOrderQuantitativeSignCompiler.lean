import Synthesis.RiemannFourthOrderLocalSignCompiler

/-!
# Quantitative fourth-order sign compiler

The existential fourth-order sign theorem is enough for local feasibility, but a
Clay-level high-zero argument needs to compare the target band with the physical
strip width.

This file gives an explicit radius from a fourth-derivative margin and a
Lipschitz constant.

Suppose

  f(0)=f'(0)=f''(0)=f'''(0)=0,
  f''''(0) <= -m,      m>0,

and

  |f''''(x)-f''''(0)| <= K |x|,   K>=0.

Set

  eps = min 1 (m / (2 (K+1))).

Then eps>0 and f'''' is strictly negative on (-eps,eps).  Repeating the
mean-value monotonicity argument four times yields

  0 < x < eps  ->  f(x)<0.

No Taylor polynomial API is required.
-/

noncomputable section

open Set Topology

namespace Synthesis

def quantitativeFourthOrderRadius (m K : ℝ) : ℝ :=
  min 1 (m / (2*(K+1)))

theorem quantitativeFourthOrderRadius_pos
    {m K : ℝ} (hm : 0 < m) (hK : 0 <= K) :
    0 < quantitativeFourthOrderRadius m K := by
  unfold quantitativeFourthOrderRadius
  apply lt_min
  · norm_num
  · positivity

theorem quantitativeFourthOrderRadius_le_one
    (m K : ℝ) :
    quantitativeFourthOrderRadius m K <= 1 := by
  unfold quantitativeFourthOrderRadius
  exact min_le_left _ _

theorem quantitativeFourthOrderRadius_mul_K_le_half
    {m K : ℝ} (hm : 0 < m) (hK : 0 <= K) :
    K * quantitativeFourthOrderRadius m K < m/2 := by
  have hK1 : 0 < K+1 := by linarith
  have heps :
      quantitativeFourthOrderRadius m K
        <= m/(2*(K+1)) := by
    unfold quantitativeFourthOrderRadius
    exact min_le_right _ _
  have hmul :=
    mul_le_mul_of_nonneg_left heps hK
  have hfrac :
      K * (m/(2*(K+1))) < m/2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hratio : K/(K+1) < 1 := by
      rw [div_lt_one hK1]
      linarith
    nlinarith [mul_pos hm (inv_pos.mpr (by positivity : 0 < (2:ℝ)))]
  exact hmul.trans_lt hfrac

/--
Explicit right-hand fourth-order sign theorem from a Lipschitz bound on the
fourth derivative.
-/
theorem neg_right_of_fourth_deriv_lipschitz
    {f f1 f2 f3 f4 : ℝ -> ℝ}
    {m K : ℝ}
    (hm : 0 < m)
    (hK : 0 <= K)
    (h01 : ∀ x : ℝ, HasDerivAt f (f1 x) x)
    (h12 : ∀ x : ℝ, HasDerivAt f1 (f2 x) x)
    (h23 : ∀ x : ℝ, HasDerivAt f2 (f3 x) x)
    (h34 : ∀ x : ℝ, HasDerivAt f3 (f4 x) x)
    (hf0 : f 0 = 0)
    (hf10 : f1 0 = 0)
    (hf20 : f2 0 = 0)
    (hf30 : f3 0 = 0)
    (hf40 : f4 0 <= -m)
    (hLip4 :
      ∀ x : ℝ,
        |f4 x - f4 0| <= K * |x|) :
    ∀ x : ℝ,
      0 < x ->
      x < quantitativeFourthOrderRadius m K ->
      f x < 0 := by
  let eps := quantitativeFourthOrderRadius m K
  have heps : 0 < eps :=
    quantitativeFourthOrderRadius_pos hm hK
  have hKeps : K*eps < m/2 :=
    quantitativeFourthOrderRadius_mul_K_le_half hm hK

  have hf4neg :
      ∀ x : ℝ, 0 < x -> x < eps -> f4 x < 0 := by
    intro x hx0 hxe
    have habs : |x| = x := abs_of_pos hx0
    have hvar := hLip4 x
    have hupp : f4 x - f4 0 <= K*x := by
      have := (abs_le.mp hvar).2
      simpa [habs] using this
    have hKx : K*x <= K*eps :=
      mul_le_mul_of_nonneg_left hxe.le hK
    linarith

  have hf3cont : Continuous f3 :=
    continuous_of_forall_continuousAt fun x => (h34 x).continuousAt
  have hf2cont : Continuous f2 :=
    continuous_of_forall_continuousAt fun x => (h23 x).continuousAt
  have hf1cont : Continuous f1 :=
    continuous_of_forall_continuousAt fun x => (h12 x).continuousAt
  have hfcont : Continuous f :=
    continuous_of_forall_continuousAt fun x => (h01 x).continuousAt

  have hanti3 : StrictAntiOn f3 (Icc (0:ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hf3cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h34 x).deriv]
    exact hf4neg x hx.1 hx.2

  have hf3neg :
      ∀ x : ℝ, 0 < x -> x < eps -> f3 x < 0 := by
    intro x hx0 hxe
    have h0 : (0:ℝ) ∈ Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hanti3 h0 hx hx0
    rw [hf30] at h
    exact h

  have hanti2 : StrictAntiOn f2 (Icc (0:ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hf2cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h23 x).deriv]
    exact hf3neg x hx.1 hx.2

  have hf2neg :
      ∀ x : ℝ, 0 < x -> x < eps -> f2 x < 0 := by
    intro x hx0 hxe
    have h0 : (0:ℝ) ∈ Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hanti2 h0 hx hx0
    rw [hf20] at h
    exact h

  have hanti1 : StrictAntiOn f1 (Icc (0:ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hf1cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h12 x).deriv]
    exact hf2neg x hx.1 hx.2

  have hf1neg :
      ∀ x : ℝ, 0 < x -> x < eps -> f1 x < 0 := by
    intro x hx0 hxe
    have h0 : (0:ℝ) ∈ Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hanti1 h0 hx hx0
    rw [hf10] at h
    exact h

  have hantif : StrictAntiOn f (Icc (0:ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hfcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h01 x).deriv]
    exact hf1neg x hx.1 hx.2

  intro x hx0 hxe
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
  have hx : x ∈ Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
  have h := hantif h0 hx hx0
  rw [hf0] at h
  exact h

end Synthesis
