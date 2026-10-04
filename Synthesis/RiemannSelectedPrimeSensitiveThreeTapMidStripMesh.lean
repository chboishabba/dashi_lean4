import Synthesis.RiemannSelectedPrimeSensitiveThreeTapGlobalize

/-!
# Finite-mesh compiler for the compact mid-strip

Once the near-line band is paid, the remaining horizontal displacement range
is compact.  This file turns a Lipschitz bound plus finitely many certified
sample values into positivity on the entire strip.

No numerical samples or derivative bound are asserted here.  The theorem is a
rigorous consumer for interval arithmetic / exact finite verification:

* K is a proved Lipschitz constant for the actual terminal profile;
* every point of [delta,1/2] lies within mesh radius r of a certified node;
* every node value is at least m>0;
* K r < m.

Then the whole mid-strip is positive.
-/

noncomputable section
namespace Synthesis

open Set
open scoped Real BigOperators NNReal

/-- Generic finite-net positivity lemma for a real Lipschitz function. -/
theorem positive_on_interval_of_finite_net
    {f : ℝ → ℝ}
    {a b r m : ℝ}
    {K : NNReal}
    (nodes : Finset ℝ)
    (hr : 0 <= r)
    (hm : 0 < m)
    (hLip : LipschitzWith K f)
    (hnode : ∀ x ∈ nodes, m <= f x)
    (hcover : ∀ y : ℝ, a <= y -> y <= b ->
      ∃ x ∈ nodes, |y-x| <= r)
    (hmargin : (K : ℝ) * r < m) :
    ∀ y : ℝ, a <= y -> y <= b -> 0 < f y := by
  intro y hay hyb
  obtain ⟨x,hx,hxy⟩ := hcover y hay hyb
  have hdist := hLip y x
  simp only [Real.dist_eq] at hdist
  have hK0 : 0 <= (K : ℝ) := K.coe_nonneg
  have hscaled : (K : ℝ) * |y-x| <= (K : ℝ) * r :=
    mul_le_mul_of_nonneg_left hxy hK0
  have hdiff : |f y - f x| <= (K : ℝ) * r := by
    exact hdist.trans hscaled
  have hlo : f x - (K : ℝ)*r <= f y := by
    have := (abs_le.mp hdiff).1
    linarith
  have hxn := hnode x hx
  linarith

/-- Specialized finite-mesh compiler for the actual three-tap terminal
profile on the compact displacement strip. -/
theorem QuarticFourSignedPolePair.threeTapMidStripPositive_of_finite_mesh
    {t eps mult delta r m : ℝ}
    {K : NNReal}
    (W : QuarticFourSignedPolePair t)
    (nodes : Finset ℝ)
    (hr : 0 <= r)
    (hm : 0 < m)
    (hLip : LipschitzWith K (W.threeTapAdaptiveTerminalProfile eps mult))
    (hnode : ∀ x ∈ nodes,
      m <= W.threeTapAdaptiveTerminalProfile eps mult x)
    (hcover : ∀ a : ℝ, delta <= a -> a <= (1/2 : ℝ) ->
      ∃ x ∈ nodes, |a-x| <= r)
    (hmargin : (K : ℝ) * r < m) :
    W.ThreeTapMidStripPositive eps mult delta := by
  intro a had haHalf
  exact positive_on_interval_of_finite_net nodes hr hm hLip hnode hcover hmargin
    a had haHalf

/-- Complete one-scale globalization from a near-line band and one finite mesh
certificate. -/
theorem QuarticFourSignedPolePair.threeTap_globalize_near_and_finite_mesh
    {t eps mult delta r m : ℝ}
    {K : NNReal}
    (W : QuarticFourSignedPolePair t)
    (hnear : ∀ a : ℝ, 0 < a -> a < delta ->
      0 < W.threeTapAdaptiveTerminalProfile eps mult a)
    (nodes : Finset ℝ)
    (hr : 0 <= r)
    (hm : 0 < m)
    (hLip : LipschitzWith K (W.threeTapAdaptiveTerminalProfile eps mult))
    (hnode : ∀ x ∈ nodes,
      m <= W.threeTapAdaptiveTerminalProfile eps mult x)
    (hcover : ∀ a : ℝ, delta <= a -> a <= (1/2 : ℝ) ->
      ∃ x ∈ nodes, |a-x| <= r)
    (hmargin : (K : ℝ) * r < m) :
    W.ThreeTapAllOffLineDisplacementsPositive eps mult := by
  apply W.threeTap_globalize_near_and_mid hnear
  exact W.threeTapMidStripPositive_of_finite_mesh nodes hr hm hLip hnode hcover hmargin

end Synthesis
