/-
# The same-ordinate reflection cluster and the positive even cone

`LiteralWeilEvenChannelTaper.lean` split the literal Weil four-sample balance as

    Q_pair + Q_rest + Q_prime + Q_Γ = 0    (in the parity quotient)

and proved the honest limitation: the pair contribution is purely even for *every*
height, so no parity coordinate distinguishes an off-line reflection pair from an
on-line one.  The next structural step is **not** a norm inequality for `Q_rest`.
The part of `Q_rest` that is most capable of being structurally coherent with the
target — the zeros sharing the target's ordinate — should be absorbed into the
signal instead of treated as noise.

This module does that.  For the target ordinate `t` the **same-ordinate fibre**

    SameOrd t = { ρ : nontrivial zero | Im ρ = t }

contains *every* zero at that ordinate; no uniqueness of the real part is assumed
anywhere.  The zero sum of the literal explicit formula is split along this fibre
into `Q_cluster` and `Q_offOrd`, and the balance becomes

    Q_cluster + Q_offOrd + Q_prime + Q_Γ + Q_pole = 0.

The key mechanism is a **positive linear functional on the even quotient**: with
the strengthened positive taper of `exists_positive_taper_poleEven_zero_pos`, the
functional `ℓ(v) = v 0 + v 1` (the sum of the two samples at radius `r`)

* kills the whole pole space, hence descends to the parity quotient, and
* evaluates every same-ordinate zero, whatever its height, to the strictly
  positive number `2 m_ρ A_{a_ρ}(r)`.

Because multiplicities are positive integers, **same-ordinate reflection pairs
cannot cancel one another in the positive even cone**.  Consequently

    ℓ(Q_cluster) ≥ ℓ(Q_pair) > 0,   Q_cluster ≠ 0,

and the residual channels are pinned with a *sign*, not merely a size:

    ℓ(Q_offOrd + Q_prime + Q_Γ) = -ℓ(Q_cluster) < 0.

Everything is unconditional: the balance comes from the literal zeta Weil explicit
formula of the companion, the splitting from the summability it supplies, and the
positivity from the explicit taper.  No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilEvenChannelTaper

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilSameOrdinateEvenCone

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOddChannelTaper Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper

/-! ## A nonnegative taper responds positively at every height -/

/-- **The positive even response.**  If the taper is nonnegative, has a point of
strict positivity, and its support is radially admissible for the sample point `s`
(so that `cos(su) > 0` there), then the even response is strictly positive — and
this holds at *every* height `a` at once, because `cosh` is everywhere positive. -/
theorem evenResp_pos_of_nonneg {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {s : ℝ} (hrad : ∀ u, g u ≠ 0 → |s * u| < π / 2)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) (a : ℝ) : 0 < evenResp g a s := by
  have hcos : ∀ u : ℝ, g u ≠ 0 → 0 < Real.cos (s * u) := by
    intro u hu
    have h := abs_lt.mp (hrad u hu)
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1], h.2⟩
  have hint : Integrable (fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hnonneg : 0 ≤ fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos (s * u)) := by
    intro u
    by_cases hu : g u = 0
    · simp [hu]
    · exact mul_nonneg (hnn u) (le_of_lt (mul_pos (Real.cosh_pos _) (hcos u hu)))
  rw [evenResp, integral_pos_iff_support_of_nonneg hnonneg hint]
  have hopen : IsOpen {u : ℝ | 0 < g u} := isOpen_lt continuous_const hg
  have hsub : {u : ℝ | 0 < g u}
      ⊆ Function.support (fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos (s * u))) := by
    intro u hu
    have hne : g u ≠ 0 := ne_of_gt hu
    exact ne_of_gt (mul_pos hu (mul_pos (Real.cosh_pos _) (hcos u hne)))
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨u₀, hu₀⟩) (measure_mono hsub)

/-- The radial admissibility clause of the positive taper, at the base radius. -/
theorem radial_of_two_radius {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (h : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) : ∀ u, g u ≠ 0 → |r * u| < π / 2 := by
  intro u hu
  have h1 := h u hu
  have h2 : |r * u| = r * |u| := by rw [abs_mul, abs_of_pos hr]
  have h3 : 0 ≤ |u| := abs_nonneg u
  nlinarith

/-- The radial admissibility clause of the positive taper, at the doubled radius. -/
theorem radial_two_radius {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (h : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) : ∀ u, g u ≠ 0 → |2 * r * u| < π / 2 := by
  intro u hu
  have h1 := h u hu
  have h2 : |2 * r * u| = 2 * r * |u| := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * r)]
  linarith [h2 ▸ h1]

/-! ## The same-ordinate fibre of the literal zero set -/

/-- **The same-ordinate fibre** at `t`: *every* nontrivial zero of `riemannZeta`
whose imaginary part equals `t`.  No uniqueness of the real part at a fixed
ordinate is assumed — the fibre is closed under the functional-equation
involution `ρ ↦ 1 - conj ρ`, and that is all that is used. -/
def SameOrd (t : ℝ) : Set Zeros := {ρ : Zeros | (ρ : ℂ).im = t}

/-- The same-ordinate cluster sum `∑_{Im ρ = t} Z_ρ`. -/
def sameOrdTerm (k : ℝ → ℂ) (t : ℝ) : ℂ := ∑' ρ : SameOrd t, zeroTerm k (ρ : Zeros)

/-- The off-ordinate sum `∑_{Im ρ ≠ t} Z_ρ`. -/
def offOrdTerm (k : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' ρ : ((SameOrd t)ᶜ : Set Zeros), zeroTerm k (ρ : Zeros)

/-- **The zero sum splits along the ordinate fibre.**  The summability is the one
the literal explicit formula supplies, so this is a decomposition step, not a
convergence step. -/
theorem zeroSum_split_ordinate {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (t : ℝ) : ∑' ρ : Zeros, zeroTerm k ρ = sameOrdTerm k t + offOrdTerm k t :=
  (Summable.tsum_add_tsum_compl ((zeroTerm_summable hk hkc).subtype _)
    ((zeroTerm_summable hk hkc).subtype _)).symm

/-- The four-sample vector of the same-ordinate cluster. -/
def clusterVec (kFam : Fin 4 → ℝ → ℂ) (t : ℝ) : Fin 4 → ℝ :=
  fun i => reim (sameOrdTerm (kFam i) t)

/-- The four-sample vector of the off-ordinate zeros. -/
def offOrdVec (kFam : Fin 4 → ℝ → ℂ) (t : ℝ) : Fin 4 → ℝ :=
  fun i => reim (offOrdTerm (kFam i) t)

/-- **The literal balance, split along the ordinate fibre.** -/
theorem literalWeilOrdinateFibreBalance {kFam : Fin 4 → ℝ → ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i)) (hkc : ∀ i, HasCompactSupport (kFam i)) (t : ℝ) :
    clusterVec kFam t + offOrdVec kFam t + primeVec kFam + gammaVec kFam + poleVec kFam = 0 := by
  funext i
  have h := literalWeilSampleBalance (hk i) (hkc i)
  rw [zeroSum_split_ordinate (hk i) (hkc i) t] at h
  have hz : reim (sameOrdTerm (kFam i) t + offOrdTerm (kFam i) t + primeTerm (kFam i)
      + (-gammaTerm (kFam i)) + (-poleTerm (kFam i))) = 0 := by
    rw [h]; exact reim_zero
  simp only [reim_add, reim_neg] at hz
  simpa [clusterVec, offOrdVec, primeVec, gammaVec, poleVec] using hz

/-! ## The positive even functional on the parity quotient -/

/-- **The even cone functional**: the sum of the two four-sample coordinates at the
base radius `r`.  It annihilates every odd pattern automatically, and — once the
taper kills the even pole response at radius `r` — the whole pole space. -/
def evenConeFunctional : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := v 0 + v 1
  map_add' u v := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem evenConeFunctional_apply (v : Fin 4 → ℝ) : evenConeFunctional v = v 0 + v 1 := rfl

theorem evenConeFunctional_evenPattern (x y : ℝ) :
    evenConeFunctional (evenPattern x y) = 2 * x := by
  show evenPattern x y 0 + evenPattern x y 1 = 2 * x
  simp [evenPattern]; ring

theorem evenConeFunctional_oddPattern (x y : ℝ) :
    evenConeFunctional (oddPattern x y) = 0 := by
  show oddPattern x y 0 + oddPattern x y 1 = 0
  simp [oddPattern]

/-- **The even cone functional annihilates the pole space** as soon as the
ordinate-modulated even pole response vanishes at the base radius. -/
theorem evenConeFunctional_poleSpace_le_ker {g : ℝ → ℝ} {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) :
    poleSpace g t r ≤ LinearMap.ker evenConeFunctional := by
  rw [poleSpace, Submodule.span_le]
  rintro v hv
  rcases hv with hv | hv
  · subst hv
    simp only [SetLike.mem_coe, LinearMap.mem_ker, evenConeFunctional_evenPattern, hpole]
    ring
  · rw [Set.mem_singleton_iff] at hv
    subst hv
    simp only [SetLike.mem_coe, LinearMap.mem_ker, evenConeFunctional_oddPattern]

/-- **The positive even functional on the parity quotient.** -/
def evenConeQuotientFunctional (g : ℝ → ℝ) (t r : ℝ) (hpole : poleEvenResp g t r = 0) :
    ParityQuotient g t r →ₗ[ℝ] ℝ :=
  Submodule.liftQ _ evenConeFunctional (evenConeFunctional_poleSpace_le_ker hpole)

theorem evenConeQuotientFunctional_qcls {g : ℝ → ℝ} {t r : ℝ} (hpole : poleEvenResp g t r = 0)
    (v : Fin 4 → ℝ) :
    evenConeQuotientFunctional g t r hpole (qcls g t r v) = v 0 + v 1 := rfl

/-! ## The cone weight of a single same-ordinate zero -/

/-- The height of a zero: its distance from the critical line, with sign. -/
def heightOf (ρ : Zeros) : ℝ := (ρ : ℂ).re - 1 / 2

/-- The **cone weight** of a zero: twice its multiplicity times its even response
at the base radius.  This is exactly what the even cone functional reads off. -/
def coneWeight (g : ℝ → ℝ) (r : ℝ) (ρ : Zeros) : ℝ :=
  2 * (((Zeta23.zetaZeroConfig).mult ρ : ℝ) * evenResp g (heightOf ρ) r)

/-- **The two samples at `±r` of a same-ordinate zero add up to its cone weight.**
The odd channel cancels between the two samples; only the even response survives,
and it enters with the positive integer multiplicity. -/
theorem reim_zeroTerm_cone {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) {ρ : Zeros} {t : ℝ} (him : (ρ : ℂ).im = t) (r : ℝ) :
    reim (zeroTerm (sampleTest g t r) ρ) + reim (zeroTerm (sampleTest g t (-r)) ρ)
      = coneWeight g r ρ := by
  have hre : (ρ : ℂ).re = 1 / 2 + heightOf ρ := by unfold heightOf; ring
  rw [reim_zeroTerm_sampleTest hg hgc heven hre him t r,
    reim_zeroTerm_sampleTest hg hgc heven hre him t (-r)]
  simp only [zeroResp, sub_self, add_zero, coneWeight]
  rw [evenResp_neg, oddResp_neg]
  ring

/-- The cone weight of a zero is strictly positive whenever the taper responds
positively at every height: multiplicities are positive integers. -/
theorem coneWeight_pos {g : ℝ → ℝ} {r : ℝ} (hA : ∀ a : ℝ, 0 < evenResp g a r) (ρ : Zeros) :
    0 < coneWeight g r ρ := by
  have hm : 1 ≤ (Zeta23.zetaZeroConfig).mult ρ :=
    (Zeta23.zetaZeroConfig).one_le_mult (ρ : ℂ) ρ.2
  have hmR : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult ρ : ℝ) := by exact_mod_cast hm
  have := hA (heightOf ρ)
  unfold coneWeight
  positivity

/-! ## The cluster value of the even cone functional -/

theorem reim_tsum {ι : Type*} {f : ι → ℂ} (hf : Summable f) :
    reim (∑' i, f i) = ∑' i, reim (f i) := by
  have hre : Summable fun i => (f i).re := (Complex.hasSum_re hf.hasSum).summable
  have him : Summable fun i => (f i).im := (Complex.hasSum_im hf.hasSum).summable
  unfold reim
  rw [Complex.re_tsum hf, Complex.im_tsum hf, ← hre.tsum_add him]

theorem summable_reim {ι : Type*} {f : ι → ℂ} (hf : Summable f) :
    Summable fun i => reim (f i) := by
  have hre : Summable fun i => (f i).re := (Complex.hasSum_re hf.hasSum).summable
  have him : Summable fun i => (f i).im := (Complex.hasSum_im hf.hasSum).summable
  exact hre.add him

theorem summable_coneWeight {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    Summable fun ρ : SameOrd t => coneWeight g r (ρ : Zeros) := by
  have h1 : Summable fun ρ : SameOrd t => reim (zeroTerm (sampleTest g t r) (ρ : Zeros)) :=
    summable_reim (((zeroTerm_summable (sampleTest_contDiff hgs t r)
      (sampleTest_hasCompactSupport hgc t r)).subtype _))
  have h2 : Summable fun ρ : SameOrd t => reim (zeroTerm (sampleTest g t (-r)) (ρ : Zeros)) :=
    summable_reim (((zeroTerm_summable (sampleTest_contDiff hgs t (-r))
      (sampleTest_hasCompactSupport hgc t (-r))).subtype _))
  have := h1.add h2
  refine this.congr (fun ρ => ?_)
  exact reim_zeroTerm_cone hgs.continuous hgc heven ρ.2 r

/-- **The even cone functional reads the cluster as a sum of positive weights.** -/
theorem clusterVec_cone_value {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    evenConeFunctional (clusterVec (sampleFam g t r) t)
      = ∑' ρ : SameOrd t, coneWeight g r (ρ : Zeros) := by
  have hs1 : Summable fun ρ : Zeros => zeroTerm (sampleTest g t r) ρ :=
    zeroTerm_summable (sampleTest_contDiff hgs t r) (sampleTest_hasCompactSupport hgc t r)
  have hs2 : Summable fun ρ : Zeros => zeroTerm (sampleTest g t (-r)) ρ :=
    zeroTerm_summable (sampleTest_contDiff hgs t (-r)) (sampleTest_hasCompactSupport hgc t (-r))
  have h1 : reim (sameOrdTerm (sampleTest g t r) t)
      = ∑' ρ : SameOrd t, reim (zeroTerm (sampleTest g t r) (ρ : Zeros)) :=
    reim_tsum (hs1.subtype _)
  have h2 : reim (sameOrdTerm (sampleTest g t (-r)) t)
      = ∑' ρ : SameOrd t, reim (zeroTerm (sampleTest g t (-r)) (ρ : Zeros)) :=
    reim_tsum (hs2.subtype _)
  have h3 : (∑' ρ : SameOrd t, reim (zeroTerm (sampleTest g t r) (ρ : Zeros)))
      + (∑' ρ : SameOrd t, reim (zeroTerm (sampleTest g t (-r)) (ρ : Zeros)))
      = ∑' ρ : SameOrd t, (reim (zeroTerm (sampleTest g t r) (ρ : Zeros))
          + reim (zeroTerm (sampleTest g t (-r)) (ρ : Zeros))) :=
    ((summable_reim (hs1.subtype _)).tsum_add (summable_reim (hs2.subtype _))).symm
  have h0 : evenConeFunctional (clusterVec (sampleFam g t r) t)
      = reim (sameOrdTerm (sampleTest g t r) t)
        + reim (sameOrdTerm (sampleTest g t (-r)) t) := rfl
  rw [h0, h1, h2, h3]
  exact tsum_congr fun ρ => reim_zeroTerm_cone hgs.continuous hgc heven ρ.2 r

/-- **`sameOrdinateClusterConePositive`.**  The same-ordinate cluster has strictly
positive even cone value: reflection pairs at the target ordinate cannot cancel
one another, whatever their heights and however many of them there are. -/
theorem sameOrdinateClusterConePositive {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hA : ∀ a : ℝ, 0 < evenResp g a r) (ρ₀ : SameOrd t) :
    0 < evenConeFunctional (clusterVec (sampleFam g t r) t) := by
  rw [clusterVec_cone_value hgs hgc heven t r]
  exact Summable.tsum_pos (summable_coneWeight hgs hgc heven t r)
    (fun ρ => (coneWeight_pos hA _).le) ρ₀ (coneWeight_pos hA _)

/-- **`clusterDominatesTargetPair`.**  The cluster value dominates the value of any
finite subfamily; in particular of the target zero alone. -/
theorem clusterDominatesZero {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hA : ∀ a : ℝ, 0 < evenResp g a r) (ρ₀ : SameOrd t) :
    coneWeight g r (ρ₀ : Zeros) ≤ evenConeFunctional (clusterVec (sampleFam g t r) t) := by
  classical
  rw [clusterVec_cone_value hgs hgc heven t r]
  have := Summable.sum_le_tsum (f := fun ρ : SameOrd t => coneWeight g r (ρ : Zeros))
    {ρ₀} (fun i _ => (coneWeight_pos hA _).le) (summable_coneWeight hgs hgc heven t r)
  simpa using this

/-- **`clusterDominatesReflectionPair`.**  For an off-line target the whole
reflection pair sits inside the fibre, and the cluster value dominates the pair's
own cone value `4 m A_a(r)`. -/
theorem clusterDominatesReflectionPair {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hA : ∀ a : ℝ, 0 < evenResp g a r) {ρstar : Zeros} {a : ℝ}
    (hre : (ρstar : ℂ).re = 1 / 2 + a) (him : (ρstar : ℂ).im = t) (ha : a ≠ 0) :
    4 * (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) * evenResp g a r)
      ≤ evenConeFunctional (clusterVec (sampleFam g t r) t) := by
  classical
  set ρ' : Zeros := reflectZero ρstar with hρ'
  have hre' : (ρ' : ℂ).re = 1 / 2 + -a := by
    show (Zeta23.reflect (ρstar : ℂ)).re = 1 / 2 + -a
    rw [Zeta23.reflect_re, hre]; ring
  have him' : (ρ' : ℂ).im = t := by
    show (Zeta23.reflect (ρstar : ℂ)).im = t
    rw [Zeta23.reflect_im, him]
  have hne : ρ' ≠ ρstar := by
    intro hcontra
    have h1 : (ρ' : ℂ).re = (ρstar : ℂ).re := by rw [hcontra]
    rw [hre, hre'] at h1
    exact ha (by linarith)
  -- both members of the pair lie in the fibre
  let P : SameOrd t := ⟨ρstar, him⟩
  let P' : SameOrd t := ⟨ρ', him'⟩
  have hPne : P' ≠ P := by
    intro hcontra
    exact hne (congrArg Subtype.val hcontra)
  have hmulteq : (Zeta23.zetaZeroConfig).mult ρ' = (Zeta23.zetaZeroConfig).mult ρstar :=
    reflectZero_mult ρstar
  have hw : coneWeight g r ρstar + coneWeight g r ρ'
      = 4 * (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) * evenResp g a r) := by
    have h1 : heightOf ρstar = a := by unfold heightOf; rw [hre]; ring
    have h2 : heightOf ρ' = -a := by unfold heightOf; rw [hre']; ring
    unfold coneWeight
    rw [h1, h2, hmulteq, evenResp_neg_height]
    ring
  rw [clusterVec_cone_value hgs hgc heven t r, ← hw]
  have hsum := Summable.sum_le_tsum (f := fun ρ : SameOrd t => coneWeight g r (ρ : Zeros))
    {P, P'} (fun i _ => (coneWeight_pos hA _).le) (summable_coneWeight hgs hgc heven t r)
  rwa [Finset.sum_pair hPne.symm] at hsum

/-! ## The capstone: the cluster carries a strictly positive even cone value -/

/-- **`literalWeilSameOrdinateEvenCone`.**  For an actual nontrivial zero `ρ*` of
`riemannZeta` with nonzero ordinate `t`, the literal zeta Weil explicit formula
supplies, for the strengthened positive even-channel taper `g` and radius `r`:

* the four-sample balance, split along the *ordinate fibre* of `ρ*`;
* a positive linear functional `ℓ` on the parity quotient — it annihilates the
  whole pole space, so `Q_pole` is invisible to it;
* `ℓ(Q_cluster) > 0`, hence `Q_cluster ≠ 0`, with the cluster containing every zero
  at the target ordinate, grouped under `ρ ↦ 1 - conj ρ`;
* the exact sign balance `ℓ(Q_offOrd + Q_prime + Q_Γ) = -ℓ(Q_cluster) < 0`.

Nothing is assumed: the balance is the explicit formula, the fibre split uses only
its summability, and the positivity is the explicit taper's. -/
theorem literalWeilSameOrdinateEvenCone {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ) (hpole : poleEvenResp g t r = 0),
      ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u) ∧ 0 < r
        ∧ (∀ u, 0 ≤ g u) ∧ (∀ a : ℝ, 0 < evenResp g a r)
        ∧ clusterVec (sampleFam g t r) t + offOrdVec (sampleFam g t r) t
            + primeVec (sampleFam g t r) + gammaVec (sampleFam g t r)
            + poleVec (sampleFam g t r) = 0
        ∧ evenConeQuotientFunctional g t r hpole (qcls g t r (poleVec (sampleFam g t r))) = 0
        ∧ 0 < evenConeQuotientFunctional g t r hpole
            (qcls g t r (clusterVec (sampleFam g t r) t))
        ∧ coneWeight g r ρstar ≤ evenConeQuotientFunctional g t r hpole
            (qcls g t r (clusterVec (sampleFam g t r) t))
        ∧ qcls g t r (clusterVec (sampleFam g t r) t) ≠ 0
        ∧ evenConeQuotientFunctional g t r hpole
            (qcls g t r (offOrdVec (sampleFam g t r) t + primeVec (sampleFam g t r)
              + gammaVec (sampleFam g t r)))
            = -evenConeQuotientFunctional g t r hpole
                (qcls g t r (clusterVec (sampleFam g t r) t))
        ∧ evenConeQuotientFunctional g t r hpole
            (qcls g t r (offOrdVec (sampleFam g t r) t + primeVec (sampleFam g t r)
              + gammaVec (sampleFam g t r))) < 0 := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hnn, -, -, hpole, hA, -⟩ :=
    exists_positive_taper_poleEven_zero ht
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hmem := poleVec_mem_poleSpace hgs.continuous hgc heven t r
  obtain ⟨-, hq1, -⟩ := parityQuotientBalance hmem hbal
  have hpos : 0 < evenConeQuotientFunctional g t r hpole
      (qcls g t r (clusterVec (sampleFam g t r) t)) := by
    rw [evenConeQuotientFunctional_qcls]
    exact sameOrdinateClusterConePositive hgs hgc heven hA ⟨ρstar, him⟩
  have hdom : coneWeight g r ρstar ≤ evenConeQuotientFunctional g t r hpole
      (qcls g t r (clusterVec (sampleFam g t r) t)) := by
    rw [evenConeQuotientFunctional_qcls]
    exact clusterDominatesZero hgs hgc heven hA ⟨ρstar, him⟩
  have hrestcls : qcls g t r (offOrdVec (sampleFam g t r) t + primeVec (sampleFam g t r)
      + gammaVec (sampleFam g t r)) = -qcls g t r (clusterVec (sampleFam g t r) t) := by
    rw [hq1, neg_neg]
  refine ⟨g, r, hpole, hgs, hgc, heven, hrpos, hnn, hA, hbal, ?_, hpos, hdom, ?_, ?_, ?_⟩
  · rw [qcls_poleVec hgs.continuous hgc heven, map_zero]
  · intro hzero
    rw [hzero, map_zero] at hpos
    exact lt_irrefl 0 hpos
  · rw [hrestcls, map_neg]
  · rw [hrestcls, map_neg]
    linarith

end LiteralWeilSameOrdinateEvenCone
end Zeta23Bridge
