import Integration.Paper9UniversalMonicSlice
import Mathlib.Order.Filter.Finite

/-! SOURCE-WRITTEN, UNCOMPILED. Existing original J analytic zero
mode, ramified chart q identities and primitive root provide separation
and infinite actual j-image directly. No inverse j, new cusp or
compactification assumption. -/
namespace Integration.Paper9SeparatedCusp
open Complex Filter UpperHalfPlane Function
open scoped Topology BigOperators
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9HeckePoleRemoval
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9ActualJSourceJet
open Integration.Paper9CyclotomicPacketReflection
open Integration.Paper9UniversalMonicSlice
open Integration.Paper9EulerMobiusTransport

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

theorem phaseInjective : Injective phase := by
  intro a b h
  rw [phaseEq,phaseEq] at h
  exact Fin.ext (primitive.pow_inj a.isLt b.isLt h)

theorem finiteScaled (a : Fin 41) (τ : ℍ) :
    tParam τ*chartValue a.castSucc τ=(phase a)⁻¹*jUnit (phase a*tParam τ) := by
  rw [jChartFinite]
  unfold jQ
  field_simp [phaseNe a,tNonzero τ]

theorem infinityScaled (τ : ℍ) :
    tParam τ^1681*chartValue (Fin.last 41) τ=jUnit (tParam τ^1681) := by
  rw [jChartInfinity,← tPower τ,← pow_mul]
  norm_num
  unfold jQ
  field_simp [tNonzero τ]

theorem finiteLimit (a : Fin 41) :
    Tendsto (fun τ => tParam τ*chartValue a.castSucc τ) atImInfty
      (𝓝 ((phase a)⁻¹)) := by
  have ht : Tendsto (fun τ => phase a*tParam τ) atImInfty (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := phase a)).mul tTendsto
  have hj : Tendsto (fun τ => jUnit (phase a*tParam τ)) atImInfty (𝓝 1) := by
    simpa [jUnitZero] using jContinuous.tendsto.comp ht
  have h := (tendsto_const_nhds (x := (phase a)⁻¹)).mul hj
  rw [mul_one] at h
  exact h.congr' (Eventually.of_forall fun τ => (finiteScaled a τ).symm)

theorem infinityLimit :
    Tendsto (fun τ => tParam τ^1681*chartValue (Fin.last 41) τ) atImInfty (𝓝 1) := by
  have ht : Tendsto (fun τ => tParam τ^1681) atImInfty (𝓝 0) := by
    simpa using tTendsto.pow 1681
  have h : Tendsto (fun τ => jUnit (tParam τ^1681)) atImInfty (𝓝 1) := by
    simpa [jUnitZero] using jContinuous.tendsto.comp ht
  exact h.congr' (Eventually.of_forall fun τ => (infinityScaled τ).symm)

theorem finiteLargeLimit (a : Fin 41) :
    Tendsto (fun τ => tParam τ^1681*chartValue a.castSucc τ) atImInfty (𝓝 0) := by
  have h := (tTendsto.pow 1680).mul (finiteLimit a)
  simp only [zero_pow (by decide : 1680≠0),zero_mul] at h
  apply h.congr'
  exact Eventually.of_forall (fun τ => by rw [← mul_assoc,← pow_succ])

theorem finitePairSeparated (a b : Fin 41) (hab : a≠b) :
    ∀ᶠ τ in atImInfty, chartValue a.castSucc τ≠chartValue b.castSucc τ := by
  have hne : (phase a)⁻¹-(phase b)⁻¹≠0 := by
    intro h
    apply hab
    apply phaseInjective
    exact inv_injective (sub_eq_zero.mp h)
  have he := ((finiteLimit a).sub (finiteLimit b)).eventually_ne hne
  filter_upwards [he] with τ h
  intro hab'
  apply h
  rw [hab',sub_self]

theorem finiteInfinitySeparated (a : Fin 41) :
    ∀ᶠ τ in atImInfty, chartValue a.castSucc τ≠chartValue (Fin.last 41) τ := by
  have he := ((finiteLargeLimit a).sub infinityLimit).eventually_ne
    (by norm_num : (0:ℂ)-1≠0)
  filter_upwards [he] with τ h
  intro hab'
  apply h
  rw [hab',sub_self]

theorem eventualChartSeparation :
    ∀ᶠ τ in atImInfty, Injective (fun i : Chart => chartValue i τ) := by
  have hpair : ∀ᶠ τ in atImInfty, ∀ a b : Fin 41, a≠b →
      chartValue a.castSucc τ≠chartValue b.castSucc τ := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    by_cases h : a=b
    · exact Eventually.of_forall (fun _ hn => (hn h).elim)
    · exact (finitePairSeparated a b h).mono (fun _ he _ => he)
  have hinf : ∀ᶠ τ in atImInfty, ∀ a : Fin 41,
      chartValue a.castSucc τ≠chartValue (Fin.last 41) τ :=
    Filter.eventually_all.mpr finiteInfinitySeparated
  filter_upwards [hpair,hinf] with τ hp hi
  intro i k
  revert k
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro k
    refine Fin.lastCases (fun _ => rfl) (fun b h => ?_) k
    exact False.elim (hi b h.symm)
  · intro k
    refine Fin.lastCases (fun h => False.elim (hi a h)) (fun b h => ?_) k
    by_contra hne
    exact hp a b (fun e => hne (congrArg Fin.castSucc e)) h

-- q*j has limit 1 from the original jUnit. For EACH fixed target,
-- q*(j-target) tends to 1, excluding that target eventually.
theorem qLimit : Tendsto (fun τ : ℍ => qExt τ) atImInfty (𝓝 0) := by
  have h := tTendsto.pow 41
  simp only [zero_pow (by decide : 41≠0)] at h
  exact h.congr' (Eventually.of_forall tPower)

theorem jAvoids (y : ℂ) : ∀ᶠ τ in atImInfty, j τ≠y := by
  have hj : Tendsto (fun τ : ℍ => jUnit (qExt τ)) atImInfty (𝓝 1) := by
    simpa [jUnitZero] using jContinuous.tendsto.comp qLimit
  have hq := qLimit.mul (tendsto_const_nhds (x := y))
  rw [zero_mul] at hq
  have he := (hj.sub hq).eventually_ne (by norm_num : (1:ℂ)-0≠0)
  filter_upwards [he] with τ h
  intro he'
  apply h
  rw [actualJUnit,he',sub_self]

def separatedImage : Set ℂ := {x | ∃ τ : ℍ,
  x=j τ ∧ Injective (fun i : Chart => chartValue i τ)}

theorem separatedImageInfinite : separatedImage.Infinite := by
  intro hfin
  have hAvoid : ∀ᶠ τ in atImInfty, ∀ y ∈ separatedImage, j τ≠y :=
    hfin.eventually_all.mpr (fun y _ => jAvoids y)
  obtain ⟨τ,hsep,havoid⟩ := (eventualChartSeparation.and hAvoid).exists
  exact havoid (j τ) ⟨τ,rfl,hsep⟩ rfl

theorem actualSymmetry (τ σ : ℍ) :
    actualProduct τ (j σ)=actualProduct σ (j τ) :=
  symmetryFromSeparatedImage separatedImageInfinite τ σ

end
end Integration.Paper9SeparatedCusp
