import Synthesis.NavierStokesActualPhysicalLocalEnergyFlowExact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
R27/R29/R30 finite continuation: actual real compact ball and clopen
agreement of local solution charts. The Base369PrefixUltrametricExact
and InverseLimitClopenRefinement donors motivate nested agreement,
but their discrete cylinders are NOT claimed clopen in the real
energy ball. Instead the equal-solution locus is genuinely clopen
in the connected time interval. Classical ODE compact continuation.
-/
namespace DASHI.NavierStokes.RealContinuation
open Set Filter Metric
open scoped Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]

def SolvesOn (F : E → E) (x : ℝ → E) (I : Set ℝ) :=
  ∀ t ∈ I, HasDerivAt x (F (x t)) t

theorem local_agreement (F : E → E) (hF : ContDiff ℝ 1 F)
    (x y : ℝ → E) (t : ℝ)
    (hx : ∀ᶠ s in 𝓝 t,HasDerivAt x (F (x s)) s)
    (hy : ∀ᶠ s in 𝓝 t,HasDerivAt y (F (y s)) s)
    (he : x t=y t) : x =ᶠ[𝓝 t] y := by
  obtain ⟨K,S,hS,hLip⟩ := (hF.contDiffAt (x:=x t)).exists_lipschitzOnWith
  have hcX : ContinuousAt x t := hx.self_of_nhds.continuousAt
  have hcY : ContinuousAt y t := hy.self_of_nhds.continuousAt
  have hxs : ∀ᶠ s in 𝓝 t,x s∈S := hcX hS
  have hys : ∀ᶠ s in 𝓝 t,y s∈S := hcY (by rwa [← he])
  exact ODE_solution_unique_of_eventually (v:=fun _=>F) (s:=fun _=>S)
    (Eventually.of_forall fun _=>hLip) (hx.and hxs) (hy.and hys) he

/-- This is the genuine clopen weld: equality is closed by continuity,
open by local uniqueness, and therefore contains the entire connected
time interval when it contains one initial time. -/
theorem agreement_clopen (F : E → E) (hF : ContDiff ℝ 1 F)
    (x y : ℝ → E) {I : Set ℝ} (hI : IsOpen I)
    (hx : SolvesOn F x I) (hy : SolvesOn F y I) :
    IsClopen {t : I | x t=y t} := by
  have hcX : ContinuousOn x I := fun t ht=>(hx t ht).continuousAt.continuousWithinAt
  have hcY : ContinuousOn y I := fun t ht=>(hy t ht).continuousAt.continuousWithinAt
  refine ⟨isClosed_eq hcX.restrict hcY.restrict,?_⟩
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have he : x t=y t := ht
  have hxe : ∀ᶠ s in 𝓝 (t:ℝ),HasDerivAt x (F (x s)) s :=
    (hI.mem_nhds t.2).mono fun s hs=>hx s hs
  have hye : ∀ᶠ s in 𝓝 (t:ℝ),HasDerivAt y (F (y s)) s :=
    (hI.mem_nhds t.2).mono fun s hs=>hy s hs
  have h := local_agreement F hF x y t hxe hye he
  exact continuous_subtype_val.continuousAt h

theorem agreement_on_connected (F : E → E) (hF : ContDiff ℝ 1 F)
    (x y : ℝ → E) {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hx : SolvesOn F x I) (hy : SolvesOn F y I)
    (t₀ : ℝ) (ht : t₀∈I) (he : x t₀=y t₀) : EqOn x y I := by
  letI : PreconnectedSpace I := hconn.preconnectedSpace
  have hu := (agreement_clopen F hF x y hI hx hy).eq_univ
    (show ({t : I | x t=y t}:Set I).Nonempty from ⟨⟨t₀,ht⟩,he⟩)
  intro t ht
  have hm : (⟨t,ht⟩:I)∈({t : I | x t=y t}:Set I) := by rw [hu]; trivial
  exact hm

/-- Compactness supplies a finite family of real solution charts.
Take the minimum of their positive existence radii. No global
Lipschitz hypothesis, and no assumption of a discrete clopen cover. -/
theorem compact_uniform_restart (F : E → E) (hF : ContDiff ℝ 1 F)
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ δ>0,∀ z∈K,∀ t₀ : ℝ,∃ y : ℝ → E,
      y t₀=z ∧ SolvesOn F y (Ioo (t₀-δ) (t₀+δ)) := by
  classical
  have hloc (p : K) : ∃ r>0,∃ ε>0,∀ z∈closedBall (p:E) r,
      ∃ y : ℝ → E,y 0=z ∧ SolvesOn F y (Ioo (-ε) ε) := by
    obtain ⟨r,hr,e,he,hh⟩ :=
      (hF.contDiffAt (x:=(p:E))).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
    exact ⟨r,hr,e,he,by simpa [SolvesOn] using hh⟩
  choose r hr e he H using hloc
  have hc : K⊆⋃ p : K,ball (p:E) (r p) := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self (hr ⟨p,hp⟩)⟩
  obtain ⟨C,hC⟩ := hK.elim_finite_subcover (fun p : K=>ball (p:E) (r p))
    (fun _=>isOpen_ball) hc
  have hneC : C.Nonempty := by
    obtain ⟨p,hp⟩ := hne
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hC hp)
    obtain ⟨hqC,_⟩ := mem_iUnion.mp hq
    exact ⟨q,hqC⟩
  obtain ⟨q,hq,hmin⟩ := C.exists_min_image e hneC
  refine ⟨e q,he q,?_⟩
  intro z hz t₀
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hC hz)
  obtain ⟨hpC,hzp⟩ := mem_iUnion.mp hp
  obtain ⟨y,hy,hd⟩ := H p z (ball_subset_closedBall hzp)
  refine ⟨fun t=>y (t-t₀),by simpa using hy,?_⟩
  intro t ht
  have hlt := hmin p hpC
  have hm : t-t₀∈Ioo (-e p) (e p) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hd' := (hd (t-t₀) hm).comp t ((hasDerivAt_id t).sub_const t₀)
  simpa using hd'

/-- Extend the same old solution through its finite right endpoint:
restart inside the old interval sufficiently close to its boundary.
Overlap agreement is the clopen uniqueness lemma above, not a
selection of an unrelated trajectory. -/
theorem extend_bounded_open_interval_tail (F : E → E) (hF : ContDiff ℝ 1 F)
    (x : ℝ → E) (a s b : ℝ) (has : a≤s) (hsb : s<b)
    (hx : SolvesOn F x (Ioo a b))
    (K : Set E) (hK : IsCompact K) (hb : ∀ t∈Ioo s b,x t∈K) :
    ∃ c>b,∃ z : ℝ → E,SolvesOn F z (Ioo a c) ∧ EqOn z x (Ioo a b) := by
  have hmid : (s+b)/2∈Ioo s b := ⟨by linarith,by linarith⟩
  obtain ⟨δ,hδ,H⟩ := compact_uniform_restart F hF K hK ⟨x _,hb _ hmid⟩
  let t₀ := b-min (δ/2) ((b-s)/2)
  have hgap : 0<min (δ/2) ((b-s)/2) := lt_min (by positivity) (by linarith)
  have ht₀tail : t₀∈Ioo s b := by
    dsimp [t₀]
    exact ⟨by linarith [min_le_right (δ/2) ((b-s)/2)],by linarith⟩
  have ht₀ : t₀∈Ioo a b := ⟨has.trans_lt ht₀tail.1,ht₀tail.2⟩
  have hc : b<t₀+δ := by
    dsimp [t₀]
    linarith [min_le_left (δ/2) ((b-s)/2)]
  obtain ⟨y,hy,hd⟩ := H (x t₀) (hb t₀ ht₀tail) t₀
  let J := Ioo (max a (t₀-δ)) b
  have hj (t : ℝ) (ht : t∈J) :
      t∈Ioo a b ∧ t∈Ioo (t₀-δ) (t₀+δ) := by
    exact ⟨⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩,
      ⟨(le_max_right _ _).trans_lt ht.1,ht.2.trans hc⟩⟩
  have htJ : t₀∈J := ⟨max_lt_iff.mpr ⟨ht₀.1,by linarith⟩,ht₀.2⟩
  have heq : EqOn x y J :=
    agreement_on_connected F hF x y isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun t ht=>hx t (hj t ht).1) (fun t ht=>hd t (hj t ht).2)
      t₀ htJ hy.symm
  let z := fun t=>if t<t₀ then x t else y t
  have hz (t : ℝ) (ht : t∈Ioo a b) : z t=x t := by
    by_cases h : t<t₀
    · simp [z,h]
    · have htj : t∈J := ⟨htJ.1.trans_le (le_of_not_gt h),ht.2⟩
      simp [z,h,heq htj]
  refine ⟨t₀+δ,hc,z,?_,hz⟩
  intro t ht
  by_cases h : t<t₀
  · have hOld : t∈Ioo a b := ⟨ht.1,h.trans ht₀.2⟩
    have hev : z =ᶠ[𝓝 t] x := by
      filter_upwards [isOpen_Iio.mem_nhds h] with s hs
      simp [z,hs]
    rw [hz t hOld]
    exact (hx t hOld).congr_of_eventuallyEq hev
  · have hNew : t∈Ioo (t₀-δ) (t₀+δ) :=
      ⟨(by linarith : t₀-δ<t₀).trans_le (le_of_not_gt h),ht.2⟩
    have hev : z =ᶠ[𝓝 t] y := by
      by_cases hgt : t₀<t
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
        simp [z,not_lt_of_gt hs]
      · have htEq : t=t₀ := le_antisymm (le_of_not_gt hgt) (le_of_not_gt h)
        subst t
        filter_upwards [isOpen_Ioo.mem_nhds htJ] with s hs
        by_cases hh : s<t₀ <;> simp [z,hh,heq hs]
    have hz' : z t=y t := by simp [z,h]
    rw [hz']
    exact (hd t hNew).congr_of_eventuallyEq hev

/-- The full-interval version is the special case s=a. -/
theorem extend_bounded_open_interval (F : E → E) (hF : ContDiff ℝ 1 F)
    (x : ℝ → E) (a b : ℝ) (hab : a<b)
    (hx : SolvesOn F x (Ioo a b))
    (K : Set E) (hK : IsCompact K) (hb : ∀ t∈Ioo a b,x t∈K) :
    ∃ c>b,∃ z : ℝ → E,SolvesOn F z (Ioo a c) ∧ EqOn z x (Ioo a b) :=
  extend_bounded_open_interval_tail F hF x a a b le_rfl hab hx K hK hb

end
end DASHI.NavierStokes.RealContinuation
