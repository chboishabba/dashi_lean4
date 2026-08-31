/-
# Row A1a — welding the position-space vanishing to the momentum-space symbol

`AveragingLorentzDiagonal` proves that every background derivative of the block
averaging operator vanishes on a mixed Lorentz component, and
`LorentzBlockDiagonal` proves the same for the constrained (kernel) projection.
Both statements are about *position-space kernels*.  The patch theorems of
`MixedComponentPatch`, on the other hand, consume `MixedVanishing` for
*momentum-space* `VertexSymbol`s, and until now took it as a hypothesis.

This file removes that hypothesis.  The bridge is the elementary but essential
observation that the momentum-space symbol is obtained from the position-space
kernel by a transform acting **only on the position indices**: the Lorentz and
colour indices are spectators.  Hence a kernel that is identically zero on a
mixed Lorentz component has an identically zero symbol there, whatever the
transform, provided only that the transform sends the zero kernel to zero — the
one property every linear transform has.

* `PositionTransform`, `AnnihilatesZero`, `symbolOfPositionKernel` : the bridge.
* `mixedVanishing_symbolOfPositionKernel` : mixed-vanishing transfers.
* `averagingVariationKernel`, `mixedVanishing_averagingVariationSymbol` : the
  `Q` piece of `V = W + Q + R` has `MixedVanishing`, *proved*.
* `constrainedProjectionVariationKernel`,
  `mixedVanishing_constrainedProjectionVariationSymbol` : the constrained part
  of the `R` piece has `MixedVanishing`, *proved*.
* `constrainedFirstVariation_mixedPatch_floor_welded` : the Row A1a patch floor
  with both `MixedVanishing` hypotheses discharged from the literal source
  objects, leaving only the identification of the three pieces of `V` with the
  literal averaging kernel, constrained projection and Wilson/gauge symbols.

**Honest status.**  What remains hypothetical is the *identification*: that the
`Q` component of the constrained first variation is the transform of the
background derivative of the literal block-averaging kernel, and likewise for
the constrained projection.  Those are stated as equations between named
objects, not assumed as bounds.  Row A1 is not closed.
-/
import RequestProject.YangMills.MixedComponentPatch
import RequestProject.YangMills.AveragingLorentzDiagonal
import RequestProject.YangMills.LorentzBlockDiagonal

namespace YangMills

open Matrix

/-! ## 1. The transform acts only on the position indices -/

/-- A momentum transform of a position-space kernel.  It takes a function of the
two position arguments to a function of the momentum; the Lorentz and colour
indices never enter. -/
abbrev PositionTransform (S S' : Type*) : Type _ := ((S × S') → ℝ) → (Fin 4 → ℝ) → ℝ

/-- The only property of the transform that is needed: it sends the zero kernel
to the zero function.  Every linear transform — in particular every Fourier
transform — has it. -/
def AnnihilatesZero {S S' : Type*} (Phi : PositionTransform S S') : Prop :=
  ∀ q, Phi (fun _ => 0) q = 0

/-- The momentum-space symbol of a fully index-resolved position-space kernel. -/
def symbolOfPositionKernel {color S S' : Type*} (Phi : PositionTransform S S')
    (K : Fin 4 → Fin 4 → Fin 4 → color → color → color → (S × S') → ℝ) :
    VertexSymbol color :=
  fun al be rho a b c q => Phi (K al be rho a b c) q

/-- **Mixed vanishing transfers from the kernel to the symbol.**  Because the
transform touches only the position indices, a kernel that vanishes identically
on the mixed Lorentz components has a symbol that vanishes there too. -/
theorem mixedVanishing_symbolOfPositionKernel {color S S' : Type*}
    {Phi : PositionTransform S S'}
    {K : Fin 4 → Fin 4 → Fin 4 → color → color → color → (S × S') → ℝ}
    (hPhi : AnnihilatesZero Phi)
    (hK : ∀ al be rho : Fin 4, ∀ a b c : color, al ≠ be → K al be rho a b c = fun _ => 0) :
    MixedVanishing (symbolOfPositionKernel Phi K) := by
  intro al be rho a b c q hne
  rw [symbolOfPositionKernel, hK al be rho a b c hne]
  exact hPhi q

/-- The concrete transform the bridge is meant for: a weighted sum over the two
position indices, i.e. a lattice Fourier transform with kernel `w`. -/
noncomputable def weightedPositionTransform {S S' : Type*} [Fintype S] [Fintype S']
    (w : (S × S') → (Fin 4 → ℝ) → ℝ) : PositionTransform S S' :=
  fun K q => ∑ p : S × S', K p * w p q

/-- Every such transform annihilates the zero kernel, so the bridge is not
vacuous. -/
theorem annihilatesZero_weightedPositionTransform {S S' : Type*} [Fintype S] [Fintype S']
    (w : (S × S') → (Fin 4 → ℝ) → ℝ) : AnnihilatesZero (weightedPositionTransform w) := by
  intro q
  simp [weightedPositionTransform]

/-! ## 2. The averaging variation `Q` -/

/-- The position-space kernel of the first background variation of the literal
block-averaging operator: the background family is differentiated in the
direction labelled by the background Lorentz index `ρ` and background colour
index `c`, and the two position slots are the coarse and fine sites. -/
noncomputable def averagingVariationKernel {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (T : Fin 4 → color → ℝ → TransportData color) (t0 : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → color → color → color → (Site × Site) → ℝ :=
  fun al be rho a b c p =>
    deriv (fun t : ℝ => averagingKernel L (T rho c t) p.1 al a p.2 be b) t0

/-- The averaging variation kernel vanishes identically on mixed Lorentz
components — this is `deriv_averagingKernel_mixed_zero` packaged as an equality
of functions of the two sites. -/
theorem averagingVariationKernel_mixed_zero {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (T : Fin 4 → color → ℝ → TransportData color) (t0 : ℝ)
    (al be rho : Fin 4) (a b c : color) (hne : al ≠ be) :
    averagingVariationKernel L T t0 al be rho a b c = fun _ => 0 := by
  funext p
  exact deriv_averagingKernel_mixed_zero L (T rho c) p.1 al a p.2 be b hne t0

/-- **`Q` has `MixedVanishing`, proved.**  The momentum symbol of the averaging
variation is identically zero on every mixed Lorentz component. -/
theorem mixedVanishing_averagingVariationSymbol {color : Type*} [Fintype color]
    [DecidableEq color] {Phi : PositionTransform Site Site} (hPhi : AnnihilatesZero Phi)
    (L : ℕ) (T : Fin 4 → color → ℝ → TransportData color) (t0 : ℝ) :
    MixedVanishing (symbolOfPositionKernel Phi (averagingVariationKernel L T t0)) :=
  mixedVanishing_symbolOfPositionKernel hPhi
    fun al be rho a b c hne => averagingVariationKernel_mixed_zero L T t0 al be rho a b c hne

/-! ## 3. The constrained projection part of `R` -/

/-- The position-space kernel of the first background variation of the
constrained (kernel) projection `Π = 1 − Qᵀ(QQᵀ)⁻¹Q`.  The internal index of the
fluctuation space is a position index paired with a colour index, so the two
position slots are the two internal position labels and the colour indices `a`,
`b` are the corresponding colour labels. -/
noncomputable def constrainedProjectionVariationKernel {color cc Idx : Type*}
    [Fintype cc] [DecidableEq cc] [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    (Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ) (t0 : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → color → color → color → (Idx × Idx) → ℝ :=
  fun al be rho a b c p =>
    deriv (fun t : ℝ => kerProjection (Qf rho c t) (al, (p.1, a)) (be, (p.2, b))) t0

/-- The constrained projection variation kernel vanishes identically on mixed
Lorentz components, for every background family whose averaging operator stays
Lorentz block diagonal and nondegenerate. -/
theorem constrainedProjectionVariationKernel_mixed_zero {color cc Idx : Type*}
    [Fintype cc] [DecidableEq cc] [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    {Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ} {t0 : ℝ}
    (hQ : ∀ rho c t, IsLorentzDiagonal (Qf rho c t))
    (hdet : ∀ rho c t, IsUnit ((Qf rho c t) * (Qf rho c t)ᵀ).det)
    (al be rho : Fin 4) (a b c : color) (hne : al ≠ be) :
    constrainedProjectionVariationKernel Qf t0 al be rho a b c = fun _ => 0 := by
  funext p
  exact deriv_kerProjection_mixed_zero (hQ rho c) (hdet rho c) (p.1, a) (p.2, b) hne t0

/-- **The constrained part of `R` has `MixedVanishing`, proved.** -/
theorem mixedVanishing_constrainedProjectionVariationSymbol {color cc Idx : Type*}
    [Fintype cc] [DecidableEq cc] [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    {Phi : PositionTransform Idx Idx} (hPhi : AnnihilatesZero Phi)
    {Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ} {t0 : ℝ}
    (hQ : ∀ rho c t, IsLorentzDiagonal (Qf rho c t))
    (hdet : ∀ rho c t, IsUnit ((Qf rho c t) * (Qf rho c t)ᵀ).det) :
    MixedVanishing
      (symbolOfPositionKernel Phi (constrainedProjectionVariationKernel Qf t0)) :=
  mixedVanishing_symbolOfPositionKernel hPhi
    fun al be rho a b c hne =>
      constrainedProjectionVariationKernel_mixed_zero hQ hdet al be rho a b c hne

/-! ## 4. The patch floor with both hypotheses discharged -/

/-- **The Row A1a patch floor, welded.**  The two `MixedVanishing` hypotheses of
`constrainedFirstVariation_mixedPatch_floor` are now *conclusions* about the
literal source objects: the block-averaging kernel and the constrained
projection.  What remains are identifications of the pieces of `V` with those
objects, and the Wilson/gauge component identifications — all displayed. -/
theorem constrainedFirstVariation_mixedPatch_floor_welded
    {color cc Idx : Type*} [Fintype color] [DecidableEq color]
    [Fintype cc] [DecidableEq cc] [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    (V : ConstrainedFirstVariation color) {Rgauge : VertexSymbol color} {f : ℝ}
    {PhiA : PositionTransform Site Site} {PhiP : PositionTransform Idx Idx}
    (hPhiA : AnnihilatesZero PhiA) (hPhiP : AnnihilatesZero PhiP)
    {L : ℕ} {T : Fin 4 → color → ℝ → TransportData color} {tA : ℝ}
    {Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ} {tP : ℝ}
    (hQ : ∀ rho c t, IsLorentzDiagonal (Qf rho c t))
    (hdet : ∀ rho c t, IsUnit ((Qf rho c t) * (Qf rho c t)ᵀ).det)
    (hQid : V.Q = symbolOfPositionKernel PhiA (averagingVariationKernel L T tA))
    (hRsplit : ∀ al be rho : Fin 4, ∀ a b c : color, ∀ q : Fin 4 → ℝ,
      V.R al be rho a b c q
        = symbolOfPositionKernel PhiP (constrainedProjectionVariationKernel Qf tP)
            al be rho a b c q
          + Rgauge al be rho a b c q)
    (hf : |f| ≤ 1) {a b c : color}
    (hW : ∀ x : Fin 4 → ℝ, V.W 0 1 1 a b c x = wilsonCubicBgZero x 0 1 1)
    (hRg : ∀ x : Fin 4 → ℝ, Rgauge 0 1 1 a b c x
      = gaugeVariationSymbol f (latticeMomentumVector x) 1 0 1)
    {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch (1 / 16)) :
    (1 : ℝ) / 5 ≤ |V.total 0 1 1 a b c x| := by
  refine constrainedFirstVariation_mixedPatch_floor V ?_ hRsplit
    (mixedVanishing_constrainedProjectionVariationSymbol hPhiP hQ hdet) hf hW hRg hx
  rw [hQid]
  exact mixedVanishing_averagingVariationSymbol hPhiA L T tA

end YangMills
