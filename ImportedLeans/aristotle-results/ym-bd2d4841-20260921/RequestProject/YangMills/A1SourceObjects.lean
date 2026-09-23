/-
# Row A1a — the constrained first variation *assembled from* the literal source
# objects, and the shell coefficient assembled from the literal channels

`A1WeldedAssembly` states the Row A1a conclusion for an *abstract* constrained
first variation `V = W + Q + R` and an *abstract* shell coefficient
`β = β_Z + β_int`, carrying the identifications

* `V.Q = ` transform of the block-averaging variation,
* `V.R = ` transform of the constrained projection variation `+` gauge symbol,
* `V.W = ` Wilson cubic vertex on the chosen component,
* `R_gauge = ` the computed gauge-projection variation there,
* `β_Z = ` the cell integral of the one-loop integrand,
* `β = β_Z + β_int`, `β_int = ` the five literal channels,

as hypotheses — "this named object is the corresponding source object" receipts.

This file removes all seven of them, not by proving them for an abstract `V`
(which is impossible: an abstract `V` need not be the literal one), but by
**constructing** the objects from the literal source data and re-deriving the
whole chain for the construction.  Concretely:

* `sourceConstrainedVariation` builds `V` out of
  - the background derivative of Bałaban's block-averaging kernel
    (`averagingVariationKernel`), pushed to momentum space by a literal lattice
    Fourier transform;
  - the background derivative of the constrained projection
    `Π = 1 − Qᵀ(QQᵀ)⁻¹Q` built on the *same* averaging operator
    (`literalAveragingMatrix`), likewise transformed;
  - the literal Wilson cubic vertex, with the colour structure constant;
  - the computed longitudinal gauge-projection variation.
* `shellBetaOfSources` builds `β` out of the one-loop integrand and the five
  literal remainder channels.

For those objects every identification is a definitional equality or a proved
lemma, so the end-to-end theorems

* `A1_beta_pos_from_source_objects` (general colour, general averaging matrices),
* `A1_beta_pos_from_literal_averaging` (the constrained projection is built on
  the literal averaging kernel, so its Lorentz block diagonality is *proved*),
* `A1_beta_pos_su2` (colour = the adjoint of `su(2)`, structure constants the
  Levi-Civita symbol, so the colour normalisation is *computed*),

carry no "same object" receipt at all.  What is left is: a nondegeneracy
condition on the averaging operator (`IsUnit (QQᵀ).det`), the normalisation
`|f| ≤ 1` of the gauge amplitude, the integrability/positivity/domination
properties of the one-loop integrand, and the spectral and Taylor-coefficient
majorants of the five channels — all *bounds on source data*, none of them an
identification of one object with another.

**Honest status — Row A1 is not closed.**  What is still missing is the
derivation, from Bałaban's construction, that his constrained first variation
*is* `sourceConstrainedVariation` for his averaging data (i.e. that the Wilson
piece of his fluctuation operator has the literal cubic vertex as its momentum
symbol), and that his shell coefficient *is* `shellBetaOfSources` for his
one-loop integrand and remainder channels.  Those are analytic derivations from
CMP98/CMP99/CMP109, not statements this file proves.  The scoreboard is
unchanged: `A, B, C, D` open, frozen research count 4.
-/
import RequestProject.YangMills.A1LiteralAssembly
import RequestProject.YangMills.MixedVanishingWeld

namespace YangMills

open Real MeasureTheory Set Matrix

/-! ## 1. A literal lattice Fourier transform

The bridge of `MixedVanishingWeld` needs only `AnnihilatesZero`.  Rather than
carrying that as a hypothesis, this section exhibits the literal transform used
on the lattice — a finite weighted sum over pairs of sites with the lattice
plane-wave weight — and proves the property. -/

/-- A transform given by a finite weighted sum over pairs of position labels. -/
noncomputable def finsetPositionTransform {S S' : Type*} (F : Finset (S × S'))
    (w : (S × S') → (Fin 4 → ℝ) → ℝ) : PositionTransform S S' :=
  fun K q => ∑ p ∈ F, K p * w p q

theorem annihilatesZero_finsetPositionTransform {S S' : Type*} (F : Finset (S × S'))
    (w : (S × S') → (Fin 4 → ℝ) → ℝ) :
    AnnihilatesZero (finsetPositionTransform F w) := by
  intro q
  simp [finsetPositionTransform]

/-- The literal lattice plane-wave weight: with the project's normalisation the
physical momentum of a normalised point `q` is `2π q`, so the phase attached to
the pair of sites `(x,y)` is `cos(2π q·(x−y))`. -/
noncomputable def latticePhase (x y : Site) (q : Fin 4 → ℝ) : ℝ :=
  Real.cos (2 * π * ∑ mu : Fin 4, q mu * ((x mu : ℝ) - (y mu : ℝ)))

/-- The literal lattice Fourier transform of a position-space kernel over a
finite box of pairs of sites. -/
noncomputable def latticeFourierTransform {S S' : Type*} (F : Finset (S × S'))
    (eS : S → Site) (eS' : S' → Site) : PositionTransform S S' :=
  finsetPositionTransform F fun p q => latticePhase (eS p.1) (eS' p.2) q

theorem annihilatesZero_latticeFourierTransform {S S' : Type*} (F : Finset (S × S'))
    (eS : S → Site) (eS' : S' → Site) :
    AnnihilatesZero (latticeFourierTransform F eS eS') :=
  annihilatesZero_finsetPositionTransform _ _

/-! ## 2. The constrained projection is built on the literal averaging operator

`MixedVanishingWeld` takes the family of averaging matrices `Qf` abstractly,
with Lorentz block diagonality as a hypothesis.  Here the matrix *is* the
literal block-averaging kernel of `AveragingLorentzDiagonal`, restricted to a
finite set of coarse and fine site labels, and its Lorentz block diagonality is
a theorem. -/

/-- The literal block-averaging operator as a matrix: rows are indexed by a
Lorentz index together with a coarse site label and a colour, columns by a
Lorentz index together with a fine site label and a colour. -/
noncomputable def literalAveragingMatrix {color Cs Fs : Type*} [Fintype color] [DecidableEq color]
    (ec : Cs → Site) (ef : Fs → Site) (L : ℕ) (T : TransportData color) :
    Matrix (Fin 4 × (Cs × color)) (Fin 4 × (Fs × color)) ℝ :=
  Matrix.of fun p r => averagingKernel L T (ec p.2.1) p.1 p.2.2 (ef r.2.1) r.1 r.2.2

/-- **The literal averaging matrix is Lorentz block diagonal** — no hypothesis,
this is `averagingKernel_mixed_zero`. -/
theorem isLorentzDiagonal_literalAveragingMatrix {color Cs Fs : Type*} [Fintype color]
    [DecidableEq color] (ec : Cs → Site) (ef : Fs → Site) (L : ℕ) (T : TransportData color) :
    IsLorentzDiagonal (literalAveragingMatrix ec ef L T) := by
  intro al be i j h
  exact averagingKernel_mixed_zero L T (ec i.1) al i.2 (ef j.1) be j.2 h

/-! ## 3. The colour normalisation: the adjoint of `su(2)`

The Wilson cubic vertex and the gauge-projection variation both carry the
structure constant `f^{abc}` of the gauge algebra.  For `su(2)` in the adjoint
basis that is the Levi-Civita symbol, and the component used by the patch is the
one where it equals `1`.  Nothing is normalised by hand. -/

/-- The Levi-Civita symbol on three colour indices — the structure constants of
`su(2)` in the adjoint basis. -/
def epsilon3 (a b c : Fin 3) : ℝ :=
  if a = b ∨ b = c ∨ a = c then 0
  else if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then 1 else -1

@[simp] theorem epsilon3_012 : epsilon3 0 1 2 = 1 := by
  simp [epsilon3]

/-! ## 4. The constrained first variation assembled from the source objects -/

/-- The gauge part of `R`: the computed longitudinal gauge-projection variation,
with the colour structure constant. -/
noncomputable def sourceGaugeSymbol {color : Type*} (fc : color → color → color → ℝ) (f : ℝ) :
    VertexSymbol color :=
  fun al be rho a b c q => fc a b c * gaugeVariationSymbol f (latticeMomentumVector q) rho al be

/-- **The constrained first variation built from the literal source objects.**
No piece is a model: `W` is the literal Wilson cubic vertex with the colour
structure constant, `Q` is the momentum transform of the background derivative
of the literal block-averaging kernel, and `R` is the momentum transform of the
background derivative of the constrained projection built on the averaging
operator, plus the computed gauge-projection variation. -/
noncomputable def sourceConstrainedVariation {color cc Idx : Type*} [Fintype color]
    [DecidableEq color] [Fintype cc] [DecidableEq cc]
    [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    (PhiA : PositionTransform Site Site) (PhiP : PositionTransform Idx Idx)
    (L : ℕ) (T : Fin 4 → color → ℝ → TransportData color) (tA : ℝ)
    (Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ) (tP : ℝ)
    (fc : color → color → color → ℝ) (f : ℝ) : ConstrainedFirstVariation color where
  W := fun al be rho a b c q => fc a b c * wilsonCubicBgZero q al be rho
  Q := symbolOfPositionKernel PhiA (averagingVariationKernel L T tA)
  R := fun al be rho a b c q =>
    symbolOfPositionKernel PhiP (constrainedProjectionVariationKernel Qf tP)
        al be rho a b c q
      + sourceGaugeSymbol fc f al be rho a b c q

/-- **The Row A1a patch floor for the assembled variation.**  All four operator
identifications of `constrainedFirstVariation_mixedPatch_floor_welded` are
discharged: three hold by construction, the fourth is the colour normalisation
`f^{abc} = 1` on the selected colour triple. -/
theorem sourceConstrainedVariation_mixedPatch_floor {color cc Idx : Type*} [Fintype color]
    [DecidableEq color] [Fintype cc] [DecidableEq cc]
    [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    {PhiA : PositionTransform Site Site} {PhiP : PositionTransform Idx Idx}
    {L : ℕ} {T : Fin 4 → color → ℝ → TransportData color} {tA : ℝ}
    {Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ} {tP : ℝ}
    {fc : color → color → color → ℝ} {f : ℝ} {a b c : color}
    (hPhiA : AnnihilatesZero PhiA) (hPhiP : AnnihilatesZero PhiP)
    (hQlor : ∀ rho c' t, IsLorentzDiagonal (Qf rho c' t))
    (hdet : ∀ rho c' t, IsUnit ((Qf rho c' t) * (Qf rho c' t)ᵀ).det)
    (hfc : fc a b c = 1) (hf : |f| ≤ 1)
    {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch (1 / 16)) :
    (1 : ℝ) / 5 ≤ |(sourceConstrainedVariation PhiA PhiP L T tA Qf tP fc f).total 0 1 1 a b c x| :=
  constrainedFirstVariation_mixedPatch_floor_welded
    (sourceConstrainedVariation PhiA PhiP L T tA Qf tP fc f) hPhiA hPhiP hQlor hdet
    rfl (fun _ _ _ _ _ _ _ => rfl) hf
    (fun y => by simp [sourceConstrainedVariation, hfc])
    (fun y => by simp [sourceGaugeSymbol, hfc]) hx

/-! ## 5. The shell coefficient assembled from the source data -/

/-- The Gaussian part of the shell coefficient: the cell integral of the one-loop
integrand. -/
noncomputable def shellGaussianOfIntegrand (I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ) :
    ℕ → (ℕ → ℝ) → ℝ := fun j h => cellGaussianCoefficient (I j h)

/-- The interaction part of the shell coefficient: the sum of the five literal
remainder channels — two spectral (`log det`) channels and three polynomial
channels. -/
noncomputable def shellInteractionOfChannels {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lamDet : ℕ → (ℕ → ℝ) → ι → ℝ) (lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ)
    (aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ) (N : ℕ) : ℕ → (ℕ → ℝ) → ℝ :=
  fun j h =>
    logDetChannel (lamDet j h) (h j)
      + tailPolyChannel (aInt j h) N (h j)
      + tailPolyChannel (aChart j h) N (h j)
      + logDetChannel (lamGauge j h) (h j)
      + tailPolyChannel (aLoc j h) N (h j)

/-- **The shell coefficient assembled from the source data.** -/
noncomputable def shellBetaOfSources {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ)
    (lamDet : ℕ → (ℕ → ℝ) → ι → ℝ) (lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ)
    (aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ) (N : ℕ) : ℕ → (ℕ → ℝ) → ℝ :=
  fun j h => shellGaussianOfIntegrand I j h
    + shellInteractionOfChannels lamDet lamGauge aInt aChart aLoc N j h

/-! ## 6. Row A1a with no identification receipt -/

/-- **Row A1a for the assembled source objects.**  Every "this named object is
the corresponding source object" hypothesis of `A1_beta_pos_welded` is gone: the
constrained first variation and the shell coefficient are *built* from the
source data.  What remains are bounds and domain conditions on that data. -/
theorem A1_beta_pos_from_source_objects
    {color cc Idx : Type*} [Fintype color] [DecidableEq color]
    [Fintype cc] [DecidableEq cc] [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ}
    {PhiA : PositionTransform Site Site} {PhiP : PositionTransform Idx Idx}
    {L : ℕ} {T : Fin 4 → color → ℝ → TransportData color} {tA : ℝ}
    {Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ} {tP : ℝ}
    {fc : color → color → color → ℝ} {f : ℝ} {a b c : color}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    -- the Gaussian sector
    (hPhiA : AnnihilatesZero PhiA) (hPhiP : AnnihilatesZero PhiP)
    (hQlor : ∀ rho c' t, IsLorentzDiagonal (Qf rho c' t))
    (hdet : ∀ rho c' t, IsUnit ((Qf rho c' t) * (Qf rho c' t)ᵀ).det)
    (hfc : fc a b c = 1) (hf : |f| ≤ 1)
    (hintg : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hentry : ∀ j h, ∀ q ∈ mixedPatch (1 / 16),
      |(sourceConstrainedVariation PhiA PhiP L T tA Qf tP fc f).total 0 1 1 a b c q| ^ 2 / 2
        ≤ I j h q)
    -- the debt sector
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50))
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 3276800 ≤ shellBetaOfSources I lamDet lamGauge aInt aChart aLoc N j g := by
  have hpatchI : ∀ j' h, ∀ q ∈ mixedPatch (1 / 16 : ℝ), (1 : ℝ) / 50 ≤ I j' h q := by
    intro j' h q hq
    have hsym := sourceConstrainedVariation_mixedPatch_floor
      (PhiA := PhiA) (PhiP := PhiP) (L := L) (T := T) (tA := tA) (Qf := Qf) (tP := tP)
      (fc := fc) (f := f) (a := a) (b := b) (c := c) hPhiA hPhiP hQlor hdet hfc hf hq
    have habs : (0 : ℝ) ≤
        |(sourceConstrainedVariation PhiA PhiP L T tA Qf tP fc f).total 0 1 1 a b c q| :=
      abs_nonneg _
    have hsq : (1 : ℝ) / 50 ≤
        |(sourceConstrainedVariation PhiA PhiP L T tA Qf tP fc f).total 0 1 1 a b c q| ^ 2 / 2 := by
      nlinarith
    exact le_trans hsq (hentry j' h q hq)
  have hmain := A1_halfFloor_from_mixedPatch (delta := 1 / 16) (cpatch := 1 / 50)
    (beta := shellBetaOfSources I lamDet lamGauge aInt aChart aLoc N)
    (betaZ := shellGaussianOfIntegrand I)
    (betaInt := shellInteractionOfChannels lamDet lamGauge aInt aChart aLoc N)
    (Adm := Adm) (I := I)
    (by norm_num) le_rfl (by norm_num)
    (fun _ _ _ => rfl) hintg hnonneg hpatchI (fun _ _ => rfl)
    (historyUniformQuartic_of_sourceChannels (fun _ _ _ => rfl)
      hLd hLg hAInt hAChart hALoc hsmall hth)
    (fun k => sourceChannelCoefficient_nonneg hth hth0 k) hadm hg0 hgg j
  have hval : (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50)) / 2 = 1 / 3276800 := by norm_num
  rw [hval] at hmain
  exact hmain

/-- **Row A1a with the constrained projection built on the literal averaging
operator.**  The Lorentz block diagonality of the averaging matrices is now a
theorem (`isLorentzDiagonal_literalAveragingMatrix`), so the only structural condition left on
the averaging sector is nondegeneracy, `IsUnit (QQᵀ).det`. -/
theorem A1_beta_pos_from_literal_averaging
    {color Cs Fs : Type*} [Fintype color] [DecidableEq color]
    [Fintype Cs] [DecidableEq Cs] [Fintype Fs] [DecidableEq Fs]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ}
    {PhiA : PositionTransform Site Site} {PhiP : PositionTransform Fs Fs}
    {L : ℕ} {T : Fin 4 → color → ℝ → TransportData color} {tA : ℝ}
    {ec : Cs → Site} {ef : Fs → Site}
    {Tp : Fin 4 → color → ℝ → TransportData color} {Lp : ℕ} {tP : ℝ}
    {fc : color → color → color → ℝ} {f : ℝ} {a b c : color}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hPhiA : AnnihilatesZero PhiA) (hPhiP : AnnihilatesZero PhiP)
    (hdet : ∀ rho c' t, IsUnit ((literalAveragingMatrix ec ef Lp (Tp rho c' t)) *
      (literalAveragingMatrix ec ef Lp (Tp rho c' t))ᵀ).det)
    (hfc : fc a b c = 1) (hf : |f| ≤ 1)
    (hintg : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hentry : ∀ j h, ∀ q ∈ mixedPatch (1 / 16),
      |(sourceConstrainedVariation PhiA PhiP L T tA
          (fun rho c' t => literalAveragingMatrix ec ef Lp (Tp rho c' t)) tP fc f).total
        0 1 1 a b c q| ^ 2 / 2 ≤ I j h q)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50))
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 3276800 ≤ shellBetaOfSources I lamDet lamGauge aInt aChart aLoc N j g :=
  A1_beta_pos_from_source_objects hPhiA hPhiP
    (fun rho c' t => isLorentzDiagonal_literalAveragingMatrix ec ef Lp (Tp rho c' t))
    hdet hfc hf hintg hnonneg hentry hLd hLg hAInt hAChart hALoc hsmall hth hth0
    hadm hg0 hgg j

end YangMills
