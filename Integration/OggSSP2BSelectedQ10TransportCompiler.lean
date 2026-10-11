import Integration.OggSSP2BFinalSameObjectCompiler
import Integration.ThreeC2TateFibreFromLinearGroupConjugacy

/-!
# Compile selected Q10 transport from linear refinements of the Tate fibre cycle

The generic three-fibre Tate compiler intentionally stores the source maps as
additive equivalences.  That is enough for Hhat representative transport, but
transporting an F2-linear subquotient requires the sourced maps to be linear.

For a genuine linear Monster/module representation that scalar structure is
not an extra hypothesis.  This owner therefore has two layers:

1. `fromLinearGroupSource` converts one actual linear group representation plus
   the order-three conjugacy relations directly into the full additive Tate
   cycle and matching linear fibre maps;
2. `compileSelectedTransport` canonically pulls a selected Q10 quotient through
   those maps.

No separate selected-Q fibre maps need to be invented.
-/

namespace Integration.OggSSP2BSelectedQ10TransportCompiler

namespace F := Integration.OggSSP2BFinalSameObjectCompiler
namespace R := Integration.OggSSP2BRevisedCompletionRecognition
namespace G := Integration.ThreeC2TateFibreFromLinearGroupConjugacy

abbrev Scalar := F.Scalar
abbrev ActualTate276 := F.ActualTate276

/-- Linear refinements of the three sourced additive fibre equivalences. -/
structure LinearThreeFibreTransportReceipt
    (full : F.ActualThreeFibreTateTransportReceipt) where
  phi01 : ActualTate276 ≃ₗ[Scalar] ActualTate276
  phi12 : ActualTate276 ≃ₗ[Scalar] ActualTate276
  phi20 : ActualTate276 ≃ₗ[Scalar] ActualTate276
  phi01_agrees : ∀ x, full.cycle.phi01 x = phi01 x
  phi12_agrees : ∀ x, full.cycle.phi12 x = phi12 x
  phi20_agrees : ∀ x, full.cycle.phi20 x = phi20 x
  sourceProvenance : String

/-- The dependent pair produced from one source-native linear group action. -/
structure CompiledLinearTransport where
  full : F.ActualThreeFibreTateTransportReceipt
  linear : LinearThreeFibreTransportReceipt full

/-- A genuine linear group representation pays both the additive Tate cycle and
its F2-linear refinements in one compiler call. -/
def fromLinearGroupSource
    {Γ : Type*} [Group Γ]
    (ρ : Γ →* (ActualTate276 ≃ₗ[Scalar] ActualTate276))
    (s : G.OrderThreeLinearConjugacyCycleSource ρ)
    (sourceProvenance : String) : CompiledLinearTransport := by
  let d := s.toLinearThreeFibreCycleData ρ
  let full : F.ActualThreeFibreTateTransportReceipt :=
    { cycle := d.additiveCycle
      sourceProvenance := sourceProvenance }
  refine
    { full := full
      linear := ?_ }
  exact
    { phi01 := d.phi01Linear
      phi12 := d.phi12Linear
      phi20 := d.phi20Linear
      phi01_agrees := d.phi01_agrees
      phi12_agrees := d.phi12_agrees
      phi20_agrees := d.phi20_agrees
      sourceProvenance := sourceProvenance }

namespace LinearThreeFibreTransportReceipt

variable {Q : Type*} [AddCommGroup Q] [Module Scalar Q]
variable {recognition : R.ActualTateCompletionTenRecognition Q}
variable {full : F.ActualThreeFibreTateTransportReceipt}

/-- Transported source in fibre 1, expressed so membership is literally
membership of the inverse image in the fibre-0 source. -/
def source1
    (t : LinearThreeFibreTransportReceipt full) :
    Submodule Scalar ActualTate276 :=
  recognition.subquotient.sourceSubmodule.comap t.phi01.symm.toLinearMap

/-- Transported source in fibre 2. -/
def source2
    (t : LinearThreeFibreTransportReceipt full) :
    Submodule Scalar ActualTate276 :=
  (t.source1 (recognition := recognition)).comap t.phi12.symm.toLinearMap

/-- Quotient in fibre 1 by pulling a representative back through phi01. -/
def quotient1
    (t : LinearThreeFibreTransportReceipt full) :
    t.source1 (recognition := recognition) →ₗ[Scalar] Q where
  toFun x := recognition.subquotient.quotient
    ⟨t.phi01.symm x.1, x.2⟩
  map_add' x y := by simp [source1]
  map_smul' c x := by simp [source1]

/-- Quotient in fibre 2 by pulling through phi12 and then phi01. -/
def quotient2
    (t : LinearThreeFibreTransportReceipt full) :
    t.source2 (recognition := recognition) →ₗ[Scalar] Q where
  toFun x := t.quotient1 (recognition := recognition)
    ⟨t.phi12.symm x.1, x.2⟩
  map_add' x y := by simp [source2, quotient1, source1]
  map_smul' c x := by simp [source2, quotient1, source1]

/-- Fibre-1 quotient is surjective because phi01 is an equivalence. -/
theorem quotient1_surjective
    (t : LinearThreeFibreTransportReceipt full) :
    Function.Surjective (t.quotient1 (recognition := recognition)) := by
  intro q
  obtain ⟨x, hx⟩ := recognition.subquotient.quotient_surjective q
  let y0 : ActualTate276 := t.phi01 x.1
  have hy0 : y0 ∈ t.source1 (recognition := recognition) := by
    change t.phi01.symm y0 ∈ recognition.subquotient.sourceSubmodule
    simpa [y0] using x.2
  refine ⟨⟨y0, hy0⟩, ?_⟩
  change recognition.subquotient.quotient
      ⟨t.phi01.symm y0, hy0⟩ = q
  simpa [y0] using hx

/-- Fibre-2 quotient is likewise surjective. -/
theorem quotient2_surjective
    (t : LinearThreeFibreTransportReceipt full) :
    Function.Surjective (t.quotient2 (recognition := recognition)) := by
  intro q
  obtain ⟨x1, hx1⟩ := t.quotient1_surjective (recognition := recognition) q
  let y0 : ActualTate276 := t.phi12 x1.1
  have hy0 : y0 ∈ t.source2 (recognition := recognition) := by
    change t.phi12.symm y0 ∈ t.source1 (recognition := recognition)
    simpa [y0] using x1.2
  refine ⟨⟨y0, hy0⟩, ?_⟩
  change t.quotient1 (recognition := recognition)
      ⟨t.phi12.symm y0, hy0⟩ = q
  simpa [y0] using hx1

/-- The third full-fibre map returns the inverse-pullback representative used by
our transported coordinates. -/
theorem phi20_eq_inverse_pullback
    (t : LinearThreeFibreTransportReceipt full)
    (x : ActualTate276) :
    full.cycle.phi20 x = t.phi01.symm (t.phi12.symm x) := by
  let y := t.phi01.symm (t.phi12.symm x)
  have hc := full.cycle.cycleCoherent y
  rw [t.phi01_agrees, t.phi12_agrees] at hc
  simpa [y] using hc

/-- The selected quotient transport is completely generated from the linear
fibre refinements.  In transported quotient coordinates each qPhi is identity. -/
noncomputable def compileSelectedTransport
    (t : LinearThreeFibreTransportReceipt full) :
    F.SelectedQ10TransportReceipt Q recognition full where
  source1 := t.source1 (recognition := recognition)
  source2 := t.source2 (recognition := recognition)
  quotient1 := t.quotient1 (recognition := recognition)
  quotient2 := t.quotient2 (recognition := recognition)
  quotient1_surjective := t.quotient1_surjective (recognition := recognition)
  quotient2_surjective := t.quotient2_surjective (recognition := recognition)
  source0_to1 := by
    intro x
    change t.phi01.symm (full.cycle.phi01 x.1) ∈
      recognition.subquotient.sourceSubmodule
    rw [t.phi01_agrees]
    simpa using x.2
  source1_to2 := by
    intro x
    change t.phi12.symm (full.cycle.phi12 x.1) ∈
      t.source1 (recognition := recognition)
    rw [t.phi12_agrees]
    simpa using x.2
  source2_to0 := by
    intro x
    have hx : t.phi01.symm (t.phi12.symm x.1) ∈
        recognition.subquotient.sourceSubmodule := x.2
    rw [t.phi20_eq_inverse_pullback x.1]
    exact hx
  qPhi01 := LinearEquiv.refl Scalar Q
  qPhi12 := LinearEquiv.refl Scalar Q
  qPhi20 := LinearEquiv.refl Scalar Q
  quotient_natural_01 := by
    intro x
    change recognition.subquotient.quotient x =
      recognition.subquotient.quotient
        ⟨t.phi01.symm (full.cycle.phi01 x.1), _⟩
    rw [t.phi01_agrees]
    simp
  quotient_natural_12 := by
    intro x
    change t.quotient1 (recognition := recognition) x =
      t.quotient1 (recognition := recognition)
        ⟨t.phi12.symm (full.cycle.phi12 x.1), _⟩
    rw [t.phi12_agrees]
    simp
  quotient_natural_20 := by
    intro x
    change t.quotient2 (recognition := recognition) x =
      recognition.subquotient.quotient
        ⟨full.cycle.phi20 x.1, _⟩
    rw [t.phi20_eq_inverse_pullback x.1]
    rfl
  quotient_cycle_coherent := by
    intro q
    rfl

end LinearThreeFibreTransportReceipt

end Integration.OggSSP2BSelectedQ10TransportCompiler
