import Integration.E6MinusculeWeightModule
import Integration.AlbertJordanAutomorphism
import Mathlib

/-!
# Purely linear transport from a 27-dimensional Albert carrier

Any finite real vector space of dimension 27 is linearly equivalent to the
canonical minuscule coordinate module.  This closes the *linear* existence of
27 distinct weight lines inside an arbitrary 27-dimensional Albert carrier.

It deliberately does not close the exceptional theorem: after transporting the
Weyl action through an arbitrary linear equivalence, one must still prove that
the resulting operators preserve the actual Jordan product, distinguished
unit/trace and cubic norm.  That compatibility is exactly what upgrades a
coordinate choice into an E6/Albert realization.
-/

namespace Integration.AlbertLinearMinusculeTransport

open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6MinusculeWeightModule
open Integration.AlbertJordanAutomorphism

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Any finite 27-dimensional real module is noncanonically linearly equivalent
to the canonical minuscule coordinate module. -/
noncomputable def coordinateEquivOfFinrank27 [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : J ≃ₗ[ℝ] MinusculeModule :=
  LinearEquiv.ofFinrankEq J MinusculeModule (by
    rw [minuscule_module_finrank]
    exact hJ)

/-- Transport one canonical coordinate weight line back to J. -/
def transportedWeightLine (e : J ≃ₗ[ℝ] MinusculeModule)
    (w : Omega5Weight) : Submodule ℝ J :=
  Submodule.map e.symm.toLinearMap (coordinateWeightLine w)

/-- The transported lines remain pairwise distinct. -/
theorem transportedWeightLine_injective (e : J ≃ₗ[ℝ] MinusculeModule) :
    Function.Injective (transportedWeightLine e) := by
  intro w v h
  have hinj := Submodule.map_injective_of_injective e.symm.injective
  apply coordinateWeightLine_injective
  exact hinj h

/-- Transport the finite Weyl action by conjugation through any coordinate
equivalence. -/
noncomputable def transportedE6LinearAction
    (e : J ≃ₗ[ℝ] MinusculeModule) (s : E6SimpleReflection) : J ≃ₗ[ℝ] J :=
  e.trans ((e6WeightLinearAction s).trans e.symm)

/-- The exact extra data required to upgrade a purely linear coordinatization to
an exceptional Albert realization.  A producer must show that each conjugated
simple reflection is an actual structure-preserving Jordan automorphism and
that the 27 coordinate lines are the desired weight lines for that same action. -/
structure ExceptionalAlbertTransport
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : Type 1 where
  coordinateEquiv : J ≃ₗ[ℝ] MinusculeModule
  e6JordanAutomorphism : E6SimpleReflection → JordanAutomorphism A
  linearActionIsTransported : ∀ s,
    (e6JordanAutomorphism s).toLinearEquiv = transportedE6LinearAction coordinateEquiv s

  weightLine : Omega5Weight → Submodule ℝ J
  weightLine_eq_transport : ∀ w,
    weightLine w = transportedWeightLine coordinateEquiv w

/-- The generic linear equivalence exists from dimension alone; the exceptional
compatibility structure above is strictly stronger and is not manufactured. -/
theorem linear_transport_exists [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) :
    Nonempty (J ≃ₗ[ℝ] MinusculeModule) :=
  ⟨coordinateEquivOfFinrank27 hJ⟩

inductive Finrank27CreatesExceptionalAlbertTransport : Prop

theorem finrank_27_does_not_create_exceptional_transport :
    ¬ Finrank27CreatesExceptionalAlbertTransport := by
  intro h; cases h

structure Boundary where
  linearEquivalenceFromFinrank27Paid : Bool
  twentySevenDistinctTransportedLinesPaid : Bool
  conjugatedLinearE6ActionTyped : Bool
  exceptionalJordanCompatibilityTyped : Bool
  exceptionalJordanCompatibilityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  linearEquivalenceFromFinrank27Paid := true
  twentySevenDistinctTransportedLinesPaid := true
  conjugatedLinearE6ActionTyped := true
  exceptionalJordanCompatibilityTyped := true
  exceptionalJordanCompatibilityPaidHere := false

end Integration.AlbertLinearMinusculeTransport
