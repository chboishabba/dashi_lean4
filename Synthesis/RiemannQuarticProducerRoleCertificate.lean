import Synthesis.RiemannQuarticBalancedTernaryStencil

/-!
# Source-native RH primitive-row producer-role certificate

This module lives on the RH analytic branch itself.  Unlike the cross-branch
manifest, it can name the actual analytic coordinate terms and prove that the
role-indexed coefficient table reconstructs the already-owned primitive kernel.

The four producer roles are:
* pole   -> quarticFourAtomicHighPoleResidual
* origin -> quarticFourAtomicProjectiveOriginCoordinate
* j      -> quarticFourAtomicJAt ... 2
* target -> quarticFourAtomicTargetStrengthAt

with coefficients 80,243,1215,972.

This is the same-object role authority needed by the SSP15 filtered-provenance
consumer.  It does not assign SSP semantics to these roles.
-/

namespace Synthesis

namespace RiemannQuarticProducerRoleCertificate

inductive ProducerRole
  | pole
  | origin
  | j
  | target
  deriving DecidableEq, Repr, Fintype

def coefficient : ProducerRole → Nat
  | .pole => 80
  | .origin => 243
  | .j => 1215
  | .target => 972

def coordinateValue : ProducerRole → ℝ → ℝ → ℝ
  | .pole => quarticFourAtomicHighPoleResidual
  | .origin => quarticFourAtomicProjectiveOriginCoordinate
  | .j => fun lam mu => quarticFourAtomicJAt lam mu 2
  | .target => quarticFourAtomicTargetStrengthAt

def piWeight : ProducerRole → ℝ
  | .pole => Real.pi^4
  | .origin => Real.pi^4
  | .j => Real.pi^2
  | .target => 1

def weightedCoordinate
    (role : ProducerRole) (lam mu : ℝ) : ℝ :=
  coefficient role * piWeight role * coordinateValue role lam mu

theorem pole_coefficient_exact : coefficient .pole = 80 := rfl
theorem origin_coefficient_exact : coefficient .origin = 243 := rfl
theorem j_coefficient_exact : coefficient .j = 1215 := rfl
theorem target_coefficient_exact : coefficient .target = 972 := rfl

theorem pole_coordinate_same_object
    (lam mu : ℝ) :
    coordinateValue .pole lam mu
      = quarticFourAtomicHighPoleResidual lam mu := rfl

theorem origin_coordinate_same_object
    (lam mu : ℝ) :
    coordinateValue .origin lam mu
      = quarticFourAtomicProjectiveOriginCoordinate lam mu := rfl

theorem j_coordinate_same_object
    (lam mu : ℝ) :
    coordinateValue .j lam mu
      = quarticFourAtomicJAt lam mu 2 := rfl

theorem target_coordinate_same_object
    (lam mu : ℝ) :
    coordinateValue .target lam mu
      = quarticFourAtomicTargetStrengthAt lam mu := rfl

theorem primitive_kernel_via_source_roles
    (lam mu : ℝ) :
    weightedCoordinate .pole lam mu
      + weightedCoordinate .origin lam mu
      + weightedCoordinate .j lam mu
      + weightedCoordinate .target lam mu
      = 0 := by
  simpa [weightedCoordinate, coefficient, piWeight, coordinateValue]
    using
      RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_primitive_integer_kernel
        lam mu

theorem depth_five_source_roles_exact :
    coefficient .origin = 3^5 * 1 ∧
    coefficient .j = 3^5 * 5 ∧
    coefficient .target = 3^5 * 4 := by
  norm_num [coefficient]

theorem pole_is_mod_three_unit :
    coefficient .pole % 3 = 2 := by
  native_decide

structure SourceNativeProducerRoleCertificate where
  role : ProducerRole → ProducerRole
  role_is_identity : ∀ r, role r = r
  coefficientOf : ProducerRole → Nat
  coefficient_is_source : coefficientOf = coefficient
  coordinateAt : ProducerRole → ℝ → ℝ → ℝ
  coordinate_is_source : coordinateAt = coordinateValue
  primitiveKernel :
    ∀ lam mu,
      coefficientOf .pole * Real.pi^4 * coordinateAt .pole lam mu
      + coefficientOf .origin * Real.pi^4 * coordinateAt .origin lam mu
      + coefficientOf .j * Real.pi^2 * coordinateAt .j lam mu
      + coefficientOf .target * coordinateAt .target lam mu
      = 0

def canonicalSourceNativeProducerRoleCertificate :
    SourceNativeProducerRoleCertificate where
  role := id
  role_is_identity := by intro r; rfl
  coefficientOf := coefficient
  coefficient_is_source := rfl
  coordinateAt := coordinateValue
  coordinate_is_source := rfl
  primitiveKernel := by
    intro lam mu
    simpa [coefficient, coordinateValue]
      using
        RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_primitive_integer_kernel
          lam mu

theorem canonical_certificate_inhabited :
    Nonempty SourceNativeProducerRoleCertificate :=
  ⟨canonicalSourceNativeProducerRoleCertificate⟩

structure Boundary where
  sourceNativeFourRolesOwned : Bool
  sourceNativeCoefficientTableOwned : Bool
  sourceNativeCoordinateTermsOwned : Bool
  primitiveKernelReconstructedFromRoles : Bool
  depthFiveSourceRoleBlockOwned : Bool
  sspSemanticIdentityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sourceNativeFourRolesOwned := true
  sourceNativeCoefficientTableOwned := true
  sourceNativeCoordinateTermsOwned := true
  primitiveKernelReconstructedFromRoles := true
  depthFiveSourceRoleBlockOwned := true
  sspSemanticIdentityClaimed := false

end RiemannQuarticProducerRoleCertificate

end Synthesis
