import Mathlib
import YangMills.LiteralSU2HalfIndexBijection
import YangMills.LiteralSU2WilsonOSFactorization
import YangMills.CMP119ResidualReflectionCut
import YangMills.CMP119LiteralCompleteCrossingRP
import YangMills.CMP119LiteralDyadicResidualWeld
import YangMills.CMP119NativeDyadicMomentBound

/-!
# YM max-cut frontier, 2026-10-02

This owner records the shortest source-facing cut after the literal finite
Wilson geometry was completed.

What is now theorem-bearing on the literal finite SU(2) carrier:

* the even-time plaquette-index reflection sends P+ exactly onto P-;
* therefore the negative noncrossing Wilson half is exactly the reflected
  positive half;
* the full literal Wilson density has the positive-half / reflected-half /
  crossing-kernel factorization;
* CMP119's vacuum contribution, when identified with the source-native
  configuration-independent vacuum constant, is a reflected-half rank-one
  factor and is not an independent cross-plane RP leaf;
* consequently complete residual RP needs only physical certificates for the
  regular E, R-operation, and boundary B sectors;
* the dyadic residual and native moment-transfer theorems remain available
  downstream once the actual source weld and Wilson moment estimate are paid.

This file deliberately does NOT manufacture any of the remaining physical
inputs.  In particular it does not claim:

* native quaternion link-Haar OS2 integration has been completed;
* E, R-operation, or B has a reflected-half/PSD cross-plane certificate;
* the selected CMP119 localized R(X) expansion has been identified with the
  literal residual tail;
* a cutoff-uniform scale-sensitive Wilson coercive moment estimate has been
  proved.

Those are the surviving max-cut leaves.
-/

namespace RequestProject.YangMills

/--
The global finite Wilson half-action identity is no longer a hypothesis.
It is an immediate consumer alias of the literal plaquette-index bijection.
-/
theorem ym_maxcut_literal_wilson_half_closed
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n))
    (β : ℝ) :
    su2LiteralWilsonProduct
        (su2EvenTimePositivePlaquettes n)
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2EvenTimeNegativePlaquettes n)
        links β :=
  su2_negative_half_eq_reflected_positive_half n links β

/--
The source-native constant vacuum factor is a reflected-half factor, not an
independent cross-plane positivity obligation.
-/
theorem ym_maxcut_constant_vacuum_is_reflected_half
    {ι : Type*} [Fintype ι]
    (vacuumEnergy : ℝ) :
    (cmp119ConstantVacuumCertificate
      (ι := ι) vacuumEnergy).placement =
      CMP119ReflectionPlacement.reflectedHalf := by
  rfl

/--
After paying the constant-vacuum source identification, only the three
nontrivial residual sectors E, R_op, and B need reflection certificates.

This theorem packages those three certificates with the exact constant
vacuum kernel and proves RP of their product.  It is intentionally agnostic
about whether each supplied certificate is a half-factor or a genuine
cross-plane PSD kernel.
-/
theorem ym_maxcut_three_sector_residual_rp
    {ι : Type*} [Fintype ι]
    (regularCert rCert boundaryCert :
      CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          regularCert.kernel i j *
          rCert.kernel i j *
          boundaryCert.kernel i j *
          Real.exp (-vacuumEnergy))
        test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j *
        rCert.kernel i j *
        boundaryCert.kernel i j *
        Real.exp (-vacuumEnergy))
      rfl
  intro test
  exact cmp119_complete_residual_kernel_rp cut test

/--
Wilson crossing RP plus the three selected residual certificates and the
constant vacuum factor imply RP of the complete finite crossing kernel.

Thus failure to source a certificate for any one of E, R_op, or B is now a
literal obstruction to this CMP119 -> OS route; V is not a fourth open leaf.
-/
theorem ym_maxcut_wilson_three_sector_complete_rp
    {ι : Type*} [Fintype ι]
    (wilsonKernel : ι → ι → ℝ)
    (hWilsonSymm : ∀ i j, wilsonKernel i j = wilsonKernel j i)
    (hWilsonRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic wilsonKernel test)
    (regularCert rCert boundaryCert :
      CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          wilsonKernel i j *
          (regularCert.kernel i j *
            rCert.kernel i j *
            boundaryCert.kernel i j *
            Real.exp (-vacuumEnergy)))
        test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j *
        rCert.kernel i j *
        boundaryCert.kernel i j *
        Real.exp (-vacuumEnergy))
      rfl
  simpa only [mul_assoc] using
    (cmp119_wilson_mul_complete_residual_rp
      wilsonKernel hWilsonSymm hWilsonRP cut)

/--
Literal specialization: the Wilson factor is no longer an input.  The existing
multi-plaquette SU(2) crossing theorem supplies it on the SAME selected
boundary map, while the constant vacuum is paid by the rank-one half factor.

The only source-facing RP inputs are therefore certificates for E, R_op and B.
-/
theorem ym_maxcut_literal_wilson_three_sector_complete_rp
    {P ι : Type*} [DecidableEq P] [Fintype ι]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (boundary : ι → SU2CrossingBoundary P)
    (regularCert rCert boundaryCert :
      CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          su2WilsonCrossingPlaneKernel crossings β
            (boundary i) (boundary j) *
          (regularCert.kernel i j *
            rCert.kernel i j *
            boundaryCert.kernel i j *
            Real.exp (-vacuumEnergy)))
        test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j *
        rCert.kernel i j *
        boundaryCert.kernel i j *
        Real.exp (-vacuumEnergy))
      rfl
  exact cmp119_literal_wilson_crossing_mul_residual_rp
    crossings β hβ boundary cut


/--
The current source-facing complete-action RP cut has exactly three residual
certificate leaves after the constant-vacuum identification.
-/
def ymMaxCutResidualCertificateLeaves : Finset CMP119ResidualSector :=
  { CMP119ResidualSector.regularE
  , CMP119ResidualSector.rOperation
  , CMP119ResidualSector.boundaryB }

theorem ym_maxcut_vacuum_not_in_residual_certificate_leaves :
    CMP119ResidualSector.vacuumV ∉ ymMaxCutResidualCertificateLeaves := by
  simp [ymMaxCutResidualCertificateLeaves]

end RequestProject.YangMills
