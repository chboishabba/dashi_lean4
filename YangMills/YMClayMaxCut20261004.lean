import Mathlib
import YangMills.LiteralSU2BoundaryAveragedCrossingRP
import YangMills.CMP119SelectedCrossingAudit
import YangMills.CMP119ResidualReflectionCut
import YangMills.CMP119SelectedSourceInstantiation
import YangMills.CountableObservableDetermining
import YangMills.ProjectiveCylinderOSContinuum
import YangMills.OSGramNullSpace
import YangMills.PreGapOSSemigroup
import YangMills.CMP116DirectClusteringCut
import YangMills.WilsonSpectralCompleteness

/-!
# Yang--Mills Clay max-cut integration board — 2026-10-04

This surface records the sharp theorem/source boundary after the finite Wilson
boundary-projection and bounded-determining-family tranches.

A — finite pure Wilson
----------------------
The boundary-Haar projected literal SU(2) Wilson kernel has now been reduced to
the independently gauged upper/lower boundary-plane finite-feature Gram kernel,
with the lower-orientation mismatch paid by an exact product-Haar coordinate
swap.  The averaged crossing kernel is RP and the positive noncrossing half
weights compile it to the exact projected Wilson OS2 statement.

B — selected complete action
----------------------------
The complete residual Schur-product compiler exists, the constant vacuum sector
is paid, periodic polymer placement is concrete, and any concrete crossing
kernel admits the sharp RP-or-negative-witness audit.  What is NOT supplied is
a source-native selected E/R/B certificate family.  This remains a genuine
proof-or-falsification source stage.

C — CMP119 provenance
---------------------
`CMP119SelectedSourceInstantiation` is the exact same-carrier provenance package
for selected E/R/B component supports/evaluators plus the E/R/B/V literal
residual dictionary.  No inhabitant is manufactured: the upstream source-native
receipt still marks literal complete-density instantiation conditional.

D — bounded determining continuum carrier
-----------------------------------------
Pointwise bounded coordinates already feed the complete D3 projective measure
machinery.  `RealCountableObservableDeterminingSource` adds the exact remaining
measure-determining criterion: the countable coordinate map is a measurable
embedding.  Coordinatewise tanh supplies a bounded injective transform for
otherwise unbounded real observables without paying a moment estimate merely
for first continuum-measure existence.

E1 — cylinder OS positivity
---------------------------
Every bounded-continuous finite-prefix OS Gram inequality passes along the one
simultaneous marginal subsequence to the corresponding continuum marginal.
The remaining E2 work is genuine OS Hilbert completion and translation-semigroup
descent/reconstruction; the algebraic null quotient and contraction/null
preservation are already theorem-bearing.

F1 — CMP116 clustering
----------------------
The weak-limit compiler is theorem-bearing.  The source-facing producer remains
the literal two-physical-J-insertions connected-shell payment identified as
conditional in the current CMP116 source receipt.

F2 — spectral completeness
---------------------------
Once Wilson/cylinder vectors are dense in the reconstructed Hilbert sector,
every nonzero spectral vector is automatically detected by one of them.  Thus
the remaining physical theorem is density/cyclicity, not a separate abstract
detector axiom.
-/

namespace RequestProject.YangMills

/-- Block A: exact terminal finite pure-Wilson boundary-projected OS2 theorem. -/
theorem ym_20261004_block_a_finite_wilson_os2 :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  literal_su2_boundary_gauge_projection_rp_exact

/-- Block B source producer: actual selected complete-residual RP certificates. -/
def YM20261004BlockBResidualReflectionProducerExists
    (ι : Type*) [Fintype ι] : Prop :=
  Nonempty (CMP119ResidualReflectionCut ι)

/-- Every supplied concrete crossing-kernel family has an exhaustive three-sector audit. -/
noncomputable def ym_20261004_block_b_audit_all
    {ι : Type*} [Fintype ι]
    (family : CMP119SelectedCrossingKernelFamily ι) :=
  family.auditAll

/-- Block C exact source provenance producer, deliberately uninhabited locally. -/
def YM20261004BlockCSelectedSourceExists : Prop :=
  CMP119SelectedSourceInstantiation.CMP119SelectedSourceInstantiationExists

/-- Block D exact bounded determining-family producer. -/
def YM20261004BlockDBoundedDeterminingProducerExists
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (observable : ℕ → Ω → ℝ) : Prop :=
  RealCountableObservableDeterminingSource.ProducerExists cutoffLaw observable

/-- D -> measure: a bounded determining source inherits the actual D3 countable law. -/
noncomputable def ym_20261004_bounded_determining_continuum_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω) :
    Measure (ℕ → ℝ) :=
  source.globalCoordinateMeasure

instance ym_20261004_bounded_determining_continuum_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω) :
    MeasureTheory.IsProbabilityMeasure
      (ym_20261004_bounded_determining_continuum_measure source) := by
  unfold ym_20261004_bounded_determining_continuum_measure
  infer_instance

/-- E1: finite-prefix cutoff OS2 compiles to projective continuum cylinder OS positivity. -/
theorem ym_20261004_e1_projective_cylinder_os
    {Ω Test : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (reflectedProduct : ∀ m, Test → Test →
      BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (hcutoff :
      ∀ (m r : ℕ) (tests : Fin r → Test) (coeff : Fin r → ℝ) (k : ℕ),
        0 ≤ ∫ x,
          (∑ i : Fin r, ∑ j : Fin r,
            (coeff i * coeff j) •
              reflectedProduct m (tests i) (tests j)) x
          ∂(((source.family.marginal m (source.diagonal.subsequence k) :
            ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      source reflectedProduct :=
  source.projective_cylinder_os_positive_of_cutoff reflectedProduct hcutoff

/-- F1 exact source producer boundary. -/
def YM20261004F1CMP116DirectClusteringProducerExists
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] : Prop :=
  CMP116DirectClusteringSource.ProducerExists (Ω := Ω) (Obs := Obs)

/-- F2: density/cyclicity implies the required nonzero spectral detection. -/
theorem ym_20261004_f2_detection_of_dense_wilson
    {H Energy : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (wilsonVectors : Set H)
    (hDense : Dense wilsonVectors)
    (spectralVector : Energy → H)
    (energy : Energy)
    (hNonzero : spectralVector energy ≠ 0) :
    ∃ w ∈ wilsonVectors,
      ⟪w, spectralVector energy⟫_ℝ ≠ 0 :=
  dense_wilson_vectors_detect_spectral_sector
    wilsonVectors hDense spectralVector energy hNonzero

end RequestProject.YangMills
