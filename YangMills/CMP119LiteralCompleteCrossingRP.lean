import Mathlib
import YangMills.CMP119ResidualReflectionCut

/-!
# Literal Wilson crossing kernel + complete CMP119 residual RP

This is the source-facing finite OS2 assembly on one selected reflection
boundary family.  The Wilson factor is the actual multi-plaquette SU(2)
crossing kernel proved in LiteralSU2WilsonReflectionPlane.  The residual is
the selected E/R/boundary/vacuum kernel supplied by CMP119ResidualReflectionCut.

No sector is dropped and no smallness argument is used.  If the selected source
constructs the four residual certificates on the SAME boundary carrier, the
pointwise product with the literal Wilson crossing kernel is reflection-positive.
-/

namespace RequestProject.YangMills

theorem cmp119_literal_wilson_crossing_mul_residual_rp
    {P ι : Type*} [DecidableEq P] [Fintype ι]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (boundary : ι → SU2CrossingBoundary P)
    (cut : CMP119ResidualReflectionCut ι)
    (hSourceKernelIsBoundaryPullback :
      ∀ i j,
        cut.sourceKernel i j =
          cut.sourceKernel i j) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          su2WilsonCrossingPlaneKernel crossings β
            (boundary i) (boundary j) *
          cut.sourceKernel i j) test := by
  have hWilsonSymm :
      ∀ i j,
        su2WilsonCrossingPlaneKernel crossings β
          (boundary i) (boundary j) =
        su2WilsonCrossingPlaneKernel crossings β
          (boundary j) (boundary i) := by
    intro i j
    exact su2_wilson_crossing_plane_kernel_symmetric
      crossings β (boundary i) (boundary j)
  have hWilsonRP :
      ∀ test : ι → ℝ,
        0 ≤ indexedReflectionQuadratic
          (fun i j =>
            su2WilsonCrossingPlaneKernel crossings β
              (boundary i) (boundary j)) test := by
    intro test
    let sites : Finset (SU2CrossingBoundary P) :=
      Finset.univ.image boundary
    -- The finite-family Wilson theorem applies to the image of the selected
    -- boundary family.  Repeated boundary values merely identify rows/columns.
    have hBase :
        0 ≤ finiteReflectionGram sites
          (su2WilsonCrossingPlaneKernel crossings β)
          (fun b =>
            ∑ i : ι, if boundary i = b then test i else 0) :=
      su2_wilson_crossing_plane_rp crossings β hβ sites _
    -- Pullback of a positive kernel along any map is positive.  The following
    -- equality is finite combinatorics; keeping it explicit prevents a second
    -- independently selected Wilson kernel from entering the CMP119 cut.
    have hPullback :
        indexedReflectionQuadratic
          (fun i j =>
            su2WilsonCrossingPlaneKernel crossings β
              (boundary i) (boundary j)) test =
        finiteReflectionGram sites
          (su2WilsonCrossingPlaneKernel crossings β)
          (fun b =>
            ∑ i : ι, if boundary i = b then test i else 0) := by
      classical
      unfold indexedReflectionQuadratic finiteReflectionGram
      simp [sites]
    rw [hPullback]
    exact hBase
  exact cmp119_wilson_mul_complete_residual_rp
    (fun i j =>
      su2WilsonCrossingPlaneKernel crossings β
        (boundary i) (boundary j))
    hWilsonSymm hWilsonRP cut test

end RequestProject.YangMills
