import Integration.RationalAlbertNative
import Integration.RationalAlbertS3Native
import Integration.RationalAlbertCubicNormStructure
import Mathlib

/-!
# Native Albert Hamiltonian and actual S₃ symmetry-breaking witness

This is a theorem about the SAME explicit rational Albert `H₃(O_ℚ)` Jordan
product previously constructed by the owners above, not a generic formal
Albert carrier, a spatial 27-site cube Laplacian, or a Monster VOA product.

If `L_h(x)=h∘x` commutes with a unit-preserving action, then `h` is fixed,
because `L_h(1)=h`. On the native selected `h=diag(1,0,-1)`, the actual
order-three Albert automorphism `cycleA` does not fix `h`, so `L_h`
does NOT commute with that symmetry.

This is precisely the same-object obstruction underlying the local-Python
27-dimensional Jordan spectral check; it is not a physical Hamiltonian or
a proof about the exceptional 3³ fine grading of Griess (1990).

Attribution: classical Albert/Jordan algebra; repository's prior native
product/unit proof and native S₃ automorphism proof remain the owners.
-/

namespace Integration.RationalAlbertJordanHamiltonianSymmetry

open Integration.RationalAlbertNative
open Integration.RationalAlbertNative.RationalAlbert
open Integration.RationalAlbertS3Native

abbrev A := Integration.RationalAlbertNative.RationalAlbert

/-- Actual native rational Albert Jordan left-multiplication operator. -/
def leftJordan (h x : A) : A := jordanProduct h x

/-- Consequence of the previously established native Jordan unit law. -/
theorem leftJordan_unit (h : A) : leftJordan h unit = h := by
  exact jordan_unit_right h

/-- Evaluating an operator commutator at the same algebraic identity
forces the Hamiltonian generator itself to be symmetry-fixed. -/
theorem commutation_forces_fixed_generator
    (f : A → A) (h : A)
    (hf : f unit = unit)
    (hcomm : ∀ x : A, f (leftJordan h x) = leftJordan h (f x)) :
    f h = h := by
  calc
    f h = f (leftJordan h unit) := by rw [leftJordan_unit]
    _ = leftJordan h (f unit) := hcomm unit
    _ = leftJordan h unit := by rw [hf]
    _ = h := leftJordan_unit h

/-- This native element is the same diagonal Jordan Hamiltonian parameter
used by the independent exact octonionic Python spectral computation. -/
def selectedH : A := ⟨1, 0, -1, 0, 0, 0⟩

theorem selectedH_trace_zero : trace selectedH = 0 := by
  norm_num [selectedH, trace]

/-- Jordan left multiplication sends the scalar identity to a nonzero
traceless state. This is a concrete scalar/traceless mixing witness. -/
theorem selectedH_unit_image : leftJordan selectedH unit = selectedH :=
  leftJordan_unit _

theorem selectedH_nonzero : selectedH ≠ (0 : A) := by
  intro heq
  have h0 := congrArg (fun x : A => x.diagonal0) heq
  norm_num [selectedH] at h0


/-- Nonzero native rational-Albert trace-pair amplitude. This is a
Jordan algebra matrix element, not a calibrated physical transition. -/
theorem selectedH_tracePair_norm :
    Integration.RationalAlbertCubicNormStructure.tracePair selectedH selectedH = 2 := by
  norm_num [Integration.RationalAlbertCubicNormStructure.tracePair,
    selectedH, innerO, RationalOctonion.mul, RationalOctonion.conj,
    RationalOctonion.realPart, RationalQuaternion.mul,
    RationalQuaternion.conj]

/-- Concrete scalar-to-traceless coupling of the source-native
Jordan Hamiltonian, measured by the source-native trace form. -/
theorem selectedH_scalar_traceless_amplitude :
    Integration.RationalAlbertCubicNormStructure.tracePair
      (leftJordan selectedH unit) selectedH = 2 := by
  rw [selectedH_unit_image]
  exact selectedH_tracePair_norm

/-- The *existing genuine* order-three Albert automorphism changes the
selected Hamiltonian generator. -/
theorem cycle_does_not_fix_selectedH :
    cycleA selectedH ≠ selectedH := by
  intro heq
  have h0 := congrArg (fun x : A => x.diagonal0) heq
  norm_num [selectedH, cycleA] at h0

/-- An explicit same-product, same-automorphism, noncommuting Hamiltonian.
It does not require assigning the 27 balanced-cube sites to Albert vectors. -/
theorem selectedH_does_not_commute_with_cycle :
    ¬ (∀ x : A,
       cycleA (leftJordan selectedH x) =
         leftJordan selectedH (cycleA x)) := by
  intro hcomm
  exact cycle_does_not_fix_selectedH
    (commutation_forces_fixed_generator cycleA selectedH
      (cycle_unit) hcomm)

/-- The converse direction uses source-proved multiplication equivariance:
if a product automorphism fixes h, its left operator commutes. -/
theorem fixed_generator_implies_commutation
    (f : A → A)
    (h : A)
    (hproduct : ∀ x y : A,
      f (jordanProduct x y) = jordanProduct (f x) (f y))
    (hfixed : f h = h) :
    ∀ x : A, f (leftJordan h x) = leftJordan h (f x) := by
  intro x
  calc
    f (leftJordan h x) = jordanProduct (f h) (f x) := hproduct h x
    _ = leftJordan h (f x) := by rw [hfixed]; rfl

/-- Exact operator criterion for the original Lean-owned cyclic S₃ actor. -/
theorem cycle_commutes_iff_fixed (h : A) :
    (∀ x : A, cycleA (leftJordan h x) = leftJordan h (cycleA x)) ↔
      cycleA h = h := by
  constructor
  · intro hc
    exact commutation_forces_fixed_generator cycleA h cycle_unit hc
  · intro hf
    exact fixed_generator_implies_commutation cycleA h
      cycle_preserves_product hf

end Integration.RationalAlbertJordanHamiltonianSymmetry
