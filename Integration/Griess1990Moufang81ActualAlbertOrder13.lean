import Integration.Griess1990Moufang81Explicit13Cycle
import Integration.Griess1990OriginalHomogeneousFormula
import Integration.Griess1990RationalTrialityFiniteProduct
import Integration.RationalAlbertNative
import Mathlib

/-!
# The same corrected Griess order-13 word acts on the ACTUAL Albert product

ORIGINAL OWNER: R. L. Griess Jr. (1990), J. Algebra 131, 281-293,
DOI 10.1016/0021-8693(90)90176-O: g-phase multiplication on
A=(F3)^3, tau-real Albert structure, and Moufang automorphism context.

Reuse (do not vendor another Albert algebra):
  Griess1990Moufang81Explicit13Cycle.shortOrder13Lift
  Griess1990OriginalHomogeneousFormula.modeGrade/modeCoefficient
  Griess1990RationalTrialityFiniteProduct.sourceTensor/toNative
  Griess1990RationalTrialityMatrixWitness.sourceToNative/nativeToSource
  RationalAlbertNative.RationalAlbert.jordanProduct

The source-graded operation sends e_x -> omega^h(x) e_(M x).
This restricts to the original Q-rational tau-real 27D carrier and
is a SOURCE PRODUCT AUTOMORPHISM, not just a permutation of 27 grade
labels. Conjugating through the already independently checked
rational 27x27 source-to-native matrix gives the SAME native H3(O_Q)
Jordan automorphism. Local exact SymPy source-equivalent check PASS:
729 source products + 729 literal native Cayley-Dickson Jordan products,
unit and trace Gram, order13; characteristic polynomial
(X-1)^3 * Phi13(X)^2, trace(A^k)=1 for all 1<=k<=12.

Unlike W(E8), the Q-Albert automorphism group can contain elements of
order 13. This is not a theorem identifying the full rational F4 group,
a selected Monster 3B VOA, nor a physical Hamiltonian.

Source-written finite Lean proof statements below have NOT been
typechecked or kernel executed. The huge 729 basis-product and source
formula-to-table payments must compile before promoting the claim
to a Lean proof.
-/

namespace Integration.Griess1990Moufang81ActualAlbertOrder13

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81Explicit13Cycle
open Integration.Griess1990OriginalHomogeneousFormula
open Integration.Griess1990RationalTrialityMatrixWitness
open Integration.Griess1990RationalTrialityFiniteProduct

/-- Original lexicographic F3^3 grade (0..26) as a true function. -/
def gradeOf (a : Fin 27) : Grade :=
  ![(a.val / 9 : ZMod 3),
    (a.val / 3 % 3 : ZMod 3),
    (a.val % 3 : ZMod 3)]

/-- Inverse grade encoding; values are the canonical 0,1,2 representatives. -/
def indexOf (a : Grade) : Fin 27 :=
  Fin.ofNat 27 (9 * (a 0).val + 3 * (a 1).val + (a 2).val)

/-- Actual original Moufang automorphism applied to the *grade*
and central scalar phase of a homogeneous Albert basis vector. -/
def gradedSourceImage (a : Fin 27) : Loop81 :=
  shortOrder13Lift ⟨gradeOf a, 0⟩

/-- Source τ-real basis vectors have at most two nonzero homogeneous
components. Apply original grade permutation AND the required
cyclotomic central phase to both of those components. -/
def transformedCoefficientAt (i a : Fin 27) : Cyclo :=
  ∑ t : Fin 2,
    if indexOf (gradedSourceImage (modeGrade i t)).grade = a then
      cycloMul
        (phasePower (gradedSourceImage (modeGrade i t)).central.val)
        (modeCoefficient i t)
    else zeroC

/-- The ORIGINAL rational 27x27 matrix of the source order-13 word.
A coefficient (p,q) means p+q*omega on the antipodal representative. -/
def sourceOrder13Matrix : Matrix (Fin 27) (Fin 27) ℚ :=
  fun k i =>
    if k = 0 then
      (transformedCoefficientAt i 0).1
    else
      let a := antipodalRepresentative (Fin.ofNat 13 ((k.val - 1) / 2))
      let coeff := transformedCoefficientAt i (Fin.ofNat 27 a.val)
      if (k.val - 1) % 2 = 0 then coeff.1 else coeff.2

theorem source_order_thirteen_matrix :
    sourceOrder13Matrix ^ 13 = 1 := by
  native_decide

theorem source_order_thirteen_unit :
    applyWitness sourceOrder13Matrix sourceOne = sourceOne := by
  native_decide

theorem source_order_thirteen_trace_gram :
    sourceOrder13Matrix.transpose * sourceTraceGram *
      sourceOrder13Matrix = sourceTraceGram := by
  native_decide

/-- Characteristic polynomial is (X-1)^3 Phi13(X)^2;
the much cheaper fingerprint is exact trace one for each of 12
nonidentity powers, plus S^13=1. -/
theorem source_nonidentity_power_trace_one :
    ∀ k : Fin 12,
      Matrix.trace (sourceOrder13Matrix ^ (k.val + 1)) = (1 : ℚ) := by
  native_decide

/-- Real source-specific 729 products, using the original published
homogeneous formula's independently materialized tau-real tensor. -/
theorem source_order_thirteen_all_products :
    ∀ i j k : Fin 27,
      (∑ a : Fin 27,
        sourceOrder13Matrix k a * sourceTensor i j a) =
      (∑ b : Fin 27, ∑ c : Fin 27,
        sourceOrder13Matrix b i * sourceOrder13Matrix c j *
          sourceTensor b c k) := by
  native_decide

/-- Literally the SAME native rational octonionic Albert, obtained from
the existing rational 27x27 Peirce related triple, not by redefining a
new 27-dimensional cubic carrier. -/
def nativeOrder13Matrix : Matrix (Fin 27) (Fin 27) ℚ :=
  sourceToNative * sourceOrder13Matrix * nativeToSource

theorem native_order_thirteen_matrix :
    nativeOrder13Matrix ^ 13 = 1 := by
  native_decide

theorem native_order_thirteen_unit :
    applyWitness nativeOrder13Matrix nativeOne = nativeOne := by
  native_decide

theorem native_order_thirteen_trace_gram :
    nativeOrder13Matrix.transpose * nativeTraceGram *
      nativeOrder13Matrix = nativeTraceGram := by
  native_decide

/-- Source-selected 729 basis-product payment in the actual native
RationalAlbertNative.jordanProduct. This is an F4-compatible
Jordan-algebra automorphism, but NOT a F4 group classification. -/
theorem native_order_thirteen_all_source_basis_products :
    ∀ i j : Fin 27,
      toNative (applyWitness nativeOrder13Matrix
        (fun k => sourceToNative k 0 * 0 +
          (∑ a : Fin 27, sourceToNative k a * sourceTensor i j a))) =
      Integration.RationalAlbertNative.RationalAlbert.jordanProduct
        (toNative (applyWitness nativeOrder13Matrix
          (fun k => sourceToNative k i)))
        (toNative (applyWitness nativeOrder13Matrix
          (fun k => sourceToNative k j))) := by
  native_decide

end Integration.Griess1990Moufang81ActualAlbertOrder13
