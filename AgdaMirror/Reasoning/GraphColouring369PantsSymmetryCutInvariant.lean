/-!
# S3 / reflection preservation of the selected maximum-cut partition

Downstream of the golden Agda
DASHI.Combinatorics.GraphColouring369PantsSymmetryCutInvariantExact.

For the 27-grid nearest-neighbour checkerboard, ALL six coordinate
permutations and the middle-coordinate sign reflection preserve
the actual selected Bool partition, not just proper-colouring
existence.  This is not invariant asymmetric weighted directed data,
a smooth cobordism, or a Monster representation.
-/
import Mathlib
import AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency
import AgdaMirror.Reasoning.GraphColouring369PantsMaxCutQid

namespace AgdaMirror.Reasoning.GraphColouring369PantsSymmetryCutInvariant

open AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency
open AgdaMirror.Reasoning.GraphColouring369PantsMaxCutQid

theorem all_six_s3_preserve_exact_cut (g : S3Code) (p : PantsPath3) :
    pantsPartition (actS3 g p) = pantsPartition p := by
  rcases p with ⟨a, b, c⟩
  cases g <;> cases a <;> cases b <;> cases c <;> decide

theorem seam_reflection_preserves_exact_cut (p : PantsPath3) :
    pantsPartition (flipSecond p) = pantsPartition p := by
  rcases p with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem s3_preserves_actual_crossing (g : S3Code)
    {p q : PantsPath3} (edge : PantsAdjacent p q) :
    pantsPartition (actS3 g p) ≠ pantsPartition (actS3 g q) := by
  rw [all_six_s3_preserve_exact_cut, all_six_s3_preserve_exact_cut]
  exact pantsEdgesAllCut edge

theorem seam_reflection_preserves_actual_crossing
    {p q : PantsPath3} (edge : PantsAdjacent p q) :
    pantsPartition (flipSecond p) ≠ pantsPartition (flipSecond q) := by
  rw [seam_reflection_preserves_exact_cut, seam_reflection_preserves_exact_cut]
  exact pantsEdgesAllCut edge

end AgdaMirror.Reasoning.GraphColouring369PantsSymmetryCutInvariant
