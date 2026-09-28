import Mathlib
import Integration.RiemannPrimitiveKernelUnimodularBasis

/-!
# Explicit Smith reduction of the primitive RH coefficient row

Starting from (80,243,1215,972), use:
1. the determinant-one 2×2 block from the previous module;
2. three elementary determinant-one column shears.

This reduces the row to (1,0,0,0), making the 1×4 Smith normal form explicit.
Hence the bare integer row has no nontrivial invariant factor beyond 1.
-/

namespace Integration.RiemannPrimitiveKernelExplicitSmithReduction

open Integration.RiemannPrimitiveKernelUnimodularBasis

structure Row4 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

def originalRow : Row4 := ⟨80,243,1215,972⟩

def firstBlockChange : Row4 → Row4
  | ⟨a,b,c,d⟩ =>
      let p := forwardU (a,b)
      ⟨p.1,p.2,c,d⟩

def firstBlockInverse : Row4 → Row4
  | ⟨a,b,c,d⟩ =>
      let p := inverseU (a,b)
      ⟨p.1,p.2,c,d⟩

theorem first_block_roundtrip_left (r : Row4) :
    firstBlockInverse (firstBlockChange r) = r := by
  rcases r with ⟨a,b,c,d⟩
  simp [firstBlockChange, firstBlockInverse, inverse_after_forward]

theorem first_block_roundtrip_right (r : Row4) :
    firstBlockChange (firstBlockInverse r) = r := by
  rcases r with ⟨a,b,c,d⟩
  simp [firstBlockChange, firstBlockInverse, forward_after_inverse]

def clearB : Row4 → Row4
  | ⟨a,b,c,d⟩ => ⟨a, b + 3*a, c, d⟩

def unClearB : Row4 → Row4
  | ⟨a,b,c,d⟩ => ⟨a, b - 3*a, c, d⟩

def clearC : Row4 → Row4
  | ⟨a,b,c,d⟩ => ⟨a, b, c - 1215*a, d⟩

def unClearC : Row4 → Row4
  | ⟨a,b,c,d⟩ => ⟨a, b, c + 1215*a, d⟩

def clearD : Row4 → Row4
  | ⟨a,b,c,d⟩ => ⟨a, b, c, d - 972*a⟩

def unClearD : Row4 → Row4
  | ⟨a,b,c,d⟩ => ⟨a, b, c, d + 972*a⟩

theorem clearB_roundtrip_left (r : Row4) :
    unClearB (clearB r) = r := by
  rcases r with ⟨a,b,c,d⟩
  ext <;> simp [clearB, unClearB] <;> ring

theorem clearB_roundtrip_right (r : Row4) :
    clearB (unClearB r) = r := by
  rcases r with ⟨a,b,c,d⟩
  ext <;> simp [clearB, unClearB] <;> ring

theorem clearC_roundtrip_left (r : Row4) :
    unClearC (clearC r) = r := by
  rcases r with ⟨a,b,c,d⟩
  ext <;> simp [clearC, unClearC] <;> ring

theorem clearC_roundtrip_right (r : Row4) :
    clearC (unClearC r) = r := by
  rcases r with ⟨a,b,c,d⟩
  ext <;> simp [clearC, unClearC] <;> ring

theorem clearD_roundtrip_left (r : Row4) :
    unClearD (clearD r) = r := by
  rcases r with ⟨a,b,c,d⟩
  ext <;> simp [clearD, unClearD] <;> ring

theorem clearD_roundtrip_right (r : Row4) :
    clearD (unClearD r) = r := by
  rcases r with ⟨a,b,c,d⟩
  ext <;> simp [clearD, unClearD] <;> ring

def smithReduce : Row4 → Row4 :=
  clearD ∘ clearC ∘ clearB ∘ firstBlockChange

def smithExpand : Row4 → Row4 :=
  firstBlockInverse ∘ unClearB ∘ unClearC ∘ unClearD

theorem smith_expand_reduce (r : Row4) :
    smithExpand (smithReduce r) = r := by
  simp [smithExpand, smithReduce, Function.comp_def,
    clearD_roundtrip_left, clearC_roundtrip_left, clearB_roundtrip_left,
    first_block_roundtrip_left]

theorem smith_reduce_expand (r : Row4) :
    smithReduce (smithExpand r) = r := by
  simp [smithExpand, smithReduce, Function.comp_def,
    first_block_roundtrip_right, clearB_roundtrip_right,
    clearC_roundtrip_right, clearD_roundtrip_right]

def smithEquiv : Row4 ≃ Row4 where
  toFun := smithReduce
  invFun := smithExpand
  left_inv := smith_expand_reduce
  right_inv := smith_reduce_expand

theorem step1_exact :
    firstBlockChange originalRow = ⟨1,-3,1215,972⟩ := by
  norm_num [firstBlockChange, originalRow, forwardU]

theorem step2_exact :
    clearB ⟨1,-3,1215,972⟩ = ⟨1,0,1215,972⟩ := by
  norm_num [clearB]

theorem step3_exact :
    clearC ⟨1,0,1215,972⟩ = ⟨1,0,0,972⟩ := by
  norm_num [clearC]

theorem step4_exact :
    clearD ⟨1,0,0,972⟩ = ⟨1,0,0,0⟩ := by
  norm_num [clearD]

theorem explicit_smith_normal_form :
    smithReduce originalRow = ⟨1,0,0,0⟩ := by
  norm_num [smithReduce, Function.comp_def, firstBlockChange, originalRow,
    forwardU, clearB, clearC, clearD]

/-- The 1×4 Smith data are therefore exactly the single invariant factor 1. -/
def smithInvariantFactors : List Nat := [1]

theorem smith_invariant_factors_exact :
    smithInvariantFactors = [1] := rfl

def rowMap (r : Row4) : Int :=
  80*r.a + 243*r.b + 1215*r.c + 972*r.d

def rowPreimage (z : Int) : Row4 :=
  ⟨-82*z, 27*z, 0, 0⟩

theorem row_map_has_preimage (z : Int) :
    rowMap (rowPreimage z) = z := by
  simp [rowMap, rowPreimage]
  ring

theorem row_map_surjective :
    Function.Surjective rowMap := by
  intro z
  exact ⟨rowPreimage z, row_map_has_preimage z⟩

structure Boundary where
  explicitDeterminantOneFirstBlock : Bool
  threeElementaryShearsOwned : Bool
  everyStepHasExplicitInverse : Bool
  completeRowEquivalenceOwned : Bool
  explicitSNFOneZeroZeroZeroOwned : Bool
  rowMapSurjectivityOwned : Bool
  nontrivialBareIntegerSmithFactorRemains : Bool
  filteredThreeAdicStructureStillAdditional : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitDeterminantOneFirstBlock := true
  threeElementaryShearsOwned := true
  everyStepHasExplicitInverse := true
  completeRowEquivalenceOwned := true
  explicitSNFOneZeroZeroZeroOwned := true
  rowMapSurjectivityOwned := true
  nontrivialBareIntegerSmithFactorRemains := false
  filteredThreeAdicStructureStillAdditional := true

end Integration.RiemannPrimitiveKernelExplicitSmithReduction
