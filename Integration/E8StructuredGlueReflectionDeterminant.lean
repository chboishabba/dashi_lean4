import Integration.E8StructuredGlueReflection
import Mathlib

/-! Explicit determinant-one certificate for the intrinsic structured E8 simple system. -/
namespace Integration.E8StructuredGlueReflectionDeterminant

open Integration.E8StructuredGlueReflection

/-- Fixed order of the eight selected simple roots. -/
def e8SimpleAt : Fin 8 → E8Simple :=
  ![.e0,.e1,.e2,.e3,.e4,.e5,.glue,.b]

/-- Literal eight-by-eight Gram matrix in that order. -/
def e8SimpleGramMatrix : Matrix (Fin 8) (Fin 8) Int :=
  fun i j => simpleGram (e8SimpleAt i) (e8SimpleAt j)

 theorem e8_simple_gram_entries :
    e8SimpleGramMatrix =
      !![2,0,-1,0,0,0,0,0;
         0,2,0,-1,0,0,0,0;
         -1,0,2,-1,0,0,0,0;
         0,-1,-1,2,-1,0,0,0;
         0,0,0,-1,2,-1,0,0;
         0,0,0,0,-1,2,-1,0;
         0,0,0,0,0,-1,2,-1;
         0,0,0,0,0,0,-1,2] := by
  native_decide

/-- The selected rank-eight root lattice is unimodular. -/
theorem e8_simple_gram_determinant_one : Matrix.det e8SimpleGramMatrix = 1 := by
  native_decide

structure Boundary where
  explicitE8GramMatrixPaid : Bool
  determinantOnePaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  explicitE8GramMatrixPaid := true
  determinantOnePaid := true

end Integration.E8StructuredGlueReflectionDeterminant
