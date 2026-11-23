import Integration.F3E6PGSpGeneratorBridge
import Integration.E6Mod3WeylAction
import Mathlib

namespace DASHI.Integration.F3E6PGSpSameObjectBridge

open F3FourSymplecticExteriorSquare
open F3E6PGSpGeneratorBridge

namespace E6Bridge
abbrev F3Five := Integration.E6Mod3QuadraticBridge.F3Five
def standardQuadratic := Integration.E6Mod3QuadraticBridge.standardQuadratic
end E6Bridge

namespace E6Weyl
abbrev E6SimpleReflection := Integration.E6Mod3WeylAction.E6SimpleReflection
def reflectStandard := Integration.E6Mod3WeylAction.reflectStandard
end E6Weyl

private def standardVec (z : E6Bridge.F3Five) : Primitive5 :=
  ![z.z0, z.z1, z.z2, z.z3, z.z4]

private def vecToStandard (v : Primitive5) : E6Bridge.F3Five :=
  ⟨v 0, v 1, v 2, v 3, v 4⟩

/-- Explicit primitive-Plucker -> repository-standard change of basis.
It carries `standardQuadratic` to `2 * primitiveQuadratic`; the scalar 2 is
nonzero in F₃, so the null cone is preserved exactly. -/
def primitiveToStandardMatrix : M5 := ![
  ![0,0,1,2,0],
  ![0,1,0,0,1],
  ![0,1,1,1,2],
  ![0,1,2,2,2],
  ![1,0,0,0,0]
]

def standardToPrimitiveMatrix : M5 := ![
  ![0,0,0,0,1],
  ![0,2,1,1,0],
  ![2,0,1,2,0],
  ![1,0,1,2,0],
  ![0,2,2,2,0]
]

def primitiveToStandard (q : Primitive5) : E6Bridge.F3Five :=
  vecToStandard (primitiveToStandardMatrix.mulVec q)

def standardToPrimitive (z : E6Bridge.F3Five) : Primitive5 :=
  standardToPrimitiveMatrix.mulVec (standardVec z)

theorem primitive_standard_matrix_inverse_left :
    standardToPrimitiveMatrix * primitiveToStandardMatrix = 1 := by
  native_decide

theorem primitive_standard_matrix_inverse_right :
    primitiveToStandardMatrix * standardToPrimitiveMatrix = 1 := by
  native_decide

theorem primitiveToStandard_scaled_isometry :
    ∀ q : Primitive5,
      E6Bridge.standardQuadratic (primitiveToStandard q) = 2 * primitiveQuadratic q := by
  native_decide

theorem standardToPrimitive_roundTrip :
    ∀ z : E6Bridge.F3Five, primitiveToStandard (standardToPrimitive z) = z := by
  native_decide

theorem primitiveToStandard_roundTrip :
    ∀ q : Primitive5, standardToPrimitive (primitiveToStandard q) = q := by
  native_decide

/-- Matrix action on the existing repository `F3Five` carrier. -/
def standardMatrixAct (m : M5) (z : E6Bridge.F3Five) : E6Bridge.F3Five :=
  vecToStandard (m.mulVec (standardVec z))

/-- Exact matrices of the existing repository E6 simple reflections. -/
def e6s0 : M5 := ![
  ![1,0,0,0,0], ![0,1,0,0,0], ![0,0,1,0,0], ![0,0,0,0,1], ![0,0,0,1,0]
]
def e6s1 : M5 := ![
  ![0,2,2,2,2], ![2,0,2,2,2], ![2,2,0,2,2], ![2,2,2,0,2], ![2,2,2,2,0]
]
def e6s2 : M5 := ![
  ![0,2,2,2,1], ![2,0,2,2,1], ![2,2,0,2,1], ![2,2,2,0,1], ![1,1,1,1,0]
]
def e6s3 : M5 := ![
  ![0,2,0,0,0], ![2,0,0,0,0], ![0,0,1,0,0], ![0,0,0,1,0], ![0,0,0,0,1]
]
def e6s4 : M5 := ![
  ![0,0,1,0,0], ![0,1,0,0,0], ![1,0,0,0,0], ![0,0,0,1,0], ![0,0,0,0,1]
]
def e6s5 : M5 := ![
  ![0,1,0,0,0], ![1,0,0,0,0], ![0,0,1,0,0], ![0,0,0,1,0], ![0,0,0,0,1]
]

def e6StandardGenerator : Fin 6 → M5 := ![e6s0, e6s1, e6s2, e6s3, e6s4, e6s5]

def reflectionIndex : Fin 6 → E6Weyl.E6SimpleReflection := ![
  .s0, .s1, .s2, .s3, .s4, .s5
]

theorem e6StandardGenerator_models_repo_action :
    ∀ i : Fin 6, ∀ z : E6Bridge.F3Five,
      standardMatrixAct (e6StandardGenerator i) z =
        E6Weyl.reflectStandard (reflectionIndex i) z := by
  native_decide

/-! Anti-symplectic lifts whose primitive exterior-square action, after the
explicit change of basis above, is the repository's E6 action. -/

def lift0 : M4 := ![
  ![1,0,1,1], ![0,1,1,2], ![2,2,2,0], ![2,1,0,2]
]
def lift1 : M4 := ![
  ![2,0,1,1], ![0,2,0,1], ![1,2,1,0], ![0,1,0,1]
]
def lift2 : M4 := ![
  ![1,0,1,1], ![0,1,0,1], ![1,2,2,0], ![0,1,0,2]
]
def lift3 : M4 := ![
  ![0,0,2,1], ![0,0,2,2], ![2,2,0,0], ![1,2,0,0]
]
def lift4 : M4 := ![
  ![0,0,1,1], ![0,0,1,0], ![0,2,0,0], ![2,1,0,0]
]
def lift5 : M4 := ![
  ![0,0,2,2], ![0,0,1,2], ![2,1,0,0], ![2,2,0,0]
]

def pgspLift : Fin 6 → M4 := ![lift0, lift1, lift2, lift3, lift4, lift5]

def standardExteriorAction (g : M4) : M5 :=
  primitiveToStandardMatrix * exteriorAction g * standardToPrimitiveMatrix

theorem pgspLift_is_antisymplectic :
    ∀ i : Fin 6,
      Matrix.transpose (pgspLift i) * symplecticMatrix * pgspLift i = -symplecticMatrix := by
  native_decide

theorem exterior_pgspLift_eq_repoE6Generator :
    ∀ i : Fin 6, standardExteriorAction (pgspLift i) = e6StandardGenerator i := by
  native_decide

def pgspStandardFiveGenerator (i : Fin 6) : M5 := standardExteriorAction (pgspLift i)

def wordAction (gen : Fin 6 → M5) : List (Fin 6) → M5
  | [] => 1
  | i :: rest => gen i * wordAction gen rest

theorem generatedRepoE6FiveSpaceAction_eq (w : List (Fin 6)) :
    wordAction pgspStandardFiveGenerator w = wordAction e6StandardGenerator w := by
  induction w with
  | nil => rfl
  | cons i rest ih =>
      simp only [wordAction]
      rw [exterior_pgspLift_eq_repoE6Generator, ih]

structure SameObjectBoundary where
  primitiveToRepoStandardIsometryPaid : Bool
  repoStandardRoundTripsPaid : Bool
  repoE6GeneratorMatricesRecognized : Bool
  sixAntiSymplecticLiftsConstructed : Bool
  repoE6GeneratorIntertwiningPaid : Bool
  generatedRepoE6FiveSpaceActionEqualityPaid : Bool
  abstractPGSpQuotientWeylIsomorphismPaid : Bool
  rawT4PuncturedPromotedToNullCone : Bool
  deriving Repr

def sameObjectBoundary : SameObjectBoundary where
  primitiveToRepoStandardIsometryPaid := true
  repoStandardRoundTripsPaid := true
  repoE6GeneratorMatricesRecognized := true
  sixAntiSymplecticLiftsConstructed := true
  repoE6GeneratorIntertwiningPaid := true
  generatedRepoE6FiveSpaceActionEqualityPaid := true
  abstractPGSpQuotientWeylIsomorphismPaid := false
  rawT4PuncturedPromotedToNullCone := false

end DASHI.Integration.F3E6PGSpSameObjectBridge
