import Integration.F3FourSymplecticExteriorSquare
import Mathlib

namespace DASHI.Integration.F3E6PGSpGeneratorBridge

open F3FourSymplecticExteriorSquare

abbrev M4 := Matrix (Fin 4) (Fin 4) F3
abbrev M5 := Matrix (Fin 5) (Fin 5) F3

/-- Standard alternating form on F₃⁴. -/
def symplecticMatrix : M4 := ![
  ![0, 1, 0, 0],
  ![2, 0, 0, 0],
  ![0, 0, 0, 1],
  ![0, 0, 2, 0]
]

/-- Polar form of `primitiveQuadratic`. -/
def primitivePolarMatrix : M5 := ![
  ![1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 2],
  ![0, 0, 0, 1, 0],
  ![0, 0, 1, 0, 0],
  ![0, 2, 0, 0, 0]
]

private def col (g : M4) (j : Fin 4) : X4 := fun i => g i j
private def bivSub (p q : Bivector6) : Bivector6 := fun i => p i - q i

/-- Primitive exterior-square action in the basis
`e12-e34, e13, e14, e23, e24`. -/
def exteriorAction (g : M4) : M5 :=
  let c0 := col g 0
  let c1 := col g 1
  let c2 := col g 2
  let c3 := col g 3
  let b0 := primitiveProjection (bivSub (wedge c0 c1) (wedge c2 c3))
  let b1 := primitiveProjection (wedge c0 c2)
  let b2 := primitiveProjection (wedge c0 c3)
  let b3 := primitiveProjection (wedge c1 c2)
  let b4 := primitiveProjection (wedge c1 c3)
  fun i j => (![b0, b1, b2, b3, b4] j) i

/-! Six explicit anti-symplectic similitude lifts. -/

def pgsp0 : M4 := ![
  ![0,0,2,0], ![0,0,0,1], ![1,0,0,0], ![0,2,0,0]
]
def pgsp1 : M4 := ![
  ![0,0,1,0], ![0,0,1,2], ![2,0,0,0], ![2,1,0,0]
]
def pgsp2 : M4 := ![
  ![0,0,0,1], ![0,0,1,0], ![0,2,0,0], ![2,0,0,0]
]
def pgsp3 : M4 := ![
  ![1,0,1,0], ![0,1,1,1], ![1,0,2,0], ![2,1,0,2]
]
def pgsp4 : M4 := ![
  ![2,0,2,0], ![0,2,0,2], ![2,0,1,0], ![0,2,0,1]
]
def pgsp5 : M4 := ![
  ![2,0,1,0], ![0,2,2,1], ![1,0,1,0], ![1,1,0,1]
]

def pgspGenerator : Fin 6 → M4 := ![pgsp0, pgsp1, pgsp2, pgsp3, pgsp4, pgsp5]

/-! The corresponding six reduced E₆ simple-reflection matrices after the
explicit mod-3 quotient and primitive-five-space isometry used by the finite
receipt.  The separate quotient provenance remains a recognition boundary;
these matrices are not inferred from their order. -/

def e60 : M5 := ![
  ![1,0,0,0,0], ![0,1,0,0,0], ![0,0,0,2,0], ![0,0,2,0,0], ![0,0,0,0,1]
]
def e61 : M5 := ![
  ![1,0,0,0,0], ![0,1,0,0,0], ![0,1,0,2,0], ![0,1,2,0,0], ![0,1,2,2,1]
]
def e62 : M5 := ![
  ![1,0,0,0,0], ![0,0,0,0,1], ![0,0,1,0,0], ![0,0,0,1,0], ![0,1,0,0,0]
]
def e63 : M5 := ![
  ![0,1,1,2,0], ![0,1,0,0,0], ![2,1,2,2,0], ![1,2,2,2,0], ![2,1,1,2,1]
]
def e64 : M5 := ![
  ![0,0,1,2,0], ![0,1,0,0,0], ![2,0,2,2,0], ![1,0,2,2,0], ![0,0,0,0,1]
]
def e65 : M5 := ![
  ![0,1,2,1,0], ![0,1,0,0,0], ![1,2,2,2,0], ![2,1,2,2,0], ![2,1,2,1,1]
]

def e6ReducedGenerator : Fin 6 → M5 := ![e60, e61, e62, e63, e64, e65]

theorem pgspGenerator_is_antisymplectic (i : Fin 6) :
    Matrix.transpose (pgspGenerator i) * symplecticMatrix * pgspGenerator i =
      -symplecticMatrix := by
  fin_cases i <;> native_decide

theorem exteriorAction_pgspGenerator (i : Fin 6) :
    exteriorAction (pgspGenerator i) = e6ReducedGenerator i := by
  fin_cases i <;> native_decide

theorem e6ReducedGenerator_isometry (i : Fin 6) :
    Matrix.transpose (e6ReducedGenerator i) * primitivePolarMatrix * e6ReducedGenerator i =
      primitivePolarMatrix := by
  fin_cases i <;> native_decide

/-- Generator-level action equality is paid.  Group-level recognition still
requires a theorem that the two generated actions are the same subgroup, not
merely the external finite closure receipt. -/
structure GeneratorBridgeBoundary where
  sixPGSpLiftsConstructed : Bool
  allSixMultiplierMinusOne : Bool
  sixReducedE6MatricesConstructed : Bool
  sixGeneratorIntertwiningPaid : Bool
  sixE6MatricesPreservePrimitivePolarForm : Bool
  fullGeneratedGroupEqualityKernelPaid : Bool
  orderEqualityPromotesGroupRecognition : Bool

def generatorBridgeBoundary : GeneratorBridgeBoundary :=
  { sixPGSpLiftsConstructed := true
    allSixMultiplierMinusOne := true
    sixReducedE6MatricesConstructed := true
    sixGeneratorIntertwiningPaid := true
    sixE6MatricesPreservePrimitivePolarForm := true
    fullGeneratedGroupEqualityKernelPaid := false
    orderEqualityPromotesGroupRecognition := false }

end DASHI.Integration.F3E6PGSpGeneratorBridge
