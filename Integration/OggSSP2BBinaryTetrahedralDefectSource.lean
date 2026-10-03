import Integration.OggSSP2BFiveByTwoDefectArchitecture

/-!
# Source meaning of the five-mode defect profile

The binary tetrahedral group 2T ≅ SL(2,3) has order 24.  Grouping its seven
conjugacy classes by element order gives five order strata

  1, 2, 4, 3, 6.

The corresponding class sizes are 1,1,6,4,4 (with the order-3 and order-6
strata each consisting of two size-4 conjugacy classes).  Hence representative
centralizer orders are

  24, 24, 4, 6, 6.

Their exact powers of two are therefore

  2^3·3, 2^3·3, 2^2, 2·3, 2·3,

so the independently defined 2-adic centralizer exponents are exactly

  (3,3,2,1,1).

This pays the *meaning* of the defect vector.  It does not identify the five
Completion10 modes with these five binary-tetrahedral order strata.  That last
recognition map is the remaining D-weld.
-/

namespace Integration.OggSSP2BBinaryTetrahedralDefectSource

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture

inductive OrderStratum
  | identity
  | centralMinusOne
  | orderFour
  | orderThree
  | orderSix
  deriving DecidableEq, Repr, Fintype

def representativeOrder : OrderStratum → ℕ
  | .identity => 1
  | .centralMinusOne => 2
  | .orderFour => 4
  | .orderThree => 3
  | .orderSix => 6

def classSize : OrderStratum → ℕ
  | .identity => 1
  | .centralMinusOne => 1
  | .orderFour => 6
  | .orderThree => 4
  | .orderSix => 4

def centralizerOrder : OrderStratum → ℕ
  | .identity => 24
  | .centralMinusOne => 24
  | .orderFour => 4
  | .orderThree => 6
  | .orderSix => 6

/-- Exact exponent of 2 in the corresponding centralizer order. -/
def centralizerTwoAdicExponent : OrderStratum → ℕ
  | .identity => 3
  | .centralMinusOne => 3
  | .orderFour => 2
  | .orderThree => 1
  | .orderSix => 1

def centralizerOddPart : OrderStratum → ℕ
  | .identity => 3
  | .centralMinusOne => 3
  | .orderFour => 1
  | .orderThree => 3
  | .orderSix => 3

theorem centralizer_two_adic_factorization (s : OrderStratum) :
    2 ^ centralizerTwoAdicExponent s * centralizerOddPart s
      = centralizerOrder s := by
  cases s <;> decide

theorem five_order_strata : Fintype.card OrderStratum = 5 := by
  decide

theorem sourced_defect_profile :
    (centralizerTwoAdicExponent .identity,
     centralizerTwoAdicExponent .centralMinusOne,
     centralizerTwoAdicExponent .orderFour,
     centralizerTwoAdicExponent .orderThree,
     centralizerTwoAdicExponent .orderSix)
      = (3,3,2,1,1) := by
  rfl

/-- A source-valid D recognition must identify the already-recognized five
Completion10 modes with the independently defined binary-tetrahedral strata
and preserve this invariant. -/
structure FiveModeDefectRecognition where
  modeToOrderStratum : F.Mode5 ≃ OrderStratum
  defectIntertwines :
    ∀ m,
      F.defectDepth m
        = centralizerTwoAdicExponent (modeToOrderStratum m)
  sourceProvenance : String

/-- There is a numerical chart with the intended profile, but it remains only
a candidate until an independent source identifies these mode labels with the
binary-tetrahedral order strata. -/
def numericalCandidateChart : F.Mode5 ≃ OrderStratum where
  toFun
    | .mode09 => .identity
    | .mode18 => .centralMinusOne
    | .mode27 => .orderFour
    | .mode36 => .orderThree
    | .mode45 => .orderSix
  invFun
    | .identity => .mode09
    | .centralMinusOne => .mode18
    | .orderFour => .mode27
    | .orderThree => .mode36
    | .orderSix => .mode45
  left_inv := by intro m; cases m <;> rfl
  right_inv := by intro s; cases s <;> rfl

theorem numericalCandidateChart_matches_profile (m : F.Mode5) :
    F.defectDepth m
      = centralizerTwoAdicExponent (numericalCandidateChart m) := by
  cases m <;> rfl

/-- Semantic boundary: numerical compatibility alone is not a sourced
recognition of mode labels. -/
inductive NumericalProfileConstructsSourceRecognition : Prop

theorem numerical_profile_does_not_construct_source_recognition :
    ¬ NumericalProfileConstructsSourceRecognition := by
  intro h
  cases h

/-- D is paid exactly when a sourced recognition receipt is supplied. -/
theorem recognized_profile
    (R : FiveModeDefectRecognition) (m : F.Mode5) :
    F.defectDepth m
      = centralizerTwoAdicExponent (R.modeToOrderStratum m) :=
  R.defectIntertwines m

end Integration.OggSSP2BBinaryTetrahedralDefectSource
