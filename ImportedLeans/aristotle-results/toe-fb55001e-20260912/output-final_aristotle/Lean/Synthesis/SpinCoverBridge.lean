import Synthesis.PhysicsInterfaces
import AgdaMirror.Algebra.FiniteQuaternionStrictCover
import AgdaMirror.Algebra.ContinuousSpin31LorentzCover

/-!
# Synthesis layer 2''''''': the one interface with genuine cover content

`Synthesis.PhysicsInterfaces` showed that inhabiting
`AgdaMirror.SpinEmergence.SpinEmergenceAxioms` proves nothing about covers,
because its `SpinIsDoubleCover` field is a bare map.  The repository does,
however, contain a *genuine* finite double cover:
`AgdaMirror.Algebra.FiniteQuaternionStrictCover` builds the quaternion map
`rho : Q8 → V4Rotation` with a homomorphism law, a kernel characterisation and
two-element fibres.

Proved here:

* `card_Q8`, `card_V4Rotation`, `card_spin_eq_two_mul_card_base` — the cover is
  two-to-one at the level of cardinalities, `8 = 2 * 4`;
* `rho_surjective`, `card_rho_fiber` — every rotation has exactly two preimages;
* `q8SpinEmergence`, `spin_interface_satisfiable_with_genuine_cover` — the spin
  interface *can* be instantiated so that its cover field really is two-to-one
  with exhaustive fibres.  Together with
  `Synthesis.PhysicsInterfaces.spin_interface_no_double_cover` this pins the
  interface down exactly: the double-cover property is an extra theorem about a
  chosen instance, never a consequence of the record;
* `continuous_cover_interface_vacuous` — by contrast the continuous
  `Spin(3,1) → SO⁺(3,1)` record is inhabited with *every* one of its
  propositional obligations instantiated as `True` over the finite carriers, so
  inhabiting it is not evidence for any continuous statement.

Boundary: `V4Rotation` is the Klein four-group of half-turns, not `SO(3,1)`, and
`Q8` is not `Spin(3,1)`.  The finite cover is a finite model and is not promoted;
the source material says so itself, and nothing here changes that.
-/

namespace Synthesis.SpinCoverBridge

open AgdaMirror.FiniteQuaternionStrictCover
open AgdaMirror.SpinEmergence

/-! ## Finiteness of the two carriers -/

instance : Fintype Sign where
  elems := {Sign.positiveSign, Sign.negativeSign}
  complete := by intro x; cases x <;> decide

instance : Fintype QuaternionBasis where
  elems := {QuaternionBasis.basisOne, QuaternionBasis.basisI, QuaternionBasis.basisJ,
    QuaternionBasis.basisK}
  complete := by intro x; cases x <;> decide

instance : Fintype V4Rotation where
  elems := {V4Rotation.identityRotation, V4Rotation.halfTurnX, V4Rotation.halfTurnY,
    V4Rotation.halfTurnZ}
  complete := by intro x; cases x <;> decide

/-- `Q8` is the product of its sign and its basis element. -/
def q8Equiv : Q8 ≃ Sign × QuaternionBasis where
  toFun q := (q.sign, q.basis)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro q; cases q; rfl
  right_inv := by intro p; cases p; rfl

instance : Fintype Q8 := Fintype.ofEquiv _ q8Equiv.symm

theorem card_Q8 : Fintype.card Q8 = 8 := by
  rw [Fintype.card_congr q8Equiv, Fintype.card_prod]
  rfl

theorem card_V4Rotation : Fintype.card V4Rotation = 4 := rfl

/-- **The finite cover is two-to-one on cardinalities.** -/
theorem card_spin_eq_two_mul_card_base :
    Fintype.card Q8 = 2 * Fintype.card V4Rotation := by
  rw [card_Q8, card_V4Rotation]

/-! ## Every rotation has exactly two preimages -/

theorem rho_surjective : Function.Surjective rho := by
  intro r
  exact ⟨chosenPreimage r, chosenPreimage_maps r⟩

/-- The fibre of `rho` over any rotation is exactly `{firstFiber r, secondFiber r}`. -/
theorem rho_fiber_eq (r : V4Rotation) :
    Finset.univ.filter (fun q : Q8 => rho q = r) = {firstFiber r, secondFiber r} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · exact fiber_exhaustive r q
  · rintro (rfl | rfl)
    · exact fiber_first_maps r
    · exact fiber_second_maps r

/-- **Every rotation has exactly two quaternion preimages.** -/
theorem card_rho_fiber (r : V4Rotation) :
    (Finset.univ.filter (fun q : Q8 => rho q = r)).card = 2 := by
  rw [rho_fiber_eq, Finset.card_pair (fiber_distinct r)]

/-! ## Instantiating the spin interface with the genuine cover -/

/-- The `SO` family of the instance: the Klein four-group in signature `(3,1)`,
a point everywhere else.  (`V4Rotation` is *not* `SO(3,1)`; this only records
where the finite model is placed.) -/
def SOFamily : Nat → Nat → Type
  | 3, 1 => V4Rotation
  | _, _ => PUnit

/-- The spin interface, instantiated by the finite quaternion cover. -/
def q8SpinEmergence : SpinEmergenceAxioms where
  QuadraticForm := PUnit
  Signature31 := PUnit.unit
  CliffordAlgebra := fun _ => Q8
  SpinGroup := Q8
  SO := SOFamily
  SpinIsDoubleCover := rho

/-- **The spin interface is satisfiable with genuine content**: there is a bundle
whose cover map really is two-to-one, with exhaustive fibres.  Contrast
`Synthesis.PhysicsInterfaces.spin_interface_no_double_cover`, which shows the
record does not force this. -/
theorem spin_interface_satisfiable_with_genuine_cover :
    ∃ A : SpinEmergenceAxioms.{0}, ∀ x : A.SO 3 1,
      ∃ a b : A.SpinGroup, a ≠ b ∧
        A.SpinIsDoubleCover a = x ∧ A.SpinIsDoubleCover b = x ∧
        ∀ c : A.SpinGroup, A.SpinIsDoubleCover c = x → c = a ∨ c = b := by
  refine ⟨q8SpinEmergence, ?_⟩
  intro x
  exact ⟨firstFiber x, secondFiber x, fiber_distinct x, fiber_first_maps x,
    fiber_second_maps x, fun c hc => fiber_exhaustive x c hc⟩

/-! ## The continuous cover record carries no continuous content -/

open AgdaMirror.ContinuousSpin31LorentzCover

/-- The finite quaternion group, presented as a "topological group" of the
supplied record type: every topological obligation is the proposition `True`. -/
def q8AsTopologicalGroup : TopologicalGroup where
  Carrier := Q8
  identity := plusOne
  product := q8Multiply
  inverse := id
  OpenSet := PUnit
  isOpen := fun _ => True
  contains := fun _ _ => True
  groupLaws := True
  groupLawsProof := trivial
  topologyLaws := True
  topologyLawsProof := trivial
  multiplicationContinuous := True
  multiplicationContinuousProof := trivial
  inverseContinuous := True
  inverseContinuousProof := trivial

/-- The Klein four-group, presented the same way. -/
def v4AsTopologicalGroup : TopologicalGroup where
  Carrier := V4Rotation
  identity := V4Rotation.identityRotation
  product := rotationMultiply
  inverse := id
  OpenSet := PUnit
  isOpen := fun _ => True
  contains := fun _ _ => True
  groupLaws := True
  groupLawsProof := trivial
  topologyLaws := True
  topologyLawsProof := trivial
  multiplicationContinuous := True
  multiplicationContinuousProof := trivial
  inverseContinuous := True
  inverseContinuousProof := trivial

/-- `rho` as a "smooth group map" of the supplied record type: the homomorphism
law is the genuine one, the smoothness obligations are `True`. -/
def rhoAsSmoothMap : SmoothGroupMap q8AsTopologicalGroup v4AsTopologicalGroup where
  map := rho
  homomorphism := rhoHomomorphism
  identityPreserved := rfl
  continuous := True
  continuousProof := trivial
  smooth := True
  smoothProof := trivial

/-- The two-sheeted cover record over the finite model. -/
def finiteTwoSheetedCover :
    TwoSheetedCover q8AsTopologicalGroup v4AsTopologicalGroup rhoAsSmoothMap where
  Preimage := fun target => Preimage rho target
  exactPreimage := exactPreimage
  plusOne := plusOne
  minusOne := minusOne
  plusAndMinusDistinct := True
  plusAndMinusDistinctProof := trivial
  kernelExactlyPlusMinusOne := fun q => q = plusOne ∨ q = minusOne
  Fiber := fun target => TwoElementFiber rho target
  fiberHasExactlyTwoPoints := fun _ => True
  evenlyCoveredNeighborhood := fun _ => True
  localHomeomorphism := True
  localHomeomorphismProof := trivial
  coveringMap := True
  coveringMapProof := trivial

/-- **The continuous Spin(3,1) record is inhabited over finite carriers with every
propositional obligation instantiated as `True`.**  Its "obligations" are
self-chosen propositions, so inhabiting the record is not evidence for a
continuous cover, a Lorentz group, or a Lie-algebra isomorphism. -/
def vacuousContinuousCover : ContinuousSpin31LorentzCover where
  Spin31 := q8AsTopologicalGroup
  SOPlus31 := v4AsTopologicalGroup
  rho := rhoAsSmoothMap
  cover := finiteTwoSheetedCover
  spin31IsConnectedDoubleCover := True
  spin31IsConnectedDoubleCoverProof := trivial
  targetIsProperOrthochronousLorentzGroup := True
  targetIsProperOrthochronousLorentzGroupProof := trivial
  lieAlgebraMapIsIsomorphism := True
  lieAlgebraMapIsIsomorphismProof := trivial
  actionPreservesMinkowskiQuadraticForm := True
  actionPreservesMinkowskiQuadraticFormProof := trivial
  orientationAndTimeOrientationPreserved := True
  orientationAndTimeOrientationPreservedProof := trivial
  algebraicSurface := finiteQuaternionStrictSpinCover
  spinCarrierAgreement := rfl
  lorentzCarrierAgreement := rfl
  algebraicAndContinuousMapsAgree := True
  algebraicAndContinuousMapsAgreeProof := trivial

/-- Explicitly: the record is inhabited by a witness whose carrier is the
eight-element quaternion group and whose "connected double cover" obligation is
literally `True`. -/
theorem continuous_cover_interface_vacuous :
    ∃ C : ContinuousSpin31LorentzCover,
      C.Spin31.Carrier = Q8 ∧ C.spin31IsConnectedDoubleCover = True :=
  ⟨vacuousContinuousCover, rfl, rfl⟩

end Synthesis.SpinCoverBridge
