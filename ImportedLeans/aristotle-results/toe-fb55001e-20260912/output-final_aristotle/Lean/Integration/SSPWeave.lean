import Integration.TernaryHub
import AgdaMirror.MonsterOntos

/-!
# The lawful SSP weave: an algebra that the 15-prime layer *does* preserve

`Integration.MonsterFifteen` records that the hyperfabric support map onto the
Monster mask geometry is non-expansive but neither isometric, injective, nor a
homomorphism.  Those are statements about one specific Boolean observer.  They
say nothing about whether the SSP-indexed layer carries preserved algebra, and
in fact it does: `DASHI/Biology/SSPIndexedWeaveHyperfabricExact.agda` equips the
fifteen lanes with a path algebra and proves its transport functorial.  This file
mirrors that structure and adds what the source leaves implicit.

* `FibreOrientation` = `inverse | mediated | forward` with `composeOrientation`;
  `compose_id_left/right`, `compose_assoc` — a **monoid**, with `mediated` as the
  unit (`instMonoidFibreOrientation`).
* `not_a_group` — it is not a group: `forward` is a non-unit idempotent, so
  nothing composes with it to give the unit.  (The source calls `forward` "the
  identity inside the nontrivial transport component"; this pins down what that
  can and cannot mean.)
* `orientationSign_hom` — the universal quotient: the sign map onto `ℤ/2` is a
  monoid homomorphism, and `laneAction_factors_through_sign` shows the lane
  action factors through it.  So the *effective* symmetry group of the weave is
  `ℤ/2`, acting by polarity reversal.
* `transportSSP_comp`, `transportSSP_id` — **the preservation theorem**:
  `T_{q ∘ p} = T_q ∘ T_p`, i.e. the SSP path algebra acts, indexed by the
  fifteen lanes and independent of the endpoints.
* `laneBal_action` — transported into the ternary hub's balanced coordinate the
  action is multiplication by `±1`: an equivariance/preservation statement in
  `ZMod 3` rather than a table.
* `laneStateHub` — the lane-state carrier is the ternary hub itself, with the
  `inverse` action **equal** to the hub's polarity involution (level-iv
  transport).

Scope: `SSP` is the corpus's fifteen-element enumeration of the supersingular
primes, used here purely as an index set; no statement about the Monster group,
moonshine or Hecke operators is made or implied.
-/

namespace Integration.SSPWeave

open Integration.Levels
open Integration.TernaryHub
open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.MonsterOntos (SSP)

/-! ## The orientation monoid -/

/-- Mirror of `DASHI.Biology.SignedSSPFRACTRANWeaveExact.FibreOrientation`. -/
inductive FibreOrientation | inverse | mediated | forward
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `SSPIndexedWeaveHyperfabricExact.composeOrientation`. -/
def composeOrientation : FibreOrientation → FibreOrientation → FibreOrientation
  | .mediated, o => o
  | .forward, .mediated => .forward
  | .inverse, .mediated => .inverse
  | .forward, .forward => .forward
  | .forward, .inverse => .inverse
  | .inverse, .forward => .inverse
  | .inverse, .inverse => .forward

theorem compose_id_left (o : FibreOrientation) : composeOrientation .mediated o = o := rfl

theorem compose_id_right (o : FibreOrientation) : composeOrientation o .mediated = o := by
  cases o <;> rfl

theorem compose_assoc (r q p : FibreOrientation) :
    composeOrientation (composeOrientation r q) p =
      composeOrientation r (composeOrientation q p) := by
  revert r q p; decide

instance instMonoidFibreOrientation : Monoid FibreOrientation where
  mul := composeOrientation
  one := .mediated
  mul_assoc := compose_assoc
  one_mul := compose_id_left
  mul_one := compose_id_right

/-- **Boundary: the orientation monoid is not a group.**  `forward` is an
idempotent different from the unit, so it has no inverse. -/
theorem not_a_group : ¬ ∀ g : FibreOrientation, ∃ h, composeOrientation g h = .mediated := by
  decide

/-- The two-element subset `{forward, inverse}` *is* a group: `forward` is its
unit and `inverse` is an involution. -/
theorem forward_inverse_group :
    composeOrientation .forward .forward = FibreOrientation.forward ∧
      composeOrientation .forward .inverse = FibreOrientation.inverse ∧
      composeOrientation .inverse .inverse = FibreOrientation.forward := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## The universal `ℤ/2` quotient -/

/-- The sign of an orientation: `inverse` reverses polarity, the other two do
not. -/
def orientationSign : FibreOrientation → ZMod 2
  | .inverse => 1 | .mediated => 0 | .forward => 0

/-- The sign is a monoid homomorphism onto `ℤ/2`. -/
theorem orientationSign_hom (q p : FibreOrientation) :
    orientationSign (composeOrientation q p) = orientationSign q + orientationSign p := by
  revert q p; decide

theorem orientationSign_surjective : Function.Surjective orientationSign := by decide

/-! ## Lane states, the action, and its functoriality -/

/-- Mirror of `SSPHyperfibreSymmetryTowerExact.LaneState`. -/
inductive LaneState | negative | mediatedState | positive
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `laneOrientationAction`. -/
def laneAction : FibreOrientation → LaneState → LaneState
  | .inverse, .negative => .positive
  | .inverse, .mediatedState => .mediatedState
  | .inverse, .positive => .negative
  | .mediated, s => s
  | .forward, s => s

/-- Mirror of the Agda's `SSPWeavePath`: a path between two lanes is an
orientation.  The lane indices are retained so that the composition law is the
Agda's, rather than a bare monoid multiplication. -/
structure SSPWeavePath (source target : SSP) where
  /-- The orientation carried by the path. -/
  orientation : FibreOrientation
  deriving DecidableEq, Repr

/-- The identity path. -/
def idPath (lane : SSP) : SSPWeavePath lane lane := ⟨.mediated⟩

/-- Path composition. -/
def thenSSP {s m t : SSP} (q : SSPWeavePath m t) (p : SSPWeavePath s m) : SSPWeavePath s t :=
  ⟨composeOrientation q.orientation p.orientation⟩

theorem thenSSP_id_left {s t : SSP} (p : SSPWeavePath s t) : thenSSP (idPath t) p = p := by
  cases p; rfl

theorem thenSSP_id_right {s t : SSP} (p : SSPWeavePath s t) : thenSSP p (idPath s) = p := by
  obtain ⟨o⟩ := p; cases o <;> rfl

theorem thenSSP_assoc {i j k l : SSP} (r : SSPWeavePath k l) (q : SSPWeavePath j k)
    (p : SSPWeavePath i j) :
    thenSSP (thenSSP r q) p = thenSSP r (thenSSP q p) := by
  obtain ⟨r⟩ := r; obtain ⟨q⟩ := q; obtain ⟨p⟩ := p
  exact congrArg SSPWeavePath.mk (compose_assoc r q p)

/-- Transport of a lane state along a path. -/
def transportSSP {s t : SSP} (p : SSPWeavePath s t) (x : LaneState) : LaneState :=
  laneAction p.orientation x

theorem transportSSP_id (lane : SSP) (x : LaneState) : transportSSP (idPath lane) x = x := rfl

/-- The action is a monoid action of the orientation monoid. -/
theorem laneAction_comp (q p : FibreOrientation) (x : LaneState) :
    laneAction (composeOrientation q p) x = laneAction q (laneAction p x) := by
  revert q p x; decide

/-- **The preservation theorem the corpus's SSP layer actually proves**: transport
is functorial, `T_{q ∘ p} = T_q ∘ T_p`. -/
theorem transportSSP_comp {s m t : SSP} (q : SSPWeavePath m t) (p : SSPWeavePath s m)
    (x : LaneState) :
    transportSSP (thenSSP q p) x = transportSSP q (transportSSP p x) :=
  laneAction_comp q.orientation p.orientation x

/-- The action factors through the sign: only the `ℤ/2` class of an orientation
matters. -/
theorem laneAction_factors_through_sign (g h : FibreOrientation) (x : LaneState) :
    orientationSign g = orientationSign h → laneAction g x = laneAction h x := by
  revert g h x; decide

/-! ## The lane-state carrier is the ternary hub -/

/-- The lane state in the hub's balanced coordinate. -/
def laneBal : LaneState → ZMod 3
  | .negative => -1 | .mediatedState => 0 | .positive => 1

/-- The lane-state carrier as the corpus's `Trit`. -/
def laneTritEquiv : LaneState ≃ Trit where
  toFun | .negative => .neg | .mediatedState => .zer | .positive => .pos
  invFun | .neg => .negative | .zer => .mediatedState | .pos => .positive
  left_inv := by decide
  right_inv := by decide

/-- **Level iv**: the lane-state carrier is the ternary hub, and the `inverse`
orientation acts as exactly the hub's polarity involution. -/
def laneStateHub : Transport LaneState Trit (laneAction .inverse) Trit.inv :=
  ⟨laneTritEquiv, by decide⟩

/-- Transported into the balanced coordinate, the action is multiplication by
`±1` according to the sign of the orientation. -/
theorem laneBal_action (g : FibreOrientation) (x : LaneState) :
    laneBal (laneAction g x) = (if orientationSign g = 0 then 1 else -1) * laneBal x := by
  revert g x; decide

/-- The residual of a path is its orientation (mirror of `sspResidualAfter`),
and the identity path has the mediated residual. -/
def residualAfter {s t : SSP} (p : SSPWeavePath s t) : FibreOrientation := p.orientation

theorem residualAfter_id (lane : SSP) : residualAfter (idPath lane) = .mediated := rfl

/-- Residuals compose by the same law as paths: the residual is a functor to the
orientation monoid, so the weave's bookkeeping is itself algebra-preserving. -/
theorem residualAfter_comp {s m t : SSP} (q : SSPWeavePath m t) (p : SSPWeavePath s m) :
    residualAfter (thenSSP q p) = composeOrientation (residualAfter q) (residualAfter p) := rfl

/-- Summary of the positive SSP row: a monoid, a functorial transport, an
effective `ℤ/2` symmetry, and the identification of the lane carrier with the
ternary hub — none of which is touched by any statement about the Boolean
support observer. -/
theorem ssp_weave_preservation :
    (∀ r q p : FibreOrientation, composeOrientation (composeOrientation r q) p =
        composeOrientation r (composeOrientation q p)) ∧
      (∀ {s m t : SSP} (q : SSPWeavePath m t) (p : SSPWeavePath s m) (x : LaneState),
        transportSSP (thenSSP q p) x = transportSSP q (transportSSP p x)) ∧
      (∀ q p, orientationSign (composeOrientation q p) =
        orientationSign q + orientationSign p) ∧
      (∀ x, laneTritEquiv (laneAction .inverse x) = Trit.inv (laneTritEquiv x)) :=
  ⟨compose_assoc, fun q p x => transportSSP_comp q p x, orientationSign_hom,
    laneStateHub.equivariant⟩

end Integration.SSPWeave
