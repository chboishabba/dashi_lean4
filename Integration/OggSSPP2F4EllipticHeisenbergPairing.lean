import Mathlib
import Integration.OggSSPP2F4ActualGroupShearReflection
import Integration.Base369Heisenberg
import Integration.OggSSPP2TernaryHeisenbergAction

/-!
# Same-object finite Heisenberg pairing on the actual Banerjee elliptic group

Use the established *additive equivalence of actual Mathlib points*

   E(F4) ≃+ (ZMod 3 × ZMod 3)

to pull back the rank-one 3-Heisenberg commutator form.  This construction
does NOT claim that the resulting form has been identified with the intrinsic
algebraic-geometric Weil pairing e_3.  That identification is an independent,
source-dependent theorem.

The transported genuine elliptic-group shear preserves the pairing, while
the transported Frobenius reflection negates it.  The already-existing
Schrödinger representation accordingly has a centre-preserving shear and a
centre-inverting, conjugate-linear reflection; no Monster 3B recognition or
exceptional exponent follows from this.
-/

namespace Integration.OggSSPP2F4EllipticHeisenbergPairing

namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace Basis := Integration.OggSSPP2F4ActualGroupBasis
namespace Action := Integration.OggSSPP2F4ActualGroupShearReflection
namespace H := Integration.Base369Heisenberg

abbrev F3 := ZMod 3
abbrev CurveGroup := E.ActualCurveGroup

/-- Coordinates of an actual elliptic point in the proved P,Q basis. -/
noncomputable def coords (p : CurveGroup) : F3 × F3 :=
  Basis.actualC3SquareAddEquiv.symm p

theorem coords_add (p q : CurveGroup) :
    coords (p+q) = coords p + coords q := by
  exact Basis.actualC3SquareAddEquiv.symm.map_add p q

theorem coords_zero : coords (0 : CurveGroup) = (0,0) := by
  exact Basis.actualC3SquareAddEquiv.symm.map_zero

theorem coords_neg (p : CurveGroup) :
    coords (-p) = -coords p :=
  Basis.actualC3SquareAddEquiv.symm.map_neg p

/-- Sign convention matches the repository's Heisenberg omega = y*x' - y'*x. -/
noncomputable def pairing (p q : CurveGroup) : F3 :=
  (coords p).2 * (coords q).1 - (coords q).2 * (coords p).1

theorem pairing_alternating (p : CurveGroup) :
    pairing p p = 0 := by
  simp [pairing]

theorem pairing_skew (p q : CurveGroup) :
    pairing p q = - pairing q p := by
  simp [pairing]
  ring

theorem pairing_add_left (p q r : CurveGroup) :
    pairing (p+q) r = pairing p r + pairing q r := by
  simp only [pairing, coords_add, Prod.fst_add, Prod.snd_add]
  ring

theorem pairing_add_right (p q r : CurveGroup) :
    pairing p (q+r) = pairing p q + pairing p r := by
  simp only [pairing, coords_add, Prod.fst_add, Prod.snd_add]
  ring

/--
Genuine rank-one Heisenberg lift of an actual elliptic point; its central
coordinate is zero, so this is a section of the Heisenberg quotient, NOT
a homomorphism into the nonabelian central extension.
-/
noncomputable def heisenbergLift (p : CurveGroup) : H.H 1 where
  x := fun _ => (coords p).1
  y := fun _ => (coords p).2
  z := 0

theorem heisenbergLift_omega (p q : CurveGroup) :
    H.omega (heisenbergLift p) (heisenbergLift q) =
      pairing p q := by
  simp [H.omega, H.dot, heisenbergLift, pairing, Fin.sum_univ_one]

/-- The commutator of the lifts is central, with the transported pairing. -/
theorem heisenberg_commutator_of_curve_points (p q : CurveGroup) :
    heisenbergLift p * heisenbergLift q *
      (heisenbergLift p)⁻¹ * (heisenbergLift q)⁻¹
      = ⟨0, 0, pairing p q⟩ := by
  rw [H.commutator_eq, heisenbergLift_omega]

theorem coords_frobenius_model (p : CurveGroup) :
    coords (Action.actualFrobeniusModel p) =
      Action.frobeniusMatrix (coords p) := by
  change Basis.actualC3SquareAddEquiv.symm
      (Basis.actualC3SquareAddEquiv (Action.frobeniusMatrix (coords p))) =
      Action.frobeniusMatrix (coords p)
  exact Basis.actualC3SquareAddEquiv.symm_apply_apply _

theorem coords_shear_model (p : CurveGroup) :
    coords (Action.actualShearModel p) =
      Action.shearMatrix (coords p) := by
  change Basis.actualC3SquareAddEquiv.symm
      (Basis.actualC3SquareAddEquiv (Action.shearMatrix (coords p))) =
      Action.shearMatrix (coords p)
  exact Basis.actualC3SquareAddEquiv.symm_apply_apply _

/-- The transported actual-group shear preserves the Heisenberg commutator. -/
theorem pairing_shear (p q : CurveGroup) :
    pairing (Action.actualShearModel p) (Action.actualShearModel q) =
      pairing p q := by
  simp only [pairing, coords_shear_model, Action.shearMatrix_apply]
  ring

/-- The transported actual-group Frobenius model inverts the centre. -/
theorem pairing_frobenius (p q : CurveGroup) :
    pairing (Action.actualFrobeniusModel p)
      (Action.actualFrobeniusModel q) = -pairing p q := by
  simp only [pairing, coords_frobenius_model, Action.frobeniusMatrix_apply]
  ring

/-- An explicit nontrivial central commutator, from the *actual* elliptic P,Q. -/
theorem selected_generators_pairing :
    pairing
      (Basis.actualC3SquareAddEquiv (1,0))
      (Basis.actualC3SquareAddEquiv (0,1)) = -1 := by
  simp [pairing, coords]

theorem pairing_nontrivial :
    pairing
      (Basis.actualC3SquareAddEquiv (1,0))
      (Basis.actualC3SquareAddEquiv (0,1)) ≠ 0 := by
  rw [selected_generators_pairing]
  norm_num

/--
Coordinate-level nondegeneracy of the transported form, on actual elliptic
group points.  We exhibit either basis point as a detector for a nonzero
coordinate, without requiring an external Weil-pairing theorem.
-/
theorem pairing_nondegenerate {p : CurveGroup} (hp : p ≠ 0) :
    ∃ q : CurveGroup, pairing p q ≠ 0 := by
  have hc : coords p ≠ (0,0) := by
    intro h
    apply hp
    apply Basis.actualC3SquareAddEquiv.symm.injective
    simpa [coords] using h
  by_cases ha : (coords p).1 = 0
  · have hb : (coords p).2 ≠ 0 := by
      intro hb
      apply hc
      exact Prod.ext ha hb
    refine ⟨Basis.actualC3SquareAddEquiv (1,0), ?_⟩
    simp [pairing, coords, hb]
  · refine ⟨Basis.actualC3SquareAddEquiv (0,1), ?_⟩
    simp [pairing, coords, ha]


structure Boundary where
  actualEllipticGroupBasisReused : Bool
  actualEllipticPairingBilinear : Bool
  actualHeisenbergCommutatorIdentified : Bool
  shearSymplectic : Bool
  FrobeniusAntisymplectic : Bool
  intrinsicWeilPairingIdentification : Bool
  VOAIntertwinerConstructed : Bool
  monsterExponentRecognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualEllipticGroupBasisReused := true
  actualEllipticPairingBilinear := true
  actualHeisenbergCommutatorIdentified := true
  shearSymplectic := true
  FrobeniusAntisymplectic := true
  intrinsicWeilPairingIdentification := false
  VOAIntertwinerConstructed := false
  monsterExponentRecognition := false

end Integration.OggSSPP2F4EllipticHeisenbergPairing
