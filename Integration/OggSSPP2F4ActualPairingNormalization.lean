import Integration.OggSSPP2F4ActualGroupBasis
import Integration.OggSSPP2F4ActualGroupShearReflection
import Integration.Base369Heisenberg

/-!
# Actual elliptic-group alternating form, via the proved additive chart

The existing AddEquiv
  (ZMod 3 × ZMod 3) ≃+ E(F₄)
makes the explicit rank-two alternating form a pairing ON THE ACTUAL
Mathlib elliptic point group. This is an independently checkable
algebraic object, not yet Mathlib's intrinsic geometric Weil pairing.

For the intrinsic Weil pairing e₃, the remaining normalization data are
its construction and the nontrivial phase e₃(P,Q). Nondegeneracy and
bilinearity of an independently supplied e₃ then determine orientation.
Do not replace that obligation by an equality of cardinalities.
-/

namespace Integration.OggSSPP2F4ActualPairingNormalization

namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace Basis := Integration.OggSSPP2F4ActualGroupBasis
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace Act := Integration.OggSSPP2F4ActualGroupShearReflection

abbrev F3 := ZMod 3
abbrev Plane := F3 × F3

def planeOmega (v w : Plane) : F3 :=
  v.1 * w.2 - v.2 * w.1

def ellipticOmega (p q : E.ActualCurveGroup) : F3 :=
  planeOmega (Basis.actualC3SquareAddEquiv.symm p)
    (Basis.actualC3SquareAddEquiv.symm q)

theorem planeOmega_add_left (v w u : Plane) :
    planeOmega (v+w) u = planeOmega v u + planeOmega w u := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  rcases u with ⟨e,f⟩
  dsimp [planeOmega]
  ring

theorem planeOmega_add_right (v w u : Plane) :
    planeOmega v (w+u) = planeOmega v w + planeOmega v u := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  rcases u with ⟨e,f⟩
  dsimp [planeOmega]
  ring

theorem planeOmega_alternating (v : Plane) :
    planeOmega v v = 0 := by
  simp [planeOmega]

theorem planeOmega_skew (v w : Plane) :
    planeOmega v w = -planeOmega w v := by
  dsimp [planeOmega]
  ring

theorem planeOmega_nondegenerate
    (v : Plane) (h : ∀ w : Plane, planeOmega v w = 0) :
    v = 0 := by
  rcases v with ⟨a,b⟩
  have ha := h (0,1)
  have hb := h (1,0)
  have ha0 : a = 0 := by simpa [planeOmega] using ha
  have hb0 : b = 0 := by
    have hneg : -b = 0 := by simpa [planeOmega] using hb
    exact neg_eq_zero.mp hneg
  exact Prod.ext ha0 hb0

theorem ellipticOmega_add_left
    (p q u : E.ActualCurveGroup) :
    ellipticOmega (p+q) u =
      ellipticOmega p u + ellipticOmega q u := by
  simp only [ellipticOmega, Basis.actualC3SquareAddEquiv.symm.map_add]
  exact planeOmega_add_left _ _ _

theorem ellipticOmega_add_right
    (p q u : E.ActualCurveGroup) :
    ellipticOmega p (q+u) =
      ellipticOmega p q + ellipticOmega p u := by
  simp only [ellipticOmega, Basis.actualC3SquareAddEquiv.symm.map_add]
  exact planeOmega_add_right _ _ _

theorem ellipticOmega_alternating (p : E.ActualCurveGroup) :
    ellipticOmega p p = 0 :=
  planeOmega_alternating _

theorem ellipticOmega_skew (p q : E.ActualCurveGroup) :
    ellipticOmega p q = -ellipticOmega q p :=
  planeOmega_skew _ _

theorem ellipticOmega_nondegenerate
    (p : E.ActualCurveGroup)
    (h : ∀ q : E.ActualCurveGroup, ellipticOmega p q = 0) :
    p = 0 := by
  have hs :
      Basis.actualC3SquareAddEquiv.symm p = (0,0) := by
    apply planeOmega_nondegenerate
    intro v
    have hv := h (Basis.actualC3SquareAddEquiv v)
    simpa [ellipticOmega] using hv
  calc
    p = Basis.actualC3SquareAddEquiv
        (Basis.actualC3SquareAddEquiv.symm p) :=
      (Basis.actualC3SquareAddEquiv.apply_symm_apply p).symm
    _ = 0 := by simpa [hs] using
      (Basis.actualC3SquareAddEquiv.map_zero)

theorem ellipticOmega_P_Q :
    ellipticOmega G.P G.Q = 1 := by
  rw [← Basis.actualC3SquareAddEquiv_first,
    ← Basis.actualC3SquareAddEquiv_second]
  simp [ellipticOmega, planeOmega]

theorem ellipticOmega_Q_P :
    ellipticOmega G.Q G.P = -1 := by
  rw [ellipticOmega_skew, ellipticOmega_P_Q]

theorem planeOmega_shear (v w : Plane) :
    planeOmega (Act.shearMatrix v) (Act.shearMatrix w)
      = planeOmega v w := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  dsimp [planeOmega, Act.shearMatrix]
  ring

theorem planeOmega_reflection (v w : Plane) :
    planeOmega (Act.frobeniusMatrix v) (Act.frobeniusMatrix w)
      = -planeOmega v w := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  dsimp [planeOmega, Act.frobeniusMatrix]
  ring

theorem ellipticOmega_shearModel (p q : E.ActualCurveGroup) :
    ellipticOmega (Act.actualShearModel p) (Act.actualShearModel q)
      = ellipticOmega p q := by
  change planeOmega
      (Act.shearMatrix (Basis.actualC3SquareAddEquiv.symm p))
      (Act.shearMatrix (Basis.actualC3SquareAddEquiv.symm q))
      =
    planeOmega (Basis.actualC3SquareAddEquiv.symm p)
      (Basis.actualC3SquareAddEquiv.symm q)
  exact planeOmega_shear _ _

theorem ellipticOmega_frobeniusModel (p q : E.ActualCurveGroup) :
    ellipticOmega (Act.actualFrobeniusModel p)
      (Act.actualFrobeniusModel q) = -ellipticOmega p q := by
  change planeOmega
      (Act.frobeniusMatrix (Basis.actualC3SquareAddEquiv.symm p))
      (Act.frobeniusMatrix (Basis.actualC3SquareAddEquiv.symm q))
      =
    -planeOmega (Basis.actualC3SquareAddEquiv.symm p)
      (Basis.actualC3SquareAddEquiv.symm q)
  exact planeOmega_reflection _ _

/-- The open geometric identification is a proposition, not a Boolean:
an independently constructed intrinsic Weil pairing must be shown equal
to this normalized elliptic form after choosing its P,Q phase. -/
def IntrinsicWeilPairingMatch (e3 : E.ActualCurveGroup →
    E.ActualCurveGroup → F3) : Prop :=
  ∀ p q, e3 p q = ellipticOmega p q


/-!
## Universality of the normalized alternating pairing

An *independently supplied* alternating biadditive pairing on the actual
elliptic group is determined by its value at (P,Q). This is the exact
arithmetic API needed for the intrinsic Weil pairing after its geometric
construction, and prevents an unjustified choice of cube-root orientation.
-/

def ellipticOmegaRightHom (p : E.ActualCurveGroup) :
    E.ActualCurveGroup →+ F3 where
  toFun := ellipticOmega p
  map_zero' := by simp [ellipticOmega, planeOmega]
  map_add' q u := ellipticOmega_add_right p q u

def ellipticOmegaHom :
    E.ActualCurveGroup →+ (E.ActualCurveGroup →+ F3) where
  toFun := ellipticOmegaRightHom
  map_zero' := by
    ext q
    simp [ellipticOmegaRightHom, ellipticOmega, planeOmega]
  map_add' p q := by
    ext u
    exact ellipticOmega_add_left p q u

/-- An additive map from the actual elliptic group is determined by the
images of P and Q. No nine-label group law is imported. -/
theorem actual_addHom_ext_PQ
    {A : Type*} [AddCommGroup A]
    (f g : E.ActualCurveGroup →+ A)
    (hP : f G.P = g G.P)
    (hQ : f G.Q = g G.Q) :
    f = g := by
  ext p
  obtain ⟨⟨a,b⟩,rfl⟩ := Basis.chartHom_bijective.2 p
  change f (G.candidateChart a b) = g (G.candidateChart a b)
  simp [G.candidateChart, map_add, map_nsmul, hP, hQ]

theorem alternating_biadditive_skew
    (β : E.ActualCurveGroup →+ (E.ActualCurveGroup →+ F3))
    (hAlt : ∀ p : E.ActualCurveGroup, β p p = 0)
    (p q : E.ActualCurveGroup) :
    β p q = -(β q p) := by
  have hsum := hAlt (p+q)
  have hp := hAlt p
  have hq := hAlt q
  change (β p p + β p q) + (β q p + β q q) = 0 at hsum
  rw [hp,hq] at hsum
  dsimp at hsum
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm, add_left_comm, add_assoc] using hsum)

/-- The entire pairing is fixed by the P,Q phase. This is a uniqueness
theorem, NOT a construction of the geometric Weil pairing. -/
theorem normalized_pairing_unique
    (β : E.ActualCurveGroup →+ (E.ActualCurveGroup →+ F3))
    (hAlt : ∀ p : E.ActualCurveGroup, β p p = 0)
    (hOrientation : β G.P G.Q = 1) :
    β = ellipticOmegaHom := by
  apply actual_addHom_ext_PQ
  · apply actual_addHom_ext_PQ
    · simpa [ellipticOmegaHom, ellipticOmegaRightHom] using
        (hAlt G.P).trans (ellipticOmega_alternating G.P).symm
    · simpa [ellipticOmegaHom, ellipticOmegaRightHom,
        ellipticOmega_P_Q] using hOrientation
  · apply actual_addHom_ext_PQ
    · have hqp : β G.Q G.P = -1 := by
        rw [alternating_biadditive_skew β hAlt, hOrientation]
      simpa [ellipticOmegaHom, ellipticOmegaRightHom,
        ellipticOmega_Q_P] using hqp
    · simpa [ellipticOmegaHom, ellipticOmegaRightHom] using
        (hAlt G.Q).trans (ellipticOmega_alternating G.Q).symm

/-- When the chosen geometric phase is inverse to the fixed F3 phase,
the normalized form changes sign rather than being silently identified. -/
theorem inverted_orientation_pairing_unique
    (β : E.ActualCurveGroup →+ (E.ActualCurveGroup →+ F3))
    (hAlt : ∀ p : E.ActualCurveGroup, β p p = 0)
    (hOrientation : β G.P G.Q = -1) :
    ∀ p q, β p q = -ellipticOmega p q := by
  let βneg : E.ActualCurveGroup →+ (E.ActualCurveGroup →+ F3) := -β
  have hAltNeg : ∀ p : E.ActualCurveGroup, βneg p p = 0 := by
    intro p
    simpa [βneg] using congrArg Neg.neg (hAlt p)
  have hphase : βneg G.P G.Q = 1 := by
    change -(β G.P G.Q) = 1
    rw [hOrientation]
    simp
  have heq := normalized_pairing_unique βneg hAltNeg hphase
  intro p q
  have h := congrArg (fun f : E.ActualCurveGroup →+
      (E.ActualCurveGroup →+ F3) => f p q) heq
  change -(β p q) = ellipticOmega p q at h
  exact (neg_eq_iff_eq_neg).mp h

/-- An intrinsic Weil pairing transported via a primitive phase is
identified with the finite form if it satisfies the genuine alternating
biadditive laws and its selected P,Q orientation. -/
theorem intrinsicWeilMatch_of_normalized_biadditive
    (β : E.ActualCurveGroup →+ (E.ActualCurveGroup →+ F3))
    (hAlt : ∀ p : E.ActualCurveGroup, β p p = 0)
    (hPhase : β G.P G.Q = 1) :
    IntrinsicWeilPairingMatch (fun p q => β p q) := by
  intro p q
  have h := normalized_pairing_unique β hAlt hPhase
  exact congrArg (fun f : E.ActualCurveGroup →+
      (E.ActualCurveGroup →+ F3) => f p q) h


/-!
## Native Heisenberg commutator orientation

The repository's Schrödinger-compatible cocycle uses
  omega_native(g,h) = <y_g,x_h> - <y_h,x_g>,
which is the NEGATIVE of the elliptic P,Q orientation
  omega_PQ((a,b),(c,d)) = a*d-b*c.
This minus sign cannot be omitted when transporting a geometric e₃ phase
through the native Heisenberg and VOA owners.
-/

def rankOneAxis (v : Plane) : Integration.Base369Heisenberg.H 1 :=
  ⟨(fun _ => v.1), (fun _ => v.2), 0⟩

theorem rankOneAxis_commutator_orientation (v w : Plane) :
    Integration.Base369Heisenberg.omega (rankOneAxis v) (rankOneAxis w)
      = -planeOmega v w := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp only [rankOneAxis, Integration.Base369Heisenberg.omega,
    Integration.Base369Heisenberg.dot, Fin.sum_univ_one]
  dsimp [planeOmega]
  ring

theorem ellipticOmega_eq_neg_nativeHeisenbergCommutator
    (p q : E.ActualCurveGroup) :
    ellipticOmega p q =
      -Integration.Base369Heisenberg.omega
        (rankOneAxis (Basis.actualC3SquareAddEquiv.symm p))
        (rankOneAxis (Basis.actualC3SquareAddEquiv.symm q)) := by
  rw [rankOneAxis_commutator_orientation]
  simp [ellipticOmega]

end Integration.OggSSPP2F4ActualPairingNormalization
