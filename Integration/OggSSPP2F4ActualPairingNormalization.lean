import Integration.OggSSPP2F4ActualGroupBasis
import Integration.OggSSPP2F4ActualGroupShearReflection

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

end Integration.OggSSPP2F4ActualPairingNormalization
