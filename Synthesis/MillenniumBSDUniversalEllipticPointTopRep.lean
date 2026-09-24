import Synthesis.MillenniumBSDUniversalRankWeld
import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Topology.Instances.Discrete

/-!
# Universal full elliptic-point Galois representation

For every literal rational elliptic curve E, this module constructs the
actual discrete G_Q-module E(Qbar) directly on mathlib's affine point group
after base change to AlgebraicClosure Q.

This is known object-level plumbing, not BSD: the absolute Galois group acts
through the generic affine point map attached to each Q-algebra automorphism
of Qbar.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open ContRepresentation

abbrev UniversalRatAlgClosure := AlgebraicClosure ℚ

noncomputable abbrev rationalEllipticCurveAlgClosure
    (E : RationalEllipticCurve) :
    WeierstrassCurve UniversalRatAlgClosure :=
  E.1.baseChange UniversalRatAlgClosure

noncomputable abbrev rationalEllipticCurveAlgClosurePoint
    (E : RationalEllipticCurve) : Type :=
  (rationalEllipticCurveAlgClosure E).toAffine.Point

noncomputable instance rationalEllipticCurveAlgClosurePointTopologicalSpace
    (E : RationalEllipticCurve) :
    TopologicalSpace (rationalEllipticCurveAlgClosurePoint E) :=
  ⊥

instance rationalEllipticCurveAlgClosurePointDiscreteTopology
    (E : RationalEllipticCurve) :
    DiscreteTopology (rationalEllipticCurveAlgClosurePoint E) :=
  ⟨rfl⟩

noncomputable instance rationalEllipticCurveAlgClosurePointIsTopologicalAddGroup
    (E : RationalEllipticCurve) :
    IsTopologicalAddGroup (rationalEllipticCurveAlgClosurePoint E) := by
  letI : E.1.IsElliptic := E.2
  infer_instance

noncomputable instance rationalEllipticCurveAlgClosurePointContinuousSMul
    (E : RationalEllipticCurve) :
    ContinuousSMul ℤ (rationalEllipticCurveAlgClosurePoint E) := by
  letI : E.1.IsElliptic := E.2
  infer_instance

/-- Galois action on the actual algebraic-closure point group. -/
noncomputable def rationalEllipticCurveAlgClosureGaloisAddHom
    (E : RationalEllipticCurve)
    (σ : RationalAbsoluteGalois) :
    rationalEllipticCurveAlgClosurePoint E →+
      rationalEllipticCurveAlgClosurePoint E := by
  letI : E.1.IsElliptic := E.2
  exact WeierstrassCurve.Affine.Point.map
    (W' := E.1.toAffine) σ.toAlgHom

@[simp] theorem rationalEllipticCurveAlgClosureGaloisAddHom_one
    (E : RationalEllipticCurve)
    (P : rationalEllipticCurveAlgClosurePoint E) :
    rationalEllipticCurveAlgClosureGaloisAddHom E
      (1 : RationalAbsoluteGalois) P = P := by
  letI : E.1.IsElliptic := E.2
  simpa [rationalEllipticCurveAlgClosureGaloisAddHom] using
    (WeierstrassCurve.Affine.Point.map_id
      (W' := E.1.toAffine) P)

theorem rationalEllipticCurveAlgClosureGaloisAddHom_mul
    (E : RationalEllipticCurve)
    (σ τ : RationalAbsoluteGalois)
    (P : rationalEllipticCurveAlgClosurePoint E) :
    rationalEllipticCurveAlgClosureGaloisAddHom E (σ * τ) P =
      rationalEllipticCurveAlgClosureGaloisAddHom E σ
        (rationalEllipticCurveAlgClosureGaloisAddHom E τ P) := by
  letI : E.1.IsElliptic := E.2
  simpa [rationalEllipticCurveAlgClosureGaloisAddHom,
    AlgEquiv.mul_apply] using
    (WeierstrassCurve.Affine.Point.map_map
      (W' := E.1.toAffine)
      τ.toAlgHom σ.toAlgHom P).symm

/-- Each Galois automorphism as a continuous Z-linear map. -/
noncomputable def rationalEllipticCurveAlgClosureGaloisCLM
    (E : RationalEllipticCurve)
    (σ : RationalAbsoluteGalois) :
    rationalEllipticCurveAlgClosurePoint E →L[ℤ]
      rationalEllipticCurveAlgClosurePoint E := by
  letI : E.1.IsElliptic := E.2
  exact
    { toLinearMap :=
        (rationalEllipticCurveAlgClosureGaloisAddHom E σ).toIntLinearMap
      cont := continuous_of_discreteTopology }

/-- The actual full E(Qbar) continuous representation for arbitrary E/Q. -/
noncomputable def rationalEllipticCurvePointContRepresentation
    (E : RationalEllipticCurve) :
    ContRepresentation ℤ RationalAbsoluteGalois
      (rationalEllipticCurveAlgClosurePoint E) := by
  letI : E.1.IsElliptic := E.2
  exact ContRepresentation.ofMonoidHom
    { toFun := fun σ => rationalEllipticCurveAlgClosureGaloisCLM E σ
      map_one' := by
        ext P
        exact rationalEllipticCurveAlgClosureGaloisAddHom_one E P
      map_mul' := by
        intro σ τ
        ext P
        exact rationalEllipticCurveAlgClosureGaloisAddHom_mul E σ τ P }

/-- Canonical actual full elliptic-point TopRep for every rational elliptic
curve. -/
noncomputable def rationalEllipticCurvePointRepresentation
    (E : RationalEllipticCurve) :
    TopRep ℤ RationalAbsoluteGalois :=
  TopRep.of (rationalEllipticCurvePointContRepresentation E)

/-- Uniform universal point-representation binding, now constructed rather
than supplied. -/
noncomputable def canonicalUniversalEllipticPointRepresentationBinding :
    RationalEllipticCurve → TopRep ℤ RationalAbsoluteGalois :=
  rationalEllipticCurvePointRepresentation

end Synthesis.Millennium.BSD
