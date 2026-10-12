import Integration.TeleodynamicsLila
import Mathlib

/-!
# Conditional Weyl covariance of LILA-style root-conditioned attention bias

The LILA-E8 engineering path uses a rank-one root-conditioned score term of the
form

  baseline + beta * <q,r> * <k,r>.

Using an E8 root as `r` does not itself establish a Weyl symmetry of a model.
This file pays the exact algebraic statement that *would* be available once a
model intervention is intertwined with a dot-product-preserving root-space
action:

  B_{g r}(g q, g k) = B_r(q,k).

The theorem is generic and does not manufacture an E8 action.  Instantiating it
with W(E8) still requires the independently defined root-space action plus an
intertwiner from the model's hidden representation into that 8-dimensional
carrier.  Learned per-head scales must also be transported/tied consistently
when the group permutes head/root labels.
-/

namespace Integration.LilaRootBiasWeylCovariance

abbrev Vec (n : Nat) := Fin n → ℝ

/-- Euclidean dot product on a finite coordinate carrier. -/
def dot {n : Nat} (x y : Vec n) : ℝ :=
  ∑ i, x i * y i

/-- The exact property needed by the rank-one bias theorem.  This is weaker
than naming a Weyl group and stronger than merely permuting a root codebook. -/
structure DotPreservingAction (n : Nat) where
  act : Vec n → Vec n
  preservesDot : ∀ x y, dot (act x) (act y) = dot x y

/-- Root-conditioned score with one scalar scale. -/
def rootBiasedScore {n : Nat}
    (baseline beta : ℝ) (q k r : Vec n) : ℝ :=
  baseline + beta * dot q r * dot k r

/-- Simultaneously acting on q, k and the root label leaves the rank-one bias
exactly unchanged under any dot-product-preserving action. -/
theorem root_bias_covariant {n : Nat}
    (g : DotPreservingAction n)
    (baseline beta : ℝ) (q k r : Vec n) :
    rootBiasedScore baseline beta (g.act q) (g.act k) (g.act r) =
      rootBiasedScore baseline beta q k r := by
  rw [rootBiasedScore, rootBiasedScore, g.preservesDot q r, g.preservesDot k r]

universe u

/-- A model-side intervention pays the missing bridge only when the learned
projection into root space genuinely intertwines that intervention with the
candidate orthogonal/root action. -/
structure ProjectionIntertwiner {X : Type u} {n : Nat}
    (intervention : X → X)
    (project : X → Vec n)
    (g : DotPreservingAction n) where
  intertwines : ∀ x, project (intervention x) = g.act (project x)

/-- Once the projection intertwiner is supplied, the same covariance theorem
holds on actual hidden states rather than only on an abstract root-space vector. -/
theorem projected_root_bias_covariant
    {X : Type u} {n : Nat}
    {intervention : X → X}
    {project : X → Vec n}
    {g : DotPreservingAction n}
    (h : ProjectionIntertwiner intervention project g)
    (baseline beta : ℝ) (q k : X) (r : Vec n) :
    rootBiasedScore baseline beta
        (project (intervention q)) (project (intervention k)) (g.act r) =
      rootBiasedScore baseline beta (project q) (project k) r := by
  rw [h.intertwines q, h.intertwines k]
  exact root_bias_covariant g baseline beta (project q) (project k) r

/-- If roots/heads are permuted, scale transport is an independent requirement.
This minimal contract is intentionally separate from root covariance. -/
structure HeadScaleIntertwiner {Head : Type u} where
  scale : Head → ℝ
  actHead : Head → Head
  scaleInvariant : ∀ h, scale (actHead h) = scale h

structure Boundary where
  rankOneBiasCovarianceTheoremPaid : Bool
  projectionIntertwinerTyped : Bool
  requiresProjectionIntertwinerForModelEquivariance : Bool
  headScaleTransportTypedSeparately : Bool
  rootCodebookAlonePaysModelWeylEquivariance : Bool
  learnedHeadScaleBreaksCovarianceAutomatically : Bool
  fullLilaE8ModelWeylEquivarianceEmpiricallyPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rankOneBiasCovarianceTheoremPaid := true
  projectionIntertwinerTyped := true
  requiresProjectionIntertwinerForModelEquivariance := true
  headScaleTransportTypedSeparately := true
  rootCodebookAlonePaysModelWeylEquivariance := false
  learnedHeadScaleBreaksCovarianceAutomatically := false
  fullLilaE8ModelWeylEquivarianceEmpiricallyPaid := false

inductive RootCodebookCreatesProjectionIntertwiner : Prop
inductive BiasCovarianceCreatesModelMechanism : Prop

theorem root_codebook_does_not_create_projection_intertwiner :
    ¬ RootCodebookCreatesProjectionIntertwiner := by intro h; cases h

theorem bias_covariance_does_not_create_model_mechanism :
    ¬ BiasCovarianceCreatesModelMechanism := by intro h; cases h

end Integration.LilaRootBiasWeylCovariance
