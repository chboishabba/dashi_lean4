import Mathlib.RepresentationTheory.Basic
import Integration.OggSSP2BCentralizerNormEquivariance

/-!
# Integral/source centralizer action -> Tate quotient action

This removes an avoidable formal-instantiation layer from the 2B same-object
programme.  One representation of the selected 2B centralizer on the source
carrier, together with the defining commutation relation with the selected
involution `a`, automatically preserves the norm range `range (1+a)`.
Mathlib's quotient-representation constructor then gives the action on the Tate
cokernel.  No separate hand-written action on plus/minus/cokernel coordinates is
scientifically required.

Attribution boundary:
* Carnahan owns the external Monster-stable integral Moonshine form/action.
* the statement that elements of `C_M(a)` commute with `a` is group-theoretic;
* Mathlib owns the generic quotient representation construction;
* DASHI owns this compiler packaging for the 2B proof spine.

This file is representation-agnostic and does not assert that the external
Moonshine carrier itself has already been instantiated as Lean data.
-/

namespace Integration.OggSSP2BIntegralCentralizerTateAction

namespace Norm := Integration.OggSSP2BCentralizerNormEquivariance

variable (K G V : Type*)
  [Semiring K] [Group G]
  [AddCommMonoid V] [Module K V]

/-- The only action datum needed before passing to the `C₂` Tate quotient:
a group representation and a selected involution commuting with every action
operator.  For the intended application `G` is the selected 2B centralizer. -/
structure IntegralCentralizerActionData where
  rho : Representation K G V
  selectedInvolution : V →ₗ[K] V
  centralizer_commutes :
    ∀ g : G, (rho g).comp selectedInvolution = selectedInvolution.comp (rho g)

namespace IntegralCentralizerActionData

variable {K G V : Type*}
  [Semiring K] [Group G]
  [AddCommMonoid V] [Module K V]

/-- Source-native norm range for the selected involution. -/
def normRange (d : IntegralCentralizerActionData K G V) : Submodule K V :=
  (Norm.normMap d.selectedInvolution).range

/-- Every centralizer operator preserves the norm range.  This is the exact
hypothesis required by `Representation.quotient`. -/
theorem normRange_stable
    (d : IntegralCentralizerActionData K G V) (g : G) :
    d.normRange ≤ d.normRange.comap (d.rho g) := by
  rintro y ⟨x, rfl⟩
  change d.rho g (Norm.normMap d.selectedInvolution x) ∈
    (Norm.normMap d.selectedInvolution).range
  refine ⟨d.rho g x, ?_⟩
  have h := congrArg
    (fun f : V →ₗ[K] V => f x)
    (Norm.norm_commutes d.selectedInvolution (d.rho g)
      (d.centralizer_commutes g))
  exact h.symm

/-- The centralizer action on the Tate quotient is compiler output, not an
independent source acquisition. -/
def tateQuotientRepresentation
    (d : IntegralCentralizerActionData K G V) :
    Representation K G (V ⧸ d.normRange) :=
  d.rho.quotient d.normRange d.normRange_stable

/-- Public max-cut statement: one source representation commuting with the
selected involution already determines the quotient action functorially. -/
theorem quotient_action_is_not_an_independent_leaf
    (d : IntegralCentralizerActionData K G V) :
    Nonempty (Representation K G (V ⧸ d.normRange)) :=
  ⟨d.tateQuotientRepresentation⟩

end IntegralCentralizerActionData

end Integration.OggSSP2BIntegralCentralizerTateAction
