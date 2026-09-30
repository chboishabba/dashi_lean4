import Integration.Selected3BCanonicalFixedLineProjection

/-!
# Canonical kernel constituent and transported action

This file removes the last *abstract retraction* ambiguity.  Given an actual
linear functional phi with phi(u)=1, the 196883-style complement is represented
by the literal submodule ker(phi).  The map

  p(v) = v - phi(v) u

is promoted to a linear retraction p : V -> ker(phi).  Any linear action fixing
u and preserving phi restricts to ker(phi), and projecting the full action of
an included kernel vector is definitionally the same restricted action.

This is the correct theorem behind the selected-3B projection lane.  To turn it
into a Monster theorem one still needs the source-native phi/u identification
for the actual weight-two representation and the selected same-element action;
no character/dimension argument is used here.
-/

namespace Integration.Selected3BKernelProjectionRestriction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace F := Integration.Selected3BCanonicalFixedLineProjection

def projectToKernel
    (phi : V →ₗ[ℝ] ℝ) (u : V) (hunit : phi u = 1) :
    V →ₗ[ℝ] LinearMap.ker phi where
  toFun v := ⟨F.removeFixedLine phi u v,
    F.removeFixedLine_in_kernel phi u hunit v⟩
  map_add' x y := by
    apply Subtype.ext
    simp [F.removeFixedLine, map_add, add_smul]
    module
  map_smul' c x := by
    apply Subtype.ext
    simp [F.removeFixedLine, map_smul, smul_sub, mul_smul]

def includeKernel (phi : V →ₗ[ℝ] ℝ) :
    LinearMap.ker phi →ₗ[ℝ] V :=
  (LinearMap.ker phi).subtype

theorem projectToKernel_leftInverse
    (phi : V →ₗ[ℝ] ℝ) (u : V) (hunit : phi u = 1)
    (w : LinearMap.ker phi) :
    projectToKernel phi u hunit (includeKernel phi w) = w := by
  apply Subtype.ext
  exact F.removeFixedLine_retracts_kernel phi u w.1 w.2

def restrictAction
    (phi : V →ₗ[ℝ] ℝ)
    (act : V →ₗ[ℝ] V)
    (hphi : ∀ v, phi (act v) = phi v) :
    LinearMap.ker phi →ₗ[ℝ] LinearMap.ker phi where
  toFun w := ⟨act w.1, by simpa [hphi] using w.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

theorem restrictAction_inclusion_intertwines
    (phi : V →ₗ[ℝ] ℝ)
    (act : V →ₗ[ℝ] V)
    (hphi : ∀ v, phi (act v) = phi v)
    (w : LinearMap.ker phi) :
    includeKernel phi (restrictAction phi act hphi w) =
      act (includeKernel phi w) := rfl

theorem projected_full_action_eq_restriction
    (phi : V →ₗ[ℝ] ℝ) (u : V) (hunit : phi u = 1)
    (act : V →ₗ[ℝ] V)
    (hphi : ∀ v, phi (act v) = phi v)
    (w : LinearMap.ker phi) :
    projectToKernel phi u hunit
      (act (includeKernel phi w))
      =
    restrictAction phi act hphi w := by
  apply Subtype.ext
  exact F.removeFixedLine_retracts_kernel
    phi u (act w.1) (by simpa [hphi] using w.2)

theorem projected_action_is_independent_of_projection_choice
    (phi : V →ₗ[ℝ] ℝ) (u : V) (hunit : phi u = 1)
    (act : V →ₗ[ℝ] V)
    (hphi : ∀ v, phi (act v) = phi v)
    (w : LinearMap.ker phi) :
    (projectToKernel phi u hunit)
        (act ((LinearMap.ker phi).subtype w))
      =
    restrictAction phi act hphi w :=
  projected_full_action_eq_restriction phi u hunit act hphi w

end Integration.Selected3BKernelProjectionRestriction
