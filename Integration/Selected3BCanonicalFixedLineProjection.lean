import Mathlib

/-!
# Canonical fixed-line removal for a 1 + W representation

A finite-dimensional Griess representation is known abstractly to
split into its invariant one-dimensional line and the 196883 constituent
in characteristic zero. This owner provides a *constructive* retraction
given a fixed unit u and an invariant normalized functional phi.

p(v) = v - phi(v) u  is in ker phi,
p(w)=w for w in ker phi,
and p intertwines any linear automorphism fixing u and phi.

It deliberately does not assert that the selected repository constituent
is ker(phi), or that its selected 3B action equals the actual Monster
restriction: both are independent same-source obligations.
-/

namespace Integration.Selected3BCanonicalFixedLineProjection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def removeFixedLine (phi : V →ₗ[ℝ] ℝ) (u v : V) : V :=
  v - (phi v) • u

theorem removeFixedLine_in_kernel
    (phi : V →ₗ[ℝ] ℝ) (u : V) (hunit : phi u = 1) (v : V) :
    phi (removeFixedLine phi u v) = 0 := by
  simp [removeFixedLine, map_sub, map_smul, hunit]

theorem removeFixedLine_retracts_kernel
    (phi : V →ₗ[ℝ] ℝ) (u v : V) (hv : phi v = 0) :
    removeFixedLine phi u v = v := by
  simp [removeFixedLine, hv]

theorem removeFixedLine_kills_unit
    (phi : V →ₗ[ℝ] ℝ) (u : V) (hunit : phi u = 1) :
    removeFixedLine phi u u = 0 := by
  simp [removeFixedLine, hunit]

theorem removeFixedLine_equivariant
    (phi : V →ₗ[ℝ] ℝ) (u : V)
    (act : V →ₗ[ℝ] V)
    (hunit : act u = u)
    (hphi : ∀ v, phi (act v) = phi v)
    (v : V) :
    removeFixedLine phi u (act v) =
      act (removeFixedLine phi u v) := by
  simp [removeFixedLine, hphi, map_sub, map_smul, hunit]

theorem action_preserves_kernel
    (phi : V →ₗ[ℝ] ℝ)
    (act : V →ₗ[ℝ] V)
    (hphi : ∀ v, phi (act v) = phi v)
    (v : V) (hv : phi v = 0) :
    phi (act v) = 0 := by
  simpa [hphi] using hv

end Integration.Selected3BCanonicalFixedLineProjection
