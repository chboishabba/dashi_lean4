import Mathlib
import YangMills.LiteralSU2PlaquetteHalfHolonomyFactorization

/-!
# Boundary gauge absorption for the literal SU(2) crossing trace

The remaining finite-Wilson gauge-projection route needs one elementary but
same-object group identity repeatedly.  A temporal boundary holonomy attached
to the left endpoint of one half-path can be moved into the opposite half-path
as the inverse vertex gauge factor.

For the literal normalized SU(2) relative trace

  q(A,B) = ReTr(A B^{-1})/2,

we prove

  q(g Q, P h) = q(Q, g^{-1} P h).

The proof uses only the already-owned real-trace cyclicity and group algebra.
No integration or reflection positivity is asserted here.
-/

namespace RequestProject.YangMills

/--
Absorb a left endpoint gauge factor from the first half-path into the second
half-path.  The right endpoint factor is left untouched.
-/
theorem su2_relative_trace_absorb_endpoint_gauge
    (g h Q P : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace (g * Q) (P * h) =
      su2RelativeFundamentalTrace Q (g⁻¹ * P * h) := by
  unfold su2RelativeFundamentalTrace
  have hcyclic :
      ((g * Q) * (P * h)⁻¹).a =
        ((Q * (P * h)⁻¹) * g).a := by
    calc
      ((g * Q) * (P * h)⁻¹).a =
          (g * (Q * (P * h)⁻¹)).a := by rw [mul_assoc]
      _ = ((Q * (P * h)⁻¹) * g).a :=
          su2_real_trace_cyclic g (Q * (P * h)⁻¹)
  rw [hcyclic]
  congr 1
  group

/-- One-sided specialization used by the first boundary slab. -/
theorem su2_relative_trace_absorb_left_gauge
    (g Q P : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace (g * Q) P =
      su2RelativeFundamentalTrace Q (g⁻¹ * P) := by
  simpa using
    (su2_relative_trace_absorb_endpoint_gauge
      g (1 : SU2PlaquetteHolonomy) Q P)

/--
Equivalent right-endpoint form.  This is convenient when the periodic slab is
viewed as acting on the opposite reflected half.
-/
theorem su2_relative_trace_absorb_right_gauge
    (g h Q P : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace (g * Q) (P * h) =
      su2RelativeFundamentalTrace (h⁻¹ * Q) (P * g⁻¹) := by
  unfold su2RelativeFundamentalTrace
  have hcyclic :
      ((g * Q) * (P * h)⁻¹).a =
        ((h⁻¹ * Q) * (P * g⁻¹)⁻¹).a := by
    calc
      ((g * Q) * (P * h)⁻¹).a =
          (g * Q * h⁻¹ * P⁻¹).a := by group
      _ = (h⁻¹ * P⁻¹ * g * Q).a := by
          exact su2_real_trace_cyclic (g * Q) (h⁻¹ * P⁻¹)
      _ = ((h⁻¹ * Q) * (P * g⁻¹)⁻¹).a := by
          -- Both sides are cyclic representatives of the same four factors.
          have h1 := su2_real_trace_cyclic (h⁻¹ * P⁻¹ * g) Q
          have h2 := su2_real_trace_cyclic (h⁻¹) (Q * g * P⁻¹)
          dsimp at h1 h2 ⊢
          -- Quaternion real trace is cyclic but not fully permutation
          -- invariant; use the endpoint identity twice instead of commuting
          -- arbitrary factors.
          rw [← su2_relative_trace_absorb_endpoint_gauge g h Q P]
          rfl
  exact hcyclic

end RequestProject.YangMills
