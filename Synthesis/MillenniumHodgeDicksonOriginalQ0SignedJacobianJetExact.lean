import Synthesis.MillenniumHodgeDicksonOriginalCoupledTenDeckGeometryExact

/-!
Section32 original Dickson Q0 root geometry:
the signed six-root coordinate dField is EXACTLY the linear coefficient
in the root-variable finite difference of the selected original Q0
equation. On the original punctured product discriminant delta!=0,
every individual derivative is nonzero.

This is a local simple-root/etale candidate on the SAME original
coupled fibre and actual original y_i, not a global projective
smoothness, algebraic cycle, primitive pairing, or Hodge theorem.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

/-- True original Q0 first jet, exact for ALL steps h:
  Q0(a,s+h)-Q0(a,s) = h * (dField(a,s) - 2h).
No Taylor remainder assumption or external differential source. -/
theorem original_Q0_signed_first_jet
    (a s h : F) :
    Q0Field a (s+h) - Q0Field a s =
      h * (dField a s - 2*h) := by
  unfold Q0Field dField
  ring

/-- Original root-variable derivative coefficient in the same
selected Q0 polynomial, not a reconstructed synthetic derivative. -/
theorem original_Q0_signed_linearization
    (a s : F) :
    Q0Field a (s+1) - Q0Field a s + 2 = dField a s := by
  have h := original_Q0_signed_first_jet a s (1:F)
  simpa using h

/-- On an ACTUAL original Q0 root with nonzero six-fold signed
discriminant product, EVERY one of the six root-variable Jacobians
is nonzero, including the one chosen as the deck anchor.
This transports generic 5+5 deck geometry toward the legitimate
unramified part of the same original affine proper chart. -/
theorem original_Q0_generic_all_jacobians_nonzero
    (a y : Address → F) (δ : F)
    (hδ : δ ≠ 0)
    (p : ActualRootFibre a y δ) :
    ∀ i : Address, dField (a i) (p.1 i) ≠ 0 := by
  intro i
  exact signedFibre_nonzero
    ((actualRootFibreEquiv a y δ) p) hδ i

/-- The first-order original Q0 Jacobian product is the SAME
signed cover coordinate delta, not a separate scalar witness. -/
theorem original_Q0_signed_jacobian_product
    (a y : Address → F) (δ : F)
    (p : ActualRootFibre a y δ) :
    (∏ i, dField (a i) (p.1 i)) = δ := p.2.2

end
end DASHI.Hodge.DicksonCoupled
