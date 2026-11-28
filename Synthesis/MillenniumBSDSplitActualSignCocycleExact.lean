import Synthesis.MillenniumBSDSplitActualPointTorsionActionExact

namespace DASHI.BSD.SplitTangent
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

/-- The product-one sign constraint excludes exactly the odd rows. -/
theorem actual_even_sign_rows (a b c : F)
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1)
    (hc : c=1 ∨ c= -1) (hp : a*b*c=1) :
    (a=1 ∧ b=1 ∧ c=1) ∨ (a=1 ∧ b= -1 ∧ c= -1) ∨
    (a= -1 ∧ b=1 ∧ c= -1) ∨ (a= -1 ∧ b= -1 ∧ c=1) := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
    rcases hc with rfl|rfl <;> norm_num at hp ⊢

/-- The actual Galois ratios select one of the four geometric addresses,
without assuming a sign label or independent half. -/
theorem actual_root_galois_rows (σ : F ≃+* F) (r s t : F)
    (hr : r≠0) (hs : s≠0) (ht : t≠0)
    (hr2 : σ (r^2)=r^2) (hs2 : σ (s^2)=s^2) (ht2 : σ (t^2)=t^2)
    (hp : σ (r*s*t)=r*s*t) :
    (σ r=r ∧ σ s=s ∧ σ t=t) ∨
    (σ r=r ∧ σ s= -s ∧ σ t= -t) ∨
    (σ r= -r ∧ σ s=s ∧ σ t= -t) ∨
    (σ r= -r ∧ σ s= -s ∧ σ t=t) := by
  have hp' : rootSign σ r*rootSign σ s*rootSign σ t=1 := by
    unfold rootSign
    rw [map_mul,map_mul] at hp
    field_simp [hr,hs,ht] <;> linear_combination hp
  have h := actual_even_sign_rows _ _ _
    (rootSign_eq_one_or_neg_one σ r hr hr2)
    (rootSign_eq_one_or_neg_one σ s hs hs2)
    (rootSign_eq_one_or_neg_one σ t ht ht2) hp'
  have er := div_mul_cancel₀ (σ r) hr
  have es := div_mul_cancel₀ (σ s) hs
  have et := div_mul_cancel₀ (σ t) ht
  change rootSign σ r*r=σ r at er
  change rootSign σ s*s=σ s at es
  change rootSign σ t*t=σ t at et
  rcases h with h|h|h|h <;> rcases h with ⟨h₁,h₂,h₃⟩ <;>
    simp [h₁] at er <;> simp [h₂] at es <;> simp [h₃] at et <;>
    aesop

/-- On the nonexceptional split chart the first nontrivial actual
Galois row gives the original root point as a difference of halves.
The other root labels use the same theorem with cyclic relabeling.
Identification with the Weil pairing and nonsplit descent remains. -/
theorem actual_first_sign_cocycle (W : WeierstrassCurve F) [W.IsElliptic]
    (e0 e1 e2 : F) (h : SplitCoefficients W e0 e1 e2)
    (σ : F ≃+* F) (x r s t : F)
    (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2)
    (h01 : e0≠e1) (h02 : e0≠e2)
    (hσr : σ r=r) (hσs : σ s= -s) (hσt : σ t= -t) :
    reverseHalfPoint W e0 e1 e2 h x (σ r) (σ s) (σ t)
      (by simpa [hσr] using hr) (by simpa [hσs] using hs)
      (by simpa [hσt] using ht) -
      reverseHalfPoint W e0 e1 e2 h x r s t hr hs ht =
      splitRootPoint W e0 e1 e2 h := by
  have he := reverseHalf_evenFlip_actual_add W e0 e1 e2 h x r s t hr hs ht h01 h02
  simp only [hσr,hσs,hσt]
  rw [he]
  abel

end
end DASHI.BSD.SplitTangent
