import Synthesis.MillenniumBSDSplitActualSignCocycleExact

namespace DASHI.BSD.SplitTangent
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

def SplitCoefficients.cycle {a b c : F} (h : SplitCoefficients W a b c) :
    SplitCoefficients W b c a where
  a1_zero := h.a1_zero
  a3_zero := h.a3_zero
  a2_eq := by rw [h.a2_eq]; ring
  a4_eq := by rw [h.a4_eq]; ring
  a6_eq := by rw [h.a6_eq]; ring

/-- The reverse half is literally invariant under cyclic relabeling,
including the nonsingularity proof carried by Mathlib's affine point. -/
theorem reverseHalfPoint_cycle (a b c : F) (h : SplitCoefficients W a b c)
    (x r s t : F) (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c) :
    reverseHalfPoint W b c a (h.cycle W) x s t r hs ht hr =
      reverseHalfPoint W a b c h x r s t hr hs ht := by
  unfold reverseHalfPoint
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor <;> simp [reverseHalfX,reverseHalfY,pairSum] <;> ring

/-- The second even sign address on the SAME original point group. -/
theorem reverseHalf_second_sign (a b c : F) (h : SplitCoefficients W a b c)
    (x r s t : F) (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hba : b≠a) (hbc : b≠c) :
    reverseHalfPoint W a b c h x (-r) s (-t)
      (by simpa using hr) hs (by simpa using ht) -
      reverseHalfPoint W a b c h x r s t hr hs ht =
      splitRootPoint W b c a (h.cycle W) := by
  have he := reverseHalf_evenFlip_actual_add W b c a (h.cycle W)
    x s t r hs ht hr hbc hba
  rw [reverseHalfPoint_cycle W a b c h, reverseHalfPoint_cycle W a b c h] at he
  rw [he]
  abel

/-- The third even sign address, via the second cyclic relabeling. -/
theorem reverseHalf_third_sign (a b c : F) (h : SplitCoefficients W a b c)
    (x r s t : F) (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hca : c≠a) (hcb : c≠b) :
    reverseHalfPoint W a b c h x (-r) (-s) t
      (by simpa using hr) (by simpa using hs) ht -
      reverseHalfPoint W a b c h x r s t hr hs ht =
      splitRootPoint W c a b ((h.cycle W).cycle W) := by
  have he := reverseHalf_second_sign W b c a (h.cycle W)
    x s t r hs ht hr hcb hca
  rw [reverseHalfPoint_cycle W a b c h, reverseHalfPoint_cycle W a b c h] at he
  exact he

/-- All actual nonexceptional split sign rows give one of the four
point-group differences. The identity row remains explicit. -/
theorem actual_split_sign_difference (a b c : F) (h : SplitCoefficients W a b c)
    (σ : F ≃+* F) (x r s t : F)
    (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hr0 : r≠0) (hs0 : s≠0) (ht0 : t≠0)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hr2 : σ (r^2)=r^2) (hs2 : σ (s^2)=s^2) (ht2 : σ (t^2)=t^2)
    (hp : σ (r*s*t)=r*s*t) :
    let D := reverseHalfPoint W a b c h x (σ r) (σ s) (σ t)
      (by rw [← map_pow,hr2,hr]) (by rw [← map_pow,hs2,hs])
      (by rw [← map_pow,ht2,ht]) -
      reverseHalfPoint W a b c h x r s t hr hs ht
    D=0 ∨ D=splitRootPoint W a b c h ∨
      D=splitRootPoint W b c a (h.cycle W) ∨
      D=splitRootPoint W c a b ((h.cycle W).cycle W) := by
  dsimp
  rcases actual_root_galois_rows σ r s t hr0 hs0 ht0 hr2 hs2 ht2 hp with
    h0|h1|h2|h3
  · rcases h0 with ⟨h1,h2,h3⟩
    left
    simp [h1,h2,h3]
  · rcases h1 with ⟨h1,h2,h3⟩
    right; left
    exact actual_first_sign_cocycle W a b c h σ x r s t hr hs ht hab hac h1 h2 h3
  · rcases h2 with ⟨h1,h2,h3⟩
    right; right; left
    simpa only [h1,h2,h3] using
      reverseHalf_second_sign W a b c h x r s t hr hs ht hab.symm hbc
  · rcases h3 with ⟨h1,h2,h3⟩
    right; right; right
    simpa only [h1,h2,h3] using
      reverseHalf_third_sign W a b c h x r s t hr hs ht hac.symm hbc.symm

end
end DASHI.BSD.SplitTangent
