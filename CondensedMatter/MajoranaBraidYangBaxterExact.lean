import Mathlib

namespace CondensedMatter

/-!
Exact signed-generator representation of the three-Majorana braid action.

sigma1 : gamma1 ↦ gamma2, gamma2 ↦ -gamma1, gamma3 ↦ gamma3
sigma2 : gamma1 ↦ gamma1, gamma2 ↦ gamma3, gamma3 ↦ -gamma2

We prove inverse laws, the B3 Artin/Yang-Baxter relation, and an explicit
noncommutativity witness.
-/

inductive Sign
  | plus
  | minus
  deriving DecidableEq, Repr

def Sign.flip : Sign → Sign
  | .plus => .minus
  | .minus => .plus

inductive Majorana3
  | gamma1
  | gamma2
  | gamma3
  deriving DecidableEq, Repr

structure SignedMajorana where
  sign : Sign
  mode : Majorana3
  deriving DecidableEq, Repr

def SignedMajorana.negate : SignedMajorana → SignedMajorana
  | ⟨s, m⟩ => ⟨s.flip, m⟩

def applyOuterSign : Sign → SignedMajorana → SignedMajorana
  | .plus, x => x
  | .minus, x => x.negate

def sigma1Basis : Majorana3 → SignedMajorana
  | .gamma1 => ⟨.plus, .gamma2⟩
  | .gamma2 => ⟨.minus, .gamma1⟩
  | .gamma3 => ⟨.plus, .gamma3⟩

def sigma2Basis : Majorana3 → SignedMajorana
  | .gamma1 => ⟨.plus, .gamma1⟩
  | .gamma2 => ⟨.plus, .gamma3⟩
  | .gamma3 => ⟨.minus, .gamma2⟩

def sigma1 : SignedMajorana → SignedMajorana
  | ⟨s, m⟩ => applyOuterSign s (sigma1Basis m)

def sigma2 : SignedMajorana → SignedMajorana
  | ⟨s, m⟩ => applyOuterSign s (sigma2Basis m)

def sigma1InvBasis : Majorana3 → SignedMajorana
  | .gamma1 => ⟨.minus, .gamma2⟩
  | .gamma2 => ⟨.plus, .gamma1⟩
  | .gamma3 => ⟨.plus, .gamma3⟩

def sigma2InvBasis : Majorana3 → SignedMajorana
  | .gamma1 => ⟨.plus, .gamma1⟩
  | .gamma2 => ⟨.minus, .gamma3⟩
  | .gamma3 => ⟨.plus, .gamma2⟩

def sigma1Inv : SignedMajorana → SignedMajorana
  | ⟨s, m⟩ => applyOuterSign s (sigma1InvBasis m)

def sigma2Inv : SignedMajorana → SignedMajorana
  | ⟨s, m⟩ => applyOuterSign s (sigma2InvBasis m)

theorem sigma1_inverse_left (x : SignedMajorana) :
    sigma1Inv (sigma1 x) = x := by
  rcases x with ⟨s, m⟩
  cases s <;> cases m <;> rfl

theorem sigma1_inverse_right (x : SignedMajorana) :
    sigma1 (sigma1Inv x) = x := by
  rcases x with ⟨s, m⟩
  cases s <;> cases m <;> rfl

theorem sigma2_inverse_left (x : SignedMajorana) :
    sigma2Inv (sigma2 x) = x := by
  rcases x with ⟨s, m⟩
  cases s <;> cases m <;> rfl

theorem sigma2_inverse_right (x : SignedMajorana) :
    sigma2 (sigma2Inv x) = x := by
  rcases x with ⟨s, m⟩
  cases s <;> cases m <;> rfl

theorem yangBaxterB3 (x : SignedMajorana) :
    sigma1 (sigma2 (sigma1 x)) =
    sigma2 (sigma1 (sigma2 x)) := by
  rcases x with ⟨s, m⟩
  cases s <;> cases m <;> rfl

theorem sigma1_sigma2_noncommuting :
    ¬ (∀ x : SignedMajorana, sigma1 (sigma2 x) = sigma2 (sigma1 x)) := by
  intro h
  have hx := h ⟨.plus, .gamma1⟩
  simp [sigma1, sigma2, sigma1Basis, sigma2Basis, applyOuterSign] at hx

theorem sigma1_square_gamma1 :
    sigma1 (sigma1 ⟨.plus, .gamma1⟩) = ⟨.minus, .gamma1⟩ := rfl

theorem sigma1_square_gamma2 :
    sigma1 (sigma1 ⟨.plus, .gamma2⟩) = ⟨.minus, .gamma2⟩ := rfl

theorem sigma1_square_gamma3 :
    sigma1 (sigma1 ⟨.plus, .gamma3⟩) = ⟨.plus, .gamma3⟩ := rfl

end CondensedMatter
