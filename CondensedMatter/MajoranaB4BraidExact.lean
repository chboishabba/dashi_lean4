import Mathlib

namespace CondensedMatter

inductive BraidSign
  | plus | minus
  deriving DecidableEq, Repr

def BraidSign.flip : BraidSign → BraidSign
  | .plus => .minus
  | .minus => .plus

inductive Majorana4
  | gamma1 | gamma2 | gamma3 | gamma4
  deriving DecidableEq, Repr

structure SignedMajorana4 where
  sign : BraidSign
  mode : Majorana4
  deriving DecidableEq, Repr

def SignedMajorana4.negate : SignedMajorana4 → SignedMajorana4
  | ⟨s,m⟩ => ⟨s.flip,m⟩

def applyOuterSign4 : BraidSign → SignedMajorana4 → SignedMajorana4
  | .plus, x => x
  | .minus, x => x.negate

def sigma1Basis4 : Majorana4 → SignedMajorana4
  | .gamma1 => ⟨.plus,.gamma2⟩
  | .gamma2 => ⟨.minus,.gamma1⟩
  | .gamma3 => ⟨.plus,.gamma3⟩
  | .gamma4 => ⟨.plus,.gamma4⟩

def sigma2Basis4 : Majorana4 → SignedMajorana4
  | .gamma1 => ⟨.plus,.gamma1⟩
  | .gamma2 => ⟨.plus,.gamma3⟩
  | .gamma3 => ⟨.minus,.gamma2⟩
  | .gamma4 => ⟨.plus,.gamma4⟩

def sigma3Basis4 : Majorana4 → SignedMajorana4
  | .gamma1 => ⟨.plus,.gamma1⟩
  | .gamma2 => ⟨.plus,.gamma2⟩
  | .gamma3 => ⟨.plus,.gamma4⟩
  | .gamma4 => ⟨.minus,.gamma3⟩

def sigma1_4 : SignedMajorana4 → SignedMajorana4
  | ⟨s,m⟩ => applyOuterSign4 s (sigma1Basis4 m)

def sigma2_4 : SignedMajorana4 → SignedMajorana4
  | ⟨s,m⟩ => applyOuterSign4 s (sigma2Basis4 m)

def sigma3_4 : SignedMajorana4 → SignedMajorana4
  | ⟨s,m⟩ => applyOuterSign4 s (sigma3Basis4 m)

theorem yangBaxter12_4 (x : SignedMajorana4) :
    sigma1_4 (sigma2_4 (sigma1_4 x)) =
    sigma2_4 (sigma1_4 (sigma2_4 x)) := by
  rcases x with ⟨s,m⟩
  cases s <;> cases m <;> rfl

theorem yangBaxter23_4 (x : SignedMajorana4) :
    sigma2_4 (sigma3_4 (sigma2_4 x)) =
    sigma3_4 (sigma2_4 (sigma3_4 x)) := by
  rcases x with ⟨s,m⟩
  cases s <;> cases m <;> rfl

theorem farCommutation13_4 (x : SignedMajorana4) :
    sigma1_4 (sigma3_4 x) = sigma3_4 (sigma1_4 x) := by
  rcases x with ⟨s,m⟩
  cases s <;> cases m <;> rfl

theorem adjacent12_noncommuting_4 :
    ¬ (∀ x : SignedMajorana4,
        sigma1_4 (sigma2_4 x) = sigma2_4 (sigma1_4 x)) := by
  intro h
  have hx := h ⟨.plus,.gamma1⟩
  simp [sigma1_4, sigma2_4, sigma1Basis4, sigma2Basis4, applyOuterSign4] at hx

inductive B4Generator
  | s1 | s2 | s3
  deriving DecidableEq, Repr

def applyB4Generator : B4Generator → SignedMajorana4 → SignedMajorana4
  | .s1 => sigma1_4
  | .s2 => sigma2_4
  | .s3 => sigma3_4

end CondensedMatter
