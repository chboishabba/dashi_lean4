import Welds.PNPBooleanFibreExact

namespace PNPBooleanSeparator
open scoped BigOperators
open PNPLiveMassPartition PNPEndpointClippedOccupancy

-- General fibre product using the actual boundary maps, not a product
-- of unrelated feasible projections.
def Compatible {X Y D : Type*} (l : X → D) (r : Y → D) :=
  {p : X × Y // l p.1 = r p.2}

def joinEquiv {X Y D : Type*} (l : X → D) (r : Y → D) :
    Compatible l r ≃ (Σ s : D, Fibre l s × Fibre r s) where
  toFun p := ⟨l p.val.1,⟨⟨p.val.1,rfl⟩,⟨p.val.2,p.property.symm⟩⟩⟩
  invFun p := ⟨(p.2.1.val,p.2.2.val),p.2.1.property.trans p.2.2.property.symm⟩
  left_inv p := by cases p; rfl
  right_inv p := by
    rcases p with ⟨s,⟨⟨x,hx⟩,⟨y,hy⟩⟩⟩
    subst s
    rfl

theorem joinCard {X Y D : Type*} (l : X → D) (r : Y → D)
    [Fintype D] [Fintype (Compatible l r)]
    [∀ s : D, Fintype (Fibre l s)] [∀ s : D, Fintype (Fibre r s)] :
    Fintype.card (Compatible l r) =
      ∑ s : D, Fintype.card (Fibre l s)*Fintype.card (Fibre r s) := by
  classical
  rw [Fintype.card_congr (joinEquiv l r),Fintype.card_sigma]
  simp only [Fintype.card_prod]

theorem clippedJoinCard {X Y D : Type*} (l : X → D) (r : Y → D)
    [Fintype D] [Fintype (Compatible l r)]
    [∀ s : D, Fintype (Fibre l s)] [∀ s : D, Fintype (Fibre r s)] :
    clip (Fintype.card (Compatible l r)) =
      clip (∑ s : D, clip (Fintype.card (Fibre l s))*clip (Fintype.card (Fibre r s))) := by
  rw [joinCard]
  calc
    clip (∑ s : D, Fintype.card (Fibre l s)*Fintype.card (Fibre r s)) =
      clip (∑ s : D, clip (Fintype.card (Fibre l s)*Fintype.card (Fibre r s))) :=
        clip_sum Finset.univ _
    _ = clip (∑ s : D, clip (clip (Fintype.card (Fibre l s))*clip (Fintype.card (Fibre r s)))) := by
      apply congrArg clip
      apply Finset.sum_congr rfl
      intro s _
      exact clip_mul _ _
    _ = _ := (clip_sum Finset.univ _).symm

-- Shared assignments appear exactly once in the original carrier.
-- Private coordinates are disjoint by construction (product of
-- independent carriers); predicates may use the same boundary.
def Joint {D X Y : Type*} (P : D → X → Prop) (Q : D → Y → Prop) :=
  {p : D × (X × Y) // P p.1 p.2.1 ∧ Q p.1 p.2.2}

def conditionedEquiv {D X Y : Type*} (P : D → X → Prop) (Q : D → Y → Prop) :
    Joint P Q ≃ (Σ s : D, {x : X // P s x} × {y : Y // Q s y}) where
  toFun p := ⟨p.val.1,⟨⟨p.val.2.1,p.property.1⟩,⟨p.val.2.2,p.property.2⟩⟩⟩
  invFun p := ⟨(p.1,(p.2.1.val,p.2.2.val)),⟨p.2.1.property,p.2.2.property⟩⟩
  left_inv p := by rcases p with ⟨⟨s,x,y⟩,h⟩; rfl
  right_inv p := by rcases p with ⟨s,⟨⟨x,hx⟩,⟨y,hy⟩⟩⟩; rfl

theorem conditionedCard {D X Y : Type*} (P : D → X → Prop) (Q : D → Y → Prop)
    [Fintype D] [Fintype (Joint P Q)]
    [∀ s : D, Fintype {x : X // P s x}]
    [∀ s : D, Fintype {y : Y // Q s y}] :
    Fintype.card (Joint P Q) =
      ∑ s : D, Fintype.card {x : X // P s x} * Fintype.card {y : Y // Q s y} := by
  classical
  rw [Fintype.card_congr (conditionedEquiv P Q),Fintype.card_sigma]
  simp only [Fintype.card_prod]

-- Scope transport: no factor is allowed to inspect omitted private
-- coordinates. Actual affine support checks instantiate this premise.
def DependsOn {X K : Type*} (key : X → K) (p : X → Prop) : Prop :=
  ∀ x y, key x=key y → (p x ↔ p y)

theorem factor_merge {X K : Type*} (key : X → K) (p q : X → Prop)
    (hp : DependsOn key p) (hq : DependsOn key q) :
    DependsOn key (fun x => p x ∧ q x) := by
  intro x y h
  exact and_congr (hp x y h) (hq x y h)

-- The weighted bucket retirement law. All factors not reading the
-- retired coordinate are pulled outside the exact finite sum.
theorem retire_weight {D B : Type*} [Fintype B]
    (owned : D → B → Nat) (rest : D → Nat) (s : D) :
    (∑ b : B, owned s b*rest s) = (∑ b : B, owned s b)*rest s := by
  rw [Finset.sum_mul]

theorem clipped_retire (a b c d : Nat) :
    clip (a*b+c*d) = clip (clip a*clip b+clip c*clip d) := by
  calc
    clip (a*b+c*d) = clip (clip (a*b)+clip (c*d)) := clip_add _ _
    _ = clip (clip (clip a*clip b)+clip (clip c*clip d)) := by
      rw [← clip_mul a b,← clip_mul c d]
    _ = _ := (clip_add _ _).symm

-- Actual affine chart receiver, with a supplied and verified split of
-- its original free coordinates and pulled-back factors.
theorem originalConditionedCard {n d : Nat} (F : PNPBooleanFibre.Bits n → Prop)
    (free : Fin d → Fin n) (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ)
    (derived : ∀ x, F x → ∀ j,
      PNPOriginalModularIncidence.emb ℚ (x j)=
        PNPBooleanFibre.value a B (fun k => x (free k)) j)
    (freeExact : ∀ u k, PNPBooleanFibre.value a B u (free k)=
      PNPOriginalModularIncidence.emb ℚ (u k))
    {D X Y : Type*} (P : D → X → Prop) (Q : D → Y → Prop)
    (split : {u : PNPBooleanFibre.Bits d // PNPBooleanFibre.Valid F a B u} ≃ Joint P Q)
    [Fintype {x : PNPBooleanFibre.Bits n // F x}]
    [Fintype (Joint P Q)] [Fintype D]
    [∀ s : D, Fintype {x : X // P s x}]
    [∀ s : D, Fintype {y : Y // Q s y}] :
    Fintype.card {x : PNPBooleanFibre.Bits n // F x} =
      ∑ s : D, Fintype.card {x : X // P s x} * Fintype.card {y : Y // Q s y} := by
  rw [Fintype.card_congr ((PNPBooleanFibre.originalEquiv F free a B derived freeExact).trans split)]
  exact conditionedCard P Q

-- The supplied split and private-factor ownership must be extracted
-- from actual source scopes. These exact receivers do not establish a
-- uniformly logarithmic separator width or native machine clock.

end PNPBooleanSeparator
