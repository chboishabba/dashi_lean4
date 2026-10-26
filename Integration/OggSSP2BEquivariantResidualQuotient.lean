/-!
# Equivariance descends through a surjective quotient

The post-Brauer norm weld repeatedly uses the following elementary fact.
Suppose

  pi : M -> V
  r  : M -> S
  f  : V -> S

with `pi` surjective and `f (pi x) = r x`.  If `pi` and `r` are equivariant for
the same source action, then `f` is equivariant.  Hence the induced residual
map on the 24-dimensional quotient does not need a separate equivariance
payment once the actual quotient chart and source-native residual coordinate
are equivariant.

This owner is deliberately representation-agnostic: concrete Co1 actions are
supplied downstream, while this file owns only the factor-through theorem.
-/

namespace Integration.OggSSP2BEquivariantResidualQuotient

/-- Pointwise equivariance for a declared pair of actions.  Group laws are not
needed for the descent argument itself. -/
def Equivariant {G X Y : Type*}
    (actX : G → X → X) (actY : G → Y → Y) (f : X → Y) : Prop :=
  ∀ g x, f (actX g x) = actY g (f x)

/-- Equivariance is inherited by the descended map through any surjective
quotient presentation. -/
theorem equivariant_of_surjective_descent
    {G M V S : Type*}
    (pi : M → V)
    (residual : M → S)
    (descended : V → S)
    (pi_surjective : Function.Surjective pi)
    (descent : ∀ x, descended (pi x) = residual x)
    {actM : G → M → M}
    {actV : G → V → V}
    {actS : G → S → S}
    (pi_equivariant : Equivariant actM actV pi)
    (residual_equivariant : Equivariant actM actS residual) :
    Equivariant actV actS descended := by
  intro g v
  rcases pi_surjective v with ⟨x, rfl⟩
  calc
    descended (actV g (pi x)) = descended (pi (actM g x)) := by
      rw [pi_equivariant g x]
    _ = residual (actM g x) := descent _
    _ = actS g (residual x) := residual_equivariant g x
    _ = actS g (descended (pi x)) := by rw [descent x]

/-- The same theorem packaged as a proof-relevant receipt for downstream
compilers. -/
structure EquivariantDescentReceipt
    {G M V S : Type*}
    (pi : M → V)
    (residual : M → S)
    (descended : V → S)
    (actM : G → M → M)
    (actV : G → V → V)
    (actS : G → S → S) : Prop where
  pi_surjective : Function.Surjective pi
  descent : ∀ x, descended (pi x) = residual x
  pi_equivariant : Equivariant actM actV pi
  residual_equivariant : Equivariant actM actS residual

namespace EquivariantDescentReceipt

variable {G M V S : Type*}
variable {pi : M → V} {residual : M → S} {descended : V → S}
variable {actM : G → M → M} {actV : G → V → V} {actS : G → S → S}

/-- A receipt contains exactly enough data to derive the quotient-map
equivariance. -/
theorem descended_equivariant
    (r : EquivariantDescentReceipt pi residual descended actM actV actS) :
    Equivariant actV actS descended :=
  equivariant_of_surjective_descent
    pi residual descended r.pi_surjective r.descent
    r.pi_equivariant r.residual_equivariant

end EquivariantDescentReceipt

end Integration.OggSSP2BEquivariantResidualQuotient
