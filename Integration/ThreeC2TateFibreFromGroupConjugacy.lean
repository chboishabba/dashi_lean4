import Integration.C2TateTransportFromGroupConjugacy
import Integration.ThreeC2TateFibreCycle

/-!
# Three C2 Tate fibres from one order-three group transporter

This file pays the generic compiler for gate A'.  Given an additive group
representation `ρ`, three involution labels `a,b,c`, and one element `r` with

  r*a = b*r,
  r*b = c*r,
  r*c = a*r,
  r*r*r = 1,

the action of `r` automatically supplies all three additive intertwiners and
the cycle coherence required by `ThreeC2TateFibreCycle`.

Thus the remaining Monster-specific obligation is source acquisition: the
actual local-group action on the integral Moonshine carrier.  No separate Tate
transport maps need to be invented once that representation is available.
-/

namespace Integration.ThreeC2TateFibreFromGroupConjugacy

namespace G := Integration.C2TateTransportFromGroupConjugacy
namespace T := Integration.ThreeC2TateFibreCycle

variable {Γ M : Type*} [Group Γ] [AddCommGroup M]

structure OrderThreeConjugacyCycleSource (ρ : Γ →* (M ≃+ M)) where
  a : Γ
  b : Γ
  c : Γ
  r : Γ

  r_a : r * a = b * r
  r_b : r * b = c * r
  r_c : r * c = a * r
  r_cubed : r * r * r = 1

namespace OrderThreeConjugacyCycleSource

variable (ρ : Γ →* (M ≃+ M))

/-- The order-three group relation gives order-three transport on the carrier. -/
theorem transport_cubed
    (S : OrderThreeConjugacyCycleSource ρ)
    (x : M) :
    ρ S.r (ρ S.r (ρ S.r x)) = x := by
  have hρ : ρ (S.r * S.r * S.r) = ρ (1 : Γ) := congrArg ρ S.r_cubed
  have hx := congrArg (fun e : M ≃+ M => e x) hρ
  simpa using hx

/-- Compile the actual group-level source into the existing generic
three-fibre Tate cycle. -/
def toThreeFibreCycleData
    (S : OrderThreeConjugacyCycleSource ρ) :
    T.ThreeFibreCycleData (M0 := M) (M1 := M) (M2 := M) where
  g0 := G.actionAddHom ρ S.a
  g1 := G.actionAddHom ρ S.b
  g2 := G.actionAddHom ρ S.c

  phi01 := G.actionAddEquiv ρ S.r
  phi12 := G.actionAddEquiv ρ S.r
  phi20 := G.actionAddEquiv ρ S.r

  intertwine01 := G.intertwines_of_group_relation ρ S.r_a
  intertwine12 := G.intertwines_of_group_relation ρ S.r_b
  intertwine20 := G.intertwines_of_group_relation ρ S.r_c

  cycleCoherent := transport_cubed ρ S

/-- Gate A' compilation theorem: an actual local representation plus the
order-three conjugacy source immediately gives the complete three-fibre Tate
transport object. -/
theorem group_source_pays_generic_three_fibre_transport
    (S : OrderThreeConjugacyCycleSource ρ) :
    ∃ D : T.ThreeFibreCycleData (M0 := M) (M1 := M) (M2 := M),
      ∀ x : M,
        D.phi20 (D.phi12 (D.phi01 x)) = x := by
  refine ⟨toThreeFibreCycleData ρ S, ?_⟩
  intro x
  exact transport_cubed ρ S x

end OrderThreeConjugacyCycleSource

end Integration.ThreeC2TateFibreFromGroupConjugacy
