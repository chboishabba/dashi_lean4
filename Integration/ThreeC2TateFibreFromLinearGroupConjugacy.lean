import Integration.ThreeC2TateFibreCycle

/-!
# Three C2 Tate fibres from a linear group representation

The original generic A' compiler works at the additive-group level because Tate
representative transport only needs additive equivalences.  The selected Q10
subquotient, however, is an F2-linear object.  For an actual module
representation there is no reason to forget that structure.

This file takes a representation

  rho : Gamma ->* (M ≃ₗ[R] M)

and the same order-three conjugacy relations and produces, in one object:

* the existing additive `ThreeFibreCycleData`;
* the three linear fibre equivalences agreeing definitionally/pointwise with
  the additive maps.

Hence F2-linearity of A' is compiled from the representation itself, not added
as a separate Monster-specific hypothesis.
-/

namespace Integration.ThreeC2TateFibreFromLinearGroupConjugacy

namespace T := Integration.ThreeC2TateFibreCycle

variable {R Γ M : Type*}
  [Semiring R] [Group Γ]
  [AddCommMonoid M] [Module R M]

structure OrderThreeLinearConjugacyCycleSource
    (ρ : Γ →* (M ≃ₗ[R] M)) where
  a : Γ
  b : Γ
  c : Γ
  r : Γ
  r_a : r * a = b * r
  r_b : r * b = c * r
  r_c : r * c = a * r
  r_cubed : r * r * r = 1

/-- Additive Tate cycle together with the retained linear maps. -/
structure LinearThreeFibreCycleData where
  additiveCycle : T.ThreeFibreCycleData (M0 := M) (M1 := M) (M2 := M)
  phi01Linear : M ≃ₗ[R] M
  phi12Linear : M ≃ₗ[R] M
  phi20Linear : M ≃ₗ[R] M
  phi01_agrees : ∀ x, additiveCycle.phi01 x = phi01Linear x
  phi12_agrees : ∀ x, additiveCycle.phi12 x = phi12Linear x
  phi20_agrees : ∀ x, additiveCycle.phi20 x = phi20Linear x

namespace OrderThreeLinearConjugacyCycleSource

variable (ρ : Γ →* (M ≃ₗ[R] M))

private def actionAddHom (g : Γ) : M →+ M := (ρ g).toLinearMap.toAddHom
private def actionAddEquiv (g : Γ) : M ≃+ M := (ρ g).toAddEquiv

private theorem intertwines_of_relation
    {u v x y : Γ} (h : u * v = x * y) (m : M) :
    ρ u (ρ v m) = ρ x (ρ y m) := by
  have hr : ρ (u * v) = ρ (x * y) := congrArg ρ h
  have hm := congrArg (fun e : M ≃ₗ[R] M => e m) hr
  simpa using hm

private theorem transport_cubed
    (s : OrderThreeLinearConjugacyCycleSource ρ)
    (m : M) :
    ρ s.r (ρ s.r (ρ s.r m)) = m := by
  have hr : ρ (s.r * s.r * s.r) = ρ (1 : Γ) := congrArg ρ s.r_cubed
  have hm := congrArg (fun e : M ≃ₗ[R] M => e m) hr
  simpa using hm

/-- Compile a linear group source directly into the additive Tate cycle while
retaining the linear maps needed for subquotient transport. -/
def toLinearThreeFibreCycleData
    (s : OrderThreeLinearConjugacyCycleSource ρ) :
    LinearThreeFibreCycleData (R := R) (M := M) where
  additiveCycle :=
    { g0 := actionAddHom ρ s.a
      g1 := actionAddHom ρ s.b
      g2 := actionAddHom ρ s.c
      phi01 := actionAddEquiv ρ s.r
      phi12 := actionAddEquiv ρ s.r
      phi20 := actionAddEquiv ρ s.r
      intertwine01 := intertwines_of_relation ρ s.r_a
      intertwine12 := intertwines_of_relation ρ s.r_b
      intertwine20 := intertwines_of_relation ρ s.r_c
      cycleCoherent := transport_cubed ρ s }
  phi01Linear := ρ s.r
  phi12Linear := ρ s.r
  phi20Linear := ρ s.r
  phi01_agrees := by intro x; rfl
  phi12_agrees := by intro x; rfl
  phi20_agrees := by intro x; rfl

/-- The linear source pays the same generic cycle coherence as the additive
compiler, without discarding scalar structure. -/
theorem linear_group_source_cycle_closes
    (s : OrderThreeLinearConjugacyCycleSource ρ)
    (x : M) :
    let d := s.toLinearThreeFibreCycleData ρ
    d.phi20Linear (d.phi12Linear (d.phi01Linear x)) = x := by
  dsimp
  exact transport_cubed ρ s x

end OrderThreeLinearConjugacyCycleSource

end Integration.ThreeC2TateFibreFromLinearGroupConjugacy
