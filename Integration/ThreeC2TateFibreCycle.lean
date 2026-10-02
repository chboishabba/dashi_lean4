import Integration.C2TateIntertwinerTransport

/-!
# Three conjugate C2 Tate fibres in a C3 cycle

This file packages the generic situation needed for a 2B-pure Klein four:
three involutions g0,g1,g2 acting on three additive carriers M0,M1,M2, with
equivalences phi01, phi12, phi20 intertwining successive actions.

The previous C2TateIntertwinerTransport theorem then gives exact transport of
Hhat0/Hhat1 representative conditions around the cycle.

This is still source-neutral algebra.  The Monster-local S3/C3 action must
supply the actual carriers and equivalences.
-/

namespace Integration.ThreeC2TateFibreCycle

namespace T := Integration.C2TateIntertwinerTransport

variable
  {M0 M1 M2 : Type*}
  [AddCommGroup M0] [AddCommGroup M1] [AddCommGroup M2]

structure ThreeFibreCycleData where
  g0 : M0 →+ M0
  g1 : M1 →+ M1
  g2 : M2 →+ M2

  phi01 : M0 ≃+ M1
  phi12 : M1 ≃+ M2
  phi20 : M2 ≃+ M0

  intertwine01 : ∀ x, phi01 (g0 x) = g1 (phi01 x)
  intertwine12 : ∀ x, phi12 (g1 x) = g2 (phi12 x)
  intertwine20 : ∀ x, phi20 (g2 x) = g0 (phi20 x)

  cycleCoherent : ∀ x, phi20 (phi12 (phi01 x)) = x

open ThreeFibreCycleData

theorem hhat0_transport_01
    (D : ThreeFibreCycleData) (x : M0) :
    (T.Fixed D.g0 x ∧ ¬ T.NormImage D.g0 x)
      ↔
    (T.Fixed D.g1 (D.phi01 x) ∧
      ¬ T.NormImage D.g1 (D.phi01 x)) :=
  T.hhat0_representative_transport
    D.g0 D.g1 D.phi01 D.intertwine01 x

theorem hhat0_transport_12
    (D : ThreeFibreCycleData) (x : M1) :
    (T.Fixed D.g1 x ∧ ¬ T.NormImage D.g1 x)
      ↔
    (T.Fixed D.g2 (D.phi12 x) ∧
      ¬ T.NormImage D.g2 (D.phi12 x)) :=
  T.hhat0_representative_transport
    D.g1 D.g2 D.phi12 D.intertwine12 x

theorem hhat0_transport_20
    (D : ThreeFibreCycleData) (x : M2) :
    (T.Fixed D.g2 x ∧ ¬ T.NormImage D.g2 x)
      ↔
    (T.Fixed D.g0 (D.phi20 x) ∧
      ¬ T.NormImage D.g0 (D.phi20 x)) :=
  T.hhat0_representative_transport
    D.g2 D.g0 D.phi20 D.intertwine20 x

theorem hhat1_transport_01
    (D : ThreeFibreCycleData) (x : M0) :
    (T.NormKernel D.g0 x ∧ ¬ T.DiffImage D.g0 x)
      ↔
    (T.NormKernel D.g1 (D.phi01 x) ∧
      ¬ T.DiffImage D.g1 (D.phi01 x)) :=
  T.hhat1_representative_transport
    D.g0 D.g1 D.phi01 D.intertwine01 x

theorem hhat1_transport_12
    (D : ThreeFibreCycleData) (x : M1) :
    (T.NormKernel D.g1 x ∧ ¬ T.DiffImage D.g1 x)
      ↔
    (T.NormKernel D.g2 (D.phi12 x) ∧
      ¬ T.DiffImage D.g2 (D.phi12 x)) :=
  T.hhat1_representative_transport
    D.g1 D.g2 D.phi12 D.intertwine12 x

theorem hhat1_transport_20
    (D : ThreeFibreCycleData) (x : M2) :
    (T.NormKernel D.g2 x ∧ ¬ T.DiffImage D.g2 x)
      ↔
    (T.NormKernel D.g0 (D.phi20 x) ∧
      ¬ T.DiffImage D.g0 (D.phi20 x)) :=
  T.hhat1_representative_transport
    D.g2 D.g0 D.phi20 D.intertwine20 x

theorem three_step_hhat0_returns
    (D : ThreeFibreCycleData) (x : M0) :
    D.phi20 (D.phi12 (D.phi01 x)) = x :=
  D.cycleCoherent x

/-- If a selected family of Hhat0 representatives is transported by phi01 and
phi12, coherence returns it after the third step.  This is the algebraic core
of the source-native 3 x Q10 architecture. -/
theorem selected_hhat0_cycle
    (D : ThreeFibreCycleData)
    (x0 : M0)
    (hx0 : T.Fixed D.g0 x0 ∧ ¬ T.NormImage D.g0 x0) :
    let x1 := D.phi01 x0
    let x2 := D.phi12 x1
    (T.Fixed D.g1 x1 ∧ ¬ T.NormImage D.g1 x1)
    ∧
    (T.Fixed D.g2 x2 ∧ ¬ T.NormImage D.g2 x2)
    ∧
    D.phi20 x2 = x0 := by
  dsimp
  have h1 := (hhat0_transport_01 D x0).mp hx0
  have h2 := (hhat0_transport_12 D (D.phi01 x0)).mp h1
  exact ⟨h1, h2, D.cycleCoherent x0⟩

end Integration.ThreeC2TateFibreCycle
