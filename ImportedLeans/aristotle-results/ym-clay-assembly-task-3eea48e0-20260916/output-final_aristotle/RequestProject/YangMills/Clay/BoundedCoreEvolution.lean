/-
# Cores and evolutions for everywhere-defined bounded Hamiltonians

The same-object weld (`SameObjectGapTransfer`) consumes three domain-theoretic
facts about the Hamiltonians it identifies: a common core, and the statement
that each differentiates its evolution on that core.  For an everywhere-defined
bounded Hamiltonian — the shape produced by `Clay.FormHamiltonian` from a
bounded energy form — those facts are *theorems*, not inputs, and this file
proves them:

* `isClosed_toPMap_top` — a bounded everywhere-defined operator is closed as an
  unbounded operator (its graph is closed);
* `hasCore_top` — consequently the whole space is a core for it, which is the
  bounded case of the "dense invariant common core" obligation;
* `expEvolution` and `isPMapEvolutionGenerator_expEvolution` — the genuine
  one-parameter group `t ↦ exp(tA)` it generates, with the derivative at `t = 0`
  computed from the exponential of a bounded operator;
* `OSWeld.ofBounded` — hence a bounded Hamiltonian is welded to any operator
  generating the *same* evolution on the whole space.

Nothing here is about unbounded operators: for a genuinely unbounded physical
Hamiltonian the core and the evolution remain inputs.  What this removes is the
need to assume them in the bounded (finite-spacing, bounded-form) case.
-/
import Mathlib
import RequestProject.YangMills.Clay.MassGapAssembly

namespace RequestProject.YangMills.Clay

open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isClosed_toPMap_top (A : E →L[ℂ] E) :
    (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤).IsClosed := by
  have hset : ((LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤).graph : Set (E × E))
      = {p : E × E | p.2 = A p.1} := by
    ext p
    simp [LinearPMap.mem_graph_iff, LinearMap.toPMap_apply, eq_comm]
  show _root_.IsClosed _
  rw [hset]
  exact isClosed_eq continuous_snd (A.continuous.comp continuous_fst)

theorem domRestrict_toPMap_top (A : E →L[ℂ] E) :
    (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤).domRestrict ⊤
      = LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤ := by
  ext x h1 h2
  · simp
  · rfl

theorem hasCore_top (A : E →L[ℂ] E) :
    (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤).HasCore ⊤ := by
  refine ⟨le_rfl, ?_⟩
  rw [domRestrict_toPMap_top]
  have hcl := isClosed_toPMap_top A
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← hcl.isClosable.graph_closure_eq_closure_graph]
  exact hcl.submodule_topologicalClosure_eq

section Evolution

variable [CompleteSpace E]

noncomputable def expEvolution (A : E →L[ℂ] E) : ℝ → E → E :=
  fun t x => (NormedSpace.exp (t • A)) x

theorem hasDerivAt_expEvolution (A : E →L[ℂ] E) (x : E) :
    HasDerivAt (fun t : ℝ => expEvolution A t x) (A x) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := E →L[ℂ] E) A (0 : ℝ)
  have hf := ContinuousLinearMap.hasFDerivAt
    (f := ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ))
    (x := NormedSpace.exp ((0 : ℝ) • A))
  have hcomp := hf.comp_hasDerivAt 0 h
  simpa [expEvolution] using hcomp

theorem isPMapEvolutionGenerator_expEvolution (A : E →L[ℂ] E) :
    IsPMapEvolutionGenerator (expEvolution A) ⊤
      (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤) := by
  refine ⟨le_rfl, ?_⟩
  intro x _
  simpa [LinearMap.toPMap_apply] using hasDerivAt_expEvolution A (x : E)

noncomputable def OSWeld.ofBounded (A : E →L[ℂ] E) {Hos : E →ₗ.[ℂ] E} {V : ℝ → E → E}
    (hUV : expEvolution A = V) (hcore : Hos.HasCore ⊤)
    (hgen : IsPMapEvolutionGenerator V ⊤ Hos) :
    OSWeld (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤) Hos where
  core := ⊤
  ymEvolution := expEvolution A
  osEvolution := V
  evolutions_eq := hUV
  core_limit := hasCore_top A
  core_os := hcore
  gen_limit := isPMapEvolutionGenerator_expEvolution A
  gen_os := hgen

noncomputable def OSWeld.selfBounded (A : E →L[ℂ] E) :
    OSWeld (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤) (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤) :=
  OSWeld.ofBounded A rfl (hasCore_top A) (isPMapEvolutionGenerator_expEvolution A)

end Evolution

end RequestProject.YangMills.Clay

section Audit

open RequestProject.YangMills.Clay

#print axioms isClosed_toPMap_top
#print axioms hasCore_top
#print axioms hasDerivAt_expEvolution
#print axioms isPMapEvolutionGenerator_expEvolution
#print axioms OSWeld.ofBounded

end Audit
