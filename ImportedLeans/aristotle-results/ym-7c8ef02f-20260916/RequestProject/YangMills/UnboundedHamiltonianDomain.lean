/-
# Domain-theoretic (genuinely unbounded) Hamiltonians

`GeneratorUniquenessCore` proves uniqueness of a generator for candidate
Hamiltonians that are *total* maps `H → H`; it assumes no boundedness, but it
also does not model an operator with a proper domain.  This module works with
Mathlib's partially defined operators

  `H : E →ₗ.[ℂ] E`,  i.e.  `H : D(H) ⊆ E → E`,

which is the setting the physical Yang–Mills Hamiltonian actually lives in, and
proves the pieces of the domain layer that the terminal lane needs:

* `IsSymmetric` — symmetry *on the domain* (`⟪Hx, y⟫ = ⟪x, Hy⟫` for `x, y ∈
  D(H)`), i.e. Mathlib's `IsFormalAdjoint H H`;
* `IsSymmetric.isClosable` — a densely defined symmetric operator is closable,
  so it has a closure `H̄` (this is the standard argument via `H ≤ H†` and
  closedness of the adjoint);
* `IsSymmetric.closure` — the closure of a densely defined symmetric operator
  is again symmetric, proved by graph approximation;
* `eq_of_hasCore_of_eqOn` — **two operators with a common core on which they
  agree are equal**: the domain-theoretic uniqueness statement, which is what
  "same operator" has to mean for unbounded Hamiltonians;
* `IsPMapEvolutionGenerator` and `pmap_generator_eqOn_core`,
  `pmap_generator_unique_of_hasCore` — the terminal weld in domain form: two
  partially defined Hamiltonians differentiating the *same* physical evolution
  on a common core agree on that core, and are **equal as unbounded operators**
  when that core is a core for both.

Nothing here constructs a Yang–Mills Hamiltonian, and nothing here claims
essential self-adjointness: those are inputs (`M7`) that this machinery is
waiting for.  What is removed is the excuse that Lean only has the total-map
version of the uniqueness statement.
-/
import Mathlib

namespace RequestProject.YangMills.UnboundedHamiltonianDomain

open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An unbounded operator is symmetric when it is a formal adjoint of itself:
`⟪Hx, y⟫ = ⟪x, Hy⟫` for all `x, y` in the domain. -/
def IsSymmetric (T : E →ₗ.[ℂ] E) : Prop := T.IsFormalAdjoint T

theorem isSymmetric_iff {T : E →ₗ.[ℂ] E} :
    IsSymmetric T ↔ ∀ x y : T.domain, ⟪T x, (y : E)⟫_ℂ = ⟪(x : E), T y⟫_ℂ := Iff.rfl

/-! ## Closability of a densely defined symmetric operator -/

section Closable

variable [CompleteSpace E] {T : E →ₗ.[ℂ] E}

/-- A densely defined symmetric operator is contained in its adjoint. -/
theorem IsSymmetric.le_adjoint (hd : Dense (T.domain : Set E)) (h : IsSymmetric T) :
    T ≤ LinearPMap.adjoint T :=
  LinearPMap.IsFormalAdjoint.le_adjoint hd h

/-- **A densely defined symmetric operator is closable**, hence has a closure:
the first genuine domain-theoretic payment for an unbounded Hamiltonian. -/
theorem IsSymmetric.isClosable (hd : Dense (T.domain : Set E)) (h : IsSymmetric T) :
    T.IsClosable :=
  ((LinearPMap.adjoint_isClosed hd).isClosable).leIsClosable (h.le_adjoint hd)

omit [CompleteSpace E] in
/-- Every point of the domain of the closure is a graph limit of points of the
domain of the operator. -/
theorem exists_seq_of_mem_closure_domain (hcl : T.IsClosable) (x : T.closure.domain) :
    ∃ a : ℕ → T.domain, Tendsto (fun n => ((a n : E))) atTop (𝓝 (x : E)) ∧
      Tendsto (fun n => T (a n)) atTop (𝓝 (T.closure x)) := by
  have hmem : ((x : E), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hcl.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hmem' : ((x : E), T.closure x) ∈ closure (T.graph : Set (E × E)) := hmem
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hmem'
  have hchoice : ∀ n, ∃ a : T.domain, ((a : E), T a) = p n := by
    intro n
    obtain ⟨a, ha1, ha2⟩ := (T.mem_graph_iff).mp (hp n)
    exact ⟨a, by rw [ha1, ha2]⟩
  choose a ha using hchoice
  refine ⟨a, ?_, ?_⟩
  · have : Tendsto (fun n => (p n).1) atTop (𝓝 (x : E)) :=
      (continuous_fst.tendsto _).comp hlim
    simpa [← ha] using this
  · have : Tendsto (fun n => (p n).2) atTop (𝓝 (T.closure x)) :=
      (continuous_snd.tendsto _).comp hlim
    simpa [← ha] using this

omit [CompleteSpace E] in
/-- Symmetry between a point of the domain and a point of the domain of the
closure. -/
theorem inner_closure_eq (hcl : T.IsClosable) (h : IsSymmetric T)
    (a : T.domain) (y : T.closure.domain) :
    ⟪T a, (y : E)⟫_ℂ = ⟪(a : E), T.closure y⟫_ℂ := by
  obtain ⟨b, hb1, hb2⟩ := exists_seq_of_mem_closure_domain hcl y
  have hstep : ∀ n, ⟪T a, ((b n : E))⟫_ℂ = ⟪(a : E), T (b n)⟫_ℂ := fun n => h a (b n)
  have hL : Tendsto (fun n => ⟪T a, ((b n : E))⟫_ℂ) atTop (𝓝 (⟪T a, (y : E)⟫_ℂ)) :=
    (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp
      (Tendsto.prodMk_nhds tendsto_const_nhds hb1)
  have hR : Tendsto (fun n => ⟪(a : E), T (b n)⟫_ℂ) atTop (𝓝 (⟪(a : E), T.closure y⟫_ℂ)) :=
    (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp
      (Tendsto.prodMk_nhds tendsto_const_nhds hb2)
  have : Tendsto (fun n => ⟪T a, ((b n : E))⟫_ℂ) atTop (𝓝 (⟪(a : E), T.closure y⟫_ℂ)) := by
    simpa [hstep] using hR
  exact tendsto_nhds_unique hL this

omit [CompleteSpace E] in
/-- **The closure of a symmetric operator is symmetric.** -/
theorem IsSymmetric.closure (hcl : T.IsClosable) (h : IsSymmetric T) :
    IsSymmetric T.closure := by
  intro x y
  obtain ⟨a, ha1, ha2⟩ := exists_seq_of_mem_closure_domain hcl x
  have hstep : ∀ n, ⟪T (a n), (y : E)⟫_ℂ = ⟪((a n : E)), T.closure y⟫_ℂ :=
    fun n => inner_closure_eq hcl h (a n) y
  have hL : Tendsto (fun n => ⟪T (a n), (y : E)⟫_ℂ) atTop (𝓝 (⟪T.closure x, (y : E)⟫_ℂ)) :=
    (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp
      (Tendsto.prodMk_nhds ha2 tendsto_const_nhds)
  have hR : Tendsto (fun n => ⟪((a n : E)), T.closure y⟫_ℂ) atTop
      (𝓝 (⟪(x : E), T.closure y⟫_ℂ)) :=
    (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp
      (Tendsto.prodMk_nhds ha1 tendsto_const_nhds)
  have : Tendsto (fun n => ⟪T (a n), (y : E)⟫_ℂ) atTop (𝓝 (⟪(x : E), T.closure y⟫_ℂ)) := by
    simpa [hstep] using hR
  exact tendsto_nhds_unique hL this

end Closable

/-! ## Uniqueness of an unbounded operator from a common core -/

/-- Two operators agreeing on a submodule contained in both domains have equal
restrictions to it. -/
theorem domRestrict_eq_of_eqOn {A B : E →ₗ.[ℂ] E} {S : Submodule ℂ E}
    (hA : S ≤ A.domain) (hB : S ≤ B.domain)
    (h : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain), x ∈ S →
      A ⟨x, hxA⟩ = B ⟨x, hxB⟩) :
    A.domRestrict S = B.domRestrict S := by
  have hdom : (A.domRestrict S).domain = (B.domRestrict S).domain := by
    simp [LinearPMap.domRestrict_domain, inf_of_le_left hA, inf_of_le_left hB]
  refine LinearPMap.ext hdom (fun x hx hy => ?_)
  simp only [LinearPMap.domRestrict_domain, Submodule.mem_inf] at hx hy
  rw [LinearPMap.domRestrict_apply (y := ⟨x, hx.2⟩) rfl,
    LinearPMap.domRestrict_apply (y := ⟨x, hy.2⟩) rfl]
  exact h x hx.2 hy.2 hx.1

/-- **Uniqueness from a common core.**  Two unbounded operators that agree on a
submodule which is a core for both are equal as unbounded operators, domains
included. -/
theorem eq_of_hasCore_of_eqOn {A B : E →ₗ.[ℂ] E} {S : Submodule ℂ E}
    (hA : A.HasCore S) (hB : B.HasCore S)
    (h : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain), x ∈ S →
      A ⟨x, hxA⟩ = B ⟨x, hxB⟩) :
    A = B := by
  have hres := domRestrict_eq_of_eqOn hA.le_domain hB.le_domain h
  calc A = (A.domRestrict S).closure := hA.closure_eq.symm
    _ = (B.domRestrict S).closure := by rw [hres]
    _ = B := hB.closure_eq

/-! ## The terminal weld in domain form -/

/-- `H` generates the evolution `U` on the core `S`: `S` lies in the domain of
`H`, and for every `ψ ∈ S` the curve `t ↦ U t ψ` is differentiable at `t = 0`
with derivative `H ψ`.  (The physical evolution carries the factor `-i`; that
convention is immaterial for the uniqueness statement.) -/
def IsPMapEvolutionGenerator (U : ℝ → E → E) (S : Submodule ℂ E) (H : E →ₗ.[ℂ] E) :
    Prop :=
  S ≤ H.domain ∧
    ∀ x : H.domain, (x : E) ∈ S → HasDerivAt (fun t : ℝ => U t (x : E)) (H x) 0

/-- Unpacked form of the generator property, with the domain membership
supplied by the caller. -/
theorem hasDerivAt_of_isPMapEvolutionGenerator {U : ℝ → E → E} {S : Submodule ℂ E}
    {H : E →ₗ.[ℂ] E} (h : IsPMapEvolutionGenerator U S H) (x : E) (hx : x ∈ S)
    (hxd : x ∈ H.domain) : HasDerivAt (fun t : ℝ => U t x) (H ⟨x, hxd⟩) 0 :=
  h.2 ⟨x, hxd⟩ hx

/-- **Same evolution ⟹ same Hamiltonian on the core**, for genuinely partially
defined operators. -/
theorem pmap_generator_eqOn_core {U V : ℝ → E → E} {S : Submodule ℂ E}
    {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (h₁ : IsPMapEvolutionGenerator U S H₁) (h₂ : IsPMapEvolutionGenerator V S H₂)
    (x : E) (hx₁ : x ∈ H₁.domain) (hx₂ : x ∈ H₂.domain) (hxS : x ∈ S) :
    H₁ ⟨x, hx₁⟩ = H₂ ⟨x, hx₂⟩ := by
  subst hUV
  exact (hasDerivAt_of_isPMapEvolutionGenerator h₁ x hxS hx₁).unique
    (hasDerivAt_of_isPMapEvolutionGenerator h₂ x hxS hx₂)

/-- **The domain-theoretic terminal weld.**  If two unbounded Hamiltonians
differentiate the same evolution on a submodule that is a core for both, they
are the *same operator*, domains included. -/
theorem pmap_generator_unique_of_hasCore {U V : ℝ → E → E} {S : Submodule ℂ E}
    {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (h₁ : IsPMapEvolutionGenerator U S H₁) (h₂ : IsPMapEvolutionGenerator V S H₂) :
    H₁ = H₂ :=
  eq_of_hasCore_of_eqOn hc₁ hc₂
    (fun x hx₁ hx₂ hxS => pmap_generator_eqOn_core hUV h₁ h₂ x hx₁ hx₂ hxS)

end RequestProject.YangMills.UnboundedHamiltonianDomain

#print axioms RequestProject.YangMills.UnboundedHamiltonianDomain.IsSymmetric.isClosable
#print axioms RequestProject.YangMills.UnboundedHamiltonianDomain.IsSymmetric.closure
#print axioms RequestProject.YangMills.UnboundedHamiltonianDomain.eq_of_hasCore_of_eqOn
#print axioms RequestProject.YangMills.UnboundedHamiltonianDomain.pmap_generator_eqOn_core
#print axioms RequestProject.YangMills.UnboundedHamiltonianDomain.pmap_generator_unique_of_hasCore
