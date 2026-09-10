/-
# Gap transport for genuinely unbounded Hamiltonians and for energy forms

`MassGapFormTransport` transports a quadratic-form gap through a strong limit
of **bounded** operators `E →L[ℂ] E`.  That is not the situation of the
continuum Yang–Mills Hamiltonian, so this module proves the corresponding
statements one level up, where the Hamiltonians are partially defined operators
`H : D(H) ⊆ E → E` and where the energy is only given as a quadratic form:

* `HasFormGapOn H v Δ` — the form gap on the *domain* of an unbounded `H`;
* `hasFormGapOn_of_core` — a gap holding on a core transports to the whole
  domain along graph limits (approximants staying orthogonal to the vacuum);
* `hasFormGapOn_of_tendsto` — a family of unbounded Hamiltonians sharing the
  states of the limit domain, with energies converging, transports a uniform
  gap to the limit;
* `VacuumOrthogonalRecoverySystem` and `gap_of_recoverySystem` — the Lean twin
  of the recovery-system gap compiler: from
  `‖u‖² ≤ ‖uₙ‖²`, `m‖uₙ‖² ≤ Qₙ(uₙ)` and `Qₙ(uₙ) → L ≤ Q∞(u)` one gets
  `m‖u‖² ≤ Q∞(u)`.  Here the forms `Qₙ, Q∞` are arbitrary real-valued energy
  functionals — no boundedness, no operator representation;
* `gap_of_recoverySystem_eventually_le` — the variant in which the recovery
  sequence satisfies `Qₙ(uₙ) ≤ Q∞(u)` directly;
* `formGap_energy_of_hasFormGapOn` — the operator energy `ψ ↦ re ⟪ψ, Hψ⟫` of an
  unbounded `H` with a form gap is an admissible input for the compiler.

What is still *not* proved anywhere in this development, and must not be read
into these statements: that a physical Yang–Mills Hamiltonian exists, that the
cut-off Hamiltonians converge in any of these senses, or that a form lower
bound for an unbounded self-adjoint operator excludes spectrum below the bound
(the bounded case of that implication is `FormGapSpectralExclusion`).
-/
import Mathlib
import RequestProject.YangMills.UnboundedHamiltonianDomain

namespace RequestProject.YangMills.UnboundedFormGapTransport

open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic-form gap `Δ` above the vacuum `v`, for an operator defined
only on its domain: every state *of the domain* orthogonal to the vacuum has
energy at least `Δ‖ψ‖²`. -/
def HasFormGapOn (H : E →ₗ.[ℂ] E) (v : E) (Δ : ℝ) : Prop :=
  ∀ ψ : H.domain, ⟪(ψ : E), v⟫_ℂ = 0 → Δ * ‖(ψ : E)‖ ^ 2 ≤ (⟪(ψ : E), H ψ⟫_ℂ).re

/-- **Gap on a core ⟹ gap on the domain.**  If every vacuum-orthogonal state of
the domain is a graph limit of vacuum-orthogonal states of a subset `S` on
which the gap holds, then the gap holds on the whole domain. -/
theorem hasFormGapOn_of_core {H : E →ₗ.[ℂ] E} {v : E} {Δ : ℝ} {S : Set E}
    (hS : ∀ ψ : H.domain, (ψ : E) ∈ S → ⟪(ψ : E), v⟫_ℂ = 0 →
      Δ * ‖(ψ : E)‖ ^ 2 ≤ (⟪(ψ : E), H ψ⟫_ℂ).re)
    (happrox : ∀ ψ : H.domain, ⟪(ψ : E), v⟫_ℂ = 0 →
      ∃ a : ℕ → H.domain, (∀ n, ((a n : E)) ∈ S) ∧ (∀ n, ⟪((a n : E)), v⟫_ℂ = 0) ∧
        Tendsto (fun n => ((a n : E))) atTop (𝓝 (ψ : E)) ∧
        Tendsto (fun n => H (a n)) atTop (𝓝 (H ψ))) :
    HasFormGapOn H v Δ := by
  intro ψ hψ
  obtain ⟨a, hmem, hperp, hconv, hEconv⟩ := happrox ψ hψ
  have hleft : Tendsto (fun n => Δ * ‖((a n : E))‖ ^ 2) atTop (𝓝 (Δ * ‖(ψ : E)‖ ^ 2)) := by
    exact tendsto_const_nhds.mul (((continuous_norm.tendsto _).comp hconv).pow 2)
  have hright : Tendsto (fun n => (⟪((a n : E)), H (a n)⟫_ℂ).re) atTop
      (𝓝 ((⟪(ψ : E), H ψ⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (((continuous_inner (𝕜 := ℂ)).tendsto _).comp (Tendsto.prodMk_nhds hconv hEconv))
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall fun n => hS (a n) (hmem n) (hperp n))

/-- **Uniform gaps survive limits of unbounded Hamiltonians.**  If every state
of the limit domain that is orthogonal to the vacuum is also a state of every
approximating domain, with converging energies, and each approximant has form
gap `Δ`, then the limit has form gap `Δ` on its domain. -/
theorem hasFormGapOn_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {H : ι → E →ₗ.[ℂ] E} {Hlim : E →ₗ.[ℂ] E} {v : E} {Δ : ℝ}
    (hshared : ∀ ψ : Hlim.domain, ⟪(ψ : E), v⟫_ℂ = 0 →
      ∃ a : ∀ n : ι, (H n).domain, (∀ n, ((a n : E)) = (ψ : E)) ∧
        Tendsto (fun n => H n (a n)) l (𝓝 (Hlim ψ)))
    (hgap : ∀ᶠ n in l, HasFormGapOn (H n) v Δ) :
    HasFormGapOn Hlim v Δ := by
  intro ψ hψ
  obtain ⟨a, hsame, hEconv⟩ := hshared ψ hψ
  have hright : Tendsto (fun n => (⟪((a n : E)), H n (a n)⟫_ℂ).re) l
      (𝓝 ((⟪(ψ : E), Hlim ψ⟫_ℂ).re)) := by
    have : Tendsto (fun n => (⟪(ψ : E), H n (a n)⟫_ℂ).re) l
        (𝓝 ((⟪(ψ : E), Hlim ψ⟫_ℂ).re)) :=
      (Complex.continuous_re.tendsto _).comp
        (((continuous_inner (𝕜 := ℂ)).tendsto _).comp
          (Tendsto.prodMk_nhds tendsto_const_nhds hEconv))
    simpa [hsame] using this
  refine ge_of_tendsto hright ?_
  filter_upwards [hgap] with n hn
  have hperp : ⟪((a n : E)), v⟫_ℂ = 0 := by rw [hsame n]; exact hψ
  have hn' := hn (a n) hperp
  rw [hsame n] at hn' ⊢
  exact hn'

/-! ## The recovery-system gap compiler -/

/-- A vacuum-orthogonal recovery system for the vector `u`: an approximating
sequence `uₙ` whose norms dominate `‖u‖`, whose energies `Qₙ(uₙ)` obey the
uniform gap `m`, and whose energies converge to a value dominated by the limit
energy `Q∞(u)`.  The forms `Qₙ`, `Q∞` are arbitrary real-valued functionals:
this is a statement about energy forms, not about bounded operators. -/
structure VacuumOrthogonalRecoverySystem (E : Type*) [NormedAddCommGroup E] where
  /-- The uniform gap constant. -/
  m : ℝ
  /-- Nonnegativity of the gap constant (needed to compare the two norms). -/
  m_nonneg : 0 ≤ m
  /-- The limit state. -/
  u : E
  /-- The recovery sequence. -/
  approx : ℕ → E
  /-- The approximating energy forms. -/
  Q : ℕ → E → ℝ
  /-- The limit energy form. -/
  Qinf : E → ℝ
  /-- The recovery sequence does not lose norm. -/
  norm_le : ∀ n, ‖u‖ ^ 2 ≤ ‖approx n‖ ^ 2
  /-- Each approximant satisfies the uniform gap. -/
  gap : ∀ n, m * ‖approx n‖ ^ 2 ≤ Q n (approx n)
  /-- The approximating energies converge. -/
  limit : ℝ
  /-- ... to `limit`, ... -/
  tendsto : Tendsto (fun n => Q n (approx n)) atTop (𝓝 limit)
  /-- ... which does not exceed the limit energy of `u`. -/
  limit_le : limit ≤ Qinf u

omit [InnerProductSpace ℂ E] in
/-- **The recovery-system gap compiler.**  A vacuum-orthogonal recovery system
transports the uniform gap to the limit energy form: `m‖u‖² ≤ Q∞(u)`. -/
theorem gap_of_recoverySystem (R : VacuumOrthogonalRecoverySystem E) :
    R.m * ‖R.u‖ ^ 2 ≤ R.Qinf R.u := by
  have hstep : ∀ n, R.m * ‖R.u‖ ^ 2 ≤ R.Q n (R.approx n) := by
    intro n
    refine le_trans ?_ (R.gap n)
    exact mul_le_mul_of_nonneg_left (R.norm_le n) R.m_nonneg
  have hlim : R.m * ‖R.u‖ ^ 2 ≤ R.limit :=
    ge_of_tendsto R.tendsto (Filter.Eventually.of_forall hstep)
  exact le_trans hlim R.limit_le

omit [InnerProductSpace ℂ E] in
/-- The variant in which each approximating energy is already dominated by the
limit energy; no convergence hypothesis is needed. -/
theorem gap_of_recoverySystem_eventually_le {m : ℝ} (hm : 0 ≤ m) {u : E}
    {approx : ℕ → E} {Q : ℕ → E → ℝ} {Qinf : ℝ}
    (hnorm : ∀ n, ‖u‖ ^ 2 ≤ ‖approx n‖ ^ 2)
    (hgap : ∀ n, m * ‖approx n‖ ^ 2 ≤ Q n (approx n))
    (hle : ∃ n, Q n (approx n) ≤ Qinf) :
    m * ‖u‖ ^ 2 ≤ Qinf := by
  obtain ⟨n, hn⟩ := hle
  calc m * ‖u‖ ^ 2 ≤ m * ‖approx n‖ ^ 2 := mul_le_mul_of_nonneg_left (hnorm n) hm
    _ ≤ Q n (approx n) := hgap n
    _ ≤ Qinf := hn

/-- The energy form of an unbounded Hamiltonian with a form gap is an
admissible uniform-gap input for the compiler: on vacuum-orthogonal states of
the domain the energy dominates `Δ‖ψ‖²`. -/
theorem formGap_energy_of_hasFormGapOn {H : E →ₗ.[ℂ] E} {v : E} {Δ : ℝ}
    (h : HasFormGapOn H v Δ) (ψ : H.domain) (hψ : ⟪(ψ : E), v⟫_ℂ = 0) :
    Δ * ‖(ψ : E)‖ ^ 2 ≤ (⟪(ψ : E), H ψ⟫_ℂ).re :=
  h ψ hψ

/-- Non-vacuity of the unbounded gap notion: on any domain, the operator
`ψ ↦ Δ • ψ` has form gap `Δ`. -/
theorem hasFormGapOn_smul (Δ : ℝ) (v : E) (D : Submodule ℂ E) :
    HasFormGapOn
      ({ domain := D, toFun := (Δ : ℂ) • (D.subtype) } : E →ₗ.[ℂ] E) v Δ := by
  intro ψ _
  have hval : ((({ domain := D, toFun := (Δ : ℂ) • (D.subtype) } : E →ₗ.[ℂ] E) ψ))
      = (Δ : ℂ) • (ψ : E) := rfl
  rw [hval]
  have : ⟪(ψ : E), (Δ : ℂ) • (ψ : E)⟫_ℂ = (Δ : ℂ) * ((‖(ψ : E)‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.ofReal_im]
  simp

end RequestProject.YangMills.UnboundedFormGapTransport

#print axioms RequestProject.YangMills.UnboundedFormGapTransport.hasFormGapOn_of_core
#print axioms RequestProject.YangMills.UnboundedFormGapTransport.hasFormGapOn_of_tendsto
#print axioms RequestProject.YangMills.UnboundedFormGapTransport.gap_of_recoverySystem
#print axioms RequestProject.YangMills.UnboundedFormGapTransport.gap_of_recoverySystem_eventually_le
#print axioms RequestProject.YangMills.UnboundedFormGapTransport.hasFormGapOn_smul
