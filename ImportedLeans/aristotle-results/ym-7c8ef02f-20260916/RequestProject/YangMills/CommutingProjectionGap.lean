/-
# A mass gap from commuting local projections

This is the first link of the chain, in the form the lattice actually presents
it.  A strong-coupling lattice Hamiltonian is a **sum of local terms `1 - Pᵢ`**,
one per link (or per site), where `Pᵢ` is the orthogonal projection onto the
states invariant under the gauge action at `i`.  Distinct links act on distinct
variables, so the `Pᵢ` **commute**.  The vacuum is the joint invariant vector,
and the mass gap is the statement that a state orthogonal to it is annihilated
by no common invariance.

This module proves exactly that, with no lattice-specific input:

* `IsOrthProj` and its basic calculus (`inner_self_eq_normSq`, `norm_apply_le`);
* `IsOrthProj.comp` — a product of two *commuting* orthogonal projections is an
  orthogonal projection;
* `sum_defect_ge_prod_defect` — the key operator inequality
  `‖x‖² - ‖(∏ᵢ Pᵢ) x‖² ≤ Σᵢ (‖x‖² - ‖Pᵢ x‖²)`, i.e. `Σᵢ (1 - Pᵢ) ≥ 1 - ∏ᵢ Pᵢ`
  for commuting orthogonal projections;
* `localHamiltonian` — the Hamiltonian `Σᵢ (1 - Pᵢ)`, self-adjoint and
  annihilating every joint invariant vector;
* `hasVacuumFormGap_localHamiltonian` — **gap `1` above the vacuum**, whenever
  the joint invariant subspace is exactly the vacuum line;
* `localGapDatum` — the resulting `VacuumGapDatum`, so the resolvent and
  no-eigenvalue statements of `VacuumSectorSpectralGap` apply verbatim, and the
  cutoff/continuum transport of `ContinuumGapTransport` can consume it.

`twoProjectionWitness` inhabits the hypotheses with a genuinely nontrivial
two-term Hamiltonian, so nothing here is vacuous.

Honest scope: this supplies the *engine*, not a Yang–Mills lattice measure.  A
concrete four-dimensional `SU(N)` lattice gauge Hilbert space, with its link
averagings verified to satisfy `joint invariants = ℂΩ`, is not constructed here
and remains an input.  Moreover a gap proved this way is uniform in nothing: it
is a finite-lattice statement, and on its own it cannot pay the continuum
theorem — `ContinuumGapTransport` is where that payment would have to be made.
-/
import Mathlib
import RequestProject.YangMills.VacuumSectorSpectralGap
import RequestProject.YangMills.UnboundedFormGapResolvent

namespace RequestProject.YangMills.CommutingProjectionGap

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Orthogonal projections -/

omit [CompleteSpace E] in
/-- The real part of the inner product of a vector with itself is its squared
norm.  Stated once, to avoid repeated `RCLike`/`Complex` coercion juggling. -/
theorem re_inner_self_norm_sq (y : E) : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) y


/-- An orthogonal projection: idempotent and self-adjoint. -/
structure IsOrthProj (T : E →L[ℂ] E) : Prop where
  /-- Idempotence. -/
  idem : T ∘L T = T
  /-- Self-adjointness. -/
  sa : IsSelfAdjoint T

namespace IsOrthProj

theorem apply_apply {T : E →L[ℂ] E} (h : IsOrthProj T) (x : E) : T (T x) = T x :=
  congrArg (fun S : E →L[ℂ] E => S x) h.idem

/-- The quadratic form of an orthogonal projection is the squared norm of the
image. -/
theorem re_inner_self {T : E →L[ℂ] E} (h : IsOrthProj T) (x : E) :
    (⟪x, T x⟫_ℂ).re = ‖T x‖ ^ 2 := by
  have h2 : ⟪x, T x⟫_ℂ = ⟪x, T (T x)⟫_ℂ := by rw [h.apply_apply]
  rw [h2, ← ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp h.sa]
  exact re_inner_self_norm_sq (T x)

/-- An orthogonal projection is a contraction. -/
theorem norm_apply_le {T : E →L[ℂ] E} (h : IsOrthProj T) (x : E) : ‖T x‖ ≤ ‖x‖ := by
  have hcs : (⟪x, T x⟫_ℂ).re ≤ ‖x‖ * ‖T x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rw [h.re_inner_self] at hcs
  rcases eq_or_lt_of_le (norm_nonneg (T x)) with hz | hz
  · rw [← hz]; exact norm_nonneg x
  · nlinarith

/-- The identity is an orthogonal projection. -/
theorem one : IsOrthProj (1 : E →L[ℂ] E) :=
  ⟨by ext x; simp, IsSelfAdjoint.one (R := E →L[ℂ] E)⟩

/-- The complementary projection. -/
theorem one_sub {T : E →L[ℂ] E} (h : IsOrthProj T) : IsOrthProj (1 - T) := by
  constructor
  · have hexp : (1 - T) ∘L (1 - T) = 1 - T - T + T ∘L T := by
      ext x; simp; abel
    rw [hexp, h.idem]; abel
  · exact IsSelfAdjoint.sub (IsSelfAdjoint.one (R := E →L[ℂ] E)) h.sa

/-- A product of two commuting orthogonal projections is an orthogonal
projection. -/
theorem comp {S T : E →L[ℂ] E} (hS : IsOrthProj S) (hT : IsOrthProj T)
    (hc : Commute S T) : IsOrthProj (S ∘L T) := by
  have hc' : ∀ y : E, T (S y) = S (T y) := by
    intro y
    have h := congrArg (fun R : E →L[ℂ] E => R y) hc
    simpa using h.symm
  constructor
  · ext x
    show S (T (S (T x))) = S (T x)
    rw [hc' (T x), hT.apply_apply, hS.apply_apply]
  · have hS' := ContinuousLinearMap.isSelfAdjoint_iff'.mp hS.sa
    have hT' := ContinuousLinearMap.isSelfAdjoint_iff'.mp hT.sa
    rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp, hS', hT']
    exact hc.symm

end IsOrthProj

/-! ## The key operator inequality -/

omit [CompleteSpace E] in
/-- Every element of a list of pairwise commuting orthogonal projections
commutes with the product of the list. -/
theorem commute_list_prod {a : E →L[ℂ] E} :
    ∀ {l : List (E →L[ℂ] E)}, (∀ T ∈ l, Commute a T) → Commute a l.prod := by
  intro l
  induction l with
  | nil => intro _; simp [Commute, SemiconjBy]
  | cons b t ih =>
      intro h
      rw [List.prod_cons]
      exact (h b (by simp)).mul_right (ih (fun T hT => h T (by simp [hT])))

/-- A product of pairwise commuting orthogonal projections is an orthogonal
projection. -/
theorem isOrthProj_list_prod :
    ∀ {l : List (E →L[ℂ] E)}, (∀ T ∈ l, IsOrthProj T) → l.Pairwise Commute →
      IsOrthProj l.prod := by
  intro l
  induction l with
  | nil => intro _ _; simpa using IsOrthProj.one
  | cons a t ih =>
      intro hp hc
      rw [List.prod_cons]
      have hct : ∀ T ∈ t, Commute a T := fun T hT => (List.pairwise_cons.mp hc).1 T hT
      exact (hp a (by simp)).comp
        (ih (fun T hT => hp T (by simp [hT])) (List.pairwise_cons.mp hc).2)
        (commute_list_prod hct)

/-- **The gap inequality for commuting projections.**
`Σᵢ (1 - Pᵢ) ≥ 1 - ∏ᵢ Pᵢ`, written on quadratic forms:
`‖x‖² - ‖(∏ᵢ Pᵢ) x‖² ≤ Σᵢ (‖x‖² - ‖Pᵢ x‖²)`.

This is what turns "no single local term detects the state" into "the state is
jointly invariant", and it is the only place commutativity is used. -/
theorem sum_defect_ge_prod_defect :
    ∀ {l : List (E →L[ℂ] E)}, (∀ T ∈ l, IsOrthProj T) → l.Pairwise Commute →
      ∀ x : E, ‖x‖ ^ 2 - ‖l.prod x‖ ^ 2
        ≤ (l.map (fun T => ‖x‖ ^ 2 - ‖T x‖ ^ 2)).sum := by
  intro l
  induction l with
  | nil => intro _ _ x; simp
  | cons a t ih =>
      intro hp hc x
      have hpa : IsOrthProj a := hp a (by simp)
      have hpt : ∀ T ∈ t, IsOrthProj T := fun T hT => hp T (by simp [hT])
      have hct : t.Pairwise Commute := (List.pairwise_cons.mp hc).2
      have hcat : ∀ T ∈ t, Commute a T := fun T hT => (List.pairwise_cons.mp hc).1 T hT
      have hQ : IsOrthProj t.prod := isOrthProj_list_prod hpt hct
      have hcomm : Commute a t.prod := commute_list_prod hcat
      -- the defect of `a` does not grow when first projecting with the tail
      have hkey : ‖t.prod x‖ ^ 2 - ‖a (t.prod x)‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖a x‖ ^ 2 := by
        have hid : ∀ y : E, ‖y‖ ^ 2 - ‖a y‖ ^ 2 = ‖y - a y‖ ^ 2 := by
          intro y
          have hcomp : ((1 : E →L[ℂ] E) - a) y = y - a y := by simp
          have h1 : ‖y - a y‖ ^ 2 = (⟪y, ((1 : E →L[ℂ] E) - a) y⟫_ℂ).re := by
            rw [hpa.one_sub.re_inner_self, hcomp]
          rw [h1, hcomp, inner_sub_right, Complex.sub_re, hpa.re_inner_self,
            re_inner_self_norm_sq]
        rw [hid, hid]
        have hcomm' : (a : E →L[ℂ] E) ∘L t.prod = t.prod ∘L a := hcomm
        have hrw : t.prod x - a (t.prod x) = t.prod (x - a x) := by
          have h1 : a (t.prod x) = t.prod (a x) :=
            congrArg (fun S : E →L[ℂ] E => S x) hcomm'
          rw [h1, map_sub]
        rw [hrw]
        have := hQ.norm_apply_le (x - a x)
        have hnn : (0 : ℝ) ≤ ‖t.prod (x - a x)‖ := norm_nonneg _
        nlinarith
      have hIH := ih hpt hct x
      have hprod : ((a :: t).prod) x = a (t.prod x) := by
        rw [List.prod_cons]; rfl
      rw [hprod, List.map_cons, List.sum_cons]
      linarith

/-! ## The local Hamiltonian -/

/-- The Hamiltonian `Σᵢ (1 - Pᵢ)` attached to a list of local projections. -/
def localHamiltonian (l : List (E →L[ℂ] E)) : E →L[ℂ] E :=
  (l.map (fun T => 1 - T)).sum

omit [CompleteSpace E] in
@[simp] theorem localHamiltonian_nil : localHamiltonian ([] : List (E →L[ℂ] E)) = 0 := rfl

omit [CompleteSpace E] in
@[simp] theorem localHamiltonian_cons (a : E →L[ℂ] E) (t : List (E →L[ℂ] E)) :
    localHamiltonian (a :: t) = (1 - a) + localHamiltonian t := rfl

/-- The quadratic form of the local Hamiltonian is the total defect. -/
theorem re_inner_localHamiltonian :
    ∀ (l : List (E →L[ℂ] E)), (∀ T ∈ l, IsOrthProj T) → ∀ x : E,
      (⟪x, localHamiltonian l x⟫_ℂ).re = (l.map (fun T => ‖x‖ ^ 2 - ‖T x‖ ^ 2)).sum := by
  intro l
  induction l with
  | nil => intro _ x; simp [localHamiltonian]
  | cons a t ih =>
      intro hp x
      have hpa : IsOrthProj a := hp a (by simp)
      have hpt : ∀ T ∈ t, IsOrthProj T := fun T hT => hp T (by simp [hT])
      rw [localHamiltonian_cons, List.map_cons, List.sum_cons]
      have happ : ((1 - a) + localHamiltonian t) x
          = (x - a x) + localHamiltonian t x := by simp
      rw [happ, inner_add_right, Complex.add_re, ih hpt x, inner_sub_right,
        Complex.sub_re, re_inner_self_norm_sq, hpa.re_inner_self]

/-- The local Hamiltonian is self-adjoint. -/
theorem isSelfAdjoint_localHamiltonian :
    ∀ (l : List (E →L[ℂ] E)), (∀ T ∈ l, IsOrthProj T) →
      IsSelfAdjoint (localHamiltonian l) := by
  intro l
  induction l with
  | nil => intro _; simp [localHamiltonian, IsSelfAdjoint]
  | cons a t ih =>
      intro hp
      rw [localHamiltonian_cons]
      exact IsSelfAdjoint.add
        (IsSelfAdjoint.sub (IsSelfAdjoint.one (R := E →L[ℂ] E)) (hp a (by simp)).sa)
        (ih (fun T hT => hp T (by simp [hT])))

omit [CompleteSpace E] in
/-- The local Hamiltonian annihilates every jointly invariant vector. -/
theorem localHamiltonian_apply_eq_zero :
    ∀ (l : List (E →L[ℂ] E)) {v : E}, (∀ T ∈ l, T v = v) → localHamiltonian l v = 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
      intro v hv
      rw [localHamiltonian_cons]
      have h1 : (1 - a) v = 0 := by simp [hv a (by simp)]
      have h2 : localHamiltonian t v = 0 := ih (fun T hT => hv T (by simp [hT]))
      simp [h1, h2]

/-! ## The gap -/

/-- **Mass gap `1` above the vacuum.**  If the local projections commute and
their joint invariant subspace meets the vacuum complement only in `0` — encoded
as: the product kills every vector orthogonal to the vacuum — then the local
Hamiltonian has form gap `1` above the vacuum. -/
theorem hasVacuumFormGap_localHamiltonian (l : List (E →L[ℂ] E))
    (hp : ∀ T ∈ l, IsOrthProj T) (hc : l.Pairwise Commute) (vac : E)
    (hker : ∀ x : E, ⟪vac, x⟫_ℂ = 0 → l.prod x = 0) :
    HasVacuumFormGap ((localHamiltonian l).toPMap ⊤) vac 1 := by
  intro ψ hψ
  have happ : ((localHamiltonian l).toPMap ⊤) ψ = localHamiltonian l (ψ : E) := rfl
  rw [happ, re_inner_localHamiltonian l hp]
  have hzero : l.prod (ψ : E) = 0 := hker (ψ : E) hψ
  have hmain := sum_defect_ge_prod_defect hp hc (ψ : E)
  rw [hzero] at hmain
  simpa using hmain

/-- **The finite local model as a `VacuumGapDatum`.**  All the spectral
consequences of `VacuumSectorSpectralGap` — unique solvability below the gap,
the resolvent bound, no eigenvalue in `(0, 1)` — apply to it. -/
noncomputable def localGapDatum (l : List (E →L[ℂ] E))
    (hp : ∀ T ∈ l, IsOrthProj T) (hc : l.Pairwise Commute) (vac : E)
    (hunit : ‖vac‖ = 1) (hinv : ∀ T ∈ l, T vac = vac)
    (hker : ∀ x : E, ⟪vac, x⟫_ℂ = 0 → l.prod x = 0) : VacuumGapDatum E where
  op := (localHamiltonian l).toPMap ⊤
  vac := vac
  gap := 1
  vac_mem := Submodule.mem_top
  vac_unit := hunit
  vac_ground := localHamiltonian_apply_eq_zero l hinv
  selfAdjoint := UnboundedFormGapResolvent.isSelfAdjoint_toPMap_top
    (isSelfAdjoint_localHamiltonian l hp)
  gap_pos := one_pos
  form_gap := hasVacuumFormGap_localHamiltonian l hp hc vac hker

@[simp] theorem localGapDatum_gap (l : List (E →L[ℂ] E))
    (hp : ∀ T ∈ l, IsOrthProj T) (hc : l.Pairwise Commute) (vac : E)
    (hunit : ‖vac‖ = 1) (hinv : ∀ T ∈ l, T vac = vac)
    (hker : ∀ x : E, ⟪vac, x⟫_ℂ = 0 → l.prod x = 0) :
    (localGapDatum l hp hc vac hunit hinv hker).gap = 1 := rfl

/-- **The spectral statement for the local model.** -/
theorem local_no_spectrum_below_gap (l : List (E →L[ℂ] E))
    (hp : ∀ T ∈ l, IsOrthProj T) (hc : l.Pairwise Commute) (vac : E)
    (hunit : ‖vac‖ = 1) (hinv : ∀ T ∈ l, T vac = vac)
    (hker : ∀ x : E, ⟪vac, x⟫_ℂ = 0 → l.prod x = 0)
    {lam : ℝ} (hlt : lam < 1) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : ((localHamiltonian l).toPMap ⊤).domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      ((localHamiltonian l).toPMap ⊤) ψ - (lam : ℂ) • (ψ : E) = y :=
  (localGapDatum l hp hc vac hunit hinv hker).exists_unique_solution_vacuumSector hlt hy

/-! ## Non-vacuity -/

section Witness

/-- The projection onto the vacuum line is an orthogonal projection. -/
theorem isOrthProj_vacLine (vac : E) : IsOrthProj ((ℂ ∙ vac).starProjection) := by
  constructor
  · ext x
    show (ℂ ∙ vac).starProjection ((ℂ ∙ vac).starProjection x)
      = (ℂ ∙ vac).starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr
      ((ℂ ∙ vac).starProjection_apply_mem x)
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    exact Submodule.inner_starProjection_left_eq_right _ _ _

/-- **A nontrivial witness.**  The one-term list consisting of the projection
onto the vacuum line satisfies every hypothesis, with the Hamiltonian
`1 - P_{ℂΩ}` — a genuinely nonzero operator — and gap `1`. -/
theorem localGapDatum_witness (vac : E) (hunit : ‖vac‖ = 1) :
    (localGapDatum [((ℂ ∙ vac).starProjection)]
      (by intro T hT; simp at hT; subst hT; exact isOrthProj_vacLine vac)
      (by simp) vac hunit
      (by
        intro T hT
        simp at hT
        subst hT
        exact Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self vac))
      (by
        intro x hx
        have hmem : x ∈ (ℂ ∙ vac)ᗮ := by
          rw [Submodule.mem_orthogonal_singleton_iff_inner_left, ← inner_conj_symm]
          simp [hx]
        have hz : (ℂ ∙ vac).starProjection x = 0 := by
          rw [Submodule.starProjection_apply_eq_zero_iff]
          exact hmem
        simpa using hz)).gap = 1 := rfl

end Witness

/-! ## Axiom audit -/

section Audit

#print axioms IsOrthProj.comp
#print axioms isOrthProj_list_prod
#print axioms sum_defect_ge_prod_defect
#print axioms re_inner_localHamiltonian
#print axioms isSelfAdjoint_localHamiltonian
#print axioms localHamiltonian_apply_eq_zero
#print axioms hasVacuumFormGap_localHamiltonian
#print axioms local_no_spectrum_below_gap
#print axioms localGapDatum_witness

end Audit

end RequestProject.YangMills.CommutingProjectionGap
