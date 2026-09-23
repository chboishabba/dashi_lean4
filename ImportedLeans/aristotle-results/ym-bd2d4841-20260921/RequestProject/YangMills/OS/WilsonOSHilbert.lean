/-
# The Osterwalder–Schrader physical Hilbert space of the literal Wilson theory

`OS/WilsonOSForm.lean` proves that

```
  ⟨F, F'⟩_OS  =  ∫ conj (F (Θ U)) · F' (U) dμ_Gibbs(U)
```

is a Hermitian, positive semi-definite, sesquilinear form on the observables of
the closed positive time half of the literal four-dimensional Wilson lattice
gauge theory.  This file performs the first step of the Osterwalder–Schrader
reconstruction on that form: it exhibits the positive-half observables as a
complex vector space (`posObs`), equips it with the OS form as a
*pre-inner product* (`osCore`), and forms the quotient-by-null-vectors and
completion (`OSHilbert`) — a genuine complex Hilbert space whose inner product
is the OS form on the image of the observables.

Nothing here is postulated: `osCore` is built from the reflection positivity
theorem `osForm_self_re_nonneg` and the Hermitian symmetry `osForm_conj_symm`,
both proved for the literal Wilson–Gibbs measure.

Main results:

* `posObs` — the ℂ-submodule of bounded measurable observables of the closed
  positive half;
* `osCore` — the OS form as a `PreInnerProductSpace.Core ℂ`;
* `osForm_cauchy_schwarz` — the Cauchy–Schwarz inequality for the OS form;
* `OSHilbert`, `osVector`, `inner_osVector` — the physical Hilbert space, the
  canonical map from observables into it, and the statement that its inner
  product *is* the OS form;
* `osVector_eq_zero_iff` — the kernel of that map is exactly the OS null space.
-/
import Mathlib
import RequestProject.YangMills.OS.WilsonOSForm

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {n L : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-! ## The data of a literal Wilson theory admitting reflection positivity -/

/-- The data entering the Osterwalder–Schrader construction for the literal
Wilson theory: an even time extent `n + 1 = 2 * L`, an inverse coupling, and a
continuous, conjugation-invariant, inversion-symmetric character. -/
structure OSData (n L : ℕ) (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The time extent of the torus is even, so the reflection `t ↦ -t` has two fixed planes. -/
  even_time : n + 1 = 2 * L
  /-- The inverse coupling of the Wilson action. -/
  beta : ℝ
  /-- The character defining the Wilson action. -/
  chi : G → ℝ
  /-- The character is continuous. -/
  chi_continuous : Continuous chi
  /-- The character is a class function. -/
  chi_conj : ∀ a g : G, chi (a * g * a⁻¹) = chi g
  /-- The character is inversion symmetric (real representation content). -/
  chi_inv : ∀ g : G, chi g⁻¹ = chi g

/-! ## Observables of the closed positive half -/

variable (n L G) in
/-- An observable of the closed positive time half: bounded, measurable, and
depending only on the links of the reflection planes and of the positive half. -/
def IsPosObs (F : Conf n G → ℂ) : Prop :=
  Measurable F ∧ (∃ M : ℝ, ∀ U, ‖F U‖ ≤ M) ∧
    ∀ U V : Conf n G,
      (∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) → F U = F V

variable (n L G) in
/-- The observables of the closed positive time half form a complex vector space. -/
def posObs : Submodule ℂ (Conf n G → ℂ) where
  carrier := {F | IsPosObs n L G F}
  zero_mem' := ⟨measurable_const, ⟨0, fun _ => by simp⟩, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro F F' ⟨hm, ⟨M, hb⟩, hloc⟩ ⟨hm', ⟨M', hb'⟩, hloc'⟩
    refine ⟨hm.add hm', ⟨M + M', fun U => ?_⟩, fun U V h => ?_⟩
    · exact le_trans (norm_add_le _ _) (add_le_add (hb U) (hb' U))
    · show F U + F' U = F V + F' V
      rw [hloc U V h, hloc' U V h]
  smul_mem' := by
    rintro c F ⟨hm, ⟨M, hb⟩, hloc⟩
    refine ⟨hm.const_mul c, ⟨‖c‖ * M, fun U => ?_⟩, fun U V h => ?_⟩
    · show ‖c * F U‖ ≤ ‖c‖ * M
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb U) (norm_nonneg c)
    · show c * F U = c * F V
      rw [hloc U V h]

theorem mem_posObs_iff {F : Conf n G → ℂ} : F ∈ posObs n L G ↔ IsPosObs n L G F := Iff.rfl

theorem posObs.measurable (F : posObs n L G) : Measurable (F : Conf n G → ℂ) := F.2.1

theorem posObs.bounded (F : posObs n L G) : ∃ M : ℝ, ∀ U, ‖(F : Conf n G → ℂ) U‖ ≤ M := F.2.2.1

theorem posObs.local' (F : posObs n L G) :
    ∀ U V : Conf n G,
      (∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) →
        (F : Conf n G → ℂ) U = (F : Conf n G → ℂ) V := F.2.2.2

/-! ## Left sesquilinearity of the OS form -/

/-- Additivity of the OS form in its *first* argument, obtained from additivity
in the second argument and Hermitian symmetry. -/
theorem osForm_add_left (D : OSData n L G) {F F₁ F₂ : Conf n G → ℂ} {M M₁ M₂ : ℝ}
    (hFm : Measurable F) (hFb : ∀ U, ‖F U‖ ≤ M)
    (hF₁m : Measurable F₁) (hF₁b : ∀ U, ‖F₁ U‖ ≤ M₁)
    (hF₂m : Measurable F₂) (hF₂b : ∀ U, ‖F₂ U‖ ≤ M₂) :
    osForm D.even_time D.beta D.chi (fun U => F₁ U + F₂ U) F
      = osForm D.even_time D.beta D.chi F₁ F + osForm D.even_time D.beta D.chi F₂ F := by
  have hsym : ∀ A B : Conf n G → ℂ,
      osForm D.even_time D.beta D.chi A B
        = (starRingEnd ℂ) (osForm D.even_time D.beta D.chi B A) := fun A B =>
    (osForm_conj_symm D.even_time D.beta D.chi_continuous D.chi_conj D.chi_inv A B).symm
  rw [hsym (fun U => F₁ U + F₂ U) F, hsym F₁ F, hsym F₂ F,
    osForm_add_right D.even_time D.beta D.chi_continuous hFm hFb hF₁m hF₁b hF₂m hF₂b, map_add]

/-- Conjugate homogeneity of the OS form in its first argument. -/
theorem osForm_smul_left (D : OSData n L G) (F F' : Conf n G → ℂ) (c : ℂ) :
    osForm D.even_time D.beta D.chi (fun U => c * F U) F'
      = (starRingEnd ℂ) c * osForm D.even_time D.beta D.chi F F' := by
  have hsym : ∀ A B : Conf n G → ℂ,
      osForm D.even_time D.beta D.chi A B
        = (starRingEnd ℂ) (osForm D.even_time D.beta D.chi B A) := fun A B =>
    (osForm_conj_symm D.even_time D.beta D.chi_continuous D.chi_conj D.chi_inv A B).symm
  rw [hsym (fun U => c * F U) F', osForm_smul_right D.even_time D.beta D.chi F' F c, map_mul,
    hsym F F']

/-! ## The OS form as a pre-inner product -/

/-- **The Osterwalder–Schrader form is a pre-inner product on the observables of
the positive half.**  Hermitian symmetry is `osForm_conj_symm`, positive
semi-definiteness is reflection positivity (`osForm_self_re_nonneg`), and
sesquilinearity is `osForm_add_left` / `osForm_smul_left`. -/
noncomputable def osCore (D : OSData n L G) :
    PreInnerProductSpace.Core ℂ (posObs n L G) where
  inner F F' := osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F' : Conf n G → ℂ)
  conj_inner_symm x y :=
    osForm_conj_symm D.even_time D.beta D.chi_continuous D.chi_conj D.chi_inv _ _
  re_inner_nonneg x := by
    obtain ⟨M, hb⟩ := posObs.bounded x
    exact osForm_self_re_nonneg D.even_time D.beta D.chi_continuous D.chi_conj D.chi_inv
      (posObs.measurable x) hb (posObs.local' x)
  add_left x y z := by
    obtain ⟨Mx, hbx⟩ := posObs.bounded x
    obtain ⟨My, hby⟩ := posObs.bounded y
    obtain ⟨Mz, hbz⟩ := posObs.bounded z
    exact osForm_add_left D (posObs.measurable z) hbz (posObs.measurable x) hbx
      (posObs.measurable y) hby
  smul_left x y r := osForm_smul_left D _ _ r

/-- The pre-inner product of the OS construction is the OS form. -/
theorem osCore_inner (D : OSData n L G) (F F' : posObs n L G) :
    (osCore D).inner F F'
      = osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F' : Conf n G → ℂ) := rfl

/-- **Cauchy–Schwarz for the Osterwalder–Schrader form.** -/
theorem osForm_cauchy_schwarz (D : OSData n L G) (F F' : posObs n L G) :
    ‖osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F' : Conf n G → ℂ)‖ *
        ‖osForm D.even_time D.beta D.chi (F' : Conf n G → ℂ) (F : Conf n G → ℂ)‖
      ≤ (osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F : Conf n G → ℂ)).re *
        (osForm D.even_time D.beta D.chi (F' : Conf n G → ℂ) (F' : Conf n G → ℂ)).re := by
  letI : PreInnerProductSpace.Core ℂ (posObs n L G) := osCore D
  letI := InnerProductSpace.Core.toPreInner' (𝕜 := ℂ) (F := (posObs n L G))
  exact InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) F F'

/-! ## The physical Hilbert space -/

/-- The pre-Hilbert space of the Osterwalder–Schrader construction: the
observables of the positive half, seminormed by the OS form. -/
def OSPre (D : OSData n L G) : Type _ := posObs n L G

namespace OSPre

instance (D : OSData n L G) : AddCommGroup (OSPre D) :=
  inferInstanceAs (AddCommGroup (posObs n L G))

instance (D : OSData n L G) : Module ℂ (OSPre D) :=
  inferInstanceAs (Module ℂ (posObs n L G))

noncomputable instance (D : OSData n L G) : SeminormedAddCommGroup (OSPre D) :=
  letI : PreInnerProductSpace.Core ℂ (OSPre D) := osCore D
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := OSPre D)

noncomputable instance (D : OSData n L G) : InnerProductSpace ℂ (OSPre D) :=
  InnerProductSpace.ofCore (osCore D)

/-- The inner product of the pre-Hilbert space is the OS form. -/
theorem inner_eq (D : OSData n L G) (F F' : posObs n L G) :
    (inner ℂ (show OSPre D from F) (show OSPre D from F') : ℂ)
      = osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F' : Conf n G → ℂ) := rfl

end OSPre

/-- **The Osterwalder–Schrader physical Hilbert space of the literal Wilson
theory**: the completion of the positive-half observables in the seminorm of
the OS form (the completion automatically quotients out the OS null vectors). -/
def OSHilbert (D : OSData n L G) : Type _ := UniformSpace.Completion (OSPre D)

namespace OSHilbert

noncomputable instance (D : OSData n L G) : NormedAddCommGroup (OSHilbert D) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (OSPre D)))

noncomputable instance (D : OSData n L G) : InnerProductSpace ℂ (OSHilbert D) :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion (OSPre D)))

instance (D : OSData n L G) : CompleteSpace (OSHilbert D) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (OSPre D)))

end OSHilbert

/-- The canonical map from observables of the positive half into the physical
Hilbert space. -/
noncomputable def osVector (D : OSData n L G) (F : posObs n L G) : OSHilbert D :=
  (UniformSpace.Completion.coe' (α := OSPre D) F : UniformSpace.Completion (OSPre D))

/-- **The inner product of the physical Hilbert space is the Osterwalder–Schrader
form.**  This is the defining property of the OS reconstruction at the level of
the Hilbert space. -/
theorem inner_osVector (D : OSData n L G) (F F' : posObs n L G) :
    (inner ℂ (osVector D F) (osVector D F') : ℂ)
      = osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F' : Conf n G → ℂ) :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := OSPre D) F F'

/-- The physical vector of an observable vanishes exactly when the observable is
an OS null vector. -/
theorem osVector_eq_zero_iff (D : OSData n L G) (F : posObs n L G) :
    osVector D F = 0 ↔
      osForm D.even_time D.beta D.chi (F : Conf n G → ℂ) (F : Conf n G → ℂ) = 0 := by
  constructor
  · intro h
    have := inner_osVector D F F
    rw [h] at this
    simpa using this.symm
  · intro h
    have hnorm : ‖osVector D F‖ = 0 := by
      have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (osVector D F)
      rw [inner_osVector D F F, h] at this
      have h2 : ((‖osVector D F‖ : ℂ)) ^ 2 = 0 := this.symm
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      exact_mod_cast this
    exact norm_eq_zero.mp hnorm

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms osCore
#print axioms osForm_cauchy_schwarz
#print axioms inner_osVector
#print axioms osVector_eq_zero_iff

end Audit
