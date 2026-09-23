/-
# Time translations and the symmetry of the Osterwalder–Schrader form

The Osterwalder–Schrader reconstruction produces a *self-adjoint* Hamiltonian
because the Euclidean time translation is symmetric for the OS form.  This file
proves that symmetry for the literal four-dimensional Wilson theory:

* `timeVec` — a purely temporal lattice vector;
* `siteRefl_sub_timeVec`, `reflConf_translate` — the time reflection `Θ`
  and the time translation `τ_v` satisfy `Θ ∘ τ_v = τ_{-v} ∘ Θ`;
* `osForm_translate_symm` — consequently
  `⟨τ_v F, B⟩_OS = ⟨F, τ_v B⟩_OS` for every pair of observables and every
  purely temporal `v`, i.e. the Euclidean time translation acts symmetrically
  on the Osterwalder–Schrader form.  This is the finite-cutoff statement that
  the transfer operator of the literal Wilson theory is symmetric, and hence
  the source of the self-adjointness of the reconstructed Hamiltonian.

Everything is derived from the literal definitions; nothing is assumed.
-/
import Mathlib
import RequestProject.YangMills.OS.WilsonOSForm

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {n L : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-! ## Purely temporal lattice vectors -/

/-- The purely temporal lattice vector of length `s`. -/
def timeVec (n : ℕ) (s : ZMod (n + 1)) : Site n := Pi.single (0 : Fin 4) s

@[simp] theorem timeVec_zero_coord (s : ZMod (n + 1)) : timeVec n s 0 = s :=
  Pi.single_eq_same _ _

theorem timeVec_other_coord {d : Fin 4} (hd : d ≠ 0) (s : ZMod (n + 1)) :
    timeVec n s d = 0 := Pi.single_eq_of_ne hd _

theorem timeVec_neg (s : ZMod (n + 1)) : timeVec n (-s) = -timeVec n s := by
  funext d
  by_cases hd : d = 0
  · subst hd; simp
  · simp [timeVec_other_coord hd]

/-- Reflecting a site shifted by a temporal vector shifts the reflected site in
the opposite direction: `Θ(x - v) = Θ(x) + v`. -/
theorem siteRefl_sub_timeVec (x : Site n) (s : ZMod (n + 1)) :
    siteRefl (x - timeVec n s) = siteRefl x + timeVec n s := by
  funext d
  by_cases hd : d = 0
  · subst hd
    show (if (0 : Fin 4) = 0 then -((x - timeVec n s) 0) else (x - timeVec n s) 0)
        = (if (0 : Fin 4) = 0 then -(x 0) else x 0) + timeVec n s 0
    rw [if_pos rfl, if_pos rfl]
    simp only [Pi.sub_apply, timeVec_zero_coord]
    ring
  · show (if d = 0 then -((x - timeVec n s) d) else (x - timeVec n s) d)
        = (if d = 0 then -(x d) else x d) + timeVec n s d
    simp only [if_neg hd, Pi.sub_apply, timeVec_other_coord hd]
    ring

/-! ## The reflection and the time translation -/

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem translateConf_translateConf (a b : Site n) (U : Conf n G) :
    Lattice.translate a (Lattice.translate b U) = Lattice.translate (a + b) U := by
  funext l
  show U (l.1 + a + b, l.2) = U (l.1 + (a + b), l.2)
  rw [add_assoc]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem translateConf_zero (U : Conf n G) : Lattice.translate (0 : Site n) U = U := by
  funext l
  show U (l.1 + 0, l.2) = U l
  simp

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **The time reflection and a temporal translation anticommute**:
`Θ ∘ τ_v = τ_{-v} ∘ Θ`. -/
theorem reflConf_translate (hN : n + 1 = 2 * L) (s : ZMod (n + 1)) (U : Conf n G) :
    reflConf hN (Lattice.translate (timeVec n s) U)
      = Lattice.translate (-timeVec n s) (reflConf hN U) := by
  funext l
  obtain ⟨x, d⟩ := l
  by_cases hd : d = 0
  · subst hd
    have hrhs : Lattice.translate (-timeVec n s) (reflConf hN U) (x, 0)
        = (U (siteRefl (x + -timeVec n s) - unitVec n 0, 0))⁻¹ := by
      show reflConf hN U (x + -timeVec n s, 0) = _
      rw [reflConf_time]
    have hlhs : reflConf hN (Lattice.translate (timeVec n s) U) (x, 0)
        = (U (siteRefl x - unitVec n 0 + timeVec n s, 0))⁻¹ := by
      rw [reflConf_time]
      rfl
    have hsite : siteRefl x - unitVec n 0 + timeVec n s
        = siteRefl (x + -timeVec n s) - unitVec n 0 := by
      rw [← sub_eq_add_neg, siteRefl_sub_timeVec]
      abel
    rw [hlhs, hrhs, hsite]
  · have hrhs : Lattice.translate (-timeVec n s) (reflConf hN U) (x, d)
        = U (siteRefl (x + -timeVec n s), d) := by
      show reflConf hN U (x + -timeVec n s, d) = _
      rw [reflConf_space _ _ _ hd]
    have hlhs : reflConf hN (Lattice.translate (timeVec n s) U) (x, d)
        = U (siteRefl x + timeVec n s, d) := by
      rw [reflConf_space _ _ _ hd]
      rfl
    have hsite : siteRefl x + timeVec n s = siteRefl (x + -timeVec n s) := by
      rw [← sub_eq_add_neg, siteRefl_sub_timeVec]
    rw [hlhs, hrhs, hsite]

/-! ## Measurability of the translation -/

/-- A lattice translation as a measurable equivalence of configuration space. -/
def translateEquiv (v : Site n) : Conf n G ≃ᵐ Conf n G where
  toFun := Lattice.translate v
  invFun := Lattice.translate (-v)
  left_inv U := by rw [translateConf_translateConf, neg_add_cancel, translateConf_zero]
  right_inv U := by rw [translateConf_translateConf, add_neg_cancel, translateConf_zero]
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [BorelSpace G] in
@[simp] theorem translateEquiv_apply (v : Site n) (U : Conf n G) :
    translateEquiv v U = Lattice.translate v U := rfl

/-! ## Symmetry of the Osterwalder–Schrader form -/

/-- **The Euclidean time translation is symmetric for the Osterwalder–Schrader
form of the literal Wilson theory**:
`⟨τ_v F, B⟩_OS = ⟨F, τ_v B⟩_OS` for every purely temporal `v`.

This is the finite-cutoff statement that the transfer operator of the literal
Wilson theory is a symmetric operator on the OS form, which is what makes the
reconstructed Hamiltonian self-adjoint. -/
theorem osForm_translate_symm (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hchi : Continuous chi) (s : ZMod (n + 1)) (F B : Conf n G → ℂ) :
    osForm hN beta chi (fun U => F (Lattice.translate (timeVec n s) U)) B
      = osForm hN beta chi F (fun U => B (Lattice.translate (timeVec n s) U)) := by
  have hmp := measurePreserving_translate_gibbs (G := G) (n := n) hchi beta (timeVec n s)
  have hcomm : ∀ U : Conf n G,
      Lattice.translate (timeVec n s) (reflConf hN U)
        = reflConf hN (Lattice.translate (-timeVec n s) U) := by
    intro U
    rw [← timeVec_neg, reflConf_translate hN (-s) U, timeVec_neg, neg_neg]
  calc osForm hN beta chi (fun U => F (Lattice.translate (timeVec n s) U)) B
      = ∫ U, (starRingEnd ℂ) (F (reflConf hN (Lattice.translate (-timeVec n s) U))) * B U
          ∂(gibbs n G beta chi) := by
        rw [osForm]
        exact integral_congr_ae (Filter.Eventually.of_forall fun U =>
          congrArg (fun g : Conf n G => (starRingEnd ℂ) (F g) * B U) (hcomm U))
    _ = ∫ U, (starRingEnd ℂ) (F (reflConf hN (Lattice.translate (-timeVec n s)
            (Lattice.translate (timeVec n s) U)))) * B (Lattice.translate (timeVec n s) U)
          ∂(gibbs n G beta chi) :=
        (hmp.integral_comp (translateEquiv (timeVec n s)).measurableEmbedding
          (fun U => (starRingEnd ℂ) (F (reflConf hN (Lattice.translate (-timeVec n s) U))) *
            B U)).symm
    _ = osForm hN beta chi F (fun U => B (Lattice.translate (timeVec n s) U)) := by
        rw [osForm]
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        have hid : Lattice.translate (-timeVec n s) (Lattice.translate (timeVec n s) U) = U := by
          rw [translateConf_translateConf, neg_add_cancel, translateConf_zero]
        exact congrArg (fun g : Conf n G =>
          (starRingEnd ℂ) (F (reflConf hN g)) * B (Lattice.translate (timeVec n s) U)) hid

/-- **The quadratic form of the Euclidean time translation is real.**  This is
the reality of the transfer-matrix expectation values `⟨F, T^s F⟩` of the
literal Wilson theory, and follows from Hermitian symmetry of the OS form
together with `osForm_translate_symm`. -/
theorem osForm_translate_self_im (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) (s : ZMod (n + 1)) (F : Conf n G → ℂ) :
    (osForm hN beta chi F (fun U => F (Lattice.translate (timeVec n s) U))).im = 0 := by
  have hherm := osForm_conj_symm hN beta hchi hconj hinv
    F (fun U => F (Lattice.translate (timeVec n s) U))
  rw [osForm_translate_symm hN beta hchi s F F] at hherm
  have := congrArg Complex.im hherm
  simp only [Complex.conj_im] at this
  linarith

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms reflConf_translate
#print axioms osForm_translate_symm

end Audit
