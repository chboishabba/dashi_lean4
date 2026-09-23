/-
# Reflection positivity for the literal Wilson loops

`OS/WilsonReflectionPositivity.lean` proves reflection positivity for every
bounded measurable observable supported on the links of the closed positive
half.  This file shows that the literal Wilson-loop observables of
`Lattice/WilsonLoop.lean` are such observables as soon as the loop stays in the
positive half, and derives reflection positivity for them.  In particular the
hypothesis class of the main theorem is inhabited by the physical observables,
not only by constants.

* `pathLinks` — the links traversed by a lattice path, with
  `pathHol_congr_of_agree`: the holonomy depends only on those link variables;
* `wilsonLoop_local` — the corresponding locality of the Wilson-loop
  observable;
* `wilson_reflection_positive_loop` — `0 ≤ Re ∫ conj (W_C (Θ U)) · W_C (U) dμ`
  for every loop `C` inside the closed positive half.
-/
import Mathlib
import RequestProject.YangMills.Lattice.WilsonLoop
import RequestProject.YangMills.OS.WilsonOSForm

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {n L : ℕ}

/-- The links traversed by the path `p` started at `x`. -/
def pathLinks (n : ℕ) : Site n → List Step → List (Link n)
  | _, [] => []
  | x, s :: rest =>
      (if s.2 then (x, s.1) else (x - unitVec n s.1, s.1)) ::
        pathLinks n (x + stepShift n s) rest

@[simp] theorem pathLinks_nil (x : Site n) : pathLinks n x [] = [] := rfl

@[simp] theorem pathLinks_cons (x : Site n) (s : Step) (p : List Step) :
    pathLinks n x (s :: p)
      = (if s.2 then (x, s.1) else (x - unitVec n s.1, s.1)) ::
          pathLinks n (x + stepShift n s) p := rfl

variable {G : Type*} [Group G]

/-- **The holonomy depends only on the links the path traverses.** -/
theorem pathHol_congr_of_agree {U V : Conf n G} (x : Site n) (p : List Step)
    (h : ∀ l ∈ pathLinks n x p, U l = V l) : pathHol U x p = pathHol V x p := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih =>
      have hhead : U (if s.2 then (x, s.1) else (x - unitVec n s.1, s.1))
          = V (if s.2 then (x, s.1) else (x - unitVec n s.1, s.1)) :=
        h _ (by simp)
      have htail : ∀ l ∈ pathLinks n (x + stepShift n s) p, U l = V l :=
        fun l hl => h l (by simp [hl])
      have hstep : stepHol U x s = stepHol V x s := by
        cases s with
        | mk d b =>
            cases b with
            | true => simpa [stepHol] using hhead
            | false =>
                simp only [stepHol, if_false, Bool.false_eq_true]
                simpa using congrArg (fun g : G => g⁻¹) (by simpa using hhead)
      rw [pathHol_cons, pathHol_cons, hstep, ih _ htail]

/-- **Locality of the Wilson-loop observable.** -/
theorem wilsonLoop_local (chi : G → ℝ) (x : Site n) (p : List Step) {U V : Conf n G}
    (h : ∀ l ∈ pathLinks n x p, U l = V l) :
    wilsonLoop chi x p U = wilsonLoop chi x p V := by
  unfold wilsonLoop
  rw [pathHol_congr_of_agree x p h]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- **Reflection positivity for a literal Wilson loop in the positive half.**
If every link traversed by the loop lies in the closed positive half
`0 ≤ t ≤ L`, then the Osterwalder–Schrader pairing of the Wilson-loop
observable with itself is nonnegative. -/
theorem wilson_reflection_positive_loop (hN : n + 1 = 2 * L) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) (beta : ℝ) (x : Site n) (p : List Step)
    (hsupp : ∀ l ∈ pathLinks n x p, l ∈ planeLinks n L ∨ l ∈ posLinks n L) :
    0 ≤ (∫ U, (starRingEnd ℂ) ((wilsonLoop chi x p (reflConf hN U) : ℝ) : ℂ) *
        ((wilsonLoop chi x p U : ℝ) : ℂ) ∂(gibbs n G beta chi)).re := by
  set F : Conf n G → ℂ := fun U => ((wilsonLoop chi x p U : ℝ) : ℂ) with hF
  have hcont : Continuous F :=
    Complex.continuous_ofReal.comp (continuous_wilsonLoop hchi x p)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ U : Conf n G, ‖F U‖ ≤ M := by
    obtain ⟨U₀, -, hU₀⟩ :=
      (isCompact_univ (X := Conf n G)).exists_isMaxOn ⟨fun _ => 1, Set.mem_univ _⟩
        hcont.norm.continuousOn
    exact ⟨‖F U₀‖, fun U => hU₀ (Set.mem_univ U)⟩
  exact wilson_reflection_positive hN hchi hconj hinv beta hcont.measurable hM
    (fun U V hUV => by
      simp only [hF]
      exact congrArg _ (wilsonLoop_local chi x p fun l hl => hUV l (hsupp l hl)))

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms pathHol_congr_of_agree
#print axioms wilson_reflection_positive_loop

end Audit
