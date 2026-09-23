/-
# Literal Wilson-loop observables on the periodic four-dimensional lattice

`Lattice/Wilson.lean` builds the literal Wilson–Gibbs measure out of the
plaquette holonomy.  The mass-gap route that the physical seams are stated on
(`S₃`, the *literal Wilson-cylinder presentation*) needs more than the
plaquette: it needs the genuine Wilson-loop observables

    W_C(U) = χ( ∏_{e ∈ C} U_e^{±1} ),

their gauge invariance, their behaviour under lattice translations, and the
fact that the plaquette — hence the Wilson action itself — is one of them.
This file supplies exactly that, with no new postulate and no placeholder.

* `Step`, `stepShift`, `pathEnd` — a directed lattice step (a direction together
  with an orientation) and the endpoint of a path of such steps;
* `stepHol`, `pathHol` — the literal parallel transporter along a step and along
  a path: `U_e` for a forward step and `U_e⁻¹` for a backward one;
* `pathHol_gaugeTransform` — gauge covariance
  `pathHol (g · U) x p = g x · pathHol U x p · g(end)⁻¹`;
* `IsLoop`, `pathHol_gaugeTransform_loop` — for a closed path the holonomy is
  *conjugated* by the gauge function at the base point;
* `pathHol_translate`, `pathEnd_translate` — translation covariance: the
  translate of a loop observable is the observable of the translated loop;
* `wilsonLoop` — the literal Wilson-loop observable `χ ∘ pathHol`, with
  `wilsonLoop_gaugeTransform` (gauge invariance for a conjugation-invariant
  character), `wilsonLoop_translate`, `continuous_wilsonLoop` and
  `measurable_wilsonLoop`;
* `plaquettePath`, `pathHol_plaquettePath`, `isLoop_plaquettePath` — the
  plaquette is the Wilson loop of the elementary square, so
  `wilsonAction_eq_sum_wilsonLoop` presents the literal Wilson action as a sum
  of literal Wilson-loop observables.
-/
import Mathlib
import RequestProject.YangMills.Lattice.Wilson

namespace RequestProject.YangMills.Lattice

open MeasureTheory

/-! ## Paths on the lattice -/

/-- A directed lattice step: a direction together with an orientation
(`true` = along the positive direction, `false` = against it). -/
abbrev Step := Fin 4 × Bool

variable {n : ℕ}

/-- The displacement produced by a step. -/
def stepShift (n : ℕ) (s : Step) : Site n :=
  if s.2 then unitVec n s.1 else -unitVec n s.1

/-- The endpoint of the path of steps `p` started at `x`. -/
def pathEnd (n : ℕ) : Site n → List Step → Site n
  | x, [] => x
  | x, s :: rest => pathEnd n (x + stepShift n s) rest

@[simp] theorem pathEnd_nil (x : Site n) : pathEnd n x [] = x := rfl

@[simp] theorem pathEnd_cons (x : Site n) (s : Step) (p : List Step) :
    pathEnd n x (s :: p) = pathEnd n (x + stepShift n s) p := rfl

/-- The endpoint map commutes with translations of the base point. -/
theorem pathEnd_add (x v : Site n) (p : List Step) :
    pathEnd n (x + v) p = pathEnd n x p + v := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
      simp only [pathEnd_cons]
      rw [add_right_comm, ih]

section Holonomy

variable {G : Type*} [Group G]

/-- The literal parallel transporter along a single step: the link variable for
a forward step, its inverse for a backward step. -/
def stepHol (U : Conf n G) (x : Site n) (s : Step) : G :=
  if s.2 then U (x, s.1) else (U (x - unitVec n s.1, s.1))⁻¹

/-- The literal holonomy along a path: the ordered product of the step
transporters. -/
def pathHol (U : Conf n G) : Site n → List Step → G
  | _, [] => 1
  | x, s :: rest => stepHol U x s * pathHol U (x + stepShift n s) rest

@[simp] theorem pathHol_nil (U : Conf n G) (x : Site n) : pathHol U x [] = 1 := rfl

@[simp] theorem pathHol_cons (U : Conf n G) (x : Site n) (s : Step) (p : List Step) :
    pathHol U x (s :: p) = stepHol U x s * pathHol U (x + stepShift n s) p := rfl

/-- A path is a **loop** when it returns to its base point. -/
def IsLoop (n : ℕ) (x : Site n) (p : List Step) : Prop := pathEnd n x p = x

/-! ### Gauge covariance -/

theorem stepHol_gaugeTransform (g : Site n → G) (U : Conf n G) (x : Site n) (s : Step) :
    stepHol (gaugeTransform g U) x s = g x * stepHol U x s * (g (x + stepShift n s))⁻¹ := by
  cases s with
  | mk d b =>
    cases b with
    | true => simp [stepHol, gaugeTransform, stepShift]
    | false =>
        have hx : x - unitVec n d + unitVec n d = x := by abel
        simp only [stepHol, gaugeTransform, stepShift, if_false, Bool.false_eq_true, hx]
        have : x + -unitVec n d = x - unitVec n d := by abel
        rw [this]
        group

/-- **Gauge covariance of the holonomy**: it is conjugated by the gauge
function at the two endpoints of the path. -/
theorem pathHol_gaugeTransform (g : Site n → G) (U : Conf n G) (x : Site n) (p : List Step) :
    pathHol (gaugeTransform g U) x p = g x * pathHol U x p * (g (pathEnd n x p))⁻¹ := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih =>
      simp only [pathHol_cons, pathEnd_cons, ih, stepHol_gaugeTransform]
      group

/-- For a **closed** path the holonomy is conjugated by the gauge function at
the base point. -/
theorem pathHol_gaugeTransform_loop {g : Site n → G} {U : Conf n G} {x : Site n}
    {p : List Step} (hp : IsLoop n x p) :
    pathHol (gaugeTransform g U) x p = g x * pathHol U x p * (g x)⁻¹ := by
  rw [pathHol_gaugeTransform, hp]

/-! ### Translation covariance -/

theorem stepHol_translate (v : Site n) (U : Conf n G) (x : Site n) (s : Step) :
    stepHol (translate v U) x s = stepHol U (x + v) s := by
  cases s with
  | mk d b =>
    cases b with
    | true => simp [stepHol, translate]
    | false =>
        have : x - unitVec n d + v = x + v - unitVec n d := by abel
        simp [stepHol, translate, this]

/-- **Translation covariance of the holonomy**: translating the configuration
translates the base point of the path. -/
theorem pathHol_translate (v : Site n) (U : Conf n G) (x : Site n) (p : List Step) :
    pathHol (translate v U) x p = pathHol U (x + v) p := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
      simp only [pathHol_cons, ih, stepHol_translate]
      rw [add_right_comm]

/-- A translated loop is a loop. -/
theorem isLoop_add {x : Site n} {p : List Step} (hp : IsLoop n x p) (v : Site n) :
    IsLoop n (x + v) p := by
  simpa [IsLoop, pathEnd_add] using congrArg (fun y : Site n => y + v) hp

end Holonomy

/-! ## The Wilson-loop observable -/

section Observable

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- The literal Wilson-loop observable of the path `p` based at `x`. -/
def wilsonLoop (chi : G → ℝ) (x : Site n) (p : List Step) (U : Conf n G) : ℝ :=
  chi (pathHol U x p)

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- **Gauge invariance of a Wilson loop** for a conjugation-invariant
character. -/
theorem wilsonLoop_gaugeTransform {chi : G → ℝ}
    (hchi : ∀ a g : G, chi (a * g * a⁻¹) = chi g) {x : Site n} {p : List Step}
    (hp : IsLoop n x p) (g : Site n → G) (U : Conf n G) :
    wilsonLoop chi x p (gaugeTransform g U) = wilsonLoop chi x p U := by
  simp only [wilsonLoop, pathHol_gaugeTransform_loop hp, hchi]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- **Translation covariance of a Wilson loop**: the translate of the observable
of a loop is the observable of the translated loop. -/
theorem wilsonLoop_translate (chi : G → ℝ) (x v : Site n) (p : List Step) (U : Conf n G) :
    wilsonLoop chi x p (translate v U) = wilsonLoop chi (x + v) p U := by
  simp [wilsonLoop, pathHol_translate]

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem continuous_stepHol (x : Site n) (s : Step) :
    Continuous fun U : Conf n G => stepHol U x s := by
  cases s with
  | mk d b =>
    cases b with
    | true =>
        simpa [stepHol] using
          continuous_apply (A := fun _ : Link n => G) ((x, d) : Link n)
    | false =>
        simpa [stepHol] using
          continuous_inv.comp
            (continuous_apply (A := fun _ : Link n => G) ((x - unitVec n d, d) : Link n))

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem continuous_pathHol (x : Site n) (p : List Step) :
    Continuous fun U : Conf n G => pathHol U x p := by
  induction p generalizing x with
  | nil => exact continuous_const
  | cons s p ih => exact (continuous_stepHol x s).mul (ih _)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem continuous_wilsonLoop {chi : G → ℝ} (hchi : Continuous chi) (x : Site n)
    (p : List Step) : Continuous (wilsonLoop chi x p : Conf n G → ℝ) :=
  hchi.comp (continuous_pathHol x p)

theorem measurable_wilsonLoop {chi : G → ℝ} (hchi : Continuous chi) (x : Site n)
    (p : List Step) : Measurable (wilsonLoop chi x p : Conf n G → ℝ) :=
  (continuous_wilsonLoop hchi x p).measurable

end Observable

/-! ## The plaquette is a Wilson loop -/

section Plaquette

variable {G : Type*} [Group G]

/-- The elementary square in the `(μ,ν)` plane, as a path of four steps. -/
def plaquettePath (mu nu : Fin 4) : List Step :=
  [(mu, true), (nu, true), (mu, false), (nu, false)]

theorem site_square_cancel (x u v : Site n) : x + u + v + -u + -v = x := by
  abel

theorem site_square_cancel' (x u v : Site n) : x + u + v + -u - v = x := by
  abel

@[simp] theorem isLoop_plaquettePath (x : Site n) (mu nu : Fin 4) :
    IsLoop n x (plaquettePath mu nu) := by
  simp only [IsLoop, plaquettePath, pathEnd_cons, pathEnd_nil, stepShift]
  exact site_square_cancel x _ _

/-- The literal plaquette holonomy **is** the holonomy of the elementary
square. -/
theorem pathHol_plaquettePath (U : Conf n G) (x : Site n) (mu nu : Fin 4) :
    pathHol U x (plaquettePath mu nu) = plaqHol U x mu nu := by
  have h2 : x + unitVec n mu + unitVec n nu - unitVec n mu = x + unitVec n nu := by
    abel
  have h3 : x + unitVec n mu + unitVec n nu + -unitVec n mu - unitVec n nu = x :=
    site_square_cancel' x _ _
  simp only [plaquettePath, pathHol_cons, pathHol_nil, stepHol, stepShift, plaqHol,
    if_true, if_false, Bool.false_eq_true, h2, h3]
  group

/-- **The literal Wilson action is a sum of literal Wilson-loop observables.**
This is the presentation the physical route calls for: no auxiliary encoding of
the action appears, only the loop observables of the elementary squares. -/
theorem wilsonAction_eq_sum_wilsonLoop (beta : ℝ) (chi : G → ℝ) (U : Conf n G) :
    wilsonAction beta chi U =
      -beta * ∑ x : Site n, ∑ mu : Fin 4, ∑ nu : Fin 4,
        wilsonLoop chi x (plaquettePath mu nu) U := by
  simp [wilsonAction, wilsonLoop, pathHol_plaquettePath]

end Plaquette

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms pathHol_gaugeTransform
#print axioms wilsonLoop_gaugeTransform
#print axioms wilsonLoop_translate
#print axioms pathHol_plaquettePath
#print axioms wilsonAction_eq_sum_wilsonLoop

end Audit
