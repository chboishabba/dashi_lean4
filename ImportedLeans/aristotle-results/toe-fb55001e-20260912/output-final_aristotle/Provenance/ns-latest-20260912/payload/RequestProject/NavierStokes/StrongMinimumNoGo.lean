/-
# The strong minimum principle is not available for `S₂`

`RequestProject/NavierStokes/KarmanHowarth.lean` derives the exact localized
Kármán–Howarth identity

`∂_t S₂ + ∇_h·F₃ = −2ν∫Φ|∇_x δ_h u|² + (cutoff errors)`,

in which the dissipation enters with a *negative* sign.  Together with
`ClayNS.khm_balance_at_zero_separation` — which shows that at `h = 0` the two
sides of the Kármán–Howarth–Monin balance reduce to `0 = 0` — this pins down
the direction of the differential inequality that `S₂` satisfies: `S₂` is a
*subsolution* of the drift-diffusion operator,

`∂_t S + ∇_h·(bS) − 2νΔ_h S ≤ 0`,

not a supersolution.  This file records the elementary but decisive
consequence: for subsolutions there is no strong minimum principle, so the
hoped-for shortcut

  "`S ≥ 0`, `S(0,t) = 0`, no positive source, hence `S ≡ 0` by an interior
  minimum argument"

is not available, no matter how good the localization is.  The witness is the
stationary, drift-free, nonnegative function `S(h) = h₀²`, which vanishes at
`h = 0`, satisfies the subsolution inequality with room to spare
(`0 ≤ 4ν`), and is not identically zero.

The point is *not* that De Giorgi–Nash–Moser theory fails here; it is that the
rigidity step must be an oscillation-decay/Harnack argument for subsolutions
(or must first flip the sign of the source), and cannot be a one-line strong
minimum principle.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.KarmanHowarth

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The first separation coordinate, as a continuous linear functional. -/
def sepCoord : STime →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 3)).comp (ContinuousLinearMap.snd ℝ ℝ E3)

@[simp] lemma sepCoord_apply (z : STime) : sepCoord z = z.2 0 := rfl

@[simp] lemma sepCoord_time : sepCoord (1, 0) = 0 := by simp [sepCoord]

lemma sepCoord_space (i : Fin 3) : sepCoord (0, ee i) = if i = 0 then 1 else 0 := by
  simp only [sepCoord_apply, ee, EuclideanSpace.single_apply]
  by_cases h : i = 0 <;> simp [h, eq_comm]

/-- The candidate structure function `S(h) = h₀²`. -/
def sqCoord : STime → ℝ := fun z => sepCoord z * sepCoord z

lemma contDiff_sqCoord : ContDiff ℝ (⊤ : ℕ∞) sqCoord :=
  sepCoord.contDiff.mul sepCoord.contDiff

lemma sqCoord_nonneg (z : STime) : 0 ≤ sqCoord z := mul_self_nonneg _

@[simp] lemma sqCoord_at_zero (t : ℝ) : sqCoord (t, 0) = 0 := by simp [sqCoord]

lemma dvec_sqCoord (a z : STime) : dvec a sqCoord z = 2 * sepCoord z * sepCoord a := by
  have hd : HasFDerivAt sqCoord (sepCoord z • sepCoord + sepCoord z • sepCoord) z :=
    sepCoord.hasFDerivAt.mul sepCoord.hasFDerivAt
  have : dvec a sqCoord z = (sepCoord z • sepCoord + sepCoord z • sepCoord) a :=
    congrArg (fun L : STime →L[ℝ] ℝ => L a) hd.fderiv
  rw [this]
  simp
  ring

lemma dvec_dvec_sqCoord (a b z : STime) :
    dvec b (fun w => dvec a sqCoord w) z = 2 * sepCoord b * sepCoord a := by
  have hfun : (fun w => dvec a sqCoord w) = fun w => (2 * sepCoord a) * sepCoord w := by
    funext w; rw [dvec_sqCoord a w]; ring
  have hd : HasFDerivAt (fun w : STime => (2 * sepCoord a) * sepCoord w)
      ((2 * sepCoord a) • sepCoord) z := sepCoord.hasFDerivAt.const_mul _
  rw [hfun]
  have : dvec b (fun w : STime => (2 * sepCoord a) * sepCoord w) z
      = ((2 * sepCoord a) • sepCoord) b :=
    congrArg (fun L : STime →L[ℝ] ℝ => L b) hd.fderiv
  rw [this]
  simp
  ring

/-- The separation Laplacian of `S(h) = h₀²` is the constant `2`. -/
lemma lap_sqCoord (z : STime) : lap sqCoord z = 2 := by
  have hterm : ∀ i : Fin 3, dspace (fun w => dspace sqCoord i w) i z
      = 2 * sepCoord (0, ee i) * sepCoord (0, ee i) := by
    intro i
    simp only [dspace_eq_dvec]
    exact dvec_dvec_sqCoord (0, ee i) (0, ee i) z
  simp only [lap, hterm, sepCoord_space, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]

/-- The zero drift field has vanishing weighted divergence. -/
lemma divg_smul_zero (S : STime → ℝ) (z : STime) :
    divg (fun w => S w • (0 : E3)) z = 0 := by
  simp only [smul_zero, divg, dspace]
  simp

/-- **No strong minimum principle for the Kármán–Howarth subsolution
inequality.**  For every `ν ≥ 0` there is a smooth, nonnegative, stationary
function `S` on separation space with bounded (indeed zero) drift `b` such that

* `S ≥ 0`,
* `S(t, 0) = 0` for every time — an interior zero minimum,
* `∂_t S + ∇_h·(bS) ≤ 2νΔ_h S` — the subsolution inequality with **no positive
  source**, exactly the form produced by the localized Kármán–Howarth identity,

and yet `S ≢ 0`.  So the interior zero of `S₂` at `h = 0` cannot by itself
force `S₂ ≡ 0`: the rigidity step of the programme has to be a genuine
oscillation-decay (De Giorgi–Nash–Moser / Harnack) argument, or has to exploit
a supersolution property that the identity does not supply. -/
theorem parabolic_strong_minimum_no_go (nu : ℝ) (hnu : 0 ≤ nu) :
    ∃ (S : STime → ℝ) (b : STime → E3),
      ContDiff ℝ (⊤ : ℕ∞) S ∧ ContDiff ℝ (⊤ : ℕ∞) b ∧
      (∀ z, 0 ≤ S z) ∧
      (∀ t : ℝ, S (t, 0) = 0) ∧
      (∀ (z : STime) (i : Fin 3), |b z i| ≤ 2) ∧
      (∀ z, dvec (1, 0) S z + divg (fun w => S w • b w) z ≤ 2 * nu * lap S z) ∧
      ∃ z : STime, S z ≠ 0 := by
  refine ⟨sqCoord, fun _ => 0, contDiff_sqCoord, contDiff_const, sqCoord_nonneg,
    sqCoord_at_zero, fun z i => by simp, fun z => ?_, ⟨(0, ee 0), ?_⟩⟩
  · rw [divg_smul_zero, dvec_sqCoord, lap_sqCoord]
    simp only [sepCoord_time, mul_zero, add_zero]
    linarith
  · have : sqCoord ((0 : ℝ), ee 0) = 1 := by
      simp only [sqCoord, sepCoord_apply]
      simp [ee]
    rw [this]
    norm_num

end ClayNS
