/-
The **one-sided** finite window retains a coercive Gram defect.

`WindowGram.lean` treats a window that is *symmetric* about the target
ordinate, where the conjugation symmetry of a real even taper makes the cross
Gram entry vanish identically.  The matrix the source actually builds indexes
its finite window by `0 ≤ k < d`, one-sided; for such a window the `+k`/`-k`
cancellation is gone and the cross entry

  `C_d = ∑_{0 ≤ k < d} Re φ̂_k · Im φ̂_k`

is **not** expected to be small.  So the question raised by the pair-block
algebra is genuine:

  `frobSq (pairBlock m a b) = 4m²(A - B)² + 8m²(AB - C²)`,

and a lower bound for the retained transverse energy `B` alone does **not**
give a positive transverse surplus: if `b` were proportional to `a` then
`AB - C² = 0` however large `B` is (`imagEnergy_pos_not_sufficient` below).
What the finite block really cares about is the Gram determinant
`ΔGram = AB - C² = |a ∧ b|²`.

This file settles the question for the one-sided source window, and the answer
is affirmative and unconditional — but for a reason different from a
tail-correlation estimate.  The one-sided window *contains the central grid
point* `k = 0`, and for a real even taper the central sample

  `φ̂(-iα) = ∫ φ(t) e^{-αt} dt`

is **real**: its imaginary part vanishes exactly (`gridSample_zero_im`).  Hence
the coordinate `k = 0` is a direction in which `a` is nonzero and `b` vanishes,
which is exactly the non-parallelism the Gram determinant measures.
Quantitatively, splitting off that coordinate and applying Cauchy--Schwarz to
the remaining ones gives the *unconditional* separation

  `AB - C² ≥ (Re φ̂(-iα))² · B`

(`gramDefect_ge_head_sq_mul`, `finiteGridGramDefect_ge`).  Both factors are
already bounded below in this development: the head factor by the plateau
bound `(Re φ̂(-iα))² ≥ (2a)²` of `WindowGram.lean`, and the transverse energy
`B` by the quantitative lattice tail of `GridTail.lean`.  The result is the
explicit one-sided floor

  `ΔGram(d) ≥ (9/16) L² ((9/512) L⁴ α² - C_φ(α)²/(h² m))`

in the source regime `a ≥ 3L/8`, i.e. a Gram defect that is coercive of order
`α²` as soon as the window is long enough to absorb the lattice tail
(`finiteGridGramDefect_source_floor`, `finiteGridGramDefect_pos`), and the
corresponding pair-block surplus floor
`oneSidedTransverseSurplus_source_floor`.

So the retained imaginary energy is *not* by itself the same thing as a
positive Frobenius defect — but on the actual one-sided source window the two
are linked by the real central sample, with an explicit constant.
-/
import RiemannAnalytic.GridVectors
import RiemannAnalytic.WindowGram

namespace RiemannAnalytic

open Complex Finset

variable {n : Type*} [Fintype n]

/-! ### The Gram defect of a pair block -/

/-- The **Gram defect** of the two real coordinate vectors of a pair block:
`ΔGram = AB - C² = |a|²|b|² - (a·b)²`, the determinant of the Gram matrix of
`a` and `b`. -/
def gramDefect (a b : n → ℝ) : ℝ := (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2

/-- The Gram defect is nonnegative: this is Cauchy--Schwarz. -/
theorem gramDefect_nonneg (a b : n → ℝ) : 0 ≤ gramDefect a b := gram_nonneg a b

/-- The transverse surplus of a pair block is `8m²` times the Gram defect. -/
theorem transverseSurplus_eq_gramDefect (m : ℝ) (a b : n → ℝ) :
    transverseSurplus m a b = 8 * m ^ 2 * gramDefect a b := rfl

/-- **Gram decomposition of the pair-block Frobenius square.**  With
`A = |a|²`, `B = |b|²`, `C = a·b`,

  `‖2m(aaᵀ - bbᵀ)‖_F² = 4m²(A - B)² + 8m²(AB - C²)`. -/
theorem pairBlock_gramDecomposition (m : ℝ) (a b : n → ℝ) :
    frobSq (pairBlock m a b)
      = 4 * m ^ 2 * ((a ⬝ᵥ a) - (b ⬝ᵥ b)) ^ 2 + 8 * m ^ 2 * gramDefect a b := by
  rw [pairBlock_frobSq]
  unfold gramDefect
  ring

/-- **Retained transverse energy is not by itself a positive Frobenius
defect.**  There are coordinate vectors with strictly positive imaginary
energy `B` whose Gram defect vanishes — namely any pair with `b` parallel to
`a`.  This is why the finite window has to retain *angular separation*, not
just energy. -/
theorem imagEnergy_pos_not_sufficient :
    ∃ a b : Fin 2 → ℝ, 0 < b ⬝ᵥ b ∧ gramDefect a b = 0 := by
  refine ⟨![1, 0], ![1, 0], ?_, ?_⟩ <;>
    simp [dotProduct, gramDefect, Fin.sum_univ_succ]

/-! ### A coordinate where the imaginary part vanishes separates the channels -/

/-- **The head-coordinate separation bound.**  If the imaginary coordinate
vector vanishes at some coordinate where the real one need not, the Gram defect
is at least the square of that real coordinate times the whole imaginary
energy:

  `AB - C² ≥ a₀² · B`.

Splitting off the coordinate and applying Cauchy--Schwarz to the rest, the
inequality is exact up to the Gram defect of the remaining coordinates. -/
theorem gramDefect_ge_head_sq_mul {d : ℕ} (a b : Fin (d + 1) → ℝ) (hb : b 0 = 0) :
    a 0 ^ 2 * (b ⬝ᵥ b) ≤ gramDefect a b := by
  set a' : Fin d → ℝ := fun i => a i.succ with ha'
  set b' : Fin d → ℝ := fun i => b i.succ with hb'
  have haa : a ⬝ᵥ a = a 0 ^ 2 + a' ⬝ᵥ a' := by
    simp [dotProduct, Fin.sum_univ_succ, ha', sq]
  have hbb : b ⬝ᵥ b = b' ⬝ᵥ b' := by
    simp [dotProduct, Fin.sum_univ_succ, hb', hb]
  have hab : a ⬝ᵥ b = a' ⬝ᵥ b' := by
    simp [dotProduct, Fin.sum_univ_succ, ha', hb', hb]
  have hrest : 0 ≤ gramDefect a' b' := gramDefect_nonneg a' b'
  unfold gramDefect at hrest ⊢
  rw [haa, hbb, hab]
  nlinarith [hrest]

/-! ### The one-sided grid window -/

/-- The Gram defect of the one-sided finite evaluation window
`u(k) = φ̂(-iα + k h)`, `0 ≤ k < d`, of a zero at transverse offset `α`. -/
noncomputable def finiteGridGramDefect (φ : ℝ → ℝ) (h α : ℝ) (d : ℕ) : ℝ :=
  gramDefect (reOf (gridVec φ h (-(Complex.I * (α : ℂ))) d))
    (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) d))

/-- The head coordinate of the one-sided window is the central grid sample. -/
theorem gridVec_head (φ : ℝ → ℝ) (h α : ℝ) (d : ℕ) :
    gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1) 0 = gridSample φ h α 0 := by
  have h0 := gridVec_eq_gridSample φ h α (d + 1) 0
  simpa using h0

/-- **The imaginary part of the head coordinate vanishes.**  For a real even
taper the central sample `φ̂(-iα)` is real. -/
theorem imOf_gridVec_head (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ) (d : ℕ) :
    imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1)) 0 = 0 := by
  unfold imOf
  rw [gridVec_head φ h α d, gridSample_zero_im φ hev h α]

/-- The real part of the head coordinate. -/
theorem reOf_gridVec_head (φ : ℝ → ℝ) (h α : ℝ) (d : ℕ) :
    reOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1)) 0 = (gridSample φ h α 0).re := by
  unfold reOf
  rw [gridVec_head φ h α d]

/-- **The one-sided window separates the two channels.**  Unconditionally,

  `ΔGram(d+1) ≥ (Re φ̂(-iα))² · B_{d+1}`,

with `B` the retained transverse energy of the window: the central grid point,
where the sample is real, supplies the required angular separation between the
real and imaginary coordinate vectors. -/
theorem finiteGridGramDefect_ge (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ) (d : ℕ) :
    (gridSample φ h α 0).re ^ 2
        * (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1))
            ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1)))
      ≤ finiteGridGramDefect φ h α (d + 1) := by
  have h0 := gramDefect_ge_head_sq_mul
    (reOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1)))
    (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1)))
    (imOf_gridVec_head φ hev h α d)
  rwa [reOf_gridVec_head φ h α d] at h0

/-! ### The explicit one-sided floor -/

/-- **Lower bound for the longitudinal head factor.**  For a nonnegative taper
with a plateau of half-width `a`, the squared central sample is at least
`4a²`. -/
theorem gridRealEnergyLower {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    (hnn : ∀ t, 0 ≤ φ t) {a : ℝ} (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (h α : ℝ) :
    4 * a ^ 2 ≤ (gridSample φ h α 0).re ^ 2 := by
  have hc := gridSample_zero_re_ge_plateau hφ hnn ha hplat h α
  nlinarith [ha]

/-- **Explicit floor for the one-sided finite Gram defect.**

For a `C¹`, nonnegative, real even taper supported in `[-R, R]` with `2R ≤ L`,
a plateau of half-width `a`, grid spacing `h = 2π/L` and any window length
`m ≥ 1`,

  `ΔGram(m+1) ≥ 4a² · ((L/4)·taperExcess φ α - C_φ(α)²/(h² m))`. -/
theorem finiteGridGramDefectLower {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    4 * a ^ 2 * (L / 4 * taperExcess φ α
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m))
      ≤ finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  set h := 2 * Real.pi / L with hh
  set B := imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
      ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1)) with hB
  have hsep := finiteGridGramDefect_ge φ hev h α m
  have hhead := gridRealEnergyLower hφ.toCompactTaper hnn ha hplat h α
  have hBlow : L / 4 * taperExcess φ α
      - derivMass φ α ^ 2 / (h ^ 2 * m) ≤ B := imOf_gridVec_lower hφ hev hL h2R α hm
  have hBnn : 0 ≤ B := by
    rw [hB, imOf_dotProduct_self]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hann : (0 : ℝ) ≤ 4 * a ^ 2 := by positivity
  nlinarith [hsep, hhead, hBlow, hBnn, hann, sq_nonneg (gridSample φ h α 0).re]

/-- **Explicit quadratic floor for the one-sided Gram defect in the source
regime.**

With plateau half-width `a ≥ 3L/8` (the source regime `8w ≤ L`),

  `ΔGram(m+1) ≥ (9/16) L² ((9/512) L⁴ α² - C_φ(α)²/(h² m))`.

So the Gram determinant of the *actual one-sided* source window — not just the
retained imaginary energy — is coercive of order `α²`, up to the explicit
lattice tail. -/
theorem finiteGridGramDefect_source_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m))
      ≤ finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  set h := 2 * Real.pi / L with hh
  have ha0 : 0 ≤ a := by linarith
  set B := imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
      ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1)) with hB
  have hsep := finiteGridGramDefect_ge φ hev h α m
  -- the head factor
  have hhead : 9 / 16 * L ^ 2 ≤ (gridSample φ h α 0).re ^ 2 := by
    have h4 := gridRealEnergyLower hφ.toCompactTaper hnn ha0 hplat h α
    nlinarith [ha, hL.le]
  -- the transverse factor
  have hBlow : 9 / 512 * L ^ 4 * α ^ 2
      - derivMass φ α ^ 2 / (h ^ 2 * m) ≤ B := by
    have hwin : L / 4 * taperExcess φ α
        - derivMass φ α ^ 2 / (h ^ 2 * m) ≤ B := imOf_gridVec_lower hφ hev hL h2R α hm
    have hexc := taperExcess_ge_plateau_quadratic hφ.toCompactTaper ha0 hplat α
    have hcube : (3 * L / 8) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by positivity) ha 3
    have hkey : 9 / 128 * L ^ 3 * α ^ 2 ≤ taperExcess φ α := by
      have hstep : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 ≤ 4 / 3 * a ^ 3 * α ^ 2 := by
        nlinarith [sq_nonneg α, hcube]
      have hval : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 = 9 / 128 * L ^ 3 * α ^ 2 := by ring
      linarith
    have hfloor : 9 / 512 * L ^ 4 * α ^ 2 ≤ L / 4 * taperExcess φ α := by
      nlinarith [hkey, hL.le]
    linarith
  have hBnn : 0 ≤ B := by
    rw [hB, imOf_dotProduct_self]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith [hsep, hhead, hBlow, hBnn, sq_nonneg L, sq_nonneg (gridSample φ h α 0).re]

/-- **Strict positivity of the one-sided Gram defect.**  Once the window is
long enough to absorb the lattice tail, an off-line offset `α` forces a
strictly positive Gram determinant on the actual one-sided source window. -/
theorem finiteGridGramDefect_pos {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m)
    (hbig : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) < 9 / 512 * L ^ 4 * α ^ 2) :
    0 < finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  have hd : 0 < 9 / 512 * L ^ 4 * α ^ 2
      - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) := by linarith
  have hprod := mul_pos (show (0 : ℝ) < 9 / 16 * L ^ 2 by positivity) hd
  linarith

/-! ### The pair-block surplus of the one-sided window -/

/-- The transverse surplus of the pair block built from the one-sided window is
`8m'²` times its Gram defect. -/
theorem oneSidedTransverseSurplus_eq (φ : ℝ → ℝ) (h α : ℝ) (d : ℕ) (m' : ℝ) :
    transverseSurplus m' (reOf (gridVec φ h (-(Complex.I * (α : ℂ))) d))
        (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) d))
      = 8 * m' ^ 2 * finiteGridGramDefect φ h α d := rfl

/-- **Explicit floor for the one-sided pair-block transverse surplus.**

In the source regime, the transverse surplus of the pair block of a
hypothetical off-line zero, computed on the *one-sided* finite window the
source matrix actually uses, is at least

  `8 m'² · (9/16) L² ((9/512) L⁴ α² - C_φ(α)²/(h² m))`. -/
theorem oneSidedTransverseSurplus_source_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (m' : ℝ) :
    8 * m' ^ 2 * (9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)))
      ≤ transverseSurplus m'
          (reOf (gridVec φ (2 * Real.pi / L) (-(Complex.I * (α : ℂ))) (m + 1)))
          (imOf (gridVec φ (2 * Real.pi / L) (-(Complex.I * (α : ℂ))) (m + 1))) := by
  rw [oneSidedTransverseSurplus_eq]
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  nlinarith [sq_nonneg m', hfloor]

end RiemannAnalytic
