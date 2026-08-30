/-
**G9.3 / G9.4 — the critical-line phase gauge, and what it does to the defect.**

The directional (one-sided damped) taper of `OneSidedDampedTaper.lean` repairs
the exponential obstruction of Lane A, but it loses the property that made the
Hermitian defect an RH *detector*: for a real **even** taper `Φ̂` is real on the
real axis, so the transverse coordinates `b_j = Im Φ̂(−jh)` all vanish at
`α = 0`; for a one-sided taper they do not, so a *baseline* defect `𝒜_ψ(0) > 0`
can appear that has nothing to do with the position of the zero.

This file settles the two structural questions G9 asks about that, exactly.

* `gramDefect_eq_hermitian_sub_bilinear` — **the transverse defect is the
  Hermitian-versus-bilinear gap.**  For any complex window vector `u`, with
  `a = Re u`, `b = Im u`,

      `ΔGram(a,b) = ¼ ( (∑ₖ|uₖ|²)² − |∑ₖ uₖ²|² )`.

  So the defect vanishes iff the two channels agree, i.e. iff the window vector
  is a single unimodular multiple of a real vector (`gramDefect_eq_zero_iff_…`).

* `Hsesq_coordGauge` — **`phaseGauge_gramInvariant`**: a coordinatewise
  unit-phase gauge `uₖ ↦ gₖuₖ`, `|gₖ| = 1`, leaves the whole Hermitian channel
  (hence every Hermitian Gram entry, every diagonal, and every Hermitian
  anchored minor `hermAnchorMinor`) unchanged; `Sbil_coordGauge` records that it
  moves the *bilinear* channel by `gₖ²`, and
  `exists_coordGauge_Sbil_ne` witnesses that this motion is real, so the
  invariance genuinely cannot be extended to the bilinear channel.

* `criticalPhase` and `gaugedBaseline_im_eq_zero` — the gauge that removes the
  critical-line phase coordinatewise, `g_k = e^{-i arg u_k}`, makes the gauged
  baseline vector *real and nonnegative* coordinatewise; hence

* `gaugedDefect_zero_at_baseline` — **the answer to G9.3/G9.4**: after the
  critical-line phase gauge the one-sided anchored defect at `α = 0` is exactly
  `0`, for *any* taper, even or not.  The unwanted "geometric phase" background
  of an asymmetric taper is removed by a unitary change of coordinates, not by
  an estimate.

* `gaugedDefect_eq` — and the price, stated exactly: at `α ≠ 0` the (frozen)
  gauge acts on the bilinear channel only,

      `ΔGram(gauged) = ¼ ( (∑|uₖ(α)|²)² − |∑ gₖ² uₖ(α)²|² )`,

  so the coercive floor for the gauged family is a statement about the *gauged
  bilinear channel* `∑ gₖ²uₖ(α)²`, which is exactly the new obligation the G9
  programme names.  It is not proved here and nothing below assumes it.

Nothing in this file refers to `ζ`.
-/
import RiemannAnalytic.GridVectors
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open Complex Finset

variable {d : ℕ}

/-! ### The transverse defect is the Hermitian-versus-bilinear gap -/

/-- The Hermitian channel of a window vector with itself is its total energy. -/
theorem Hsesq_self_re (u : Fin d → ℂ) : (Hsesq u u).re = ∑ k, ‖u k‖ ^ 2 := by
  unfold Hsesq
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- **The transverse defect of a complex window is the Hermitian-versus-bilinear
gap.**  With `a = Re u`, `b = Im u`,

    `ΔGram(a,b) = ¼((∑|uₖ|²)² − |∑uₖ²|²)`.

No hypothesis on the taper: this is pure algebra of the real/imaginary split. -/
theorem gramDefect_eq_hermitian_sub_bilinear (u : Fin d → ℂ) :
    gramDefect (reOf u) (imOf u)
      = 1 / 4 * ((Hsesq u u).re ^ 2 - Complex.normSq (Sbil u u)) := by
  have hH : (Hsesq u u).re = (reOf u ⬝ᵥ reOf u) + (imOf u ⬝ᵥ imOf u) := by
    unfold Hsesq reOf imOf dotProduct
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re]
  have hSre : (Sbil u u).re = (reOf u ⬝ᵥ reOf u) - (imOf u ⬝ᵥ imOf u) := by
    unfold Sbil reOf imOf dotProduct
    rw [Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re]
  have hSim : (Sbil u u).im = 2 * (reOf u ⬝ᵥ imOf u) := by
    unfold Sbil reOf imOf dotProduct
    rw [Complex.im_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_im]
    ring
  unfold gramDefect
  rw [Complex.normSq_apply, hH, hSre, hSim]
  ring

/-- The defect vanishes exactly when the two channels agree in modulus. -/
theorem gramDefect_eq_zero_iff_channels (u : Fin d → ℂ) :
    gramDefect (reOf u) (imOf u) = 0 ↔ (Hsesq u u).re ^ 2 = Complex.normSq (Sbil u u) := by
  rw [gramDefect_eq_hermitian_sub_bilinear]
  constructor
  · intro h; linarith [h]
  · intro h; rw [h]; ring

/-! ### The coordinatewise unit-phase gauge -/

/-- A coordinatewise gauge: multiply each coordinate by its own scalar. -/
def coordGauge (g u : Fin d → ℂ) : Fin d → ℂ := fun k => g k * u k

/-- **`phaseGauge_gramInvariant`.**  A coordinatewise *unit* gauge preserves the
whole Hermitian channel: every Hermitian Gram entry of every pair of window
vectors is unchanged. -/
theorem Hsesq_coordGauge (g u v : Fin d → ℂ) (hg : ∀ k, ‖g k‖ = 1) :
    Hsesq (coordGauge g u) (coordGauge g v) = Hsesq u v := by
  unfold Hsesq coordGauge
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : g k * (starRingEnd ℂ) (g k) = 1 := by
    rw [Complex.mul_conj]
    have hnk : Complex.normSq (g k) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hg k]; norm_num
    simp [hnk]
  calc g k * u k * (starRingEnd ℂ) (g k * v k)
      = (g k * (starRingEnd ℂ) (g k)) * (u k * (starRingEnd ℂ) (v k)) := by
        rw [map_mul]; ring
    _ = u k * (starRingEnd ℂ) (v k) := by rw [hk, one_mul]

/-- The energy of a window is gauge invariant. -/
theorem energy_coordGauge (g u : Fin d → ℂ) (hg : ∀ k, ‖g k‖ = 1) :
    ∑ k, ‖coordGauge g u k‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
  rw [← Hsesq_self_re, ← Hsesq_self_re, Hsesq_coordGauge g u u hg]

/-- The **Hermitian** anchored minor of a pair of window vectors. -/
noncomputable def hermAnchorMinor (u v : Fin d → ℂ) : ℝ :=
  (Hsesq u u).re * (Hsesq v v).re - Complex.normSq (Hsesq u v)

/-- **The Hermitian anchored minor is gauge invariant.** -/
theorem hermAnchorMinor_coordGauge (g u v : Fin d → ℂ) (hg : ∀ k, ‖g k‖ = 1) :
    hermAnchorMinor (coordGauge g u) (coordGauge g v) = hermAnchorMinor u v := by
  unfold hermAnchorMinor
  rw [Hsesq_coordGauge g u u hg, Hsesq_coordGauge g v v hg, Hsesq_coordGauge g u v hg]

/-- The gauge moves the **bilinear** channel by the squares of the phases. -/
theorem Sbil_coordGauge (g u v : Fin d → ℂ) :
    Sbil (coordGauge g u) (coordGauge g v) = ∑ k, (g k) ^ 2 * (u k * v k) := by
  unfold Sbil coordGauge
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The bilinear channel is genuinely not gauge invariant**: an explicit
unit gauge that changes it.  So the invariance above cannot be extended, and the
real/imaginary split — hence the transverse defect — is *not* a gauge invariant
of the window. -/
theorem exists_coordGauge_Sbil_ne :
    ∃ (g u : Fin 1 → ℂ), (∀ k, ‖g k‖ = 1) ∧
      Sbil (coordGauge g u) (coordGauge g u) ≠ Sbil u u := by
  refine ⟨fun _ => Complex.I, fun _ => 1, fun _ => by simp, ?_⟩
  simp [Sbil, coordGauge, Complex.ext_iff]
  norm_num

/-! ### The critical-line phase gauge -/

/-- The unit phase that rotates `z` onto the nonnegative reals. -/
noncomputable def criticalPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.exp (-(z.arg : ℂ) * Complex.I)

theorem norm_criticalPhase (z : ℂ) : ‖criticalPhase z‖ = 1 := by
  unfold criticalPhase
  split_ifs with h
  · simp
  · rw [Complex.norm_exp]
    simp

/-- The gauge does what it is designed to do: `e^{-i arg z}·z = |z| ≥ 0`. -/
theorem criticalPhase_mul_self (z : ℂ) : criticalPhase z * z = (‖z‖ : ℂ) := by
  unfold criticalPhase
  split_ifs with h
  · simp [h]
  · have hz : (‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I) = z := Complex.norm_mul_exp_arg_mul_I z
    calc Complex.exp (-(z.arg : ℂ) * Complex.I) * z
        = Complex.exp (-(z.arg : ℂ) * Complex.I) *
            ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) := by rw [hz]
      _ = (‖z‖ : ℂ) * (Complex.exp (-(z.arg : ℂ) * Complex.I)
            * Complex.exp ((z.arg : ℂ) * Complex.I)) := by ring
      _ = (‖z‖ : ℂ) := by
            rw [← Complex.exp_add]
            simp

/-- The critical-line gauge of a window vector: freeze the phases of the
baseline (`α = 0`) samples and apply them coordinatewise. -/
noncomputable def gaugeOf (u₀ : Fin d → ℂ) : Fin d → ℂ := fun k => criticalPhase (u₀ k)

theorem norm_gaugeOf (u₀ : Fin d → ℂ) (k : Fin d) : ‖gaugeOf u₀ k‖ = 1 := norm_criticalPhase _

/-- **The gauged baseline is real.**  `Im (g_k u₀_k) = 0` for every coordinate:
the transverse channel of the gauged family vanishes identically at `α = 0`,
*whatever* the taper — no evenness is used. -/
theorem gaugedBaseline_im_eq_zero (u₀ : Fin d → ℂ) :
    imOf (coordGauge (gaugeOf u₀) u₀) = 0 := by
  funext k
  unfold imOf coordGauge gaugeOf
  rw [criticalPhase_mul_self]
  simp

/-- … and it is nonnegative: the gauged baseline coordinate is `|u₀ k|`. -/
theorem gaugedBaseline_re (u₀ : Fin d → ℂ) (k : Fin d) :
    reOf (coordGauge (gaugeOf u₀) u₀) k = ‖u₀ k‖ := by
  unfold reOf coordGauge gaugeOf
  rw [criticalPhase_mul_self]
  simp

/-- **G9.3/G9.4, the answer.**  After the critical-line phase gauge the anchored
transverse defect at the baseline is exactly zero — the geometric-phase
background produced by an asymmetric (one-sided) taper is removed by a unitary
coordinate change, not by an estimate. -/
theorem gaugedDefect_zero_at_baseline (u₀ : Fin d → ℂ) :
    gramDefect (reOf (coordGauge (gaugeOf u₀) u₀)) (imOf (coordGauge (gaugeOf u₀) u₀)) = 0 := by
  rw [gaugedBaseline_im_eq_zero]
  unfold gramDefect
  simp [dotProduct]

/-- **The price of the gauge, stated exactly.**  With the gauge frozen at the
baseline, the defect of the displaced family is the Hermitian energy against the
*gauged bilinear channel*: -/
theorem gaugedDefect_eq (g u : Fin d → ℂ) (hg : ∀ k, ‖g k‖ = 1) :
    gramDefect (reOf (coordGauge g u)) (imOf (coordGauge g u))
      = 1 / 4 * ((∑ k, ‖u k‖ ^ 2) ^ 2
          - Complex.normSq (∑ k, (g k) ^ 2 * (u k * u k))) := by
  rw [gramDefect_eq_hermitian_sub_bilinear, Hsesq_self_re, energy_coordGauge g u hg,
    Sbil_coordGauge]

/-- A one-sided (non-even) taper really can have a nonzero baseline defect: it is
enough that two coordinates of the baseline window have different phases.  The
witness makes the point concretely — the ungauged defect at `α = 0` is `1`, and
by `gaugedDefect_zero_at_baseline` the gauge removes it. -/
theorem exists_nonzero_baseline_defect :
    ∃ u : Fin 2 → ℂ, gramDefect (reOf u) (imOf u) ≠ 0 := by
  refine ⟨![1, Complex.I], ?_⟩
  have : gramDefect (reOf ![1, Complex.I]) (imOf ![1, Complex.I]) = 1 := by
    unfold gramDefect reOf imOf dotProduct
    simp [Fin.sum_univ_two]
  rw [this]
  norm_num

end RiemannAnalytic
