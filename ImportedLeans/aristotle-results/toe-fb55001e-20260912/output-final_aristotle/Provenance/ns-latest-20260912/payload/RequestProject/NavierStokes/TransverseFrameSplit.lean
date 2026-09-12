/-
# The fixed-output operator bound is exactly two scalar bounds

At a retained output `k ≠ 0` every outer cell `G_p = P_k(N_p × u_{k−p})` is
Leray-projected, hence lies in the two-complex-dimensional transverse plane
`k^⊥`.  This file makes that structural fact usable: it builds an explicit
*real* orthogonal frame `f₁, f₂` of `k^⊥` out of cross products of `k`,
decomposes every transverse vector exactly in that frame, and shows that the
signed resolvent Gram form of a cell family splits, with no loss, as

  `resForm(G) = ‖f₁‖² · resForm(a) + ‖f₂‖² · resForm(b)`,

where `a_p`, `b_p` are the two scalar polarization coefficients of `G_p`, and
that the cell masses split the same way, `‖G_p‖² = ‖f₁‖²|a_p|² + ‖f₂‖²|b_p|²`.

Consequently `gramOperatorBound_of_components` reduces the truncation-uniform
`ℓ² → ℓ²` bound for the outer-cell Gram operator at one output — the single
remaining hypothesis of the critical spacetime consumer — to two *scalar*
resolvent-form bounds, one per polarization.  The vector-valued
almost-orthogonality question at a fixed output is therefore equivalent to a
question about two scalar sequences against the Cauchy kernel
`1/(λ_p + λ_q)`.

The frame is built from `k` alone (`f₁ = k × e`, `f₂ = k × f₁` for a lattice
vector `e` not parallel to `k`, which `exists_frame_seed` supplies for every
`k ≠ 0`), so all of its entries are integers and the frame vectors are genuinely
real; the norms that appear are the literal real `|k|²`-type quantities, not
rational surrogates.

Nothing here supplies either scalar bound; the open analytic question is
unchanged, only restated in scalar coordinates.  Package A and the literal
periodic Clay target are not closed and nothing is claimed for them.
-/
import RequestProject.NavierStokes.OperatorSchurBlockCancellation

noncomputable section

namespace ClayNS.Frame

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar ClayNS.Schur

/-! ## 1.  A real orthogonal frame of the transverse plane -/

/-- First transverse frame vector at `k`, seeded by a lattice vector `e`. -/
def frame1 (k e : Wave) : Fin 3 → ℂ := cross (wC k) (wC e)

/-- Second transverse frame vector at `k`. -/
def frame2 (k e : Wave) : Fin 3 → ℂ := cross (wC k) (frame1 k e)

theorem conj_frame1 (k e : Wave) (i : Fin 3) :
    (starRingEnd ℂ) (frame1 k e i) = frame1 k e i := by
  fin_cases i <;> simp [frame1, cross, crossProduct, wC]

theorem conj_frame2 (k e : Wave) (i : Fin 3) :
    (starRingEnd ℂ) (frame2 k e i) = frame2 k e i := by
  fin_cases i <;> simp [frame2, frame1, cross, crossProduct, wC]

theorem herm_frame1 (k e : Wave) (v : Fin 3 → ℂ) :
    herm (frame1 k e) v = dotb (frame1 k e) v := by
  simp [herm, dotb, conj_frame1]

theorem herm_frame2 (k e : Wave) (v : Fin 3 → ℂ) :
    herm (frame2 k e) v = dotb (frame2 k e) v := by
  simp [herm, dotb, conj_frame2]

theorem dotb_k_frame1 (k e : Wave) : dotb (wC k) (frame1 k e) = 0 := by
  simp [dotb, frame1, cross, crossProduct, wC, Fin.sum_univ_three]
  ring_nf

theorem dotb_k_frame2 (k e : Wave) : dotb (wC k) (frame2 k e) = 0 := by
  simp [dotb, frame2, frame1, cross, crossProduct, wC, Fin.sum_univ_three]
  ring_nf

theorem dotb_frame1_frame2 (k e : Wave) : dotb (frame1 k e) (frame2 k e) = 0 := by
  simp [dotb, frame2, frame1, cross, crossProduct, wC, Fin.sum_univ_three]
  ring_nf

theorem dotb_frame2_frame1 (k e : Wave) : dotb (frame2 k e) (frame1 k e) = 0 := by
  rw [dotb_comm]; exact dotb_frame1_frame2 k e

theorem dotb_self_frame1 (k e : Wave) :
    dotb (frame1 k e) (frame1 k e) = (nsq (frame1 k e) : ℂ) := by
  rw [← herm_frame1, herm_self]

theorem dotb_self_frame2 (k e : Wave) :
    dotb (frame2 k e) (frame2 k e) = (nsq (frame2 k e) : ℂ) := by
  rw [← herm_frame2, herm_self]

theorem herm_k_frame1 (k e : Wave) : herm (wC k) (frame1 k e) = 0 := by
  have h : herm (wC k) (frame1 k e) = dotb (wC k) (frame1 k e) := by
    simp [herm, dotb, wC]
  rw [h, dotb_k_frame1]

theorem nsq_wC (k : Wave) : nsq (wC k) = wsq k := by
  simp [nsq, wsq, wC, Complex.normSq_apply]
  ring_nf

/-- The second frame vector has the length forced by the first: `|f₂| = |k||f₁|`,
in squared form.  In particular it is nonzero as soon as `k` and `f₁` are. -/
theorem nsq_frame2 (k e : Wave) : nsq (frame2 k e) = wsq k * nsq (frame1 k e) := by
  have hl := lagrange (wC k) (frame1 k e)
  rw [herm_k_frame1, nsq_wC] at hl
  simpa using hl

theorem nsq_frame2_ne_zero {k e : Wave} (hk : wsq k ≠ 0) (h1 : nsq (frame1 k e) ≠ 0) :
    nsq (frame2 k e) ≠ 0 := by
  rw [nsq_frame2]
  exact mul_ne_zero hk h1

/-- For every nonzero wavevector there is a lattice seed producing a nonzero
frame, so the frame construction is available at every retained output. -/
theorem exists_frame_seed {k : Wave} (hk : wsq k ≠ 0) :
    ∃ e : Wave, nsq (frame1 k e) ≠ 0 := by
  classical
  have hk0 : ¬ (k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0) := by
    intro h
    apply hk
    simp [wsq, Fin.sum_univ_three, h.1, h.2.1, h.2.2]
  by_cases h12 : k 1 = 0 ∧ k 2 = 0
  · refine ⟨fun i => if i = 1 then 1 else 0, ?_⟩
    have hk0' : k 0 ≠ 0 := by
      intro h
      exact hk0 ⟨h, h12.1, h12.2⟩
    have : nsq (frame1 k (fun i => if i = 1 then 1 else 0)) = (k 0 : ℝ) ^ 2 := by
      simp [nsq, frame1, cross, crossProduct, wC, Fin.sum_univ_three, h12.1, h12.2,
        Complex.normSq_apply]
      ring_nf
    rw [this]
    have : (k 0 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk0'
    positivity
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_⟩
    have hne : ¬ ((k 1 : ℝ) = 0 ∧ (k 2 : ℝ) = 0) := by
      intro h
      exact h12 ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    have hval : nsq (frame1 k (fun i => if i = 0 then 1 else 0))
        = (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2 := by
      simp [nsq, frame1, cross, crossProduct, wC, Fin.sum_univ_three, Complex.normSq_apply]
      ring_nf
    rw [hval]
    rcases (not_and_or.mp hne) with h | h
    · positivity
    · positivity

/-! ## 2.  The exact two-component decomposition -/

theorem dotb_sub_smul (a b : ℂ) (u w x y : Fin 3 → ℂ) :
    dotb (fun i => u i - a * w i - b * x i) y
      = dotb u y - a * dotb w y - b * dotb x y := by
  simp [dotb, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- A vector orthogonal to `k`, `f₁` and `f₂` vanishes. -/
theorem eq_zero_of_dotb_frame {k e : Wave} {r : Fin 3 → ℂ} (h2 : nsq (frame2 k e) ≠ 0)
    (hk : dotb r (wC k) = 0) (h1 : dotb r (frame1 k e) = 0) (hr2 : dotb r (frame2 k e) = 0) :
    ∀ i, r i = 0 := by
  have hcr : cross r (frame2 k e) = fun _ => 0 := by
    have ht := cross_triple r (wC k) (frame1 k e)
    rw [frame2, ht, h1, hk]
    funext i; ring
  have hkey := cross_triple (frame2 k e) r (frame2 k e)
  rw [hcr] at hkey
  have hzero : cross (frame2 k e) (fun _ => (0 : ℂ)) = fun _ => 0 := by
    funext i; fin_cases i <;> simp [cross, crossProduct]
  rw [hzero] at hkey
  have hd : dotb (frame2 k e) (frame2 k e) = (nsq (frame2 k e) : ℂ) := dotb_self_frame2 k e
  have hdr : dotb (frame2 k e) r = 0 := by rw [dotb_comm]; exact hr2
  have hne : ((nsq (frame2 k e) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  intro i
  have hi := congrFun hkey i
  rw [hd, hdr, zero_mul, sub_zero] at hi
  rcases mul_eq_zero.mp hi.symm with h | h
  · exact absurd h hne
  · exact h

/-- The first polarization coefficient of a transverse vector. -/
def comp1 (k e : Wave) (v : Fin 3 → ℂ) : ℂ := dotb (frame1 k e) v / (nsq (frame1 k e) : ℂ)

/-- The second polarization coefficient of a transverse vector. -/
def comp2 (k e : Wave) (v : Fin 3 → ℂ) : ℂ := dotb (frame2 k e) v / (nsq (frame2 k e) : ℂ)

/-- **The exact decomposition.**  Every transverse vector at `k` is the sum of
its two polarization components in the frame. -/
theorem transverse_decomp {k e : Wave} {v : Fin 3 → ℂ} (h1 : nsq (frame1 k e) ≠ 0)
    (h2 : nsq (frame2 k e) ≠ 0) (hv : dotb (wC k) v = 0) :
    ∀ i, v i = comp1 k e v * frame1 k e i + comp2 k e v * frame2 k e i := by
  have hn1 : ((nsq (frame1 k e) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
  have hn2 : ((nsq (frame2 k e) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  set a := comp1 k e v with ha
  set b := comp2 k e v with hb
  set r : Fin 3 → ℂ := fun i => v i - a * frame1 k e i - b * frame2 k e i with hr
  have hrk : dotb r (wC k) = 0 := by
    rw [hr, dotb_sub_smul, dotb_comm v (wC k), hv,
      dotb_comm (frame1 k e) (wC k), dotb_k_frame1,
      dotb_comm (frame2 k e) (wC k), dotb_k_frame2]
    ring
  have hr1 : dotb r (frame1 k e) = 0 := by
    rw [hr, dotb_sub_smul, dotb_comm v (frame1 k e), dotb_self_frame1,
      dotb_frame2_frame1, ha, comp1]
    field_simp
    ring
  have hr2 : dotb r (frame2 k e) = 0 := by
    rw [hr, dotb_sub_smul, dotb_comm v (frame2 k e), dotb_frame1_frame2,
      dotb_self_frame2, hb, comp2]
    field_simp
    ring
  have hz := eq_zero_of_dotb_frame h2 hrk hr1 hr2
  intro i
  have hzi := hz i
  rw [hr] at hzi
  simp only at hzi
  linear_combination hzi

/-! ## 3.  The Gram form splits along the polarizations -/

/-- The Hermitian pairing of two frame combinations: the cross terms vanish. -/
theorem herm_frame_comb (k e : Wave) (a b c d : ℂ) :
    herm (fun i => a * frame1 k e i + b * frame2 k e i)
        (fun i => c * frame1 k e i + d * frame2 k e i)
      = (starRingEnd ℂ) a * c * (nsq (frame1 k e) : ℂ)
        + (starRingEnd ℂ) b * d * (nsq (frame2 k e) : ℂ) := by
  have hexp : herm (fun i => a * frame1 k e i + b * frame2 k e i)
      (fun i => c * frame1 k e i + d * frame2 k e i)
      = (starRingEnd ℂ) a * c * dotb (frame1 k e) (frame1 k e)
        + (starRingEnd ℂ) a * d * dotb (frame1 k e) (frame2 k e)
        + (starRingEnd ℂ) b * c * dotb (frame2 k e) (frame1 k e)
        + (starRingEnd ℂ) b * d * dotb (frame2 k e) (frame2 k e) := by
    simp only [herm, dotb, Fin.sum_univ_three, map_add, map_mul, conj_frame1, conj_frame2]
    ring
  rw [hexp, dotb_self_frame1, dotb_self_frame2, dotb_frame1_frame2, dotb_frame2_frame1]
  ring

/-- The real part of the pairing of two transverse vectors splits into the two
polarization channels. -/
theorem herm_re_split {k e : Wave} {v w : Fin 3 → ℂ} (h1 : nsq (frame1 k e) ≠ 0)
    (h2 : nsq (frame2 k e) ≠ 0) (hv : dotb (wC k) v = 0) (hw : dotb (wC k) w = 0) :
    (herm v w).re
      = nsq (frame1 k e) * ((starRingEnd ℂ) (comp1 k e v) * comp1 k e w).re
        + nsq (frame2 k e) * ((starRingEnd ℂ) (comp2 k e v) * comp2 k e w).re := by
  have hv' : v = fun i => comp1 k e v * frame1 k e i + comp2 k e v * frame2 k e i :=
    funext (transverse_decomp h1 h2 hv)
  have hw' : w = fun i => comp1 k e w * frame1 k e i + comp2 k e w * frame2 k e i :=
    funext (transverse_decomp h1 h2 hw)
  have hcalc := herm_frame_comb k e (comp1 k e v) (comp2 k e v) (comp1 k e w) (comp2 k e w)
  rw [← hv', ← hw'] at hcalc
  rw [hcalc]
  simp [Complex.add_re, Complex.mul_re]
  ring

/-- The cell mass splits the same way. -/
theorem nsq_split {k e : Wave} {v : Fin 3 → ℂ} (h1 : nsq (frame1 k e) ≠ 0)
    (h2 : nsq (frame2 k e) ≠ 0) (hv : dotb (wC k) v = 0) :
    nsq v = nsq (frame1 k e) * Complex.normSq (comp1 k e v)
      + nsq (frame2 k e) * Complex.normSq (comp2 k e v) := by
  have h := herm_re_split h1 h2 hv hv
  rw [← nsq_eq_herm_re] at h
  rw [h]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-! ## 4.  The operator bound reduces to two scalar bounds -/

/-- **The fixed-output operator bound is exactly two scalar bounds.**  If both
polarization coefficient sequences of the cell family satisfy the scalar
resolvent-form bound with constant `A`, then the outer-cell Gram operator at the
output satisfies `GramOperatorBound` with the same `A` — and conversely the
split is exact, so nothing is lost in passing to the scalar problem. -/
theorem gramOperatorBound_of_components {nu A : ℝ} (modes : Finset Wave)
    (G : Wave → Fin 3 → ℂ) (k e : Wave)
    (h1 : nsq (frame1 k e) ≠ 0) (h2 : nsq (frame2 k e) ≠ 0)
    (htr : ∀ p ∈ modes, dotb (wC k) (G p) = 0)
    (hA1 : ∑ p ∈ modes, ∑ q ∈ modes,
        ((starRingEnd ℂ) (comp1 k e (G p)) * comp1 k e (G q)).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
        ≤ A * (∑ p ∈ modes, Complex.normSq (comp1 k e (G p)) / wsq p) / (2 * nu))
    (hA2 : ∑ p ∈ modes, ∑ q ∈ modes,
        ((starRingEnd ℂ) (comp2 k e (G p)) * comp2 k e (G q)).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
        ≤ A * (∑ p ∈ modes, Complex.normSq (comp2 k e (G p)) / wsq p) / (2 * nu)) :
    GramOperatorBound nu modes G k A := by
  classical
  have hn1 : 0 ≤ nsq (frame1 k e) := nsq_nonneg _
  have hn2 : 0 ≤ nsq (frame2 k e) := nsq_nonneg _
  have hsplit : ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      = nsq (frame1 k e) * (∑ p ∈ modes, ∑ q ∈ modes,
          ((starRingEnd ℂ) (comp1 k e (G p)) * comp1 k e (G q)).re
            / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)))
        + nsq (frame2 k e) * (∑ p ∈ modes, ∑ q ∈ modes,
          ((starRingEnd ℂ) (comp2 k e (G p)) * comp2 k e (G q)).re
            / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [herm_re_split h1 h2 (htr p hp) (htr q hq)]
    ring
  have hmass : ∑ p ∈ modes, nsq (G p) / wsq p
      = nsq (frame1 k e) * (∑ p ∈ modes, Complex.normSq (comp1 k e (G p)) / wsq p)
        + nsq (frame2 k e) * (∑ p ∈ modes, Complex.normSq (comp2 k e (G p)) / wsq p) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [nsq_split h1 h2 (htr p hp)]
    ring
  show ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
    ≤ A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu)
  rw [hsplit, hmass]
  have s1 := mul_le_mul_of_nonneg_left hA1 hn1
  have s2 := mul_le_mul_of_nonneg_left hA2 hn2
  have hcollect :
      nsq (frame1 k e) * (A * (∑ p ∈ modes, Complex.normSq (comp1 k e (G p)) / wsq p) / (2 * nu))
        + nsq (frame2 k e) * (A * (∑ p ∈ modes, Complex.normSq (comp2 k e (G p)) / wsq p)
            / (2 * nu))
      = A * (nsq (frame1 k e) * (∑ p ∈ modes, Complex.normSq (comp1 k e (G p)) / wsq p)
          + nsq (frame2 k e) * (∑ p ∈ modes, Complex.normSq (comp2 k e (G p)) / wsq p))
        / (2 * nu) := by
    field_simp
  linarith [s1, s2, hcollect.le, hcollect.ge]


/-- The literal outer cells are transverse at their output, so the split above
applies to them. -/
theorem dotb_wC_outerCellVec (N u : Wave → Fin 3 → ℂ) (k p : Wave) (hk : wsq k ≠ 0) :
    dotb (wC k) (outerCellVec N u k p) = 0 := by
  have hh := herm_wC_leray k (cross (N p) (u (k - p))) hk
  have hconv : herm (wC k) (outerCellVec N u k p) = dotb (wC k) (outerCellVec N u k p) := by
    simp [herm, dotb, wC]
  rw [← hconv]
  exact hh

/-- **The physical instance.**  At a retained output, a truncation-uniform
`ℓ² → ℓ²` bound for the outer-cell Gram operator follows from the two scalar
polarization bounds — and by `spacetime_remainder_le_critical_of_gramBound`
that is all the critical spacetime consumer needs. -/
theorem gramOperatorBound_outerCells_of_components {nu A : ℝ} (modes : Finset Wave)
    (N u : Wave → Fin 3 → ℂ) (k e : Wave) (hk : wsq k ≠ 0)
    (h1 : nsq (frame1 k e) ≠ 0) (h2 : nsq (frame2 k e) ≠ 0)
    (hA1 : ∑ p ∈ modes, ∑ q ∈ modes,
        ((starRingEnd ℂ) (comp1 k e (outerCellVec N u k p)) * comp1 k e (outerCellVec N u k q)).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
        ≤ A * (∑ p ∈ modes, Complex.normSq (comp1 k e (outerCellVec N u k p)) / wsq p) / (2 * nu))
    (hA2 : ∑ p ∈ modes, ∑ q ∈ modes,
        ((starRingEnd ℂ) (comp2 k e (outerCellVec N u k p)) * comp2 k e (outerCellVec N u k q)).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
        ≤ A * (∑ p ∈ modes, Complex.normSq (comp2 k e (outerCellVec N u k p)) / wsq p) / (2 * nu)) :
    GramOperatorBound nu modes (fun p => outerCellVec N u k p) k A :=
  gramOperatorBound_of_components modes (fun p => outerCellVec N u k p) k e h1 h2
    (fun p _ => dotb_wC_outerCellVec N u k p hk) hA1 hA2

end ClayNS.Frame
