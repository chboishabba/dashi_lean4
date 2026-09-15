/-
# The heterochiral row of the R571 commutator square *is* output-controlled

## Lane

Lane **B** (unforced periodic `T³`).  No transport to lane A, no use of the
released forced C/D material.

## The seam this closes

`NSUnforced.HelicalMultiplierDifference.heterochiral_multiplierDifference_not_output_controlled`
(TOE task `759f2a06`, imported verbatim in `Lean/NSUnforced/`) proves a genuine
obstruction: on a triad `k + p + q = 0` the heterochiral multiplier difference
is `‖p‖ + ‖q‖`, which is unbounded in terms of `‖k‖`.  The TOE programme report
ranks this first among the remaining seams and states that "a purely homochiral
gain argument is provably insufficient, so the sign split (or an equivalent) is
forced".

That obstruction is about the *scalar multiplier alone*.  The object the
commutator square actually contains is the multiplier **times the helical
vertex** `h^{s}(p) × h^{-s}(q)`, and the two degenerate together: the multiplier
blows up exactly when `q̂ → -p̂`, and the heterochiral vertex vanishes there.
This file proves both halves and multiplies them, on the lane's own `ℂ³`
carrier (`ClayNS.Waleffe.cross`, `ClayNS.SlotKernel.bdot`).

1. **Antiparallel defect carries the output gain** (real geometry):

   `(‖p‖ + ‖q‖) · ‖p̂ + q̂‖ ≤ 4‖k‖`   (`heterochiral_radialSum_mul_defect_le`)

   with no hypothesis beyond `p ≠ 0`, `q ≠ 0` and the triad relation.

2. **The heterochiral vertex is Lipschitz in the defect** (`ℂ³` helical
   algebra):

   `‖h_p × h_q‖ ≤ (3/2)·‖δ‖`   (`nrm_cross_helical_le`)

   for `h_p` an `s`-helical vector of the axis `n`, `h_q` a `(-s)`-helical
   vector of the axis `m`, `δ = n + m`, both unit.  At exact antiparallelism
   `m = -n` this specialises to the exact identity `h_p × h_q = 0`
   (`cross_helical_antiparallel_eq_zero`), proved frame-free from the curl
   eigen-relation, with no choice of helical frame anywhere.

3. **Consequence** (`heterochiral_vertex_output_controlled`):

   `(‖p‖ + ‖q‖) · ‖h_p × h_q‖ ≤ 6‖k‖`.

   So the heterochiral *row of the commutator square* has exactly the same one
   power of output gain as the homochiral row
   (`abs_multiplierDifference_homochiral_le`), and the TOE obstruction is not an
   obstruction to the A1 route: it only rules out discarding the vertex.

## Status

This is a geometric estimate on the carrier, proved without PDE input.  It does
**not** by itself supply the `∑ A² ≤ c_A · Dissip` clause of
`DASHI.NS.Unforced.A1ChannelObligation`: that additionally needs the
identification of the aggregated cross-product square with the dissipation.
Nothing here closes R568 or any Clay statement.
-/
import RequestProject.NavierStokes.SlotKernelAntiParallel
import NSUnforced.HelicalMultiplierDifference

noncomputable section

namespace RequestProject.NavierStokes.Heterochiral

open ClayNS.Waleffe ClayNS.SlotKernel Matrix

/-! ## 1.  The antiparallel defect carries the output gain -/

section RealGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One half of the defect gain: the defect `p̂ + q̂`, weighted by either radius,
is controlled by twice the output radius. -/
theorem norm_mul_unitSum_le {k p q : E} (h : k + p + q = 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    ‖p‖ * ‖‖p‖⁻¹ • p + ‖q‖⁻¹ • q‖ ≤ 2 * ‖k‖ := by
  set a := ‖p‖ with ha
  set b := ‖q‖ with hb
  have hapos : 0 < a := norm_pos_iff.2 hp
  have hbpos : 0 < b := norm_pos_iff.2 hq
  have hpq : p + q = -k := by linear_combination (norm := abel) h
  have hab : |a - b| ≤ ‖k‖ := by
    have h1 := abs_norm_sub_norm_le p (-q)
    rw [norm_neg] at h1
    rwa [show p - -q = p + q by abel, hpq, norm_neg] at h1
  have key : a • (‖p‖⁻¹ • p + ‖q‖⁻¹ • q) = -k + ((a - b) / b) • q := by
    rw [smul_add, ← ha, ← hb, smul_smul, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hapos), one_smul]
    have hab2 : a * b⁻¹ = 1 + (a - b) / b := by field_simp; ring
    rw [hab2, add_smul, one_smul, ← hpq]
    abel
  have hnorm : ‖a • (‖p‖⁻¹ • p + ‖q‖⁻¹ • q)‖ = a * ‖‖p‖⁻¹ • p + ‖q‖⁻¹ • q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hapos]
  rw [← hnorm, key]
  have hqq : |(a - b) / b| * b = |a - b| := by
    rw [abs_div, abs_of_pos hbpos]; field_simp
  have h1 : ‖-k + ((a - b) / b) • q‖ ≤ ‖k‖ + |a - b| := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg, norm_smul, Real.norm_eq_abs, ← hb, hqq]
  linarith

/-- **The heterochiral multiplier times the antiparallel defect is
output-controlled.**  On a triad `k + p + q = 0` with `p, q ≠ 0`,

`(‖p‖ + ‖q‖) · ‖p̂ + q̂‖ ≤ 4‖k‖`.

The heterochiral multiplier `‖p‖ + ‖q‖` of
`NSUnforced.multiplierDifference_heterochiral` is unbounded relative to `‖k‖`,
but the antiparallel defect it is paired with decays at exactly the
compensating rate. -/
theorem heterochiral_radialSum_mul_defect_le {k p q : E} (h : k + p + q = 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (‖p‖ + ‖q‖) * ‖‖p‖⁻¹ • p + ‖q‖⁻¹ • q‖ ≤ 4 * ‖k‖ := by
  have h1 := norm_mul_unitSum_le h hp hq
  have h2 : ‖q‖ * ‖‖q‖⁻¹ • q + ‖p‖⁻¹ • p‖ ≤ 2 * ‖k‖ := by
    refine norm_mul_unitSum_le ?_ hq hp
    linear_combination (norm := abel) h
  rw [show ‖q‖⁻¹ • q + ‖p‖⁻¹ • p = ‖p‖⁻¹ • p + ‖q‖⁻¹ • q by abel] at h2
  rw [add_mul]
  linarith

/-- The defect really is the antiparallelism measure: it vanishes exactly when
the two high modes are antiparallel. -/
theorem unitSum_eq_zero_iff_antiparallel (p q : E) :
    ‖p‖⁻¹ • p + ‖q‖⁻¹ • q = 0 ↔ ‖q‖⁻¹ • q = -(‖p‖⁻¹ • p) := by
  constructor
  · intro h; linear_combination (norm := abel) h
  · intro h; rw [h]; abel

end RealGeometry

/-! ## 2.  A norm toolkit for the lane's `ℂ³` carrier

`ClayNS.Waleffe.nrm` is the Hermitian norm `√(∑ |u i|²)` on `Fin 3 → ℂ`.  The
lane's carrier is the plain pi type, whose `NormedAddCommGroup` instance is the
sup norm, so the standard triangle inequality does not apply to `nrm` directly;
these four lemmas transport it from `EuclideanSpace ℂ (Fin 3)`. -/

theorem nrm_eq_euclid (u : Fin 3 → ℂ) :
    nrm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [nrm, nsq, Complex.norm_def]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (Real.sq_sqrt (Complex.normSq_nonneg _)).symm

theorem nrm_add_le (u v : Fin 3 → ℂ) : nrm (u + v) ≤ nrm u + nrm v := by
  rw [nrm_eq_euclid, nrm_eq_euclid, nrm_eq_euclid]
  simpa using norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3)) (WithLp.toLp 2 v)

theorem nrm_smul (c : ℂ) (u : Fin 3 → ℂ) : nrm (c • u) = ‖c‖ * nrm u := by
  rw [nrm_eq_euclid, nrm_eq_euclid]
  simpa using norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3))

theorem nrm_neg (u : Fin 3 → ℂ) : nrm (-u) = nrm u := by
  rw [show (-u) = (-1 : ℂ) • u by module, nrm_smul]; simp

theorem nrm_real_smul (a : ℝ) (u : Fin 3 → ℂ) : nrm (a • u) = |a| * nrm u := by
  rw [nrm_eq_euclid, nrm_eq_euclid]
  rw [show (WithLp.toLp 2 (a • u) : EuclideanSpace ℂ (Fin 3))
      = a • WithLp.toLp 2 u from rfl, norm_smul, Real.norm_eq_abs]

theorem nrm_eq_zero_iff (u : Fin 3 → ℂ) : nrm u = 0 ↔ u = 0 := by
  rw [nrm_eq_euclid, norm_eq_zero]
  constructor
  · intro h; simpa using h
  · intro h; simp [h]

theorem nrm_sub_le (u v : Fin 3 → ℂ) : nrm (u - v) ≤ nrm u + nrm v := by
  have h := nrm_add_le u (-v)
  rw [show u + -v = u - v from (sub_eq_add_neg u v).symm, nrm_neg] at h
  exact h

/-- Cauchy–Schwarz for the **bilinear** dot product, from the lane's Hermitian
`normSq_herm_le`. -/
theorem norm_bdot_le (u v : Fin 3 → ℂ) : ‖bdot u v‖ ≤ nrm u * nrm v := by
  have hconj : bdot u v = herm (fun i => (starRingEnd ℂ) (u i)) v := by
    simp [bdot, herm]
  have hns : nsq (fun i => (starRingEnd ℂ) (u i)) = nsq u := by
    simp [nsq]
  have h := normSq_herm_le (fun i => (starRingEnd ℂ) (u i)) v
  rw [hns] at h
  have h2 : ‖bdot u v‖ ^ 2 ≤ nsq u * nsq v := by
    rw [hconj, ← Complex.normSq_eq_norm_sq]; exact h
  have hnn : 0 ≤ nrm u * nrm v := mul_nonneg (nrm_nonneg u) (nrm_nonneg v)
  calc ‖bdot u v‖ = Real.sqrt (‖bdot u v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((nrm u * nrm v) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow, nrm_sq, nrm_sq]; exact h2
    _ = nrm u * nrm v := Real.sqrt_sq hnn

/-- The cross product is submultiplicative for `nrm`, from the lane's
`nsq_cross_le`. -/
theorem nrm_cross_le (u v : Fin 3 → ℂ) : nrm (cross u v) ≤ nrm u * nrm v := by
  have h := nsq_cross_le u v
  have hnn : 0 ≤ nrm u * nrm v := mul_nonneg (nrm_nonneg u) (nrm_nonneg v)
  calc nrm (cross u v) = Real.sqrt (nrm (cross u v) ^ 2) :=
        (Real.sqrt_sq (nrm_nonneg _)).symm
    _ ≤ Real.sqrt ((nrm u * nrm v) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow, nrm_sq, nrm_sq, nrm_sq]; exact h
    _ = nrm u * nrm v := Real.sqrt_sq hnn

/-! ## 3.  Frame-free helical algebra on `ℂ³` -/

theorem bdot_eq_dotProduct (u v : Fin 3 → ℂ) : bdot u v = u ⬝ᵥ v := rfl

/-- BAC–CAB on the lane's carrier: `a × (b × c) = (a·c) b − (a·b) c`. -/
theorem cross_cross (a b c : Fin 3 → ℂ) :
    cross a (cross b c) = bdot a c • b - bdot a b • c := by
  funext i
  fin_cases i <;>
    simp [cross, crossProduct, bdot, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring

theorem bdot_self_cross (u v : Fin 3 → ℂ) : bdot u (cross u v) = 0 := by
  rw [bdot_eq_dotProduct, cross]; exact dot_self_cross u v

theorem bdot_triple_cyclic (a b c : Fin 3 → ℂ) :
    bdot a (cross b c) = bdot b (cross c a) := by
  rw [bdot_eq_dotProduct, bdot_eq_dotProduct, cross, cross]
  exact triple_product_permutation a b c

theorem cross_swap (u v : Fin 3 → ℂ) : cross u v = -cross v u := by
  rw [cross, cross, cross_anticomm]

theorem cross_neg_left (u v : Fin 3 → ℂ) : cross (-u) v = -cross u v := by
  funext i; fin_cases i <;> simp [cross, crossProduct]

@[simp] theorem cross_zero_right (u : Fin 3 → ℂ) : cross u 0 = 0 := by
  funext i; fin_cases i <;> simp [cross, crossProduct]

theorem bdot_smul_right (c : ℂ) (u v : Fin 3 → ℂ) : bdot u (c • v) = c * bdot u v := by
  simp only [bdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem bdot_neg_right (u v : Fin 3 → ℂ) : bdot u (-v) = -bdot u v := by
  rw [show (-v) = (-1 : ℂ) • v by module, bdot_smul_right]; ring

theorem bdot_sub_left (u v w : Fin 3 → ℂ) : bdot (u - v) w = bdot u w - bdot v w := by
  simp only [bdot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem cross_sub_left (u v w : Fin 3 → ℂ) : cross (u - v) w = cross u w - cross v w := by
  funext i
  fin_cases i <;> simp [cross, crossProduct, Pi.sub_apply]

/-- **Helical vector, frame-free.**  `h` is an `s`-helical vector for the axis
`n` when `i (n × h) = s h`, i.e. `h` is an eigenvector of the curl symbol.  For
a real unit axis `n` the values `s = ±1` give exactly Waleffe's `h^{±}(n)`, up
to a complex scalar, and no choice of helical frame is made anywhere. -/
def IsHelical (s : ℂ) (n h : Fin 3 → ℂ) : Prop := Complex.I • cross n h = s • h

theorem cross_axis_of_helical {s : ℂ} {n h : Fin 3 → ℂ} (hh : IsHelical s n h) :
    cross n h = (-Complex.I * s) • h := by
  have h2 : (-Complex.I) • (Complex.I • cross n h) = (-Complex.I) • (s • h) := by
    rw [show Complex.I • cross n h = s • h from hh]
  rw [smul_smul, smul_smul] at h2
  simpa [Complex.I_mul_I] using h2

/-- A helical vector is bilinearly orthogonal to its axis. -/
theorem bdot_axis_of_helical {s : ℂ} {n h : Fin 3 → ℂ} (hs : s ≠ 0)
    (hh : IsHelical s n h) : bdot n h = 0 := by
  have h0 : bdot n (cross n h) = 0 := bdot_self_cross n h
  rw [cross_axis_of_helical hh, bdot_smul_right] at h0
  have hne : (-Complex.I * s) ≠ 0 := by simp [Complex.I_ne_zero, hs]
  exact (mul_eq_zero.1 h0).resolve_left hne

/-! ### The exact antiparallel cancellation -/

/-- **Two helical vectors of the same sign and the same axis have vanishing
cross product.**  Purely algebraic: the eigen-relation forces bilinear
orthogonality to the axis and, read through the cyclic triple product in two
different slots, forces `h_p · h_q = 0`; BAC–CAB then makes the cross product a
multiple of the axis with zero coefficient. -/
theorem cross_helical_same_axis_eq_zero {s : ℂ} {n hp hq : Fin 3 → ℂ} (hs : s ≠ 0)
    (hn : bdot n n = 1) (hP : IsHelical s n hp) (hQ : IsHelical s n hq) :
    cross hp hq = 0 := by
  have hcp := cross_axis_of_helical hP
  have hcq := cross_axis_of_helical hQ
  have hnp : bdot n hp = 0 := bdot_axis_of_helical hs hP
  have hnq : bdot n hq = 0 := bdot_axis_of_helical hs hQ
  have hkill : cross n (cross hp hq) = 0 := by
    rw [cross_cross, hnp, hnq]; simp
  have e1 : bdot n (cross hp hq) = bdot hq (cross n hp) := by
    rw [bdot_triple_cyclic n hp hq, bdot_triple_cyclic hp hq n]
  have e2 : bdot hp (cross hq n) = bdot n (cross hp hq) :=
    (bdot_triple_cyclic n hp hq).symm
  have hb1 : bdot hp (cross hq n) = -bdot hp (cross n hq) := by
    rw [cross_swap hq n, bdot_neg_right]
  have v1 : bdot n (cross hp hq) = (-Complex.I * s) * bdot hp hq := by
    rw [e1, hcp, bdot_smul_right, bdot_comm hq hp]
  have v2 : bdot n (cross hp hq) = (Complex.I * s) * bdot hp hq := by
    rw [← e2, hb1, hcq, bdot_smul_right]; ring
  have hzero : bdot hp hq = 0 := by
    have hI : (2 * Complex.I * s) * bdot hp hq = 0 := by
      linear_combination v1 - v2
    have hne : (2 * Complex.I * s) ≠ 0 := by simp [Complex.I_ne_zero, hs]
    exact (mul_eq_zero.1 hI).resolve_left hne
  have hzz : bdot n (cross hp hq) = 0 := by rw [v2, hzero]; ring
  have hrec : cross hp hq = bdot n (cross hp hq) • n - cross n (cross n (cross hp hq)) := by
    rw [cross_cross n n (cross hp hq), hn]; module
  rw [hkill, hzz] at hrec
  simpa using hrec

/-- **Exact heterochiral vanishing at antiparallelism.**  If `h_p` is `s`-helical
for `n` and `h_q` is `(-s)`-helical for the *opposite* axis `-n`, then
`h_p × h_q = 0`.  This is the frame-free form of Waleffe's
`h^{s}(-p) = h^{-s}(p)`: at exact antiparallelism the heterochiral vertex is
identically zero, so the divergent heterochiral multiplier multiplies nothing. -/
theorem cross_helical_antiparallel_eq_zero {s : ℂ} {n hp hq : Fin 3 → ℂ} (hs : s ≠ 0)
    (hn : bdot n n = 1) (hP : IsHelical s n hp) (hQ : IsHelical (-s) (-n) hq) :
    cross hp hq = 0 := by
  have hQ' : IsHelical s n hq := by
    have h1 : Complex.I • cross (-n) hq = (-s) • hq := hQ
    rw [cross_neg_left] at h1
    show Complex.I • cross n hq = s • hq
    have h3 := congrArg (fun z => -z) h1
    simpa using h3
  exact cross_helical_same_axis_eq_zero hs hn hP hQ'

/-! ### The quantitative version -/

/-- **The heterochiral vertex is Lipschitz in the antiparallel defect.**

Let `h_p` be `s`-helical for the unit axis `n` (`‖s‖ = 1`), `h_q` be
`(-s)`-helical for the axis `m`, both of unit length, and let `δ = n + m` be the
antiparallel defect of the two axes.  Then

`‖h_p × h_q‖ ≤ (3/2)‖δ‖`.

For `δ = 0` this recovers `cross_helical_antiparallel_eq_zero`. -/
theorem nrm_cross_helical_le {s : ℂ} {n m hp hq : Fin 3 → ℂ}
    (hs : ‖s‖ = 1) (hsne : s ≠ 0) (hn : bdot n n = 1) (hnu : nrm n = 1)
    (hpu : nrm hp = 1) (hqu : nrm hq = 1)
    (hP : IsHelical s n hp) (hQ : IsHelical (-s) m hq) :
    nrm (cross hp hq) ≤ 3 / 2 * nrm (n + m) := by
  set d := n + m with hd
  have hmn : m = d - n := by rw [hd]; abel
  have hcp : cross n hp = (-Complex.I * s) • hp := cross_axis_of_helical hP
  have hcm : cross m hq = (-Complex.I * -s) • hq := cross_axis_of_helical hQ
  have hnp : bdot n hp = 0 := bdot_axis_of_helical hsne hP
  have hmq : bdot m hq = 0 := bdot_axis_of_helical (by simpa using hsne) hQ
  -- (a) the axis component of `hq` is small
  have hnq : bdot n hq = bdot d hq := by
    rw [hmn, bdot_sub_left] at hmq
    linear_combination -hmq
  have hnqle : ‖bdot n hq‖ ≤ nrm d := by
    rw [hnq]
    have h := norm_bdot_le d hq
    rwa [hqu, mul_one] at h
  -- (b) `n × hq` differs from a multiple of `hq` by `d × hq`
  have hcnq : cross n hq = cross d hq - (Complex.I * s) • hq := by
    have h1 : cross n hq = cross d hq - cross m hq := by
      rw [hmn, cross_sub_left]; abel
    rw [h1, hcm]
    congr 1
    module
  -- (c) `hp · hq` is small
  have e2 : bdot hp (cross hq n) = bdot n (cross hp hq) :=
    (bdot_triple_cyclic n hp hq).symm
  have e1 : bdot n (cross hp hq) = bdot hq (cross n hp) := by
    rw [bdot_triple_cyclic n hp hq, bdot_triple_cyclic hp hq n]
  have hb1 : bdot hp (cross hq n) = -bdot hp (cross n hq) := by
    rw [cross_swap hq n, bdot_neg_right]
  have hb2 : bdot hp (cross n hq)
      = bdot hp (cross d hq) - (Complex.I * s) * bdot hp hq := by
    rw [hcnq, show cross d hq - (Complex.I * s) • hq
        = cross d hq + (-(Complex.I * s)) • hq by module,
      bdot_add_right, bdot_smul_right]
    ring
  have v1 : bdot n (cross hp hq) = (-Complex.I * s) * bdot hp hq := by
    rw [e1, hcp, bdot_smul_right, bdot_comm hq hp]
  have v2 : bdot n (cross hp hq)
      = (Complex.I * s) * bdot hp hq - bdot hp (cross d hq) := by
    rw [← e2, hb1, hb2]; ring
  have hXsmall : ‖bdot hp hq‖ ≤ nrm d / 2 := by
    have hcomb : (2 * Complex.I * s) * bdot hp hq = bdot hp (cross d hq) := by
      linear_combination v1 - v2
    have hb : ‖bdot hp (cross d hq)‖ ≤ nrm d := by
      have h1 := norm_bdot_le hp (cross d hq)
      have h2 := nrm_cross_le d hq
      rw [hqu, mul_one] at h2
      rw [hpu, one_mul] at h1
      linarith
    have hlhs : ‖(2 * Complex.I * s) * bdot hp hq‖ = 2 * ‖bdot hp hq‖ := by
      rw [norm_mul, norm_mul, norm_mul, hs]
      simp
    rw [hcomb] at hlhs
    linarith [hlhs ▸ hb]
  -- (d) assemble
  have hkill : cross n (cross hp hq) = bdot n hq • hp := by
    rw [cross_cross, hnp]; simp
  have hkillnorm : nrm (cross n (cross hp hq)) ≤ nrm d := by
    rw [hkill, nrm_smul, hpu, mul_one]
    exact hnqle
  have hrec : cross hp hq
      = bdot n (cross hp hq) • n - cross n (cross n (cross hp hq)) := by
    rw [cross_cross n n (cross hp hq), hn]; module
  have haxis : ‖bdot n (cross hp hq)‖ ≤ nrm d / 2 := by
    rw [v1, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, hs, one_mul]
    exact hXsmall
  have h2 : nrm (cross n (cross n (cross hp hq))) ≤ nrm d := by
    refine le_trans (nrm_cross_le n (cross n (cross hp hq))) ?_
    rw [hnu, one_mul]; exact hkillnorm
  have hsplit : nrm (cross hp hq)
      ≤ nrm (bdot n (cross hp hq) • n) + nrm (cross n (cross n (cross hp hq))) := by
    conv_lhs => rw [hrec]
    exact nrm_sub_le _ _
  have hfirst : nrm (bdot n (cross hp hq) • n) ≤ nrm d / 2 := by
    rw [nrm_smul, hnu, mul_one]; exact haxis
  linarith

/-! ## 4.  The two halves multiplied: the heterochiral row has output gain -/

/-- The defect gain of `heterochiral_radialSum_mul_defect_le`, transported to the
lane's `ℂ³` carrier and its Hermitian norm `nrm`. -/
theorem heterochiral_radialSum_mul_defect_le_nrm {k p q : Fin 3 → ℂ}
    (h : k + p + q = 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    (nrm p + nrm q) * nrm ((nrm p)⁻¹ • p + (nrm q)⁻¹ • q) ≤ 4 * nrm k := by
  have hE : (WithLp.toLp 2 k : EuclideanSpace ℂ (Fin 3))
      + WithLp.toLp 2 p + WithLp.toLp 2 q = 0 := by
    simpa using congrArg (fun z => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))) h
  have hpE : (WithLp.toLp 2 p : EuclideanSpace ℂ (Fin 3)) ≠ 0 := by
    intro hc; exact hp (by simpa using hc)
  have hqE : (WithLp.toLp 2 q : EuclideanSpace ℂ (Fin 3)) ≠ 0 := by
    intro hc; exact hq (by simpa using hc)
  rw [nrm_eq_euclid ((nrm p)⁻¹ • p + (nrm q)⁻¹ • q), nrm_eq_euclid p, nrm_eq_euclid q,
    nrm_eq_euclid k]
  exact heterochiral_radialSum_mul_defect_le hE hpE hqE

/-- **The heterochiral row of the R571 commutator square is output-controlled.**

On a triad `k + p + q = 0` with `p, q ≠ 0`, let `h_p` be a unit `s`-helical
vector for the (real, bilinearly normalised) axis `p̂` and `h_q` a unit
`(-s)`-helical vector for the axis `q̂`.  Then

`(‖p‖ + ‖q‖) · ‖h_p × h_q‖ ≤ 6‖k‖`.

The scalar factor `‖p‖ + ‖q‖` is exactly the heterochiral multiplier difference
of `NSUnforced.multiplierDifference_heterochiral`, which
`NSUnforced.heterochiral_multiplierDifference_not_output_controlled` shows is
*not* bounded by any multiple of `‖k‖` on its own.  Paired with the helical
vertex it is, with the absolute constant `6`; so the heterochiral row buys the
same one power of output gain as the homochiral row
(`NSUnforced.abs_multiplierDifference_homochiral_le`), and no sign split is
forced at this point of the argument. -/
theorem heterochiral_vertex_output_controlled {s : ℂ} {k p q hp hq : Fin 3 → ℂ}
    (htriad : k + p + q = 0) (hpne : p ≠ 0) (hqne : q ≠ 0)
    (hs : ‖s‖ = 1) (hsne : s ≠ 0)
    (hn : bdot ((nrm p)⁻¹ • p) ((nrm p)⁻¹ • p) = 1)
    (hpu : nrm hp = 1) (hqu : nrm hq = 1)
    (hP : IsHelical s ((nrm p)⁻¹ • p) hp)
    (hQ : IsHelical (-s) ((nrm q)⁻¹ • q) hq) :
    (nrm p + nrm q) * nrm (cross hp hq) ≤ 6 * nrm k := by
  have hpn : 0 < nrm p :=
    lt_of_le_of_ne (nrm_nonneg p) (fun hc => hpne ((nrm_eq_zero_iff p).1 hc.symm))
  have hqn : 0 < nrm q := lt_of_le_of_ne (nrm_nonneg q)
    (fun hc => hqne ((nrm_eq_zero_iff q).1 hc.symm))
  have hnu : nrm ((nrm p)⁻¹ • p) = 1 := by
    rw [nrm_real_smul, abs_of_pos (inv_pos.2 hpn), inv_mul_cancel₀ (ne_of_gt hpn)]
  have hvertex := nrm_cross_helical_le hs hsne hn hnu hpu hqu hP hQ
  have hdefect := heterochiral_radialSum_mul_defect_le_nrm htriad hpne hqne
  have hsum_nonneg : 0 ≤ nrm p + nrm q := by linarith
  calc (nrm p + nrm q) * nrm (cross hp hq)
      ≤ (nrm p + nrm q) * (3 / 2 * nrm ((nrm p)⁻¹ • p + (nrm q)⁻¹ • q)) :=
        mul_le_mul_of_nonneg_left hvertex hsum_nonneg
    _ = 3 / 2 * ((nrm p + nrm q) * nrm ((nrm p)⁻¹ • p + (nrm q)⁻¹ • q)) := by ring
    _ ≤ 3 / 2 * (4 * nrm k) := by linarith
    _ = 6 * nrm k := by ring

/-- **The heterochiral forcing-side square carries the output gain.**  Summed
over a finite family of heterochiral cells, the commutator squares are dominated
by the output radii squared, with the absolute constant `36`.

This is the heterochiral counterpart of
`NSUnforced.sum_commutator_square_homochiral_le`, whose docstring records that
"the heterochiral rows are excluded here precisely because
`heterochiral_multiplierDifference_not_output_controlled` shows they cannot be
included".  With the helical vertex kept, they can be: the shape
`∑ ‖k‖²·(…)` that the `∑ A² ≤ c_A · Dissip` clause of
`DASHI.NS.Unforced.A1ChannelObligation` needs is available on both rows. -/
theorem sum_heterochiral_square_le {ι : Type*} (fam : Finset ι)
    {sv : ι → ℂ} (kv pv qv hpv hqv : ι → Fin 3 → ℂ)
    (htriad : ∀ i ∈ fam, kv i + pv i + qv i = 0)
    (hpne : ∀ i ∈ fam, pv i ≠ 0) (hqne : ∀ i ∈ fam, qv i ≠ 0)
    (hs : ∀ i ∈ fam, ‖sv i‖ = 1) (hsne : ∀ i ∈ fam, sv i ≠ 0)
    (hn : ∀ i ∈ fam, bdot ((nrm (pv i))⁻¹ • pv i) ((nrm (pv i))⁻¹ • pv i) = 1)
    (hpu : ∀ i ∈ fam, nrm (hpv i) = 1) (hqu : ∀ i ∈ fam, nrm (hqv i) = 1)
    (hP : ∀ i ∈ fam, IsHelical (sv i) ((nrm (pv i))⁻¹ • pv i) (hpv i))
    (hQ : ∀ i ∈ fam, IsHelical (-(sv i)) ((nrm (qv i))⁻¹ • qv i) (hqv i)) :
    ∑ i ∈ fam, ((nrm (pv i) + nrm (qv i)) * nrm (cross (hpv i) (hqv i))) ^ 2
      ≤ 36 * ∑ i ∈ fam, nrm (kv i) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := heterochiral_vertex_output_controlled (htriad i hi) (hpne i hi) (hqne i hi)
    (hs i hi) (hsne i hi) (hn i hi) (hpu i hi) (hqu i hi) (hP i hi) (hQ i hi)
  have hnn : 0 ≤ (nrm (pv i) + nrm (qv i)) * nrm (cross (hpv i) (hqv i)) :=
    mul_nonneg (by linarith [nrm_nonneg (pv i), nrm_nonneg (qv i)]) (nrm_nonneg _)
  nlinarith [nrm_nonneg (kv i)]

/-- **The helical hypotheses are satisfiable.**  With the axis `n = e₃`, sign
`s = 1` and `h = (1, i, 0)/√2`, all of `bdot n n = 1`, `nrm n = 1`, `nrm h = 1`
and `IsHelical 1 n h` hold simultaneously, so `nrm_cross_helical_le` and
`heterochiral_vertex_output_controlled` are not vacuous. -/
theorem exists_unit_helical_vector :
    ∃ (n h : Fin 3 → ℂ), bdot n n = 1 ∧ nrm n = 1 ∧ nrm h = 1 ∧ IsHelical 1 n h := by
  refine ⟨![0, 0, 1], ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹ * Complex.I, 0], ?_, ?_, ?_, ?_⟩
  · simp [bdot, Fin.sum_univ_three]
  · rw [nrm_eq_euclid]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]
  · rw [nrm_eq_euclid, EuclideanSpace.norm_eq]
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [show ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ by simp,
      show ‖((Real.sqrt 2)⁻¹ * Complex.I : ℂ)‖ = (Real.sqrt 2)⁻¹ by
        rw [norm_mul, Complex.norm_I, mul_one]; simp]
    rw [show ‖(0 : ℂ)‖ = 0 by simp]
    have : (Real.sqrt 2)⁻¹ ^ 2 + (Real.sqrt 2)⁻¹ ^ 2 + 0 ^ 2 = 1 := by
      field_simp
      nlinarith [hsq, h2]
    rw [this, Real.sqrt_one]
  · show Complex.I • cross _ _ = (1 : ℂ) • _
    funext i
    fin_cases i <;> simp [cross, crossProduct, Complex.ext_iff]

end RequestProject.NavierStokes.Heterochiral
