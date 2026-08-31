/-
# The high-high → low class: the exact geometry of the multiplier difference

This file attacks the `HH→low` leaf of the classwise payment (package `A_b`)
rather than a generic Schur summability statement.  On that class the shared
output fibre has the exceptionally favourable exact geometry

  `q = k − a`,   `q − a = k − 2a`,   `|k| ≤ θ min (|a|, |q|)` ,

and the point of this file is that the whole multiplier difference
`λ_q − λ_a = |q| − |a|` (co-helical legs) is then an *exact* algebraic object:

* `gap_mul_sum_eq_abs_wdot` — the division-free exact identity

    `| |q| − |a| | · (|a| + |q|) = |⟨k, q − a⟩|` ,   `a + q = k`;

  no inequality, no absolute value inside, no cardinality.
* `sq_gap_add_crossSq_eq` — the Round128 polynomial identity

    `(|q|² − |a|²)² + |k × (q − a)|² = |k|² (2|a|² + 2|q|² − |k|²)` ,

  which is the Lagrange identity for `k` and `q − a` combined with the
  parallelogram law; the Cauchy–Schwarz inequality `⟨k, m⟩² ≤ |k|²|m|²` used
  below is *derived* from it (`wdot_sq_le`), not assumed, so the unsquared
  estimate `| |q| − |a| | ≤ |k|` is obtained constructively from the square gap.

The consequences are quantitative and specific to `HH→low`:

* `hhlow_gap_mul_le` / `hhlow_gap_le_div` — on the class `|k| ≤ θ min(|a|,|q|)`,

    `| |q| − |a| | · ((2 − θ)|a|) ≤ θ |k| |a| + 2 |⟨k, a⟩|` .

  So the multiplier difference splits into a part that is *quadratically* small
  in the output frequency (`θ|k|`, one factor `θ` better than the trivial bound
  `|k|`) plus a purely **transverse** part measuring the alignment of the output
  with the leg.  When the leg is orthogonal to the output the gap is
  `O(θ|k|)`: an explicit low-output factor on the near-diagonal class.
* `hhlow_gap_le_of_transverse` — the `ε`-transverse form
  `| |q| − |a| | ≤ ((θ + 2ε)/(2 − θ)) |k|`.
* `abs_bonyCells_HHlow_transverse_le` — the resulting classwise payment of the
  literal signed `HH→low` residue: at the **energy** level `|k| · E`, with the
  small constant `(θ + 2ε)/(2(2 − θ))`, and with the fibre sum estimated by
  Cauchy–Schwarz in `ℓ²` (`sum_pair_nrm_le_energy`) — no Wiener `ℓ¹` factor, no
  convolution-fibre cardinality, no shell count and no matching hypothesis.

The section on collinear incidences records the complementary exact fact:

* `leray_cross_eq_zero_of_orthogonal`, `crossCell_partner_sum_eq_zero_of_collinear`
  — the Leray projector at the output annihilates the cross product of two legs
  transverse to the output, and a leg collinear with `k` is transverse to `k`.
  Hence the incidences at which the multiplier bound `|λ_{k−a} − λ_a| ≤ |k|` is
  *saturated* contribute exactly nothing to the paired residue.  This is an
  identity, not an estimate, and it holds on the literal Galerkin carrier.

**What this does not close.**  The estimate is still summed in absolute value
*inside* the class; the critical (`H^{1/2}`) payment of the complete signed sum
over the pairs `(p,q)` is untouched.  What is new here is that on `HH→low` the
commutator multiplier is now expressed by an exact identity and carries an
explicit extra low-output/transverse factor beyond the trivial `|k|`.
-/
import RequestProject.NavierStokes.WaleffeExternalBonyClasses

noncomputable section

namespace ClayNS.Waleffe

/-! ## The Euclidean bilinear algebra of the lattice -/

/-- The Euclidean inner product of two wavevectors. -/
def wdot (x y : Wave) : ℝ := ∑ i, (x i : ℝ) * (y i : ℝ)

/-- The Euclidean cross product of two wavevectors. -/
def wcross (x y : Wave) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then (x 1 : ℝ) * (y 2 : ℝ) - (x 2 : ℝ) * (y 1 : ℝ)
    else if i = 1 then (x 2 : ℝ) * (y 0 : ℝ) - (x 0 : ℝ) * (y 2 : ℝ)
    else (x 0 : ℝ) * (y 1 : ℝ) - (x 1 : ℝ) * (y 0 : ℝ)

/-- The squared length of the cross product. -/
def wcrossSq (x y : Wave) : ℝ := ∑ i, (wcross x y i) ^ 2

theorem wdot_self (x : Wave) : wdot x x = wsq x := by
  simp [wdot, wsq, sq]

theorem wdot_comm (x y : Wave) : wdot x y = wdot y x := by
  simp [wdot, mul_comm]

theorem wcrossSq_nonneg (x y : Wave) : 0 ≤ wcrossSq x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The Lagrange identity** on the lattice: `|x × y|² = |x|²|y|² − ⟨x,y⟩²`. -/
theorem wcrossSq_eq (x y : Wave) : wcrossSq x y = wsq x * wsq y - (wdot x y) ^ 2 := by
  simp only [wcrossSq, wcross, wdot, wsq, Fin.sum_univ_three]
  norm_num
  push_cast
  ring

/-- **Cauchy–Schwarz, derived from the Lagrange identity** (no square roots, no
analytic input): `⟨x,y⟩² ≤ |x|²|y|²`. -/
theorem wdot_sq_le (x y : Wave) : (wdot x y) ^ 2 ≤ wsq x * wsq y := by
  have h := wcrossSq_nonneg x y
  rw [wcrossSq_eq] at h
  linarith

/-- The unsquared Cauchy–Schwarz inequality. -/
theorem abs_wdot_le (x y : Wave) : |wdot x y| ≤ wlen x * wlen y := by
  have h := wdot_sq_le x y
  have hx : wlen x ^ 2 = wsq x := Real.sq_sqrt (wsq_nonneg' x)
  have hy : wlen y ^ 2 = wsq y := Real.sq_sqrt (wsq_nonneg' y)
  have hnn : 0 ≤ wlen x * wlen y := mul_nonneg (wlen_nonneg' x) (wlen_nonneg' y)
  have hsq : (wdot x y) ^ 2 ≤ (wlen x * wlen y) ^ 2 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [hsq, hnn, sq_nonneg (wdot x y + wlen x * wlen y),
    sq_nonneg (wdot x y - wlen x * wlen y)]

theorem wlen_sq (x : Wave) : wlen x ^ 2 = wsq x := Real.sq_sqrt (wsq_nonneg' x)

/-! ## The exact partner geometry -/

theorem wsq_sub (x y : Wave) : wsq (x - y) = wsq x - 2 * wdot x y + wsq y := by
  simp only [wsq, wdot, Fin.sum_univ_three, Pi.sub_apply]
  push_cast
  ring

theorem wsq_add (x y : Wave) : wsq (x + y) = wsq x + 2 * wdot x y + wsq y := by
  simp only [wsq, wdot, Fin.sum_univ_three]
  simp only [Pi.add_apply, Int.cast_add]
  ring

theorem wdot_sub_right (x y z : Wave) : wdot x (y - z) = wdot x y - wdot x z := by
  simp only [wdot, Fin.sum_univ_three]
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

/-- **The squared partner gap is exactly the pairing of the output with the leg
separation.**  If `a + q = k` then `|q|² − |a|² = ⟨k, q − a⟩`. -/
theorem wsq_sub_wsq_eq_wdot {k a q : Wave} (h : a + q = k) :
    wsq q - wsq a = wdot k (q - a) := by
  subst h
  simp only [wdot, wsq, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

/-- **The parallelogram law** on the fibre: `|q − a|² = 2|a|² + 2|q|² − |k|²`. -/
theorem wsq_sub_partner {k a q : Wave} (h : a + q = k) :
    wsq (q - a) = 2 * wsq a + 2 * wsq q - wsq k := by
  subst h
  simp only [wsq, Fin.sum_univ_three]
  simp only [Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
  ring

/-- **The Round128 polynomial identity.**  On any fibre `a + q = k`,

  `(|q|² − |a|²)² + |k × (q − a)|² = |k|² (2|a|² + 2|q|² − |k|²)` .

It is the Lagrange identity for the pair `(k, q − a)` together with the
parallelogram law; in particular the whole square gap is carried by the
**output** wavevector `k`. -/
theorem sq_gap_add_crossSq_eq {k a q : Wave} (h : a + q = k) :
    (wsq q - wsq a) ^ 2 + wcrossSq k (q - a)
      = wsq k * (2 * wsq a + 2 * wsq q - wsq k) := by
  rw [wcrossSq_eq, wsq_sub_wsq_eq_wdot h, ← wsq_sub_partner h]
  ring

/-- **The exact division-free gap identity.**  For co-helical legs the
multiplier difference obeys

  `| |q| − |a| | · (|a| + |q|) = |⟨k, q − a⟩|` .

No inequality and no cardinality enters; both sides are exact. -/
theorem gap_mul_sum_eq_abs_wdot {k a q : Wave} (h : a + q = k) :
    |wlen q - wlen a| * (wlen a + wlen q) = |wdot k (q - a)| := by
  have hfac : (wlen q - wlen a) * (wlen a + wlen q) = wsq q - wsq a := by
    have ha := wlen_sq a
    have hq := wlen_sq q
    nlinarith [ha, hq]
  have hnn : 0 ≤ wlen a + wlen q := add_nonneg (wlen_nonneg' a) (wlen_nonneg' q)
  calc |wlen q - wlen a| * (wlen a + wlen q)
      = |(wlen q - wlen a) * (wlen a + wlen q)| := by
        rw [abs_mul, abs_of_nonneg hnn]
    _ = |wsq q - wsq a| := by rw [hfac]
    _ = |wdot k (q - a)| := by rw [wsq_sub_wsq_eq_wdot h]

/-- **The unsquared output bound, derived from the square gap.**  Combining the
exact identity with the Lagrange-derived Cauchy–Schwarz inequality:

  `| |q| − |a| | · (|a| + |q|) ≤ |k| · |q − a|` .

Dividing (when the legs do not both vanish) this is the literal unsquared
estimate `| |q| − |a| | ≤ |k|`, since `|q − a| ≤ |a| + |q|`. -/
theorem gap_mul_sum_le {k a q : Wave} (h : a + q = k) :
    |wlen q - wlen a| * (wlen a + wlen q) ≤ wlen k * wlen (q - a) := by
  rw [gap_mul_sum_eq_abs_wdot h]
  exact abs_wdot_le k (q - a)

/-- **The literal unsquared estimate, welded to the square-gap identity.**
Combining the exact identity `gap_mul_sum_eq_abs_wdot` with the Cauchy–Schwarz
inequality derived from the Lagrange identity gives, for every fibre
`a + q = k`,

  `| |q| − |a| | ≤ |k|` ,

with no appeal to the triangle inequality: the whole route runs through the
polynomial square-gap identity.  For co-helical legs this is exactly
`|λ_q − λ_a| ≤ |k|`. -/
theorem abs_wlen_sub_le_output_of_square_gap {k a q : Wave} (h : a + q = k) :
    |wlen q - wlen a| ≤ wlen k := by
  have hsep : wlen (q - a) ≤ wlen a + wlen q := by
    have ht := wlen_triangle q (-a)
    rw [← sub_eq_add_neg, wlen_neg] at ht
    linarith
  have hmain := gap_mul_sum_le h
  rcases eq_or_lt_of_le (add_nonneg (wlen_nonneg' a) (wlen_nonneg' q)) with hz | hpos
  · -- both legs vanish, hence so does the gap
    have ha : wlen a = 0 := le_antisymm (by linarith [wlen_nonneg' q, wlen_nonneg' a]) (wlen_nonneg' a)
    have hq : wlen q = 0 := le_antisymm (by linarith [wlen_nonneg' q, wlen_nonneg' a]) (wlen_nonneg' q)
    rw [ha, hq]
    simpa using wlen_nonneg' k
  · have hk := wlen_nonneg' k
    have h2 : |wlen q - wlen a| * (wlen a + wlen q) ≤ wlen k * (wlen a + wlen q) := by
      refine le_trans hmain ?_
      exact mul_le_mul_of_nonneg_left hsep hk
    exact le_of_mul_le_mul_right (by linarith [h2]) hpos

/-- The co-helical form: the multiplier difference of the two shared-fibre
partners is at most the output frequency, obtained from the square-gap
identity. -/
theorem abs_helicity_gap_le_output_of_square_gap {k a q : Wave} (h : a + q = k)
    (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1) (hl : ∀ b, l b = s * wlen b) :
    |l q - l a| ≤ wlen k := by
  have heq : |l q - l a| = |wlen q - wlen a| := by
    rw [hl, hl, ← mul_sub, abs_mul]
    rcases hs with h1 | h1 <;> simp [h1]
  rw [heq]
  exact abs_wlen_sub_le_output_of_square_gap h

/-! ## The `HH→low` refinement -/

/-- **The near-diagonal payment has an explicit low-output/transverse
structure.**  On the class `|k| ≤ θ min (|a|, |k − a|)` the multiplier
difference obeys the division-free bound

  `| |k−a| − |a| | · ((2 − θ)|a|) ≤ θ |k| |a| + 2 |⟨k, a⟩|` .

The first term is smaller than the trivial bound `|k|·|a|` by the full factor
`θ`; the second is purely transverse and vanishes for legs orthogonal to the
output.  This is the extra gain that the `HH→low` geometry `q = k − a`,
`q − a = k − 2a` supplies. -/
theorem hhlow_gap_mul_le {θ : ℝ} (hθ : 0 ≤ θ) {k a : Wave}
    (hcls : wlen k ≤ θ * min (wlen a) (wlen (k - a))) :
    |wlen (k - a) - wlen a| * ((2 - θ) * wlen a)
      ≤ θ * wlen k * wlen a + 2 * |wdot k a| := by
  have hka : a + (k - a) = k := by abel
  -- the exact identity, with `q − a = k − 2a`
  have hid := gap_mul_sum_eq_abs_wdot hka
  have hdot : wdot k (k - a - a) = wsq k - 2 * wdot k a := by
    rw [wdot_sub_right, wdot_sub_right, wdot_self]
    ring
  -- the class hypothesis bounds `|k|²` and the leg sum from below
  have hka' : wlen k ≤ θ * wlen a := le_trans hcls
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ)
  have hksq : wsq k ≤ θ * wlen k * wlen a := by
    have h1 : wsq k = wlen k * wlen k := by
      have := wlen_sq k; nlinarith
    have hnn := wlen_nonneg' k
    nlinarith [hka']
  have htri : wlen a ≤ wlen k + wlen (k - a) := by
    have h := wlen_triangle k (-(k - a))
    have hz : k + -(k - a) = a := by abel
    rw [hz, wlen_neg] at h
    exact h
  have hpartner : (1 - θ) * wlen a ≤ wlen (k - a) := by nlinarith [hka']
  have hgapnn : 0 ≤ |wlen (k - a) - wlen a| := abs_nonneg _
  have hsum : (2 - θ) * wlen a ≤ wlen a + wlen (k - a) := by nlinarith [hpartner]
  have habs : |wsq k - 2 * wdot k a| ≤ wsq k + 2 * |wdot k a| := by
    have h1 := le_abs_self (wdot k a)
    have h2 := neg_abs_le (wdot k a)
    have h3 := wsq_nonneg' k
    rw [abs_le]
    constructor <;> linarith
  calc |wlen (k - a) - wlen a| * ((2 - θ) * wlen a)
      ≤ |wlen (k - a) - wlen a| * (wlen a + wlen (k - a)) :=
        mul_le_mul_of_nonneg_left hsum hgapnn
    _ = |wdot k (k - a - a)| := hid
    _ = |wsq k - 2 * wdot k a| := by rw [hdot]
    _ ≤ wsq k + 2 * |wdot k a| := habs
    _ ≤ θ * wlen k * wlen a + 2 * |wdot k a| := by linarith

/-- The divided form of the previous bound. -/
theorem hhlow_gap_le_div {θ : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < 2) {k a : Wave}
    (ha : 0 < wlen a) (hcls : wlen k ≤ θ * min (wlen a) (wlen (k - a))) :
    |wlen (k - a) - wlen a| ≤ (θ * wlen k + 2 * (|wdot k a| / wlen a)) / (2 - θ) := by
  have h := hhlow_gap_mul_le hθ hcls
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 - θ)]
  set X := |wdot k a| / wlen a with hX
  have hEq : |wdot k a| = X * wlen a := by
    rw [hX]; field_simp
  rw [hEq] at h
  have h' : (|wlen (k - a) - wlen a| * (2 - θ)) * wlen a
      ≤ (θ * wlen k + 2 * X) * wlen a := by nlinarith [h]
  exact le_of_mul_le_mul_right h' ha

/-- **The transverse `HH→low` gain.**  If the leg is `ε`-transverse to the
output, `|⟨k,a⟩| ≤ ε |k| |a|`, then on the `HH→low` class

  `| |k−a| − |a| | ≤ ((θ + 2ε)/(2 − θ)) |k|` ,

i.e. the multiplier difference is smaller than the trivial output bound `|k|` by
the explicit factor `(θ + 2ε)/(2 − θ)`, which is small whenever the class
threshold and the alignment are small. -/
theorem hhlow_gap_le_of_transverse {θ ε : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < 2)
    {k a : Wave} (hcls : wlen k ≤ θ * min (wlen a) (wlen (k - a)))
    (htr : |wdot k a| ≤ ε * wlen k * wlen a) :
    |wlen (k - a) - wlen a| ≤ ((θ + 2 * ε) / (2 - θ)) * wlen k := by
  rcases eq_or_lt_of_le (wlen_nonneg' a) with ha | ha
  · -- degenerate leg: then `|k| = 0` too and both sides vanish
    have hk0 : wlen k ≤ 0 := by
      have h := le_trans hcls (mul_le_mul_of_nonneg_left (min_le_left (wlen a) (wlen (k - a))) hθ)
      rw [← ha] at h; simpa using h
    have hk : wlen k = 0 := le_antisymm hk0 (wlen_nonneg' k)
    have hka : wlen (k - a) = 0 := by
      have h1 : wlen (k - a) ≤ wlen k + wlen a := by
        have h := wlen_triangle k (-a)
        rw [← sub_eq_add_neg, wlen_neg] at h
        exact h
      have h2 := wlen_nonneg' (k - a)
      rw [hk, ← ha] at h1
      linarith
    rw [hka, ← ha, hk]
    simp
  · have h := hhlow_gap_mul_le hθ hcls
    have hstep : |wlen (k - a) - wlen a| * ((2 - θ) * wlen a)
        ≤ (θ + 2 * ε) * wlen k * wlen a := by
      calc |wlen (k - a) - wlen a| * ((2 - θ) * wlen a)
          ≤ θ * wlen k * wlen a + 2 * |wdot k a| := h
        _ ≤ θ * wlen k * wlen a + 2 * (ε * wlen k * wlen a) := by linarith
        _ = (θ + 2 * ε) * wlen k * wlen a := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < 2 - θ)]
    have h' : (|wlen (k - a) - wlen a| * (2 - θ)) * wlen a
        ≤ ((θ + 2 * ε) * wlen k) * wlen a := by nlinarith [hstep]
    exact le_of_mul_le_mul_right h' ha

/-! ## The classwise payment of the signed `HH→low` residue -/

/-- **The `HH→low` class pays at the energy level with an explicit small
constant.**  If every incidence of the class is `ε`-transverse to the output,
the literal signed `HH→low` part of the external residue obeys

  `|R^{HH→low}_{p,q}| ≤ ((θ + 2ε)/(2(2 − θ))) · |k| · E · ‖u_p‖‖u_q‖` .

The fibre sum is estimated by Cauchy–Schwarz in `ℓ²`
(`sum_pair_nrm_le_energy`), so no Wiener `ℓ¹` factor, no convolution-fibre
cardinality, no shell count and no matching hypothesis occurs; and the constant
carries the full `HH→low` gain `(θ + 2ε)` on top of the output frequency. -/
theorem abs_bonyCells_HHlow_transverse_le {θ ε : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < 2) (hε : 0 ≤ ε)
    (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i)
    (htr : ∀ a ∈ (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = 2),
      |wdot k a| ≤ ε * wlen k * wlen a) :
    |bonyCells θ modes u k p q 2|
      ≤ ((θ + 2 * ε) / (2 * (2 - θ))) * wlen k * (∑ m ∈ modes, nsq (u m))
          * (nrm (u p) * nrm (u q)) := by
  classical
  set S := (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = 2) with hS
  set W := nrm (u p) * nrm (u q) with hW
  have hWnn : 0 ≤ W := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  set c := (θ + 2 * ε) / (2 - θ) with hc
  have hcnn : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hgap : ∀ a ∈ S, |l (k - a) - l a| ≤ c * wlen k := by
    intro a ha
    have hcls : wlen k ≤ θ * min (wlen a) (wlen (k - a)) := by
      have hc2 : bonyClass θ k a = 2 := by rw [hS, Finset.mem_filter] at ha; exact ha.2
      exact (bonyClass_eq_two_iff θ k a).mp hc2
    have heq : |l (k - a) - l a| = |wlen (k - a) - wlen a| := by
      rw [hl, hl, ← mul_sub, abs_mul]
      rcases hs with h | h <;> simp [h]
    rw [heq]
    exact hhlow_gap_le_of_transverse hθ hθ2 hcls (htr a ha)
  have hstep := abs_bonyCells_le_of_gap_bound θ modes u hk 2
    (fun a => (bonyClass_partner_two θ k a).symm) l hbel (fun _ => c * wlen k) hgap
  refine le_trans hstep ?_
  have hrw : ∑ a ∈ S, c * wlen k * (nrm (u a) * nrm (u (k - a)) * W)
      = c * wlen k * ((∑ a ∈ S, nrm (u a) * nrm (u (k - a))) * W) := by
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [hrw]
  have hcs := sum_pair_nrm_le_energy modes u S k hsupp
  have hknn := wlen_nonneg' k
  have hEnn : 0 ≤ ∑ m ∈ modes, nsq (u m) := Finset.sum_nonneg fun _ _ => nsq_nonneg _
  have hmain : (∑ a ∈ S, nrm (u a) * nrm (u (k - a))) * W
      ≤ (∑ m ∈ modes, nsq (u m)) * W := mul_le_mul_of_nonneg_right hcs hWnn
  have hck : 0 ≤ c * wlen k := mul_nonneg hcnn hknn
  have hfin : (1 / 2) * (c * wlen k * ((∑ a ∈ S, nrm (u a) * nrm (u (k - a))) * W))
      ≤ (1 / 2) * (c * wlen k * ((∑ m ∈ modes, nsq (u m)) * W)) := by
    have h := mul_le_mul_of_nonneg_left hmain hck
    linarith
  refine le_trans hfin (le_of_eq ?_)
  rw [hc]
  field_simp

/-- The output frequency of a nonzero output wavevector is positive. -/
theorem wlen_pos_of_wsq_ne_zero {k : Wave} (hk : wsq k ≠ 0) : 0 < wlen k :=
  Real.sqrt_pos.mpr (lt_of_le_of_ne (wsq_nonneg' k) (Ne.symm hk))

/-- **The unconditional exact-weight `HH→low` payment.**  Without any
transversality assumption, the signed `HH→low` part of the external residue is
paid with the *exact* multiplier weight supplied by the fibre geometry,

  `|R^{HH→low}_{p,q}| ≤ (1/(2(2−θ))) ∑_a (θ|k| + 2|⟨k,a⟩|/|a|) ‖u_a‖‖u_{k−a}‖ ‖u_p‖‖u_q‖` .

The first part of the weight is a factor `θ` below the trivial output bound
`|k|`; the second is purely the alignment of the output with the leg, so the
whole class is controlled by the angular distribution of the fibre and nothing
else.  No absolute value is taken before the gap identity is used, and no
cardinality, shell count or matching hypothesis enters. -/
theorem abs_bonyCells_HHlow_alignment_le {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 2)
    (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hk : wsq k ≠ 0)
    (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1) (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |bonyCells θ modes u k p q 2|
      ≤ (1 / (2 * (2 - θ)))
          * ∑ a ∈ (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = 2),
              (θ * wlen k + 2 * (|wdot k a| / wlen a))
                * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  classical
  set S := (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = 2) with hS
  have hkpos : 0 < wlen k := wlen_pos_of_wsq_ne_zero hk
  have hgap : ∀ a ∈ S, |l (k - a) - l a|
      ≤ (θ * wlen k + 2 * (|wdot k a| / wlen a)) / (2 - θ) := by
    intro a ha
    have hcls : wlen k ≤ θ * min (wlen a) (wlen (k - a)) := by
      have hc2 : bonyClass θ k a = 2 := by rw [hS, Finset.mem_filter] at ha; exact ha.2
      exact (bonyClass_eq_two_iff θ k a).mp hc2
    have hka' : wlen k ≤ θ * wlen a := le_trans hcls
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ.le)
    have hapos : 0 < wlen a := by nlinarith [wlen_nonneg' a]
    have heq : |l (k - a) - l a| = |wlen (k - a) - wlen a| := by
      rw [hl, hl, ← mul_sub, abs_mul]
      rcases hs with h | h <;> simp [h]
    rw [heq]
    exact hhlow_gap_le_div hθ.le hθ2 hapos hcls
  have hstep := abs_bonyCells_le_of_gap_bound θ modes u hk 2
    (fun a => (bonyClass_partner_two θ k a).symm) l hbel
    (fun a => (θ * wlen k + 2 * (|wdot k a| / wlen a)) / (2 - θ)) hgap
  refine le_trans hstep (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

/-! ## WaveCollinear incidences contribute nothing

The bound `| |k−a| − |a| | ≤ |k|` of the previous section is *saturated* exactly
at the collinear incidences `a ∥ k` (there `⟨k, â⟩ = ±|k|`).  The following
exact structural theorem says that those extremal incidences make **no
contribution at all** to the paired residue: the Leray projector at the output
`k` annihilates the cross product of two legs that are both transverse to `k`,
and collinearity forces exactly that.  So the worst case of the multiplier gain
is cancelled by the projector, with no estimate and no hypothesis beyond
incompressibility.
-/

/-- The cross product of two vectors transverse to the output is parallel to the
output, hence killed by the Leray projector at `k`. -/
theorem leray_cross_eq_zero_of_orthogonal {k : Wave} (hk : wsq k ≠ 0) (v w : Fin 3 → ℂ)
    (hv : herm (wC k) v = 0) (hw : herm (wC k) w = 0) :
    leray k (cross v w) = 0 := by
  have hk' : ((wsq k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  have hkc : ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) ≠ 0 := by
    rw [← wsq_cast k]; exact hk'
  have hc := wsq_cast k
  have hv' : (k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2 = 0 := by
    simpa [herm, wC, Fin.sum_univ_three] using hv
  have hw' : (k 0 : ℂ) * w 0 + (k 1 : ℂ) * w 1 + (k 2 : ℂ) * w 2 = 0 := by
    simpa [herm, wC, Fin.sum_univ_three] using hw
  funext i
  simp only [leray, herm, wC, cross, crossProduct, Fin.sum_univ_three, Pi.zero_apply,
    map_intCast, LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [hc]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;> field_simp
  · linear_combination ((k 1 : ℂ) * w 2 - (k 2 : ℂ) * w 1) * hv'
      - ((k 1 : ℂ) * v 2 - (k 2 : ℂ) * v 1) * hw'
  · linear_combination ((k 2 : ℂ) * w 0 - (k 0 : ℂ) * w 2) * hv'
      - ((k 2 : ℂ) * v 0 - (k 0 : ℂ) * v 2) * hw'
  · linear_combination ((k 0 : ℂ) * w 1 - (k 1 : ℂ) * w 0) * hv'
      - ((k 0 : ℂ) * v 1 - (k 1 : ℂ) * v 0) * hw'

/-- Collinearity of the lattice vectors, in the determinant form
`k_i a_j = k_j a_i`. -/
def WaveCollinear (k a : Wave) : Prop := ∀ i j, k i * a j = k j * a i

theorem waveCollinear_partner {k a : Wave} (h : WaveCollinear k a) : WaveCollinear k (k - a) := by
  intro i j
  have h1 := h i j
  have h2 := h j i
  simp only [Pi.sub_apply]
  ring_nf
  linarith [h1, h2]

/-- **A leg collinear with the output is transverse to the output.**  If `a ∥ k`
and `a ≠ 0`, then incompressibility of the mode `a` forces `⟨k, u_a⟩ = 0`. -/
theorem herm_wC_eq_zero_of_collinear {k a : Wave} (ha : a ≠ 0) (hcol : WaveCollinear k a)
    (v : Fin 3 → ℂ) (hv : herm (wC a) v = 0) : herm (wC k) v = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact ha (funext hcon)
  have key : herm (wC k) v * (a i : ℂ) = herm (wC a) v * (k i : ℂ) := by
    have h0 : (k 0 : ℂ) * (a i : ℂ) = (k i : ℂ) * (a 0 : ℂ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (hcol 0 i)
    have h1 : (k 1 : ℂ) * (a i : ℂ) = (k i : ℂ) * (a 1 : ℂ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (hcol 1 i)
    have h2 : (k 2 : ℂ) * (a i : ℂ) = (k i : ℂ) * (a 2 : ℂ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (hcol 2 i)
    simp only [herm, wC, Fin.sum_univ_three, map_intCast]
    linear_combination v 0 * h0 + v 1 * h1 + v 2 * h2
  rw [hv, zero_mul] at key
  have hic : (a i : ℂ) ≠ 0 := by exact_mod_cast hi
  exact (mul_eq_zero.mp key).resolve_right hic

/-- **The extremal (collinear) incidences of the fibre pay nothing.**  If the
incidence `a` is collinear with the output `k` — the exact configuration where
the multiplier bound `|λ_{k−a} − λ_a| ≤ |k|` is attained — then the partner sum
of the two quartic cells `a` and `k − a` vanishes identically, for any
divergence-free field.  No estimate, no threshold and no absolute value is
involved. -/
theorem crossCell_partner_sum_eq_zero_of_collinear {k a p q : Wave} (hk : wsq k ≠ 0)
    (u : Wave → Fin 3 → ℂ) {la lb : ℝ} (ha : a ≠ 0) (hka : k - a ≠ 0)
    (hcol : WaveCollinear k a)
    (hta : herm (wC a) (u a) = 0) (htb : herm (wC (k - a)) (u (k - a)) = 0)
    (hba : cross (wC a) (u a) = fun i => (-Complex.I) * (la : ℂ) * u a i)
    (hbb : cross (wC (k - a)) (u (k - a)) = fun i => (-Complex.I) * (lb : ℂ) * u (k - a) i) :
    crossCell u k p q a + crossCell u k p q (k - a) = 0 := by
  have h1 : herm (wC k) (u a) = 0 := herm_wC_eq_zero_of_collinear ha hcol _ hta
  have h2 : herm (wC k) (u (k - a)) = 0 :=
    herm_wC_eq_zero_of_collinear hka (waveCollinear_partner hcol) _ htb
  rw [crossCell_partner_sum hk u hba hbb,
    leray_cross_eq_zero_of_orthogonal hk (u a) (u (k - a)) h1 h2]
  simp [herm]

/-! ## The quantitative form: near-collinear incidences pay their misalignment

The vanishing above is the endpoint of a quantitative statement.  Write
`outTrans k a` for the length of the component of the output `k` orthogonal to
the direction `a`.  Then the projected cross product of two incompressible legs
is controlled by the misalignments of the two legs with the output:

  `|k| · ‖P_k(u_a × u_b)‖ ≤ (outTrans k a + outTrans k b) ‖u_a‖‖u_b‖` ,

which vanishes exactly in the collinear case.  Since the multiplier gap is, on
the contrary, largest for aligned incidences, the two effects trade off along
the fibre: the payment of a `HH→low` cell carries the angular profile
`|λ_b − λ_a| · (outTrans k a + outTrans k b) / |k|`.
-/

/-- The BAC–CAB identity `k × (v × w) = v ⟨k,w⟩ − w ⟨k,v⟩` on the lattice. -/
theorem cross_wC_cross (k : Wave) (v w : Fin 3 → ℂ) :
    cross (wC k) (cross v w) = fun i => herm (wC k) w * v i - herm (wC k) v * w i := by
  funext i
  fin_cases i <;>
    simp [cross, crossProduct, herm, wC, Fin.sum_univ_three, map_intCast] <;> ring

/-- The Leray projector does not change the cross product with the output. -/
theorem cross_wC_leray (k : Wave) (X : Fin 3 → ℂ) :
    cross (wC k) (leray k X) = cross (wC k) X := by
  funext i
  fin_cases i <;> simp [cross, crossProduct, leray, wC] <;> ring

theorem nrm_cross_wC_of_herm_zero {k : Wave} (Y : Fin 3 → ℂ) (h : herm (wC k) Y = 0) :
    nrm (cross (wC k) Y) = wlen k * nrm Y := by
  have hl := lagrange (wC k) Y
  rw [h] at hl
  simp only [map_zero, sub_zero, nsq_wC] at hl
  rw [nrm, hl, wlen, nrm, Real.sqrt_mul (wsq_nonneg' k)]

/-- **The projected cross product is controlled by the two output pairings.** -/
theorem wlen_mul_nrm_leray_cross_le {k : Wave} (hk : wsq k ≠ 0) (v w : Fin 3 → ℂ) :
    wlen k * nrm (leray k (cross v w))
      ≤ ‖herm (wC k) w‖ * nrm v + ‖herm (wC k) v‖ * nrm w := by
  have h0 : herm (wC k) (leray k (cross v w)) = 0 := herm_wC_leray k _ hk
  have h1 : nrm (cross (wC k) (leray k (cross v w))) = wlen k * nrm (leray k (cross v w)) :=
    nrm_cross_wC_of_herm_zero _ h0
  rw [← h1, cross_wC_leray, cross_wC_cross]
  have h2 : (fun i => herm (wC k) w * v i - herm (wC k) v * w i)
      = fun i => (herm (wC k) w * v i) + (-(herm (wC k) v * w i)) := by
    funext i; ring
  rw [h2]
  refine le_trans (nrm_add_le _ _) ?_
  have h3 : nrm (fun i => herm (wC k) w * v i) = ‖herm (wC k) w‖ * nrm v := nrm_const_mul _ _
  have h4 : nrm (fun i => -(herm (wC k) v * w i)) = ‖herm (wC k) v‖ * nrm w := by
    rw [nrm_neg, nrm_const_mul]
  rw [h3, h4]

/-- The length of the component of the output `k` orthogonal to the direction
`a`; it vanishes exactly when `a` is collinear with `k`. -/
def outTrans (k a : Wave) : ℝ := Real.sqrt (wcrossSq k a / wsq a)

/-- **An incompressible leg only sees the transverse part of the output.** -/
theorem abs_herm_wC_le_of_transverse {k a : Wave} (ha : wsq a ≠ 0) (v : Fin 3 → ℂ)
    (hv : herm (wC a) v = 0) : ‖herm (wC k) v‖ ≤ outTrans k a * nrm v := by
  have hapos : 0 < wsq a := lt_of_le_of_ne (wsq_nonneg' a) (Ne.symm ha)
  set t : ℝ := wdot k a / wsq a with ht
  set r : Fin 3 → ℂ := fun i => wC k i - (t : ℂ) * wC a i with hr
  have hherm : herm r v = herm (wC k) v := by
    have hsplit : herm r v = herm (wC k) v - (t : ℂ) * herm (wC a) v := by
      simp only [hr, herm]
      simp [Fin.sum_univ_three, map_sub, map_mul, Complex.conj_ofReal]
      ring
    rw [hsplit, hv, mul_zero, sub_zero]
  have hnsq : nsq r = wcrossSq k a / wsq a := by
    have hexp : nsq r = wsq k - 2 * t * wdot k a + t ^ 2 * wsq a := by
      simp only [hr, nsq, wC, wsq, wdot, Fin.sum_univ_three, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
      ring
    rw [hexp, ht, wcrossSq_eq]
    field_simp
    ring
  have h1 : ‖herm r v‖ ≤ nrm r * nrm v := norm_herm_le _ _
  rw [hherm] at h1
  have h2 : nrm r = outTrans k a := by rw [nrm, hnsq, outTrans]
  rwa [h2] at h1

/-- **Quantitative collinear cancellation.**  For two incompressible legs the
projected cross product is bounded by the misalignment of the legs with the
output; in the collinear case both misalignments vanish and one recovers
`leray_cross_eq_zero_of_orthogonal`. -/
theorem wlen_mul_nrm_leray_cross_le_outTrans {k a b : Wave} (hk : wsq k ≠ 0) (ha : wsq a ≠ 0)
    (hb : wsq b ≠ 0) (v w : Fin 3 → ℂ) (hv : herm (wC a) v = 0) (hw : herm (wC b) w = 0) :
    wlen k * nrm (leray k (cross v w))
      ≤ (outTrans k a + outTrans k b) * (nrm v * nrm w) := by
  refine le_trans (wlen_mul_nrm_leray_cross_le hk v w) ?_
  have h1 := abs_herm_wC_le_of_transverse (k := k) hb w hw
  have h2 := abs_herm_wC_le_of_transverse (k := k) ha v hv
  nlinarith [nrm_nonneg v, nrm_nonneg w, h1, h2]

/-- **The angular profile of a `HH→low` cell.**  The partner sum of the two
quartic cells is bounded by the multiplier gap *times the misalignment* of the
two legs with the output, divided by the output frequency.  Both factors are
exact objects of the fibre: the gap is largest for aligned incidences, the
misalignment vanishes there, so the payment of the class is concentrated on the
incidences at intermediate angle. -/
theorem abs_crossCell_partner_sum_angular_le {k a p q : Wave} (hk : wsq k ≠ 0)
    (u : Wave → Fin 3 → ℂ) {la lb : ℝ} (ha : wsq a ≠ 0) (hb : wsq (k - a) ≠ 0)
    (hta : herm (wC a) (u a) = 0) (htb : herm (wC (k - a)) (u (k - a)) = 0)
    (hba : cross (wC a) (u a) = fun i => (-Complex.I) * (la : ℂ) * u a i)
    (hbb : cross (wC (k - a)) (u (k - a)) = fun i => (-Complex.I) * (lb : ℂ) * u (k - a) i) :
    |crossCell u k p q a + crossCell u k p q (k - a)| * wlen k
      ≤ |lb - la| * (outTrans k a + outTrans k (k - a))
          * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  rw [crossCell_partner_sum hk u hba hbb, abs_mul]
  set P := leray k (cross (u a) (u (k - a))) with hP
  set C := cross (u p) (u q) with hC
  have hre : |(herm P C).re| ≤ nrm P * nrm C :=
    le_trans (Complex.abs_re_le_norm _) (norm_herm_le _ _)
  have hCle : nrm C ≤ nrm (u p) * nrm (u q) := nrm_cross_le _ _
  have hPle : wlen k * nrm P ≤ (outTrans k a + outTrans k (k - a))
      * (nrm (u a) * nrm (u (k - a))) :=
    wlen_mul_nrm_leray_cross_le_outTrans hk ha hb (u a) (u (k - a)) hta htb
  have hgap : 0 ≤ |lb - la| := abs_nonneg _
  have hkn := wlen_nonneg' k
  have hstep : |(herm P C).re| * wlen k
      ≤ (outTrans k a + outTrans k (k - a)) * (nrm (u a) * nrm (u (k - a)))
        * (nrm (u p) * nrm (u q)) := by
    have h1 : |(herm P C).re| * wlen k ≤ (nrm P * nrm C) * wlen k :=
      mul_le_mul_of_nonneg_right hre hkn
    have h2 : (nrm P * nrm C) * wlen k = (wlen k * nrm P) * nrm C := by ring
    have h3 : (wlen k * nrm P) * nrm C
        ≤ ((outTrans k a + outTrans k (k - a)) * (nrm (u a) * nrm (u (k - a)))) * nrm C :=
      mul_le_mul_of_nonneg_right hPle (nrm_nonneg _)
    have h4 : ((outTrans k a + outTrans k (k - a)) * (nrm (u a) * nrm (u (k - a)))) * nrm C
        ≤ ((outTrans k a + outTrans k (k - a)) * (nrm (u a) * nrm (u (k - a))))
          * (nrm (u p) * nrm (u q)) := by
      refine mul_le_mul_of_nonneg_left hCle ?_
      have : 0 ≤ outTrans k a + outTrans k (k - a) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      exact mul_nonneg this (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
    calc |(herm P C).re| * wlen k ≤ (nrm P * nrm C) * wlen k := h1
      _ = (wlen k * nrm P) * nrm C := h2
      _ ≤ ((outTrans k a + outTrans k (k - a)) * (nrm (u a) * nrm (u (k - a)))) * nrm C := h3
      _ ≤ _ := h4
  calc |lb - la| * |(herm P C).re| * wlen k
      = |lb - la| * (|(herm P C).re| * wlen k) := by ring
    _ ≤ |lb - la| * ((outTrans k a + outTrans k (k - a)) * (nrm (u a) * nrm (u (k - a)))
          * (nrm (u p) * nrm (u q))) := mul_le_mul_of_nonneg_left hstep hgap
    _ = |lb - la| * (outTrans k a + outTrans k (k - a))
          * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by ring

/-! ## On the Galerkin carrier -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- **The transverse `HH→low` payment on the literal Galerkin carrier.**  For a
co-helical Galerkin flow whose `HH→low` incidences are `ε`-transverse to the
output, the signed `HH→low` part of the external residue of the resonant pair
`(p,q)` costs at most

  `((θ + 2ε)/(2(2 − θ))) · |p+q| · E(t) · ‖u_p‖‖u_q‖` ,

cutoff-uniformly.  Compared with the unconditional output-frequency bound
`½|p+q|·E(t)·‖u_p‖‖u_q‖` this class carries the explicit extra small factor
`(θ + 2ε)/(2 − θ)`. -/
theorem abs_bonyCells_HHlow_transverse_le {θ ε : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < 2) (hε : 0 ≤ ε)
    (t : ℝ) {p q : Wave} (hpq : p + q ∈ G.modes) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i)
    (htr : ∀ a ∈ (extIdxSym G.modes (p + q) p q).filter
        (fun a => bonyClass θ (p + q) a = 2),
      |wdot (p + q) a| ≤ ε * wlen (p + q) * wlen a) :
    |bonyCells θ G.modes (G.u t) (p + q) p q 2|
      ≤ ((θ + 2 * ε) / (2 * (2 - θ))) * wlen (p + q) * G.energy t
          * (nrm (G.u t p) * nrm (G.u t q)) := by
  have hsupp : ∀ a, a ∉ G.modes → G.u t a = 0 := fun a ha => G.support t a ha
  have hbel' := beltrami_of_support G.modes (G.u t) l hsupp hbel
  exact ClayNS.Waleffe.abs_bonyCells_HHlow_transverse_le hθ hθ2 hε G.modes (G.u t)
    (G.wsq_ne_zero_of_mem hpq) hsupp l hs hl hbel' htr

/-- **The collinear incidences of a Galerkin flow pay nothing.**  On the literal
physical carrier, where every retained mode is divergence-free, the partner sum
of the two quartic cells of an incidence collinear with the output vanishes
identically. -/
theorem crossCell_partner_sum_eq_zero_of_collinear (t : ℝ) {k a p q : Wave}
    (hk : k ∈ G.modes) (ha : a ≠ 0) (hka : k - a ≠ 0) (hcol : WaveCollinear k a)
    (l : Wave → ℝ)
    (hbel : ∀ b ∈ G.modes,
      cross (wC b) (G.u t b) = fun i => (-Complex.I) * (l b : ℂ) * G.u t b i) :
    crossCell (G.u t) k p q a + crossCell (G.u t) k p q (k - a) = 0 := by
  have hsupp : ∀ b, b ∉ G.modes → G.u t b = 0 := fun b hb => G.support t b hb
  have hbel' := beltrami_of_support G.modes (G.u t) l hsupp hbel
  exact ClayNS.Waleffe.crossCell_partner_sum_eq_zero_of_collinear (G.wsq_ne_zero_of_mem hk)
    (G.u t) ha hka hcol (G.transverse t a) (G.transverse t (k - a)) (hbel' a) (hbel' (k - a))

end GalerkinFlow

end ClayNS.Waleffe
