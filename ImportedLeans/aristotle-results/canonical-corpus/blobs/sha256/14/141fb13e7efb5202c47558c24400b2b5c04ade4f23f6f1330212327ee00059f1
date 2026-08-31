/-
# The critical companion: the fibre-as-operator reduction, its Wiener bound,
# and the exact failure of the cellwise route

This file addresses the first of the two remaining "welds" of the `A` package:
*cutoff-uniform fibre/network summation preserving the low-output `|k|` gain*.

The setting is the literal Fourier lattice `Wave = ℤ³` of the periodic problem.
Write `N_k` for the (signed) projected nonlinearity of the mode `k`, `u_k` for
the velocity mode.  The critical (`H^{1/2}`) production, the critical
dissipation and the *companion* are

  `P   = ∑_k |k| Re⟪u_k , N_k⟫`,
  `D₁₂ = ∑_k |k|³ ‖u_k‖²`,
  `Q   = ∑_k |k|⁻¹ ‖N_k‖²`.

**1. The reduction is cardinality-free.**  `abs_critProduction_le` proves

  `|P| ≤ √D₁₂ · √Q`

with no expansion of `N_k` into convolution cells: the whole `k`-fibre is kept
as one vector.  No fibre cardinality, shell count, matching number or Wiener
`ℓ¹` factor is created.  This is exactly the shape needed by the weighted Young
absorption `2ab ≤ θa² + θ⁻¹b²`: the missing ingredient of `A` is a
cutoff-uniform time-integrated budget for `Q`.

**2. What the low-output gain gives, and what it costs.**  Assume the
`HH→low`-type pointwise gain `‖N_k‖ ≤ |k| · ∑_{a} ‖u_a‖‖u_{k−a}‖`, i.e. the
frequency factor is the *output* `|k|` and not a leg frequency.  Then
`critCompanion_le_cellCompanion` gives `Q ≤ Q_cell` with

  `Q_cell = ∑_k |k| ( ∑_a E_a E_{k−a} )²`,   `E_a = ‖u_a‖`,

and `cellCompanion_le_wiener` bounds the cellwise companion by

  `Q_cell ≤ 4 (∑_a E_a)² (∑_a |a| E_a²)`,

i.e. by the squared **Wiener** (`ℓ¹`) mass times the critical energy.  This is
proved by two Young-type estimates (`young_l1_first`, `young_l1_second`) with no
cardinality anywhere; the `ℓ¹` factor is the entire cost.

**3. The cellwise route cannot be repaired.**  The main theorem
`cellwise_companion_not_controlled_by_energy_enstrophy` shows that the `ℓ¹`
factor above is *not* an artefact of the proof: the cellwise companion is not
bounded by any constant multiple of energy × enstrophy, even after restricting
to a strictly high-high-to-low configuration.  The witnesses are the flat
spectra on a pair of antipodal lattice cubes of scale `N` far from the origin,
with outputs in a cube of scale `N` at the origin: every leg has frequency at
least `16N`, every output at most `4N`, and

  `Q_cell ≥ N¹⁰`,  `(∑E²)(∑|a|²E²) ≤ 4·10⁹ N⁸`,

so the ratio grows like `N²` and no cutoff-uniform companion budget survives the
cellwise absolute value.  Since energy and enstrophy are exactly the quantities
with a cutoff-uniform time budget, this is a precise no-go for the route
"triangle inequality over `p + q = k`, then sum": the signed cancellation inside
the fibre is not optional.

Nothing here is postulated; all bounds are proved from the definitions.
-/
import RequestProject.NavierStokes.WaleffeHighHighOutputGain

noncomputable section

namespace ClayNS.Waleffe

/-- Subadditivity of the square root. -/
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have h2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt hxy
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))

/-! ## 1. The critical production, dissipation and companion -/

/-- The critical (`H^{1/2}`) production of a signed modal nonlinearity `N`
against the field `u`: `∑_k |k| Re⟪u_k, N_k⟫`. -/
def critProduction (T : Finset Wave) (u N : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ T, wlen k * (herm (u k) (N k)).re

/-- The critical dissipation `∑_k |k|³ ‖u_k‖²`. -/
def critDissipation (T : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ T, wlen k ^ 3 * nsq (u k)

/-- The companion quadratic variation `∑_k |k|⁻¹ ‖N_k‖²`. -/
def critCompanion (T : Finset Wave) (N : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ T, (wlen k)⁻¹ * nsq (N k)

theorem critDissipation_nonneg (T : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ critDissipation T u :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (pow_nonneg (wlen_nonneg' k) 3) (nsq_nonneg _)

theorem critCompanion_nonneg (T : Finset Wave) (N : Wave → Fin 3 → ℂ) :
    0 ≤ critCompanion T N :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (inv_nonneg.2 (wlen_nonneg' k)) (nsq_nonneg _)

/-- **The fibre-as-operator reduction.**  The critical production of any signed
modal nonlinearity is bounded by the geometric mean of the critical dissipation
and the companion.  The `k`-fibre is never expanded: no cardinality, shell
count, matching number or Wiener factor appears. -/
theorem abs_critProduction_le (T : Finset Wave) (u N : Wave → Fin 3 → ℂ)
    (hT : ∀ k ∈ T, wsq k ≠ 0) :
    |critProduction T u N| ≤ Real.sqrt (critDissipation T u) * Real.sqrt (critCompanion T N) := by
  classical
  set f : Wave → ℝ := fun k => Real.sqrt (wlen k ^ 3 * nsq (u k)) with hf
  set g : Wave → ℝ := fun k => Real.sqrt ((wlen k)⁻¹ * nsq (N k)) with hg
  have hkey : ∀ k ∈ T, |wlen k * (herm (u k) (N k)).re| ≤ f k * g k := by
    intro k hk
    have hpos : 0 < wlen k := wlen_pos_of_wsq_ne_zero (hT k hk)
    have hre : |(herm (u k) (N k)).re| ≤ nrm (u k) * nrm (N k) :=
      le_trans (Complex.abs_re_le_norm _) (norm_herm_le _ _)
    have hd0 : 0 ≤ wlen k ^ 3 * nsq (u k) :=
      mul_nonneg (pow_nonneg (wlen_nonneg' k) 3) (nsq_nonneg _)
    have hprod : f k * g k = wlen k * (nrm (u k) * nrm (N k)) := by
      rw [hf, hg, ← Real.sqrt_mul hd0]
      have hne : wlen k ≠ 0 := ne_of_gt hpos
      have hval : wlen k ^ 3 * nsq (u k) * ((wlen k)⁻¹ * nsq (N k))
          = (wlen k * (nrm (u k) * nrm (N k))) ^ 2 := by
        rw [← nrm_sq (u k), ← nrm_sq (N k)]
        field_simp
      rw [hval, Real.sqrt_sq (mul_nonneg (wlen_nonneg' k)
        (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))]
    rw [abs_mul, abs_of_nonneg (wlen_nonneg' k), hprod]
    exact mul_le_mul_of_nonneg_left hre (wlen_nonneg' k)
  have h1 : |critProduction T u N| ≤ ∑ k ∈ T, f k * g k := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum hkey
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T f g
  have hfsq : ∑ k ∈ T, f k ^ 2 = critDissipation T u := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    exact Real.sq_sqrt (mul_nonneg (pow_nonneg (wlen_nonneg' k) 3) (nsq_nonneg _))
  have hgsq : ∑ k ∈ T, g k ^ 2 = critCompanion T N := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg]
    refine Real.sq_sqrt ?_
    exact mul_nonneg (inv_nonneg.2 (wlen_nonneg' k)) (nsq_nonneg _)
  rw [hfsq, hgsq] at hcs
  refine le_trans h1 ?_
  rw [← Real.sqrt_mul (critDissipation_nonneg T u)]
  exact Real.le_sqrt_of_sq_le hcs

/-! ## 2. The cellwise majorant and its Wiener bound -/

/-- The cellwise (triangle-inequality) majorant of the `k`-fibre:
`M(k) = ∑_{a} E_a E_{k−a}`. -/
def cellMajorant (S : Finset Wave) (E : Wave → ℝ) (k : Wave) : ℝ :=
  ∑ a ∈ S, E a * E (k - a)

/-- The companion obtained from the cellwise majorant together with the
low-output gain: `∑_k |k| M(k)²`. -/
def cellCompanion (S T : Finset Wave) (E : Wave → ℝ) : ℝ :=
  ∑ k ∈ T, wlen k * (cellMajorant S E k) ^ 2

/-- A nonnegative function supported in `S` has total mass over any finite set
at most its mass over `S`. -/
theorem sum_le_total_of_support {U S : Finset Wave} {g : Wave → ℝ} (hg0 : ∀ b, 0 ≤ g b)
    (hgS : ∀ b, b ∉ S → g b = 0) : ∑ b ∈ U, g b ≤ ∑ b ∈ S, g b := by
  classical
  have h1 : ∑ b ∈ U, g b = ∑ b ∈ U ∩ S, g b := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro x hx hxni
    exact hgS x fun hxs => hxni (Finset.mem_inter.2 ⟨hx, hxs⟩)
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun i _ _ => hg0 i

/-- Translation bound: summing a supported nonnegative function along a shifted
finite set of outputs costs nothing. -/
theorem sum_shift_le {T S : Finset Wave} {g : Wave → ℝ} (hg0 : ∀ b, 0 ≤ g b)
    (hgS : ∀ b, b ∉ S → g b = 0) (a : Wave) :
    ∑ k ∈ T, g (k - a) ≤ ∑ b ∈ S, g b := by
  classical
  have himg : ∑ k ∈ T, g (k - a) = ∑ b ∈ T.image (fun k => k - a), g b := by
    refine (Finset.sum_image ?_).symm
    intro x _ y _ h
    exact sub_left_injective h
  rw [himg]
  exact sum_le_total_of_support hg0 hgS

/-- Reflection bound: the same, for the fibre variable `a ↦ k − a`. -/
theorem sum_reflect_le {S : Finset Wave} {g : Wave → ℝ} (hg0 : ∀ b, 0 ≤ g b)
    (hgS : ∀ b, b ∉ S → g b = 0) (k : Wave) :
    ∑ a ∈ S, g (k - a) ≤ ∑ b ∈ S, g b := by
  classical
  have himg : ∑ a ∈ S, g (k - a) = ∑ b ∈ S.image (fun a => k - a), g b := by
    refine (Finset.sum_image ?_).symm
    intro x _ y _ h
    exact sub_right_injective h
  rw [himg]
  exact sum_le_total_of_support hg0 hgS

/-- **Young's convolution estimate, `ℓ¹` on the first factor.**  No cardinality,
shell count or matching number. -/
theorem young_l1_first {S T : Finset Wave} {f g : Wave → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hgS : ∀ b, b ∉ S → g b = 0) :
    ∑ k ∈ T, (∑ a ∈ S, f a * g (k - a)) ^ 2 ≤ (∑ a ∈ S, f a) ^ 2 * (∑ b ∈ S, g b ^ 2) := by
  classical
  have hpt : ∀ k : Wave, (∑ a ∈ S, f a * g (k - a)) ^ 2
      ≤ (∑ a ∈ S, f a) * (∑ a ∈ S, f a * g (k - a) ^ 2) := by
    intro k
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun a => Real.sqrt (f a))
      (fun a => Real.sqrt (f a) * g (k - a))
    have h1 : ∀ a ∈ S, Real.sqrt (f a) * (Real.sqrt (f a) * g (k - a)) = f a * g (k - a) := by
      intro a _
      have hff : Real.sqrt (f a) * Real.sqrt (f a) = f a := Real.mul_self_sqrt (hf0 a)
      calc Real.sqrt (f a) * (Real.sqrt (f a) * g (k - a))
          = (Real.sqrt (f a) * Real.sqrt (f a)) * g (k - a) := by ring
        _ = f a * g (k - a) := by rw [hff]
    have h2 : ∀ a ∈ S, Real.sqrt (f a) ^ 2 = f a := fun a _ => Real.sq_sqrt (hf0 a)
    have h3 : ∀ a ∈ S, (Real.sqrt (f a) * g (k - a)) ^ 2 = f a * g (k - a) ^ 2 := by
      intro a _
      rw [mul_pow, Real.sq_sqrt (hf0 a)]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3] at hcs
    exact hcs
  have hstep : ∑ k ∈ T, (∑ a ∈ S, f a * g (k - a)) ^ 2
      ≤ ∑ k ∈ T, (∑ a ∈ S, f a) * (∑ a ∈ S, f a * g (k - a) ^ 2) :=
    Finset.sum_le_sum fun k _ => hpt k
  refine le_trans hstep ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hswap : ∑ a ∈ S, ∑ k ∈ T, f a * g (k - a) ^ 2
      ≤ ∑ a ∈ S, f a * (∑ b ∈ S, g b ^ 2) := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (hf0 a)
    have hsupp : ∀ b, b ∉ S → g b ^ 2 = 0 := by
      intro b hb
      simp [hgS b hb]
    exact sum_shift_le (g := fun b => g b ^ 2) (fun b => sq_nonneg _) hsupp a
  have hfin : ∑ a ∈ S, f a * (∑ b ∈ S, g b ^ 2) = (∑ a ∈ S, f a) * (∑ b ∈ S, g b ^ 2) :=
    (Finset.sum_mul _ _ _).symm
  have hfnn : 0 ≤ ∑ a ∈ S, f a := Finset.sum_nonneg fun a _ => hf0 a
  calc (∑ a ∈ S, f a) * ∑ a ∈ S, ∑ k ∈ T, f a * g (k - a) ^ 2
      ≤ (∑ a ∈ S, f a) * ((∑ a ∈ S, f a) * (∑ b ∈ S, g b ^ 2)) := by
        rw [← hfin]
        exact mul_le_mul_of_nonneg_left hswap hfnn
    _ = (∑ a ∈ S, f a) ^ 2 * (∑ b ∈ S, g b ^ 2) := by ring

/-- **Young's convolution estimate, `ℓ¹` on the second factor.** -/
theorem young_l1_second {S T : Finset Wave} {f g : Wave → ℝ} (hg0 : ∀ b, 0 ≤ g b)
    (hgS : ∀ b, b ∉ S → g b = 0) :
    ∑ k ∈ T, (∑ a ∈ S, f a * g (k - a)) ^ 2 ≤ (∑ b ∈ S, g b) ^ 2 * (∑ a ∈ S, f a ^ 2) := by
  classical
  set G := ∑ b ∈ S, g b with hG
  have hGnn : 0 ≤ G := Finset.sum_nonneg fun b _ => hg0 b
  have hpt : ∀ k : Wave, (∑ a ∈ S, f a * g (k - a)) ^ 2
      ≤ G * (∑ a ∈ S, f a ^ 2 * g (k - a)) := by
    intro k
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun a => Real.sqrt (g (k - a)))
      (fun a => f a * Real.sqrt (g (k - a)))
    have h1 : ∀ a ∈ S, Real.sqrt (g (k - a)) * (f a * Real.sqrt (g (k - a)))
        = f a * g (k - a) := by
      intro a _
      have : Real.sqrt (g (k - a)) * Real.sqrt (g (k - a)) = g (k - a) :=
        Real.mul_self_sqrt (hg0 _)
      calc Real.sqrt (g (k - a)) * (f a * Real.sqrt (g (k - a)))
          = f a * (Real.sqrt (g (k - a)) * Real.sqrt (g (k - a))) := by ring
        _ = f a * g (k - a) := by rw [this]
    have h2 : ∀ a ∈ S, Real.sqrt (g (k - a)) ^ 2 = g (k - a) :=
      fun a _ => Real.sq_sqrt (hg0 _)
    have h3 : ∀ a ∈ S, (f a * Real.sqrt (g (k - a))) ^ 2 = f a ^ 2 * g (k - a) := by
      intro a _
      rw [mul_pow, Real.sq_sqrt (hg0 _)]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3] at hcs
    refine le_trans hcs ?_
    refine mul_le_mul_of_nonneg_right (sum_reflect_le hg0 hgS k) ?_
    exact Finset.sum_nonneg fun a _ => mul_nonneg (sq_nonneg _) (hg0 _)
  have hstep : ∑ k ∈ T, (∑ a ∈ S, f a * g (k - a)) ^ 2
      ≤ ∑ k ∈ T, G * (∑ a ∈ S, f a ^ 2 * g (k - a)) :=
    Finset.sum_le_sum fun k _ => hpt k
  refine le_trans hstep ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hswap : ∑ a ∈ S, ∑ k ∈ T, f a ^ 2 * g (k - a) ≤ ∑ a ∈ S, f a ^ 2 * G := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le hg0 hgS a) (sq_nonneg _)
  calc G * ∑ a ∈ S, ∑ k ∈ T, f a ^ 2 * g (k - a)
      ≤ G * ∑ a ∈ S, f a ^ 2 * G := mul_le_mul_of_nonneg_left hswap hGnn
    _ = G ^ 2 * (∑ a ∈ S, f a ^ 2) := by rw [← Finset.sum_mul]; ring

/-- **The Wiener bound for the cellwise companion.**  With the low-output gain
already used, the cellwise companion costs exactly the squared Wiener (`ℓ¹`)
mass times the critical energy `∑_a |a| E_a²`; no cardinality enters. -/
theorem cellCompanion_le_wiener {S T : Finset Wave} {E : Wave → ℝ} (hE0 : ∀ a, 0 ≤ E a)
    (hES : ∀ a, a ∉ S → E a = 0) :
    cellCompanion S T E ≤ 4 * (∑ a ∈ S, E a) ^ 2 * (∑ a ∈ S, wlen a * E a ^ 2) := by
  classical
  set W := fun a : Wave => Real.sqrt (wlen a) * E a with hW
  have hW0 : ∀ a, 0 ≤ W a := fun a => mul_nonneg (Real.sqrt_nonneg _) (hE0 a)
  have hWS : ∀ a, a ∉ S → W a = 0 := by
    intro a ha
    rw [hW]
    simp [hES a ha]
  have hWsq : ∑ a ∈ S, W a ^ 2 = ∑ a ∈ S, wlen a * E a ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hW, mul_pow, Real.sq_sqrt (wlen_nonneg' a)]
  have hpt : ∀ k : Wave, wlen k * (cellMajorant S E k) ^ 2
      ≤ 2 * (∑ a ∈ S, W a * E (k - a)) ^ 2 + 2 * (∑ a ∈ S, E a * W (k - a)) ^ 2 := by
    intro k
    have hsub : Real.sqrt (wlen k) * cellMajorant S E k
        ≤ (∑ a ∈ S, W a * E (k - a)) + (∑ a ∈ S, E a * W (k - a)) := by
      rw [cellMajorant, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a _ => ?_
      have htri : wlen k ≤ wlen a + wlen (k - a) := by
        have h := wlen_triangle a (k - a)
        have hk : a + (k - a) = k := by abel
        rwa [hk] at h
      have hsq : Real.sqrt (wlen k) ≤ Real.sqrt (wlen a) + Real.sqrt (wlen (k - a)) := by
        refine le_trans (Real.sqrt_le_sqrt htri) ?_
        exact sqrt_add_le_add_sqrt (wlen_nonneg' a) (wlen_nonneg' (k - a))
      have hnn : 0 ≤ E a * E (k - a) := mul_nonneg (hE0 a) (hE0 _)
      calc Real.sqrt (wlen k) * (E a * E (k - a))
          ≤ (Real.sqrt (wlen a) + Real.sqrt (wlen (k - a))) * (E a * E (k - a)) :=
            mul_le_mul_of_nonneg_right hsq hnn
        _ = W a * E (k - a) + E a * W (k - a) := by rw [hW]; ring
    have hM0 : 0 ≤ cellMajorant S E k :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hE0 a) (hE0 _)
    have hlhs : wlen k * (cellMajorant S E k) ^ 2
        = (Real.sqrt (wlen k) * cellMajorant S E k) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (wlen_nonneg' k)]
    rw [hlhs]
    have hA0 : 0 ≤ ∑ a ∈ S, W a * E (k - a) :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hW0 a) (hE0 _)
    have hB0 : 0 ≤ ∑ a ∈ S, E a * W (k - a) :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hE0 a) (hW0 _)
    have hL0 : 0 ≤ Real.sqrt (wlen k) * cellMajorant S E k :=
      mul_nonneg (Real.sqrt_nonneg _) hM0
    have hsq2 : (Real.sqrt (wlen k) * cellMajorant S E k) ^ 2
        ≤ ((∑ a ∈ S, W a * E (k - a)) + (∑ a ∈ S, E a * W (k - a))) ^ 2 :=
      pow_le_pow_left₀ hL0 hsub 2
    refine le_trans hsq2 ?_
    nlinarith [sq_nonneg ((∑ a ∈ S, W a * E (k - a)) - (∑ a ∈ S, E a * W (k - a)))]
  have hsum : cellCompanion S T E
      ≤ ∑ k ∈ T, (2 * (∑ a ∈ S, W a * E (k - a)) ^ 2 + 2 * (∑ a ∈ S, E a * W (k - a)) ^ 2) :=
    Finset.sum_le_sum fun k _ => hpt k
  have hA : ∑ k ∈ T, (∑ a ∈ S, W a * E (k - a)) ^ 2
      ≤ (∑ a ∈ S, E a) ^ 2 * (∑ a ∈ S, wlen a * E a ^ 2) := by
    have := young_l1_second (S := S) (T := T) (f := W) (g := E) hE0 hES
    rwa [hWsq] at this
  have hB : ∑ k ∈ T, (∑ a ∈ S, E a * W (k - a)) ^ 2
      ≤ (∑ a ∈ S, E a) ^ 2 * (∑ a ∈ S, wlen a * E a ^ 2) := by
    have := young_l1_first (S := S) (T := T) (f := E) (g := W) hE0 hWS
    rwa [hWsq] at this
  have hsplit : ∑ k ∈ T, (2 * (∑ a ∈ S, W a * E (k - a)) ^ 2
        + 2 * (∑ a ∈ S, E a * W (k - a)) ^ 2)
      = 2 * (∑ k ∈ T, (∑ a ∈ S, W a * E (k - a)) ^ 2)
        + 2 * (∑ k ∈ T, (∑ a ∈ S, E a * W (k - a)) ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit] at hsum
  linarith

/-- **The cardinality bound for the cellwise companion.**  Paying the fibre
cardinality instead of the Wiener mass, the cellwise companion is bounded by
`2·#S·(energy)·(critical energy)`.  Together with `cellCompanion_le_wiener` this
exhausts the two ways of closing the fibre after absolute values; the no-go
below shows that neither factor can be removed. -/
theorem cellCompanion_le_card {S T : Finset Wave} {E : Wave → ℝ}
    (hES : ∀ a, a ∉ S → E a = 0) :
    cellCompanion S T E
      ≤ 2 * (S.card : ℝ) * ((∑ a ∈ S, E a ^ 2) * (∑ a ∈ S, wlen a * E a ^ 2)) := by
  classical
  have hsupp2 : ∀ b, b ∉ S → E b ^ 2 = 0 := by
    intro b hb
    simp [hES b hb]
  have hsuppW : ∀ b, b ∉ S → wlen b * E b ^ 2 = 0 := by
    intro b hb
    simp [hES b hb]
  have hpt : ∀ k : Wave, wlen k * (cellMajorant S E k) ^ 2
      ≤ (S.card : ℝ) * (∑ a ∈ S, ((wlen a * E a ^ 2) * E (k - a) ^ 2
          + E a ^ 2 * (wlen (k - a) * E (k - a) ^ 2))) := by
    intro k
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
      (fun a => E a * E (k - a))
    have hone : ∑ _a ∈ S, ((1 : ℝ)) ^ 2 = (S.card : ℝ) := by
      simp
    have hmul : ∑ a ∈ S, ((1 : ℝ)) * (E a * E (k - a)) = cellMajorant S E k := by
      simp [cellMajorant]
    rw [hone, hmul] at hcs
    have hstep : wlen k * (cellMajorant S E k) ^ 2
        ≤ wlen k * ((S.card : ℝ) * ∑ a ∈ S, (E a * E (k - a)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (wlen_nonneg' k)
    refine le_trans hstep ?_
    rw [← mul_assoc, mul_comm (wlen k) (S.card : ℝ), mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun a _ => ?_
    have htri : wlen k ≤ wlen a + wlen (k - a) := by
      have h := wlen_triangle a (k - a)
      have hk : a + (k - a) = k := by abel
      rwa [hk] at h
    have hnn : 0 ≤ (E a * E (k - a)) ^ 2 := sq_nonneg _
    calc wlen k * (E a * E (k - a)) ^ 2
        ≤ (wlen a + wlen (k - a)) * (E a * E (k - a)) ^ 2 :=
          mul_le_mul_of_nonneg_right htri hnn
      _ = (wlen a * E a ^ 2) * E (k - a) ^ 2 + E a ^ 2 * (wlen (k - a) * E (k - a) ^ 2) := by
          ring
  have hsum : cellCompanion S T E
      ≤ ∑ k ∈ T, (S.card : ℝ) * (∑ a ∈ S, ((wlen a * E a ^ 2) * E (k - a) ^ 2
          + E a ^ 2 * (wlen (k - a) * E (k - a) ^ 2))) :=
    Finset.sum_le_sum fun k _ => hpt k
  refine le_trans hsum ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hrow : ∀ a ∈ S, ∑ k ∈ T, ((wlen a * E a ^ 2) * E (k - a) ^ 2
        + E a ^ 2 * (wlen (k - a) * E (k - a) ^ 2))
      ≤ (wlen a * E a ^ 2) * (∑ b ∈ S, E b ^ 2) + E a ^ 2 * (∑ b ∈ S, wlen b * E b ^ 2) := by
    intro a _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 : (wlen a * E a ^ 2) * (∑ k ∈ T, E (k - a) ^ 2)
        ≤ (wlen a * E a ^ 2) * (∑ b ∈ S, E b ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (wlen_nonneg' a) (sq_nonneg _))
      exact sum_shift_le (g := fun b => E b ^ 2) (fun b => sq_nonneg _) hsupp2 a
    have h2 : E a ^ 2 * (∑ k ∈ T, wlen (k - a) * E (k - a) ^ 2)
        ≤ E a ^ 2 * (∑ b ∈ S, wlen b * E b ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact sum_shift_le (g := fun b => wlen b * E b ^ 2)
        (fun b => mul_nonneg (wlen_nonneg' b) (sq_nonneg _)) hsuppW a
    linarith
  have hinner : (∑ a ∈ S, ∑ k ∈ T, ((wlen a * E a ^ 2) * E (k - a) ^ 2
        + E a ^ 2 * (wlen (k - a) * E (k - a) ^ 2)))
      ≤ 2 * ((∑ a ∈ S, E a ^ 2) * (∑ a ∈ S, wlen a * E a ^ 2)) := by
    refine le_trans (Finset.sum_le_sum hrow) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    have hEE : (∑ a ∈ S, wlen a * E a ^ 2) * (∑ b ∈ S, E b ^ 2)
        + (∑ a ∈ S, E a ^ 2) * (∑ b ∈ S, wlen b * E b ^ 2)
        = 2 * ((∑ a ∈ S, E a ^ 2) * (∑ a ∈ S, wlen a * E a ^ 2)) := by ring
    rw [hEE]
  have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hinner hcard0]

/-- **The low-output gain transfers the companion to the cellwise companion.**
If the projected nonlinearity obeys the `HH→low` gain `‖N_k‖ ≤ |k| M(k)` — the
frequency factor being the *output* — then the companion is dominated by the
cellwise companion. -/
theorem critCompanion_le_cellCompanion {S T : Finset Wave} {E : Wave → ℝ}
    {N : Wave → Fin 3 → ℂ} (hE0 : ∀ a, 0 ≤ E a)
    (hN : ∀ k ∈ T, nrm (N k) ≤ wlen k * cellMajorant S E k) :
    critCompanion T N ≤ cellCompanion S T E := by
  refine Finset.sum_le_sum fun k hk => ?_
  have hM0 : 0 ≤ cellMajorant S E k :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hE0 a) (hE0 _)
  have hn0 : 0 ≤ nrm (N k) := nrm_nonneg _
  have hsq : nsq (N k) ≤ (wlen k * cellMajorant S E k) ^ 2 := by
    rw [← nrm_sq]
    exact pow_le_pow_left₀ hn0 (hN k hk) 2
  have hinv : 0 ≤ (wlen k)⁻¹ := inv_nonneg.2 (wlen_nonneg' k)
  calc (wlen k)⁻¹ * nsq (N k)
      ≤ (wlen k)⁻¹ * (wlen k * cellMajorant S E k) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hinv
    _ ≤ wlen k * (cellMajorant S E k) ^ 2 := by
        rcases eq_or_lt_of_le (wlen_nonneg' k) with h | h
        · rw [← h]
          simp
        · have hne : wlen k ≠ 0 := ne_of_gt h
          have heq : (wlen k)⁻¹ * (wlen k * cellMajorant S E k) ^ 2
              = wlen k * (cellMajorant S E k) ^ 2 := by
            field_simp
          rw [heq]

/-- The composite statement: with the low-output gain, the critical production is
paid by the critical dissipation against the cellwise companion. -/
theorem abs_critProduction_le_cellCompanion {S T : Finset Wave} {E : Wave → ℝ}
    {u N : Wave → Fin 3 → ℂ} (hE0 : ∀ a, 0 ≤ E a) (hT : ∀ k ∈ T, wsq k ≠ 0)
    (hN : ∀ k ∈ T, nrm (N k) ≤ wlen k * cellMajorant S E k) :
    |critProduction T u N| ≤ Real.sqrt (critDissipation T u) * Real.sqrt (cellCompanion S T E) := by
  refine le_trans (abs_critProduction_le T u N hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (critCompanion_le_cellCompanion hE0 hN)

/-- **The weighted Young absorption shape.**  For every `θ > 0` the critical
production splits into a part absorbed by the critical dissipation and the
companion; closing `A` is exactly the problem of a cutoff-uniform time-integrated
bound for the second term. -/
theorem critProduction_absorption (T : Finset Wave) (u N : Wave → Fin 3 → ℂ)
    (hT : ∀ k ∈ T, wsq k ≠ 0) {theta : ℝ} (hth : 0 < theta) :
    |critProduction T u N| ≤ theta * critDissipation T u + (1 / (4 * theta)) * critCompanion T N := by
  have hbase := abs_critProduction_le T u N hT
  have hD := critDissipation_nonneg T u
  have hQ := critCompanion_nonneg T N
  have hsplit : Real.sqrt (critDissipation T u) * Real.sqrt (critCompanion T N)
      ≤ theta * critDissipation T u + (1 / (4 * theta)) * critCompanion T N := by
    have hsD : Real.sqrt (critDissipation T u) ^ 2 = critDissipation T u := Real.sq_sqrt hD
    have hsQ : Real.sqrt (critCompanion T N) ^ 2 = critCompanion T N := Real.sq_sqrt hQ
    set x := Real.sqrt (critDissipation T u)
    set y := Real.sqrt (critCompanion T N)
    have hne : theta ≠ 0 := ne_of_gt hth
    have hxy : x * y ≤ theta * x ^ 2 + (1 / (4 * theta)) * y ^ 2 := by
      rw [← sub_nonneg]
      have hid : theta * x ^ 2 + (1 / (4 * theta)) * y ^ 2 - x * y
          = (2 * theta * x - y) ^ 2 / (4 * theta) := by
        field_simp
        ring
      rw [hid]
      positivity
    rw [hsD, hsQ] at hxy
    exact hxy
  linarith

/-! ### On the literal Galerkin carrier -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The critical (`H^{1/2}`) production of the literal Galerkin network. -/
def critProd (t : ℝ) : ℝ := critProduction G.modes (G.u t) (G.force t)

/-- The `H^{1/2}` dissipation of the literal Galerkin network. -/
def critDiss (t : ℝ) : ℝ := critDissipation G.modes (G.u t)

theorem nrm_u_support (t : ℝ) {a : Wave} (ha : a ∉ G.modes) : nrm (G.u t a) = 0 := by
  rw [G.support t a ha]
  simp [nrm, nsq]

/-- **The critical absorption shape on the physical carrier.**  Assume only the
`HH→low` output gain for the projected nonlinearity of the flow.  Then, for every
`θ > 0`, the critical production of the literal Galerkin network is absorbed by
the critical dissipation up to the Wiener companion.  Everything is
cutoff-uniform: no fibre cardinality, shell count or matching number occurs. -/
theorem abs_critProd_le_wiener_absorption (t : ℝ) {theta : ℝ} (hth : 0 < theta)
    (hgain : ∀ k ∈ G.modes,
      nrm (G.force t k) ≤ wlen k * cellMajorant G.modes (fun a => nrm (G.u t a)) k) :
    |G.critProd t| ≤ theta * G.critDiss t
      + (1 / theta) * ((∑ a ∈ G.modes, nrm (G.u t a)) ^ 2
          * (∑ a ∈ G.modes, wlen a * nrm (G.u t a) ^ 2)) := by
  have hT : ∀ k ∈ G.modes, wsq k ≠ 0 := fun k hk => G.wsq_ne_zero_of_mem hk
  have hE0 : ∀ a, 0 ≤ nrm (G.u t a) := fun a => nrm_nonneg _
  have hES : ∀ a, a ∉ G.modes → nrm (G.u t a) = 0 := fun a ha => G.nrm_u_support t ha
  have habs := critProduction_absorption G.modes (G.u t) (G.force t) hT hth
  have hcell := critCompanion_le_cellCompanion (S := G.modes) (T := G.modes)
    (E := fun a => nrm (G.u t a)) (N := G.force t) hE0 hgain
  have hwie := cellCompanion_le_wiener (S := G.modes) (T := G.modes)
    (E := fun a => nrm (G.u t a)) hE0 hES
  have hstep : critCompanion G.modes (G.force t)
      ≤ 4 * (∑ a ∈ G.modes, nrm (G.u t a)) ^ 2
          * (∑ a ∈ G.modes, wlen a * nrm (G.u t a) ^ 2) := le_trans hcell hwie
  have hcoef : 0 < 1 / (4 * theta) := by positivity
  have hmul : (1 / (4 * theta)) * critCompanion G.modes (G.force t)
      ≤ (1 / (4 * theta)) * (4 * (∑ a ∈ G.modes, nrm (G.u t a)) ^ 2
          * (∑ a ∈ G.modes, wlen a * nrm (G.u t a) ^ 2)) :=
    mul_le_mul_of_nonneg_left hstep (le_of_lt hcoef)
  have hne : theta ≠ 0 := ne_of_gt hth
  have hid : (1 / (4 * theta)) * (4 * (∑ a ∈ G.modes, nrm (G.u t a)) ^ 2
        * (∑ a ∈ G.modes, wlen a * nrm (G.u t a) ^ 2))
      = (1 / theta) * ((∑ a ∈ G.modes, nrm (G.u t a)) ^ 2
          * (∑ a ∈ G.modes, wlen a * nrm (G.u t a) ^ 2)) := by
    field_simp
  rw [hid] at hmul
  have : |G.critProd t| ≤ theta * G.critDiss t
      + (1 / (4 * theta)) * critCompanion G.modes (G.force t) := habs
  linarith

end GalerkinFlow

/-! ## 3. The cellwise route is not repairable

The witnesses: two antipodal lattice cubes of scale `N` at distance `16N` from
the origin (the legs), and a cube of scale `N` at the origin (the outputs).
-/

/-- The high cube `[16N, 24N]³`. -/
def hiBox (N : ℕ) : Finset Wave :=
  Fintype.piFinset fun _ => Finset.Icc (16 * (N : ℤ)) (24 * (N : ℤ))

/-- The legs: the high cube together with its reflection. -/
def legBox (N : ℕ) : Finset Wave := hiBox N ∪ (hiBox N).image (fun a => -a)

/-- The outputs: the cube `[N, 2N]³`. -/
def outBox (N : ℕ) : Finset Wave :=
  Fintype.piFinset fun _ => Finset.Icc ((N : ℤ)) (2 * (N : ℤ))

/-- The flat unit spectrum on the legs. -/
def flatLegs (N : ℕ) : Wave → ℝ := fun a => if a ∈ legBox N then 1 else 0

/-- The part of the fibre of `k` used for the lower bound. -/
def fibreBox (N : ℕ) (k : Wave) : Finset Wave :=
  Fintype.piFinset fun i => Finset.Icc (16 * (N : ℤ) + k i) (24 * (N : ℤ))

theorem mem_hiBox {N : ℕ} {a : Wave} :
    a ∈ hiBox N ↔ ∀ i, 16 * (N : ℤ) ≤ a i ∧ a i ≤ 24 * (N : ℤ) := by
  simp [hiBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem mem_outBox {N : ℕ} {k : Wave} :
    k ∈ outBox N ↔ ∀ i, (N : ℤ) ≤ k i ∧ k i ≤ 2 * (N : ℤ) := by
  simp [outBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem mem_fibreBox {N : ℕ} {k a : Wave} :
    a ∈ fibreBox N k ↔ ∀ i, 16 * (N : ℤ) + k i ≤ a i ∧ a i ≤ 24 * (N : ℤ) := by
  simp [fibreBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem flatLegs_nonneg (N : ℕ) (a : Wave) : 0 ≤ flatLegs N a := by
  rw [flatLegs]
  split <;> norm_num

theorem flatLegs_support (N : ℕ) (a : Wave) (ha : a ∉ legBox N) : flatLegs N a = 0 := by
  rw [flatLegs, if_neg ha]

theorem flatLegs_of_mem {N : ℕ} {a : Wave} (ha : a ∈ legBox N) : flatLegs N a = 1 := by
  rw [flatLegs, if_pos ha]

/-- Every leg has frequency at least `16N`. -/
theorem wlen_legBox_ge {N : ℕ} {a : Wave} (ha : a ∈ legBox N) : (16 * N : ℝ) ≤ wlen a := by
  have habs : (16 * N : ℝ) ≤ |(a 0 : ℝ)| := by
    rcases Finset.mem_union.1 ha with h | h
    · have := (mem_hiBox.1 h) 0
      have h1 : (16 * N : ℝ) ≤ (a 0 : ℝ) := by exact_mod_cast this.1
      exact le_trans h1 (le_abs_self _)
    · rcases Finset.mem_image.1 h with ⟨b, hb, hba⟩
      have hb0 := (mem_hiBox.1 hb) 0
      have : a 0 = -b 0 := by rw [← hba]; rfl
      have h1 : (16 * N : ℝ) ≤ (b 0 : ℝ) := by exact_mod_cast hb0.1
      rw [this]
      push_cast
      rw [abs_neg]
      exact le_trans h1 (le_abs_self _)
  have hsq : ((16 * N : ℝ)) ^ 2 ≤ wsq a := by
    have : ((16 * N : ℝ)) ^ 2 ≤ ((a 0 : ℝ)) ^ 2 := by
      have h16 : (0 : ℝ) ≤ 16 * N := by positivity
      calc ((16 * N : ℝ)) ^ 2 ≤ |(a 0 : ℝ)| ^ 2 := by
            exact pow_le_pow_left₀ h16 habs 2
        _ = ((a 0 : ℝ)) ^ 2 := sq_abs _
    refine le_trans this ?_
    have : wsq a = ((a 0 : ℝ)) ^ 2 + ((a 1 : ℝ)) ^ 2 + ((a 2 : ℝ)) ^ 2 := by
      simp [wsq, Fin.sum_univ_three]
    rw [this]
    nlinarith [sq_nonneg ((a 1 : ℝ)), sq_nonneg ((a 2 : ℝ))]
  have h16 : (0 : ℝ) ≤ 16 * N := by positivity
  calc (16 * N : ℝ) = Real.sqrt (((16 * N : ℝ)) ^ 2) := (Real.sqrt_sq h16).symm
    _ ≤ Real.sqrt (wsq a) := Real.sqrt_le_sqrt hsq
    _ = wlen a := rfl

/-- Every output has frequency between `N` and `4N`. -/
theorem wlen_outBox_bounds {N : ℕ} {k : Wave} (hk : k ∈ outBox N) :
    (N : ℝ) ≤ wlen k ∧ wlen k ≤ (4 * N : ℝ) := by
  have hco : ∀ i, ((N : ℝ)) ≤ (k i : ℝ) ∧ (k i : ℝ) ≤ (2 * N : ℝ) := by
    intro i
    have := (mem_outBox.1 hk) i
    constructor
    · exact_mod_cast this.1
    · exact_mod_cast this.2
  have hexp : wsq k = ((k 0 : ℝ)) ^ 2 + ((k 1 : ℝ)) ^ 2 + ((k 2 : ℝ)) ^ 2 := by
    simp [wsq, Fin.sum_univ_three]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  constructor
  · have hlow : ((N : ℝ)) ^ 2 ≤ wsq k := by
      rw [hexp]
      have h0 := hco 0
      have h1 := hco 1
      have h2 := hco 2
      nlinarith [h0.1, h1.1, h2.1]
    calc (N : ℝ) = Real.sqrt (((N : ℝ)) ^ 2) := (Real.sqrt_sq hN0).symm
      _ ≤ Real.sqrt (wsq k) := Real.sqrt_le_sqrt hlow
      _ = wlen k := rfl
  · have hhigh : wsq k ≤ ((4 * N : ℝ)) ^ 2 := by
      rw [hexp]
      have h0 := hco 0
      have h1 := hco 1
      have h2 := hco 2
      nlinarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
    have h4 : (0 : ℝ) ≤ 4 * N := by positivity
    calc wlen k = Real.sqrt (wsq k) := rfl
      _ ≤ Real.sqrt (((4 * N : ℝ)) ^ 2) := Real.sqrt_le_sqrt hhigh
      _ = (4 * N : ℝ) := Real.sqrt_sq h4

/-- The configuration is strictly high-high-to-low: every output frequency is at
most a quarter of every leg frequency. -/
theorem outBox_legBox_hh {N : ℕ} {k a : Wave} (hk : k ∈ outBox N) (ha : a ∈ legBox N) :
    2 * wlen k ≤ wlen a := by
  have h1 := (wlen_outBox_bounds hk).2
  have h2 := wlen_legBox_ge ha
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- The chosen part of the fibre lies in the legs. -/
theorem fibreBox_subset {N : ℕ} {k : Wave} (hk : k ∈ outBox N) : fibreBox N k ⊆ legBox N := by
  intro a ha
  refine Finset.mem_union.2 (Or.inl (mem_hiBox.2 fun i => ?_))
  have h := (mem_fibreBox.1 ha) i
  have hki := (mem_outBox.1 hk) i
  have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  exact ⟨by omega, h.2⟩

/-- Its reflection through the output also lies in the legs. -/
theorem fibreBox_partner {N : ℕ} {k a : Wave} (hk : k ∈ outBox N) (ha : a ∈ fibreBox N k) :
    k - a ∈ legBox N := by
  refine Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨a - k, mem_hiBox.2 fun i => ?_, ?_⟩))
  · have h := (mem_fibreBox.1 ha) i
    have hki := (mem_outBox.1 hk) i
    have : (a - k) i = a i - k i := rfl
    rw [this]
    constructor
    · omega
    · omega
  · funext i
    have h1 : (-(a - k)) i = -(a i - k i) := rfl
    have h2 : (k - a) i = k i - a i := rfl
    rw [h1, h2]
    ring

/-- The fibre of every output contains at least `N³` incidences. -/
theorem cellMajorant_lower {N : ℕ} {k : Wave} (hk : k ∈ outBox N) :
    ((N : ℝ)) ^ 3 ≤ cellMajorant (legBox N) (flatLegs N) k := by
  classical
  have hsub := fibreBox_subset hk
  have hterm : ∀ a ∈ fibreBox N k, flatLegs N a * flatLegs N (k - a) = 1 := by
    intro a ha
    rw [flatLegs_of_mem (hsub ha), flatLegs_of_mem (fibreBox_partner hk ha)]
    ring
  have hsum : ∑ a ∈ fibreBox N k, flatLegs N a * flatLegs N (k - a)
      = ((fibreBox N k).card : ℝ) := by
    rw [Finset.sum_congr rfl hterm]
    simp
  have hle : ∑ a ∈ fibreBox N k, flatLegs N a * flatLegs N (k - a) ≤ cellMajorant (legBox N)
      (flatLegs N) k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro a _ _
    exact mul_nonneg (flatLegs_nonneg N a) (flatLegs_nonneg N _)
  have hcard : (N : ℕ) ^ 3 ≤ (fibreBox N k).card := by
    have hc : (fibreBox N k).card = ∏ i, (Finset.Icc (16 * (N : ℤ) + k i) (24 * (N : ℤ))).card := by
      rw [fibreBox, Fintype.card_piFinset]
    have hcoord : ∀ i, N ≤ (Finset.Icc (16 * (N : ℤ) + k i) (24 * (N : ℤ))).card := by
      intro i
      rw [Int.card_Icc]
      have hki := (mem_outBox.1 hk) i
      omega
    rw [hc, Fin.prod_univ_three, pow_succ, pow_succ, pow_one]
    exact Nat.mul_le_mul (Nat.mul_le_mul (hcoord 0) (hcoord 1)) (hcoord 2)
  have hcard' : ((N : ℝ)) ^ 3 ≤ ((fibreBox N k).card : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    simpa using this
  rw [← hsum] at hcard'
  exact le_trans hcard' hle

/-- The cellwise companion of the flat leg spectrum is at least `N¹⁰`. -/
theorem cellCompanion_flat_lower (N : ℕ) :
    ((N : ℝ)) ^ 10 ≤ cellCompanion (legBox N) (outBox N) (flatLegs N) := by
  classical
  have hterm : ∀ k ∈ outBox N,
      ((N : ℝ)) ^ 7 ≤ wlen k * (cellMajorant (legBox N) (flatLegs N) k) ^ 2 := by
    intro k hk
    have h1 := (wlen_outBox_bounds hk).1
    have h2 := cellMajorant_lower hk
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hM0 : 0 ≤ ((N : ℝ)) ^ 3 := by positivity
    have hsq : (((N : ℝ)) ^ 3) ^ 2 ≤ (cellMajorant (legBox N) (flatLegs N) k) ^ 2 :=
    pow_le_pow_left₀ hM0 h2 2
    calc ((N : ℝ)) ^ 7 = (N : ℝ) * (((N : ℝ)) ^ 3) ^ 2 := by ring
      _ ≤ wlen k * (((N : ℝ)) ^ 3) ^ 2 := by
          refine mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ wlen k * (cellMajorant (legBox N) (flatLegs N) k) ^ 2 := by
          refine mul_le_mul_of_nonneg_left hsq ?_
          exact le_trans hN0 h1
  have hsum : ∑ k ∈ outBox N, ((N : ℝ)) ^ 7 ≤ cellCompanion (legBox N) (outBox N) (flatLegs N) :=
    Finset.sum_le_sum hterm
  have hcard : (outBox N).card = (N + 1) ^ 3 := by
    have hc : (outBox N).card = ∏ _i : Fin 3, (Finset.Icc ((N : ℤ)) (2 * (N : ℤ))).card := by
      rw [outBox, Fintype.card_piFinset]
    rw [hc, Fin.prod_univ_three, Int.card_Icc]
    have : (2 * (N : ℤ) + 1 - (N : ℤ)).toNat = N + 1 := by omega
    rw [this]
    ring
  have hconst : ∑ k ∈ outBox N, ((N : ℝ)) ^ 7 = ((outBox N).card : ℝ) * ((N : ℝ)) ^ 7 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst, hcard] at hsum
  refine le_trans ?_ hsum
  have h1 : ((N : ℝ)) ^ 3 ≤ (((N + 1 : ℕ)) ^ 3 : ℝ) := by
    have : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) this 3
  calc ((N : ℝ)) ^ 10 = ((N : ℝ)) ^ 3 * ((N : ℝ)) ^ 7 := by ring
    _ ≤ (((N + 1 : ℕ)) ^ 3 : ℝ) * ((N : ℝ)) ^ 7 := by
        refine mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((((N + 1) ^ 3 : ℕ)) : ℝ) * ((N : ℝ)) ^ 7 := by push_cast; ring

/-- The energy of the flat leg spectrum is the number of legs, at most `1458N³`. -/
theorem energy_flat_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ legBox N, (flatLegs N a) ^ 2 ≤ 1458 * ((N : ℝ)) ^ 3 := by
  classical
  have hterm : ∀ a ∈ legBox N, (flatLegs N a) ^ 2 = 1 := by
    intro a ha
    rw [flatLegs_of_mem ha]
    norm_num
  have hsum : ∑ a ∈ legBox N, (flatLegs N a) ^ 2 = ((legBox N).card : ℝ) := by
    rw [Finset.sum_congr rfl hterm]
    simp
  have hcard : (legBox N).card ≤ 2 * (8 * N + 1) ^ 3 := by
    have h1 : (legBox N).card ≤ (hiBox N).card + ((hiBox N).image (fun a : Wave => -a)).card :=
      Finset.card_union_le _ _
    have h2 : ((hiBox N).image (fun a : Wave => -a)).card ≤ (hiBox N).card :=
      Finset.card_image_le
    have h3 : (hiBox N).card = (8 * N + 1) ^ 3 := by
      have hc : (hiBox N).card
          = ∏ _i : Fin 3, (Finset.Icc (16 * (N : ℤ)) (24 * (N : ℤ))).card := by
        rw [hiBox, Fintype.card_piFinset]
      rw [hc, Fin.prod_univ_three, Int.card_Icc]
      have : (24 * (N : ℤ) + 1 - 16 * (N : ℤ)).toNat = 8 * N + 1 := by omega
      rw [this]
      ring
    omega
  rw [hsum]
  have hcast : ((legBox N).card : ℝ) ≤ (2 * (8 * N + 1) ^ 3 : ℕ) := by
    exact_mod_cast hcard
  refine le_trans hcast ?_
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  push_cast
  nlinarith [hNR, sq_nonneg ((N : ℝ) - 1)]

/-- The enstrophy of the flat leg spectrum is at most `1458·1728 N⁵`. -/
theorem enstrophy_flat_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2 ≤ 2519424 * ((N : ℝ)) ^ 5 := by
  classical
  have hwsq : ∀ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2 ≤ 1728 * ((N : ℝ)) ^ 2 := by
    intro a ha
    have hb : ∀ i, |(a i : ℝ)| ≤ 24 * (N : ℝ) := by
      intro i
      rcases Finset.mem_union.1 ha with h | h
      · have h' := (mem_hiBox.1 h) i
        have h1 : (16 * N : ℝ) ≤ (a i : ℝ) := by exact_mod_cast h'.1
        have h2 : (a i : ℝ) ≤ (24 * N : ℝ) := by exact_mod_cast h'.2
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rw [abs_le]
        constructor <;> nlinarith
      · rcases Finset.mem_image.1 h with ⟨b, hb', hba⟩
        have h' := (mem_hiBox.1 hb') i
        have hai : a i = -b i := by rw [← hba]; rfl
        have h1 : (16 * N : ℝ) ≤ (b i : ℝ) := by exact_mod_cast h'.1
        have h2 : (b i : ℝ) ≤ (24 * N : ℝ) := by exact_mod_cast h'.2
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rw [hai]
        push_cast
        rw [abs_le]
        constructor <;> nlinarith
    have hexp : wsq a = ((a 0 : ℝ)) ^ 2 + ((a 1 : ℝ)) ^ 2 + ((a 2 : ℝ)) ^ 2 := by
      simp [wsq, Fin.sum_univ_three]
    have hsq : ∀ i, ((a i : ℝ)) ^ 2 ≤ 576 * ((N : ℝ)) ^ 2 := by
      intro i
      have := hb i
      nlinarith [abs_nonneg ((a i : ℝ)), sq_abs ((a i : ℝ))]
    have hle : wsq a ≤ 1728 * ((N : ℝ)) ^ 2 := by
      rw [hexp]
      have h0 := hsq 0
      have h1 := hsq 1
      have h2 := hsq 2
      linarith
    have hf : (flatLegs N a) ^ 2 = 1 := by
      rw [flatLegs_of_mem ha]; norm_num
    rw [hf, mul_one]
    exact hle
  have hsum : ∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2
      ≤ ∑ _a ∈ legBox N, 1728 * ((N : ℝ)) ^ 2 := Finset.sum_le_sum hwsq
  have hconst : ∑ _a ∈ legBox N, 1728 * ((N : ℝ)) ^ 2
      = ((legBox N).card : ℝ) * (1728 * ((N : ℝ)) ^ 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardR : ((legBox N).card : ℝ) ≤ 1458 * ((N : ℝ)) ^ 3 := by
    have h := energy_flat_le N hN
    have hterm : ∀ a ∈ legBox N, (flatLegs N a) ^ 2 = 1 := by
      intro a ha
      rw [flatLegs_of_mem ha]; norm_num
    have hsum' : ∑ a ∈ legBox N, (flatLegs N a) ^ 2 = ((legBox N).card : ℝ) := by
      rw [Finset.sum_congr rfl hterm]; simp
    rwa [hsum'] at h
  rw [hconst] at hsum
  refine le_trans hsum ?_
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [pow_nonneg hN0 3, pow_nonneg hN0 2]

/-- **The cellwise companion is not controlled by energy × enstrophy.**  Even on
a strictly high-high-to-low configuration — every output frequency at most half
of every leg frequency — and with the low-output `|k|` gain already inserted, the
cellwise majorant produces a companion whose ratio to energy × enstrophy is
unbounded.  Since energy and enstrophy are exactly the quantities with a
cutoff-uniform time budget, no cutoff-uniform companion budget can be obtained
after taking absolute values inside the fibre. -/
theorem cellwise_companion_not_controlled_by_energy_enstrophy (C : ℝ) :
    ∃ (S T : Finset Wave) (E : Wave → ℝ),
      (∀ a, 0 ≤ E a) ∧ (∀ a, a ∉ S → E a = 0) ∧
      (∀ k ∈ T, ∀ a ∈ S, 2 * wlen k ≤ wlen a) ∧
      C * ((∑ a ∈ S, E a ^ 2) * (∑ a ∈ S, wsq a * E a ^ 2)) < cellCompanion S T E := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4000000000 * (|C| + 1))
  refine ⟨legBox (N₀ + 1), outBox (N₀ + 1), flatLegs (N₀ + 1), flatLegs_nonneg _,
    flatLegs_support _, fun k hk a ha => outBox_legBox_hh hk ha, ?_⟩
  set N := N₀ + 1 with hNdef
  have hN1 : 1 ≤ N := Nat.le_add_left 1 N₀
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNbig : 4000000000 * (|C| + 1) < (N : ℝ) := by
    have : ((N₀ : ℝ)) < (N : ℝ) := by
      rw [hNdef]; push_cast; linarith
    linarith
  have hen := energy_flat_le N hN1
  have hens := enstrophy_flat_le N hN1
  have hen0 : 0 ≤ ∑ a ∈ legBox N, (flatLegs N a) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hens0 : 0 ≤ ∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2 :=
    Finset.sum_nonneg fun a _ => mul_nonneg (wsq_nonneg' a) (sq_nonneg _)
  have hprod : (∑ a ∈ legBox N, (flatLegs N a) ^ 2)
      * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2) ≤ 4000000000 * ((N : ℝ)) ^ 8 := by
    have h1 : (∑ a ∈ legBox N, (flatLegs N a) ^ 2)
        * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2)
        ≤ (1458 * ((N : ℝ)) ^ 3) * (2519424 * ((N : ℝ)) ^ 5) := by
      refine mul_le_mul hen hens hens0 ?_
      positivity
    refine le_trans h1 ?_
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [pow_nonneg hN0 8]
  have hcell := cellCompanion_flat_lower N
  have hX0 : 0 ≤ (∑ a ∈ legBox N, (flatLegs N a) ^ 2)
      * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2) := mul_nonneg hen0 hens0
  have hCabs : C * ((∑ a ∈ legBox N, (flatLegs N a) ^ 2)
      * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2))
      ≤ |C| * (4000000000 * ((N : ℝ)) ^ 8) := by
    calc C * ((∑ a ∈ legBox N, (flatLegs N a) ^ 2)
          * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2))
        ≤ |C * ((∑ a ∈ legBox N, (flatLegs N a) ^ 2)
            * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2))| := le_abs_self _
      _ = |C| * ((∑ a ∈ legBox N, (flatLegs N a) ^ 2)
            * (∑ a ∈ legBox N, wsq a * (flatLegs N a) ^ 2)) := by
          rw [abs_mul, abs_of_nonneg hX0]
      _ ≤ |C| * (4000000000 * ((N : ℝ)) ^ 8) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg C)
  have hfinal : |C| * (4000000000 * ((N : ℝ)) ^ 8) < ((N : ℝ)) ^ 10 := by
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hkey : |C| * 4000000000 < ((N : ℝ)) ^ 2 := by
      have h1 : |C| * 4000000000 < (N : ℝ) := by nlinarith [abs_nonneg C]
      nlinarith
    have h8 : (0 : ℝ) < ((N : ℝ)) ^ 8 := by positivity
    calc |C| * (4000000000 * ((N : ℝ)) ^ 8) = (|C| * 4000000000) * ((N : ℝ)) ^ 8 := by ring
      _ < ((N : ℝ)) ^ 2 * ((N : ℝ)) ^ 8 := by exact mul_lt_mul_of_pos_right hkey h8
      _ = ((N : ℝ)) ^ 10 := by ring
  linarith

end ClayNS.Waleffe
