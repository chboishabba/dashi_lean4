/-
# The signed remainder family `F_s`: exact derivative relocation, the `TT*`
# resolvent expansion, and a cardinality-free nested bound

The resolvent/flux architecture of `ResolventGramFlux.lean` leaves exactly one
unpaid object, the *spacetime remainder energy*

  `R_F = ∫_t ∫_s ‖F_s(t)‖² ds dt`,

for the heat-weighted nonlinear remainder family `F_s`.  This file works on that
object directly, and deliberately **before** any absolute-value (ℓ¹) reduction,
which earlier rounds recorded as fatal at critical regularity.

Three independent things are proved, all on the literal physical carrier (the
integer lattice `Wave = ℤ³`, complex amplitudes `ℂ³`, the bilinear cross
product and the Leray projection).

## 1.  Exact derivative relocation for the raw rotational kernel

`rawKernel a b u v = (a × u) × v − u × (b × v)` is the raw directional slot
kernel of the *rotational* form of the nonlinearity (`curl_p u = i (p × u)`, so
`Rot = i·rawKernel`).  On divergence-free legs (`a·u = 0`, `b·v = 0`) it is
proved to *relocate every derivative onto the output frequency* `p = a + b`:

  `rawKernel a b u v = −p (u·v) + u (p·v) + v (p·u)`      (`rawKernel_relocate`)

Consequences, all exact and all free of the high-leg frequencies:

* `rawKernel_swap`   — the kernel is symmetric under swapping the two legs;
* `nrm_rawKernel_le` — `‖rawKernel a b u v‖ ≤ 3|p| ‖u‖‖v‖`;
* `nsq_rawKernel_le` — `‖rawKernel a b u v‖² ≤ 9|p|² ‖u‖²‖v‖²`.

No inner high-leg derivative, no convolution-fibre cardinality and no
irrational radius enters: the estimate is a polynomial identity plus
Cauchy–Schwarz.

## 2.  The inner fibre is paid without any cardinality factor

Summing the projected cells over the literal inner fibre `a + b = p` and using
Cauchy–Schwarz *in the convolution variable* (not a cardinality count) gives

  `‖N_p‖ ≤ 3 |p| · E`   (`nrm_innerForcing_le_energy`),

`E = ∑_a ‖u_a‖²` the Galerkin energy.  So the dependent-row multiplicity of the
nested carrier `a+b=p, p+q=k` is **not** a genuine obstruction at the inner
level: it is paid by ℓ²-convolution, uniformly in the cutoff.

## 3.  `TT*`: the exact signed resolvent expansion of `∫_0^∞ ‖F_s‖² ds`

With the literal viscous pair rate `λ_{pq} = ν(|p|²+|q|²)` and the heat weights
`e^{-sν|p|²}e^{-sν|q|²}`, the whole `s`-integral of the squared remainder is
*identically* the signed resolvent Gram form of the cells:

  `∫_0^∞ ‖F_s(k)‖² ds = ∑_{p,p'} Re⟪G_p, G_{p'}⟫ / (λ_p + λ_{p'})`
      (`integral_nsq_Fs_eq_resForm`)

— an identity, with no absolute value taken anywhere, whose diagonal part is the
plain cell resolvent energy and whose off-diagonal part carries all the phase
information.  `resForm_eq_diag_add_off` and `neg_resOff_le_resDiag` (proved in
`ResolventHeatFactorization.lean`) then apply verbatim.

A quantitative companion is proved for the *majorized* route, to record exactly
what it costs: combining item 2 with a discrete Young inequality
(`sum_sq_conv_le`, `‖f∗g‖_{ℓ²} ≤ ‖f‖_{ℓ¹}‖g‖_{ℓ²}`) gives

  `∑_k ‖F_s(k)‖² ≤ 9 E³ · W_s²`,   `W_s = ∑_p e^{-sν|p|²}|p|`
      (`sum_nsq_Fs_le_heatMass`)

with **no** fibre cardinality, no shell count and no Wiener factor at either
level of the nested carrier.  This is cutoff-uniform for each fixed `s > 0`
modulo the single scalar lattice heat mass `W_s`.

## 4.  The diagonal of the `TT*` identity is paid, cardinality-free

The `p = p'` part of the exact identity, `∑_p ‖G_p‖²/(2λ_p)`, is bounded by
`9E³/(2ν)` for every output `k` (`resDiag_le_energy_cube`): the `|p|²` gain of
the relocated inner kernel is exactly cancelled by the viscous pair rate, and
what survives is a reflected energy sum.  Again no cardinality of any kind
enters.  So on this carrier the surviving obligation is precisely the
*off-diagonal*, phase-carrying part of the signed Gram sum.

**What this does not close.**  `W_s` blows up as `s ↓ 0`, so the majorized
bound of item 3 is *not* `s`-integrable and does not bound `R_F`; and the
diagonal bound of item 4, while cardinality-free per output, is not summed over
outputs.  The `s`-integrable payment has to come from the signed off-diagonal
structure recorded by the exact `TT*` identity, which is not estimated here.
Package A and the literal Clay periodic target are not closed and nothing is
claimed for them.
-/
import RequestProject.NavierStokes.ResolventGramFlux
import RequestProject.NavierStokes.WaleffeBetweenBlockGram
import RequestProject.NavierStokes.WaleffeSelfPhaseEnergyPayment
import RequestProject.NavierStokes.WaleffeTriadInternalPayment
import RequestProject.NavierStokes.WaleffeHighHighOutputGain
import RequestProject.NavierStokes.WaleffeWienerBudget

noncomputable section

open MeasureTheory Set

namespace ClayNS.TTStar

open ClayNS.Waleffe ClayNS.Resolvent

/-! ## 1.  The raw rotational slot kernel -/

/-- The raw directional slot kernel `(a × u) × v − u × (b × v)`.  With the
literal curl convention `curl_p u = i (p × u)` the rotational forcing pair is
`Rot(a,b;u,v) = i · rawKernel a b u v`. -/
def rawKernel (a b : Wave) (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => cross (cross (wC a) u) v i - cross u (cross (wC b) v) i

/-- Pure algebra: the raw kernel expanded by the triple-product identity. -/
theorem rawKernel_expand (a b : Wave) (u v : Fin 3 → ℂ) :
    rawKernel a b u v = fun i =>
      (-(dotb u v)) * (wC a i + wC b i)
        + (dotb (wC a) v) * u i + (dotb (wC b) u) * v i := by
  funext i
  fin_cases i <;>
    simp [rawKernel, cross, crossProduct, dotb, wC, Fin.sum_univ_three] <;> ring

/-- **Derivative relocation.**  On divergence-free legs the raw kernel contains
no leg frequency at all: every derivative sits on the output frequency
`p = a + b`. -/
theorem rawKernel_relocate {a b : Wave} {u v : Fin 3 → ℂ}
    (hu : dotb (wC a) u = 0) (hv : dotb (wC b) v = 0) :
    rawKernel a b u v = fun i =>
      (-(dotb u v)) * wC (a + b) i
        + (dotb (wC (a + b)) v) * u i + (dotb (wC (a + b)) u) * v i := by
  have hadd : ∀ i, wC (a + b) i = wC a i + wC b i := by
    intro i; simp [wC]
  have hdl : ∀ w : Fin 3 → ℂ, dotb (wC (a + b)) w = dotb (wC a) w + dotb (wC b) w := by
    intro w
    simp only [dotb]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hadd j]; ring
  rw [rawKernel_expand]
  funext i
  rw [hadd i, hdl v, hdl u, hu, hv]
  ring

/-- The relocated kernel is symmetric under swapping the two legs. -/
theorem rawKernel_swap {a b : Wave} {u v : Fin 3 → ℂ}
    (hu : dotb (wC a) u = 0) (hv : dotb (wC b) v = 0) :
    rawKernel a b u v = rawKernel b a v u := by
  rw [rawKernel_relocate hu hv, rawKernel_relocate hv hu, add_comm b a]
  funext i
  rw [dotb_comm v u]
  ring

/-- **The physical inner cell bound.**  `‖rawKernel a b u v‖ ≤ 3 |a+b| ‖u‖‖v‖`:
only the *output* frequency appears. -/
theorem nrm_rawKernel_le {a b : Wave} {u v : Fin 3 → ℂ}
    (hu : dotb (wC a) u = 0) (hv : dotb (wC b) v = 0) :
    nrm (rawKernel a b u v) ≤ 3 * wlen (a + b) * nrm u * nrm v := by
  have hcs : ∀ x y : Fin 3 → ℂ, ‖dotb x y‖ ≤ nrm x * nrm y := by
    intro x y; simpa [dotb] using abs_bilin_le x y
  have hsplit : rawKernel a b u v = fun i =>
      (-(dotb u v)) * wC (a + b) i
        + ((dotb (wC (a + b)) v) * u i + (dotb (wC (a + b)) u) * v i) := by
    rw [rawKernel_relocate hu hv]; funext i; ring
  rw [hsplit]
  have h1 : nrm (fun i => (-(dotb u v)) * wC (a + b) i
        + ((dotb (wC (a + b)) v) * u i + (dotb (wC (a + b)) u) * v i))
      ≤ nrm (fun i => (-(dotb u v)) * wC (a + b) i)
        + nrm (fun i => (dotb (wC (a + b)) v) * u i + (dotb (wC (a + b)) u) * v i) :=
    nrm_add_le _ _
  have h2 : nrm (fun i => (dotb (wC (a + b)) v) * u i + (dotb (wC (a + b)) u) * v i)
      ≤ nrm (fun i => (dotb (wC (a + b)) v) * u i)
        + nrm (fun i => (dotb (wC (a + b)) u) * v i) := nrm_add_le _ _
  rw [nrm_const_mul, nrm_wC] at h1
  rw [nrm_const_mul, nrm_const_mul] at h2
  have e1 : ‖-dotb u v‖ ≤ nrm u * nrm v := by rw [norm_neg]; exact hcs u v
  have e2 : ‖dotb (wC (a + b)) v‖ ≤ wlen (a + b) * nrm v := by
    have := hcs (wC (a + b)) v; rwa [nrm_wC] at this
  have e3 : ‖dotb (wC (a + b)) u‖ ≤ wlen (a + b) * nrm u := by
    have := hcs (wC (a + b)) u; rwa [nrm_wC] at this
  have hw : 0 ≤ wlen (a + b) := wlen_nonneg _
  have hu0 : 0 ≤ nrm u := nrm_nonneg _
  have hv0 : 0 ≤ nrm v := nrm_nonneg _
  nlinarith [h1, h2, e1, e2, e3]

/-- Squared form of the physical inner cell bound. -/
theorem nsq_rawKernel_le {a b : Wave} {u v : Fin 3 → ℂ}
    (hu : dotb (wC a) u = 0) (hv : dotb (wC b) v = 0) :
    nsq (rawKernel a b u v) ≤ 9 * wsq (a + b) * nsq u * nsq v := by
  have h := nrm_rawKernel_le hu hv
  have h0 : 0 ≤ nrm (rawKernel a b u v) := nrm_nonneg _
  have hsq : nrm (rawKernel a b u v) ^ 2 ≤ (3 * wlen (a + b) * nrm u * nrm v) ^ 2 := by
    have hr : 0 ≤ 3 * wlen (a + b) * nrm u * nrm v := by
      have := wlen_nonneg (a + b); have := nrm_nonneg u; have := nrm_nonneg v; positivity
    nlinarith [h, h0]
  rw [nrm_sq] at hsq
  calc nsq (rawKernel a b u v) ≤ (3 * wlen (a + b) * nrm u * nrm v) ^ 2 := hsq
    _ = 9 * wsq (a + b) * nsq u * nsq v := by
        rw [show (3 * wlen (a + b) * nrm u * nrm v) ^ 2
          = 9 * (wlen (a + b) ^ 2) * (nrm u ^ 2) * (nrm v ^ 2) by ring,
          wlen_sq, nrm_sq, nrm_sq]

/-! ### A literal witness: the relocated kernel is not the zero object

The legs `a = (1,0,0)`, `u_a = (0,1,0)` and `b = (0,1,0)`, `u_b = (0,0,1)` are
divergence free, and the raw kernel of the pair is the nonzero vector `(0,0,1)`.
So the relocation identity and the `3|p|` bound above are statements about a
nontrivial object. -/

/-- First leg frequency of the witness. -/
def wtA : Wave := ![1, 0, 0]
/-- Second leg frequency of the witness. -/
def wtB : Wave := ![0, 1, 0]
/-- First leg amplitude of the witness. -/
def wtUA : Fin 3 → ℂ := ![0, 1, 0]
/-- Second leg amplitude of the witness. -/
def wtUB : Fin 3 → ℂ := ![0, 0, 1]

theorem wtA_div : dotb (wC wtA) wtUA = 0 := by
  simp [dotb, wC, wtA, wtUA, Fin.sum_univ_three]

theorem wtB_div : dotb (wC wtB) wtUB = 0 := by
  simp [dotb, wC, wtB, wtUB, Fin.sum_univ_three]

theorem wt_rawKernel : rawKernel wtA wtB wtUA wtUB = ![0, 0, 1] := by
  funext i
  fin_cases i <;>
    simp [rawKernel, cross, crossProduct, wC, wtA, wtB, wtUA, wtUB]

theorem wt_rawKernel_ne_zero : nsq (rawKernel wtA wtB wtUA wtUB) = 1 := by
  rw [wt_rawKernel]
  simp [nsq, Fin.sum_univ_three]

/-! ## 2.  The inner fibre: paired forcing and the cardinality-free bound -/

/-- The literal projected inner cell at output `p` coming from the incidence
`a + (p − a) = p`. -/
def innerCell (u : Wave → Fin 3 → ℂ) (p a : Wave) : Fin 3 → ℂ :=
  leray p (rawKernel a (p - a) (u a) (u (p - a)))

/-- The paired inner forcing at `p`: the literal sum over the inner fibre. -/
def innerForcing (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (p : Wave) : Fin 3 → ℂ :=
  fun i => ∑ a ∈ modes, innerCell u p a i

/-- The Galerkin energy of the retained modes. -/
def energy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ := ∑ a ∈ modes, nsq (u a)

theorem energy_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ energy modes u :=
  Finset.sum_nonneg fun _ _ => nsq_nonneg _

/-- Cellwise: the projected inner cell obeys the relocated bound. -/
theorem nrm_innerCell_le {u : Wave → Fin 3 → ℂ} {p a : Wave} (hp : wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0) :
    nrm (innerCell u p a) ≤ 3 * wlen p * nrm (u a) * nrm (u (p - a)) := by
  have hsum : a + (p - a) = p := by abel
  have h := nrm_rawKernel_le (a := a) (b := p - a) (u := u a) (v := u (p - a))
    (hdiv a) (hdiv (p - a))
  rw [hsum] at h
  exact le_trans (nrm_leray_le p _ hp) h

/-- The inner fibre sum is bounded by the convolution of the leg norms. -/
theorem nrm_innerForcing_le_conv {u : Wave → Fin 3 → ℂ} {p : Wave}
    (modes : Finset Wave) (hp : wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0) :
    nrm (innerForcing modes u p)
      ≤ 3 * wlen p * ∑ a ∈ modes, nrm (u a) * nrm (u (p - a)) := by
  have h1 : nrm (innerForcing modes u p) ≤ ∑ a ∈ modes, nrm (innerCell u p a) :=
    nrm_sum_le modes (fun a => innerCell u p a)
  have h2 : ∑ a ∈ modes, nrm (innerCell u p a)
      ≤ ∑ a ∈ modes, 3 * wlen p * (nrm (u a) * nrm (u (p - a))) := by
    refine Finset.sum_le_sum fun a _ => ?_
    have := nrm_innerCell_le (u := u) (p := p) (a := a) hp hdiv
    linarith [this]
  rw [← Finset.mul_sum] at h2
  exact le_trans h1 h2

/-- The reflected fibre mass is bounded by the energy: no cardinality. -/
theorem sum_nsq_reflect_le {u : Wave → Fin 3 → ℂ} {p : Wave} (modes : Finset Wave)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ a ∈ modes, nsq (u (p - a)) ≤ energy modes u := by
  classical
  have hinj : ∀ x ∈ modes, ∀ y ∈ modes, p - x = p - y → x = y := by
    intro x _ y _ h
    simpa [sub_sub_cancel] using congrArg (fun z : Wave => p - z) h
  have himg : ∑ b ∈ modes.image (fun a => p - a), nsq (u b)
      = ∑ a ∈ modes, nsq (u (p - a)) := Finset.sum_image hinj
  rw [← himg]
  set img := modes.image (fun a => p - a) with himgdef
  have hzero : ∑ b ∈ img.filter (fun b => b ∉ modes), nsq (u b) = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ∉ modes := (Finset.mem_filter.mp hb).2
    rw [hsupp b hb']
    simp [nsq]
  have hsplit : ∑ b ∈ img, nsq (u b)
      = ∑ b ∈ img.filter (fun b => b ∈ modes), nsq (u b)
        + ∑ b ∈ img.filter (fun b => b ∉ modes), nsq (u b) :=
    (Finset.sum_filter_add_sum_filter_not img (fun b => b ∈ modes) _).symm
  rw [hsplit, hzero, add_zero]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => nsq_nonneg _)
  intro b hb
  exact (Finset.mem_filter.mp hb).2

/-- **The convolution of the leg norms over the inner fibre is bounded by the
energy, with no cardinality factor.** -/
theorem conv_le_energy {u : Wave → Fin 3 → ℂ} {p : Wave} (modes : Finset Wave)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ a ∈ modes, nrm (u a) * nrm (u (p - a)) ≤ energy modes u := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq modes (fun a => nrm (u a))
    (fun a => nrm (u (p - a)))
  have h1 : ∑ a ∈ modes, nrm (u a) ^ 2 = energy modes u := by
    simp [energy, nrm_sq]
  have h2 : ∑ a ∈ modes, nrm (u (p - a)) ^ 2 ≤ energy modes u := by
    have := sum_nsq_reflect_le (u := u) (p := p) modes hsupp
    simpa [nrm_sq] using this
  have h3 : 0 ≤ ∑ a ∈ modes, nrm (u a) * nrm (u (p - a)) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hE : 0 ≤ energy modes u := energy_nonneg modes u
  nlinarith [hcs, h1, h2, h3, hE]

/-- **The inner (row) fibre is paid without any multiplicity factor:**
`‖N_p‖ ≤ 3|p| E`. -/
theorem nrm_innerForcing_le_energy {u : Wave → Fin 3 → ℂ} {p : Wave}
    (modes : Finset Wave) (hp : wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    nrm (innerForcing modes u p) ≤ 3 * wlen p * energy modes u := by
  have h1 := nrm_innerForcing_le_conv (u := u) (p := p) modes hp hdiv
  have h2 := conv_le_energy (u := u) (p := p) modes hsupp
  have hw : 0 ≤ 3 * wlen p := by have := wlen_nonneg p; linarith
  nlinarith [h1, h2, hw]

/-! ## 3.  The heat-weighted signed remainder family and its `TT*` expansion -/

/-- The scalar heat factor `e^{-sν|p|²}` of one leg. -/
def heatFactor (nu s : ℝ) (p : Wave) : ℝ := Real.exp (-(s * (nu * wsq p)))

theorem heatFactor_pos (nu s : ℝ) (p : Wave) : 0 < heatFactor nu s p := Real.exp_pos _

/-- The literal outer cell at output `k` from the outer incidence `p + (k−p) = k`:
the projected commutator of the inner forcing with the remaining leg. -/
def outerCellVec (N u : Wave → Fin 3 → ℂ) (k p : Wave) : Fin 3 → ℂ :=
  leray k (cross (N p) (u (k - p)))

/-- The heat-weighted signed remainder family at output `k`.  No absolute value
is taken: the sum over the outer fibre is signed. -/
def Fs (nu s : ℝ) (modes : Finset Wave) (N u : Wave → Fin 3 → ℂ) (k : Wave) : Fin 3 → ℂ :=
  fun i => ∑ p ∈ modes,
    ((heatFactor nu s p * heatFactor nu s (k - p) : ℝ) : ℂ) * outerCellVec N u k p i

/-- **The `TT*` expansion, before any absolute value.**  The squared mass of the
signed remainder is the full Gram sum of its cells. -/
theorem nsq_Fs_eq_gram (nu s : ℝ) (modes : Finset Wave) (N u : Wave → Fin 3 → ℂ)
    (k : Wave) :
    nsq (Fs nu s modes N u k)
      = ∑ p ∈ modes, ∑ p' ∈ modes,
          (heatFactor nu s p * heatFactor nu s (k - p))
            * (heatFactor nu s p' * heatFactor nu s (k - p'))
            * (herm (outerCellVec N u k p) (outerCellVec N u k p')).re := by
  have hFs : Fs nu s modes N u k = fun i => ∑ p ∈ modes,
      ((heatFactor nu s p * heatFactor nu s (k - p) : ℝ) : ℂ) * outerCellVec N u k p i := rfl
  rw [hFs, nsq_sum_herm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rw [herm_smul_left, herm_smul_right]
  simp [Complex.mul_re]
  ring

/-- The remainder family is exactly the heat superposition of the cells at the
literal viscous pair rate. -/
theorem Fs_eq_heatCombo (nu s : ℝ) (modes : Finset Wave) (N u : Wave → Fin 3 → ℂ)
    (k : Wave) :
    Fs nu s modes N u k
      = PSDForm.heatCombo (V := Fin 3 → ℂ)
          (fun p : ↥modes => viscousPairRate nu (p : Wave) (k - (p : Wave)))
          (fun p : ↥modes => outerCellVec N u k (p : Wave)) s := by
  funext i
  rw [PSDForm.heatCombo]
  rw [Finset.sum_apply]
  rw [Finset.sum_coe_sort modes
    (fun p => (Real.exp (-(s * viscousPairRate nu p (k - p))) • outerCellVec N u k p) i)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hfac : heatFactor nu s p * heatFactor nu s (k - p)
      = Real.exp (-(s * viscousPairRate nu p (k - p))) := by
    rw [heatFactor, heatFactor, ← Real.exp_add, viscousPairRate]
    ring_nf
  rw [← hfac]
  simp [Complex.real_smul]

/-- **The exact signed resolvent (`TT*`) identity.**  The whole heat-parameter
integral of the squared signed remainder equals the signed resolvent Gram form
of its cells — an identity, with no majorization anywhere. -/
theorem integral_nsq_Fs_eq_resForm {nu : ℝ} (modes : Finset Wave)
    (N u : Wave → Fin 3 → ℂ) (k : Wave)
    (hrate : ∀ p ∈ modes, 0 < viscousPairRate nu p (k - p)) :
    (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      = ∑ p ∈ modes, ∑ p' ∈ modes,
          (herm (outerCellVec N u k p) (outerCellVec N u k p')).re
            / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')) := by
  set lam : ↥modes → ℝ := fun p => viscousPairRate nu (p : Wave) (k - (p : Wave)) with hlam
  set A : ↥modes → (Fin 3 → ℂ) := fun p => outerCellVec N u k (p : Wave) with hA
  have hrate' : ∀ p : ↥modes, 0 < lam p := fun p => hrate (p : Wave) p.2
  have h1 : ∀ s : ℝ, nsq (Fs nu s modes N u k)
      = nsPSD.form (PSDForm.heatCombo lam A s) (PSDForm.heatCombo lam A s) := by
    intro s
    rw [Fs_eq_heatCombo]
    simp [nsPSD_form, nsq_eq_herm_re, hlam, hA]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => h1 s)]
  rw [← PSDForm.resForm_eq_integral nsPSD lam hrate' A A]
  rw [PSDForm.resForm]
  have key : ∀ i : ↥modes, ∑ j : ↥modes, nsPSD.form (A i) (A j) / (lam i + lam j)
      = ∑ p' ∈ modes, (herm (outerCellVec N u k (i : Wave)) (outerCellVec N u k p')).re
          / (viscousPairRate nu (i : Wave) (k - (i : Wave)) + viscousPairRate nu p' (k - p')) := by
    intro i
    exact Finset.sum_coe_sort modes (fun p' =>
      (herm (outerCellVec N u k (i : Wave)) (outerCellVec N u k p')).re
        / (viscousPairRate nu (i : Wave) (k - (i : Wave)) + viscousPairRate nu p' (k - p')))
  simp_rw [key]
  exact Finset.sum_coe_sort modes (fun p => ∑ p' ∈ modes,
    (herm (outerCellVec N u k p) (outerCellVec N u k p')).re
      / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')))

/-! ## 4.  The majorized route, and exactly what it costs -/

/-- Shifting the summation variable cannot increase the mass of a nonnegative
sequence supported in `S`. -/
theorem sum_shift_le (S T : Finset Wave) (h : Wave → ℝ) (hnn : ∀ q, 0 ≤ h q)
    (hsupp : ∀ q ∉ S, h q = 0) (p : Wave) :
    ∑ k ∈ T, h (k - p) ≤ ∑ q ∈ S, h q := by
  classical
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x - p = y - p → x = y := by
    intro x _ y _ hxy
    simpa using congrArg (fun z : Wave => z + p) hxy
  have himg : ∑ b ∈ T.image (fun x => x - p), h b = ∑ k ∈ T, h (k - p) :=
    Finset.sum_image hinj
  rw [← himg]
  set img := T.image (fun x => x - p) with himgdef
  have hzero : ∑ b ∈ img.filter (fun b => b ∉ S), h b = 0 :=
    Finset.sum_eq_zero fun b hb => hsupp b (Finset.mem_filter.mp hb).2
  have hsplit : ∑ b ∈ img, h b
      = ∑ b ∈ img.filter (fun b => b ∈ S), h b
        + ∑ b ∈ img.filter (fun b => b ∉ S), h b :=
    (Finset.sum_filter_add_sum_filter_not img (fun b => b ∈ S) _).symm
  rw [hsplit, hzero, add_zero]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hnn b)
  intro b hb
  exact (Finset.mem_filter.mp hb).2

/-- Discrete Young inequality `‖f ∗ g‖_{ℓ²} ≤ ‖f‖_{ℓ¹} ‖g‖_{ℓ²}` on the lattice,
for nonnegative sequences.  No cardinality of any fibre appears. -/
theorem sum_sq_conv_le (S T : Finset Wave) (f g : Wave → ℝ)
    (hf : ∀ p, 0 ≤ f p) (hgsupp : ∀ q ∉ S, g q = 0) :
    ∑ k ∈ T, (∑ p ∈ S, f p * g (k - p)) ^ 2
      ≤ (∑ p ∈ S, f p) ^ 2 * ∑ q ∈ S, g q ^ 2 := by
  classical
  have hstep : ∀ k : Wave, (∑ p ∈ S, f p * g (k - p)) ^ 2
      ≤ (∑ p ∈ S, f p) * ∑ p ∈ S, f p * g (k - p) ^ 2 := by
    intro k
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => Real.sqrt (f p))
      (fun p => Real.sqrt (f p) * g (k - p))
    have e1 : ∑ p ∈ S, Real.sqrt (f p) * (Real.sqrt (f p) * g (k - p))
        = ∑ p ∈ S, f p * g (k - p) :=
      Finset.sum_congr rfl fun p _ => by
        rw [← mul_assoc, Real.mul_self_sqrt (hf p)]
    have e2 : ∑ p ∈ S, Real.sqrt (f p) ^ 2 = ∑ p ∈ S, f p :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (hf p)
    have e3 : ∑ p ∈ S, (Real.sqrt (f p) * g (k - p)) ^ 2
        = ∑ p ∈ S, f p * g (k - p) ^ 2 :=
      Finset.sum_congr rfl fun p _ => by rw [mul_pow, Real.sq_sqrt (hf p)]
    rw [e1, e2, e3] at hcs
    exact hcs
  have hsum : ∑ k ∈ T, (∑ p ∈ S, f p * g (k - p)) ^ 2
      ≤ ∑ k ∈ T, (∑ p ∈ S, f p) * ∑ p ∈ S, f p * g (k - p) ^ 2 :=
    Finset.sum_le_sum fun k _ => hstep k
  have hswap : ∑ k ∈ T, (∑ p ∈ S, f p) * (∑ p ∈ S, f p * g (k - p) ^ 2)
      = (∑ p ∈ S, f p) * ∑ p ∈ S, f p * ∑ k ∈ T, g (k - p) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
  have htail : ∑ p ∈ S, f p * ∑ k ∈ T, g (k - p) ^ 2
      ≤ ∑ p ∈ S, f p * ∑ q ∈ S, g q ^ 2 := by
    refine Finset.sum_le_sum fun p _ => ?_
    have hshift := sum_shift_le S T (fun q => g q ^ 2) (fun q => sq_nonneg _)
      (fun q hq => by simp [hgsupp q hq]) p
    exact mul_le_mul_of_nonneg_left hshift (hf p)
  have hfin : ∑ p ∈ S, f p * ∑ q ∈ S, g q ^ 2 = (∑ p ∈ S, f p) * ∑ q ∈ S, g q ^ 2 := by
    rw [← Finset.sum_mul]
  have hfnn : 0 ≤ ∑ p ∈ S, f p := Finset.sum_nonneg fun p _ => hf p
  calc ∑ k ∈ T, (∑ p ∈ S, f p * g (k - p)) ^ 2
      ≤ ∑ k ∈ T, (∑ p ∈ S, f p) * ∑ p ∈ S, f p * g (k - p) ^ 2 := hsum
    _ = (∑ p ∈ S, f p) * ∑ p ∈ S, f p * ∑ k ∈ T, g (k - p) ^ 2 := hswap
    _ ≤ (∑ p ∈ S, f p) * ((∑ p ∈ S, f p) * ∑ q ∈ S, g q ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hfnn
        rw [← hfin]; exact htail
    _ = (∑ p ∈ S, f p) ^ 2 * ∑ q ∈ S, g q ^ 2 := by ring

/-- The heat-weighted ℓ¹ lattice mass `W_s = ∑_p e^{-sν|p|²}|p|` of the retained
modes: the single scalar that survives the majorized route. -/
def heatMass (nu s : ℝ) (modes : Finset Wave) : ℝ :=
  ∑ p ∈ modes, heatFactor nu s p * wlen p

/-- Pointwise bound on the signed remainder by the convolution of the two
weighted profiles. -/
theorem nrm_Fs_le_conv {nu s : ℝ} {N u : Wave → Fin 3 → ℂ} {k : Wave}
    (modes : Finset Wave) (hk : wsq k ≠ 0) (En : ℝ)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * En) :
    nrm (Fs nu s modes N u k)
      ≤ ∑ p ∈ modes, (3 * En * (heatFactor nu s p * wlen p))
          * (heatFactor nu s (k - p) * nrm (u (k - p))) := by
  have hFs : Fs nu s modes N u k = fun i => ∑ p ∈ modes,
      ((heatFactor nu s p * heatFactor nu s (k - p) : ℝ) : ℂ) * outerCellVec N u k p i := rfl
  rw [hFs]
  refine le_trans (nrm_sum_le modes (fun p => fun i =>
    ((heatFactor nu s p * heatFactor nu s (k - p) : ℝ) : ℂ) * outerCellVec N u k p i))
    (Finset.sum_le_sum fun p hp => ?_)
  rw [nrm_const_mul]
  have hcpos : 0 < heatFactor nu s p * heatFactor nu s (k - p) :=
    mul_pos (heatFactor_pos _ _ _) (heatFactor_pos _ _ _)
  have hc : ‖((heatFactor nu s p * heatFactor nu s (k - p) : ℝ) : ℂ)‖
      = heatFactor nu s p * heatFactor nu s (k - p) := by
    simp [Complex.norm_real, abs_of_pos (heatFactor_pos nu s p),
      abs_of_pos (heatFactor_pos nu s (k - p))]
  rw [hc]
  have h1 : nrm (outerCellVec N u k p) ≤ nrm (cross (N p) (u (k - p))) :=
    nrm_leray_le k _ hk
  have h2 : nrm (cross (N p) (u (k - p))) ≤ nrm (N p) * nrm (u (k - p)) :=
    nrm_cross_le _ _
  have h3 := hN p hp
  have hcell : nrm (outerCellVec N u k p) ≤ 3 * wlen p * En * nrm (u (k - p)) := by
    have hq : 0 ≤ nrm (u (k - p)) := nrm_nonneg _
    nlinarith [h1, h2, h3, hq]
  calc heatFactor nu s p * heatFactor nu s (k - p) * nrm (outerCellVec N u k p)
      ≤ heatFactor nu s p * heatFactor nu s (k - p) * (3 * wlen p * En * nrm (u (k - p))) :=
        mul_le_mul_of_nonneg_left hcell (le_of_lt hcpos)
    _ = 3 * En * (heatFactor nu s p * wlen p) * (heatFactor nu s (k - p) * nrm (u (k - p))) := by
        ring

/-- **The majorized nested bound, cardinality-free at both levels.**
`∑_k ‖F_s(k)‖² ≤ 9 E_N² · W_s² · E`, with `E_N` the constant of the inner cell
bound and `E` the energy: no inner fibre count, no outer fibre count, no shell
multiplicity. -/
theorem sum_nsq_Fs_le_heatMass {nu s : ℝ} {N u : Wave → Fin 3 → ℂ}
    (modes outs : Finset Wave) (En : ℝ) (hEn : 0 ≤ En) (hs : 0 ≤ s) (hnu : 0 ≤ nu)
    (hk : ∀ k ∈ outs, wsq k ≠ 0)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * En)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ k ∈ outs, nsq (Fs nu s modes N u k)
      ≤ 9 * En ^ 2 * heatMass nu s modes ^ 2 * energy modes u := by
  classical
  set f : Wave → ℝ := fun p => 3 * En * (heatFactor nu s p * wlen p) with hfdef
  set g : Wave → ℝ := fun q => heatFactor nu s q * nrm (u q) with hgdef
  have hfnn : ∀ p, 0 ≤ f p := fun p => by
    have := (heatFactor_pos nu s p).le
    have := wlen_nonneg p
    simp only [hfdef]
    positivity
  have hgsupp : ∀ q ∉ modes, g q = 0 := by
    intro q hq
    simp [hgdef, hsupp q hq, nrm, nsq]
  have hcell : ∑ k ∈ outs, nsq (Fs nu s modes N u k)
      ≤ ∑ k ∈ outs, (∑ p ∈ modes, f p * g (k - p)) ^ 2 := by
    refine Finset.sum_le_sum fun k hkm => ?_
    have hb := nrm_Fs_le_conv (nu := nu) (s := s) (N := N) (u := u) (k := k) modes
      (hk k hkm) En hN
    have hnn : 0 ≤ ∑ p ∈ modes, f p * g (k - p) :=
      Finset.sum_nonneg fun p _ => by
        have h1 := hfnn p
        have h2 : 0 ≤ g (k - p) := by
          have := (heatFactor_pos nu s (k - p)).le
          have := nrm_nonneg (u (k - p))
          simp only [hgdef]
          positivity
        exact mul_nonneg h1 h2
    have h0 : 0 ≤ nrm (Fs nu s modes N u k) := nrm_nonneg _
    have : nrm (Fs nu s modes N u k) ≤ ∑ p ∈ modes, f p * g (k - p) := by
      simpa [hfdef, hgdef, mul_comm, mul_left_comm, mul_assoc] using hb
    calc nsq (Fs nu s modes N u k) = nrm (Fs nu s modes N u k) ^ 2 := (nrm_sq _).symm
      _ ≤ (∑ p ∈ modes, f p * g (k - p)) ^ 2 := by nlinarith [this, h0, hnn]
  have hyoung := sum_sq_conv_le modes outs f g hfnn hgsupp
  have hfsum : ∑ p ∈ modes, f p = 3 * En * heatMass nu s modes := by
    simp only [hfdef, heatMass]
    rw [← Finset.mul_sum]
  have hgsum : ∑ q ∈ modes, g q ^ 2 ≤ energy modes u := by
    refine le_trans (Finset.sum_le_sum fun q _ => ?_) (le_of_eq (rfl : energy modes u = energy modes u))
    · show g q ^ 2 ≤ nsq (u q)
      have hle : heatFactor nu s q ≤ 1 := by
        rw [heatFactor, Real.exp_le_one_iff]
        have : 0 ≤ s * (nu * wsq q) := by
          have := wsq_nonneg' q
          positivity
        linarith
      have hpos := (heatFactor_pos nu s q).le
      have hq : 0 ≤ nrm (u q) := nrm_nonneg _
      have : g q ^ 2 = heatFactor nu s q ^ 2 * nrm (u q) ^ 2 := by
        simp [hgdef, mul_pow]
      rw [this, nrm_sq]
      have h1 : heatFactor nu s q ^ 2 ≤ 1 := by nlinarith [hpos, hle]
      have h2 : 0 ≤ nsq (u q) := nsq_nonneg _
      nlinarith [h1, h2]
  have hEsum : 0 ≤ ∑ q ∈ modes, g q ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hmass : 0 ≤ heatMass nu s modes :=
    Finset.sum_nonneg fun p _ => mul_nonneg (heatFactor_pos _ _ _).le (wlen_nonneg p)
  calc ∑ k ∈ outs, nsq (Fs nu s modes N u k)
      ≤ ∑ k ∈ outs, (∑ p ∈ modes, f p * g (k - p)) ^ 2 := hcell
    _ ≤ (∑ p ∈ modes, f p) ^ 2 * ∑ q ∈ modes, g q ^ 2 := hyoung
    _ ≤ (3 * En * heatMass nu s modes) ^ 2 * energy modes u := by
        rw [hfsum]
        have hsq : 0 ≤ (3 * En * heatMass nu s modes) ^ 2 := sq_nonneg _
        exact mul_le_mul_of_nonneg_left hgsum hsq
    _ = 9 * En ^ 2 * heatMass nu s modes ^ 2 * energy modes u := by ring

/-- The same bound with the inner constant supplied by the physical inner fibre
theorem: the whole nested object is controlled by the energy and the scalar
heat mass alone. -/
theorem sum_nsq_Fs_le_energy {nu s : ℝ} {u : Wave → Fin 3 → ℂ}
    (modes outs : Finset Wave) (hs : 0 ≤ s) (hnu : 0 ≤ nu)
    (hk : ∀ k ∈ outs, wsq k ≠ 0)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ k ∈ outs, nsq (Fs nu s modes (innerForcing modes u) u k)
      ≤ 9 * energy modes u ^ 2 * heatMass nu s modes ^ 2 * energy modes u := by
  refine sum_nsq_Fs_le_heatMass modes outs (energy modes u) (energy_nonneg modes u) hs hnu hk
    (fun p hpm => nrm_innerForcing_le_energy modes (hp p hpm) hdiv hsupp) hsupp

/-! ## 5.  The diagonal of the `TT*` identity is paid, cardinality-free

The `p = p'` terms of `integral_nsq_Fs_eq_resForm` are
`∑_p ‖G_p‖²/(2λ_p)`.  Inserting the physical inner cell bound and using that the
viscous pair rate dominates `ν|p|²` cancels the whole `|p|²` gain of the inner
kernel, and the surviving sum is a reflected energy sum.  So, for each output
`k`, the diagonal is bounded by `9E³/(2ν)` with no fibre cardinality, no shell
count and no dependence on the cutoff.  The unpaid object is therefore exactly
the off-diagonal (coherent) part of the signed Gram sum. -/
theorem resDiag_le_energy_cube {nu : ℝ} {N u : Wave → Fin 3 → ℂ} {k : Wave}
    (modes : Finset Wave) (hnu : 0 < nu) (En : ℝ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0) (hk : wsq k ≠ 0)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * En)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ p ∈ modes, nsq (outerCellVec N u k p) / (2 * viscousPairRate nu p (k - p))
      ≤ 9 * En ^ 2 * energy modes u / (2 * nu) := by
  have hstep : ∀ p ∈ modes,
      nsq (outerCellVec N u k p) / (2 * viscousPairRate nu p (k - p))
        ≤ 9 * En ^ 2 * nsq (u (k - p)) / (2 * nu) := by
    intro p hpm
    have hwp : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg' p) (Ne.symm (hp p hpm))
    have hwq : 0 ≤ wsq (k - p) := wsq_nonneg' (k - p)
    have hrate : 0 < viscousPairRate nu p (k - p) := by
      rw [viscousPairRate]
      have : 0 < wsq p + wsq (k - p) := by linarith
      exact mul_pos hnu this
    have hcellsq : nsq (outerCellVec N u k p) ≤ 9 * wsq p * En ^ 2 * nsq (u (k - p)) := by
      have h1 : nsq (outerCellVec N u k p) ≤ nsq (cross (N p) (u (k - p))) :=
        nsq_leray_le k _ hk
      have h2 : nsq (cross (N p) (u (k - p))) ≤ nsq (N p) * nsq (u (k - p)) :=
        nsq_cross_le _ _
      have h3 : nsq (N p) ≤ 9 * wsq p * En ^ 2 := by
        have h4 := hN p hpm
        have h5 : 0 ≤ nrm (N p) := nrm_nonneg _
        have h6 : nrm (N p) ^ 2 ≤ (3 * wlen p * En) ^ 2 := by nlinarith [h4, h5]
        rw [nrm_sq] at h6
        calc nsq (N p) ≤ (3 * wlen p * En) ^ 2 := h6
          _ = 9 * wsq p * En ^ 2 := by
              rw [show (3 * wlen p * En) ^ 2 = 9 * wlen p ^ 2 * En ^ 2 by ring, wlen_sq]
      have h7 : 0 ≤ nsq (u (k - p)) := nsq_nonneg _
      nlinarith [h1, h2, h3, h7]
    have hdenom : 2 * nu * wsq p ≤ 2 * viscousPairRate nu p (k - p) := by
      rw [viscousPairRate]
      nlinarith [hnu.le, hwq]
    have hnum : 0 ≤ nsq (outerCellVec N u k p) := nsq_nonneg _
    have hle : nsq (outerCellVec N u k p) / (2 * viscousPairRate nu p (k - p))
        ≤ (9 * wsq p * En ^ 2 * nsq (u (k - p))) / (2 * nu * wsq p) := by
      have hcnn : 0 ≤ 9 * wsq p * En ^ 2 * nsq (u (k - p)) := by
        have := nsq_nonneg (u (k - p)); positivity
      exact div_le_div₀ hcnn hcellsq (by positivity) hdenom
    calc nsq (outerCellVec N u k p) / (2 * viscousPairRate nu p (k - p))
        ≤ (9 * wsq p * En ^ 2 * nsq (u (k - p))) / (2 * nu * wsq p) := hle
      _ = 9 * En ^ 2 * nsq (u (k - p)) / (2 * nu) := by
          field_simp
  have hsum : ∑ p ∈ modes, nsq (outerCellVec N u k p) / (2 * viscousPairRate nu p (k - p))
      ≤ ∑ p ∈ modes, 9 * En ^ 2 * nsq (u (k - p)) / (2 * nu) :=
    Finset.sum_le_sum hstep
  have hrefl : ∑ p ∈ modes, nsq (u (k - p)) ≤ energy modes u :=
    sum_nsq_reflect_le (u := u) (p := k) modes hsupp
  have hfac : ∑ p ∈ modes, 9 * En ^ 2 * nsq (u (k - p)) / (2 * nu)
      = (9 * En ^ 2 / (2 * nu)) * ∑ p ∈ modes, nsq (u (k - p)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hc : 0 ≤ 9 * En ^ 2 / (2 * nu) := by positivity
  calc ∑ p ∈ modes, nsq (outerCellVec N u k p) / (2 * viscousPairRate nu p (k - p))
      ≤ ∑ p ∈ modes, 9 * En ^ 2 * nsq (u (k - p)) / (2 * nu) := hsum
    _ = (9 * En ^ 2 / (2 * nu)) * ∑ p ∈ modes, nsq (u (k - p)) := hfac
    _ ≤ (9 * En ^ 2 / (2 * nu)) * energy modes u := mul_le_mul_of_nonneg_left hrefl hc
    _ = 9 * En ^ 2 * energy modes u / (2 * nu) := by ring

end ClayNS.TTStar
