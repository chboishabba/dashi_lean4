/-
# G21 — the exact pair kernel of the two-channel exterior observable

`ExteriorCore.lean` proved the algebraic annihilation step.  This module carries
out the second half of the design at literal strength: expand the pole-quotiented
exterior observable in the arithmetic modes **exactly**, before any inequality,
and read off the surviving pair kernel.

The setting is an arbitrary antisymmetric bilinear form `B` on the row space
(`AntisymBilin`), which both `augDet3 · · m` and `augDet4 · · p q` satisfy.  With

```
E₁(x) = ∑_r a_r e^{i x λ_r},        E₂(x) = ∂_x E₁(x) = ∑_r i λ_r a_r e^{i x λ_r},
```

`AntisymBilin.channelPair_eq_pairKernel` gives the identity

```
B(E₁-samples, E₂-samples) = i ∑_{r < t} K(r,t),
K(r,t) = a_r a_t (λ_t − λ_r) B(v_r, v_t).
```

Three exact structural facts come with it:

* `pairKernel_diag` — `K(n,n) = 0`: the diagonal literally never enters, both
  because `λ_t − λ_r` vanishes there and because `B(v,v) = 0`;
* `pairKernel_symm` — `K` is symmetric, since both factors change sign under the
  swap involution;
* `sum_pair_eq_two_mul_sum_lt` — the exact finite reindexing
  `∑_{r,t ∈ s} K = 2 ∑_{r<t} K`, performed as an identity on the duplicate-free
  product carrier, with no triangle inequality anywhere.

Finally, the two admission certificates are proved in the sharp form: a kernel
that is symmetric and vanishes on the diagonal is separable (`L(r) + R(t)`) or of
rank one (`A(r)B(t)`) **only if it is identically zero**
(`separable_of_symm_diagZero_eq_zero`, `rankOne_of_symm_diagZero_eq_zero`).  So a
single nonvanishing value of `K` certifies genuine nonseparability, and the
four-point rectangle defect is then explicitly `−2K(r,t)`.
-/
import RiemannAnalytic.ExteriorCore

open Finset

namespace RiemannAnalytic

noncomputable section

/-! ## Antisymmetric bilinear forms on the row space -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An antisymmetric `ℂ`-bilinear form: the abstract shape shared by the
three-sample and four-sample augmented determinants in their two channel rows. -/
structure AntisymBilin (B : V → V → ℂ) : Prop where
  add_left : ∀ u v w, B (u + v) w = B u w + B v w
  smul_left : ∀ (c : ℂ) (u w : V), B (c • u) w = c * B u w
  antisymm : ∀ u w, B u w = -B w u

namespace AntisymBilin

variable {B : V → V → ℂ} (hB : AntisymBilin B)
include hB

theorem add_right (u w v : V) : B u (w + v) = B u w + B u v := by
  rw [hB.antisymm u (w + v), hB.add_left, hB.antisymm w u, hB.antisymm v u]; ring

theorem smul_right (c : ℂ) (u w : V) : B u (c • w) = c * B u w := by
  rw [hB.antisymm u (c • w), hB.smul_left, hB.antisymm w u]; ring

theorem self (u : V) : B u u = 0 := by
  have h := hB.antisymm u u
  linear_combination h / 2

theorem zero_left (w : V) : B (0 : V) w = 0 := by
  have h := hB.smul_left 0 (0 : V) w
  simpa using h

theorem zero_right (u : V) : B u (0 : V) = 0 := by
  have h := hB.smul_right 0 u (0 : V)
  simpa using h

theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    B (∑ r ∈ s, f r) w = ∑ r ∈ s, B (f r) w := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hB.zero_left w
  | @insert r s hr ih =>
      rw [Finset.sum_insert hr, hB.add_left, ih, Finset.sum_insert hr]

theorem sum_right {ι : Type*} (s : Finset ι) (u : V) (g : ι → V) :
    B u (∑ t ∈ s, g t) = ∑ t ∈ s, B u (g t) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hB.zero_right u
  | @insert t s ht ih =>
      rw [Finset.sum_insert ht, hB.add_right, ih, Finset.sum_insert ht]

/-- Exact bilinear expansion of the observable on two mode expansions. -/
theorem sum_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ) (v : ι → V) :
    B (∑ r ∈ s, a r • v r) (∑ t ∈ s, b t • v t)
      = ∑ r ∈ s, ∑ t ∈ s, a r * b t * B (v r) (v t) := by
  classical
  rw [hB.sum_left]
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [hB.sum_right]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [hB.smul_left, hB.smul_right]
  ring

end AntisymBilin

/-! ## The surviving pair kernel -/

variable {ι : Type*}

/-- The pair kernel `K(r,t) = a_r a_t (λ_t − λ_r) D(r,t)` produced by the
contrastive-derivative channel pair. -/
def pairKernel (a : ι → ℂ) (lam : ι → ℝ) (D : ι → ι → ℂ) (r t : ι) : ℂ :=
  a r * a t * ((lam t : ℂ) - (lam r : ℂ)) * D r t

/-- The diagonal literally never enters: `K(n,n) = 0`. -/
theorem pairKernel_diag (a : ι → ℂ) (lam : ι → ℝ) (D : ι → ι → ℂ) (n : ι) :
    pairKernel a lam D n n = 0 := by
  simp [pairKernel]

/-- The pair kernel is symmetric: both the frequency difference and the
determinant change sign under the swap involution. -/
theorem pairKernel_symm {a : ι → ℂ} {lam : ι → ℝ} {D : ι → ι → ℂ}
    (hD : ∀ r t, D t r = -D r t) (r t : ι) :
    pairKernel a lam D t r = pairKernel a lam D r t := by
  simp only [pairKernel, hD r t]; ring

/-! ## Exact finite reindexing (no inequality is used) -/

section Reindex

variable [LinearOrder ι] [DecidableEq ι]

/-- Exact three-fibre decomposition of the duplicate-free product carrier
`s ×ˢ s` into `r < t`, `t < r` and the diagonal. -/
theorem sum_product_split (s : Finset ι) (K : ι → ι → ℂ) :
    ∑ p ∈ s ×ˢ s, K p.1 p.2
      = (∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), K p.1 p.2)
        + (∑ p ∈ (s ×ˢ s).filter (fun p => p.2 < p.1), K p.1 p.2)
        + ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 = p.2), K p.1 p.2 := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg (ne_of_lt h)]; ring
  · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_pos h]; ring
  · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (ne_of_gt h)]; ring

omit [DecidableEq ι] in
/-- The swap involution identifies the two off-diagonal fibres exactly, for a
symmetric kernel. -/
theorem sum_gt_eq_sum_lt (s : Finset ι) {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) :
    ∑ p ∈ (s ×ˢ s).filter (fun p => p.2 < p.1), K p.1 p.2
      = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), K p.1 p.2 := by
  classical
  refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · intro p _; simp
  · intro p _; simp
  · intro p _; exact hsymm p.2 p.1

/-- **Exact pair reindexing.**  For a symmetric kernel vanishing on the diagonal,
the full double sum is exactly twice the strictly-ordered sum.  This is an
identity on the finite carrier; no estimate has been made. -/
theorem sum_pair_eq_two_mul_sum_lt (s : Finset ι) {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) (hdiag : ∀ n, K n n = 0) :
    ∑ r ∈ s, ∑ t ∈ s, K r t
      = 2 * ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), K p.1 p.2 := by
  classical
  have hprod : ∑ r ∈ s, ∑ t ∈ s, K r t = ∑ p ∈ s ×ˢ s, K p.1 p.2 := by
    rw [Finset.sum_product]
  have hdiagsum : ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 = p.2), K p.1 p.2 = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [hp.2]; exact hdiag p.2
  rw [hprod, sum_product_split, sum_gt_eq_sum_lt s hsymm, hdiagsum]
  ring

end Reindex

/-! ## The channel pair identity -/

section ChannelPair

variable [LinearOrder ι] [DecidableEq ι]

/-- **The exact two-channel pair-kernel identity.**  For a contrastive-derivative
channel pair — channel one the mode sum with amplitudes `a_r`, channel two the
`x`-derivative, i.e. amplitudes `i λ_r a_r` — the pole-quotiented exterior
observable equals `i ∑_{r<t} K(r,t)` with
`K(r,t) = a_r a_t (λ_t − λ_r) B(v_r, v_t)`. -/
theorem AntisymBilin.channelPair_eq_pairKernel {B : V → V → ℂ} (hB : AntisymBilin B)
    (s : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (v : ι → V) :
    B (∑ r ∈ s, a r • v r) (∑ t ∈ s, (Complex.I * (lam t : ℂ) * a t) • v t)
      = Complex.I * ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2),
          pairKernel a lam (fun r t => B (v r) (v t)) p.1 p.2 := by
  classical
  set D : ι → ι → ℂ := fun r t => B (v r) (v t) with hDdef
  have hDanti : ∀ r t, D t r = -D r t := by
    intro r t; simp only [hDdef]; exact hB.antisymm (v t) (v r)
  set X : ℂ := ∑ r ∈ s, ∑ t ∈ s, a r * (Complex.I * (lam t : ℂ) * a t) * D r t with hX
  set Y : ℂ := ∑ r ∈ s, ∑ t ∈ s, a r * (Complex.I * (lam r : ℂ) * a t) * D r t with hY
  have hX' : B (∑ r ∈ s, a r • v r) (∑ t ∈ s, (Complex.I * (lam t : ℂ) * a t) • v t) = X := by
    rw [hB.sum_sum s a (fun t => Complex.I * (lam t : ℂ) * a t) v]
  -- swapping the summation names and using antisymmetry of `D`
  have hswap : Y = -X := by
    have h1 : Y = ∑ r ∈ s, ∑ t ∈ s, a t * (Complex.I * (lam t : ℂ) * a r) * D t r := by
      rw [hY]; exact Finset.sum_comm
    rw [h1, hX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [hDanti r t]
    ring
  have hXY : X - Y = Complex.I * ∑ r ∈ s, ∑ t ∈ s, pairKernel a lam D r t := by
    rw [hX, hY, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro t _
    simp only [pairKernel]
    ring
  have hsymmK : ∀ r t, pairKernel a lam D t r = pairKernel a lam D r t :=
    fun r t => pairKernel_symm hDanti r t
  have hdiagK : ∀ n, pairKernel a lam D n n = 0 := pairKernel_diag a lam D
  have hre := sum_pair_eq_two_mul_sum_lt (K := pairKernel a lam D) s hsymmK hdiagK
  rw [hX']
  rw [hre] at hXY
  rw [hswap] at hXY
  linear_combination hXY / 2

end ChannelPair

/-! ## Nonseparability certificates -/

/-- A symmetric kernel vanishing on the diagonal is endpoint-separable **only if
it is identically zero**. -/
theorem separable_of_symm_diagZero_eq_zero {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) (hdiag : ∀ n, K n n = 0)
    {L R : ι → ℂ} (hsep : ∀ r t, K r t = L r + R t) (r t : ι) :
    K r t = 0 := by
  have hR : ∀ n, R n = -L n := by
    intro n
    have := hdiag n
    rw [hsep n n] at this
    linear_combination this
  have h1 : K r t = L r - L t := by rw [hsep r t, hR t]; ring
  have h2 : K t r = L t - L r := by rw [hsep t r, hR r]; ring
  have h3 := hsymm r t
  rw [h1, h2] at h3
  rw [h1]
  linear_combination (-1 / 2 : ℂ) * h3

/-- **`NonseparablePrimePairKernel`.**  One nonvanishing value of a symmetric,
diagonal-free kernel certifies that it is not of the endpoint-separable form
`L(r) + R(t)`. -/
theorem not_separable_of_ne_zero {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) (hdiag : ∀ n, K n n = 0)
    {r₀ t₀ : ι} (hne : K r₀ t₀ ≠ 0) :
    ¬ ∃ L R : ι → ℂ, ∀ r t, K r t = L r + R t := by
  rintro ⟨L, R, hsep⟩
  exact hne (separable_of_symm_diagZero_eq_zero hsymm hdiag hsep r₀ t₀)

/-- A symmetric kernel vanishing on the diagonal has rank one only if it is
identically zero. -/
theorem rankOne_of_symm_diagZero_eq_zero {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) (hdiag : ∀ n, K n n = 0)
    {A Bc : ι → ℂ} (hrk : ∀ r t, K r t = A r * Bc t) (r t : ι) :
    K r t = 0 := by
  by_contra hne
  have hA : A r ≠ 0 := by
    intro h; exact hne (by rw [hrk r t, h]; ring)
  have hB : Bc t ≠ 0 := by
    intro h; exact hne (by rw [hrk r t, h]; ring)
  have hBr : Bc r = 0 := by
    have := hdiag r; rw [hrk r r] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hA
    · exact h
  have hAt : A t = 0 := by
    have := hdiag t; rw [hrk t t] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hB
  have : K t r = 0 := by rw [hrk t r, hAt]; ring
  rw [hsymm r t] at this
  exact hne this

/-- **`PrimePairRankGreaterThanOne`.**  One nonvanishing value of a symmetric,
diagonal-free kernel also excludes the rank-one form `A(r)B(t)`. -/
theorem not_rankOne_of_ne_zero {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) (hdiag : ∀ n, K n n = 0)
    {r₀ t₀ : ι} (hne : K r₀ t₀ ≠ 0) :
    ¬ ∃ A Bc : ι → ℂ, ∀ r t, K r t = A r * Bc t := by
  rintro ⟨A, Bc, hrk⟩
  exact hne (rankOne_of_symm_diagZero_eq_zero hsymm hdiag hrk r₀ t₀)

/-- The four-point rectangle defect of a symmetric diagonal-free kernel on the
rectangle `{r,t} × {r,t}` is exactly `−2K(r,t)`; any endpoint-separable kernel
has vanishing rectangle defect, so this is the explicit separability witness. -/
theorem rectangleDefect_eq {K : ι → ι → ℂ}
    (hsymm : ∀ r t, K t r = K r t) (hdiag : ∀ n, K n n = 0) (r t : ι) :
    K r r + K t t - K r t - K t r = -2 * K r t := by
  rw [hdiag r, hdiag t, hsymm r t]; ring

/-! ## The two augmented determinants are antisymmetric bilinear forms -/

theorem antisymBilin_augDet3 (m : Fin 3 → ℂ) :
    AntisymBilin (fun u w : Fin 3 → ℂ => augDet3 u w m) where
  add_left := fun u v w => augDet3_add_left u v w m
  smul_left := fun c u w => augDet3_smul_left c u w m
  antisymm := fun u w => augDet3_antisymm u w m

theorem antisymBilin_augDet4 (p q : Fin 4 → ℂ) :
    AntisymBilin (fun u w : Fin 4 → ℂ => augDet4 u w p q) where
  add_left := fun u v w => augDet4_add_left u v w p q
  smul_left := fun c u w => augDet4_smul_left c u w p q
  antisymm := fun u w => augDet4_antisymm u w p q

/-! ## The literal mode vectors and the contrastive-derivative channel -/

/-- The sampled arithmetic mode `v_λ = (e^{i x_j λ})_j`. -/
def modeVector {n : ℕ} (x : Fin n → ℝ) (l : ℝ) : Fin n → ℂ :=
  fun j => Complex.exp (Complex.I * ((x j : ℂ) * (l : ℂ)))

/-- Channel two really is the `x`-derivative of channel one: the amplitudes
`i λ_r a_r` used below are exactly the derivative amplitudes. -/
theorem hasDerivAt_modeSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => ∑ r ∈ s, a r * Complex.exp (Complex.I * ((z : ℂ) * (lam r : ℂ))))
      (∑ r ∈ s, (Complex.I * (lam r : ℂ) * a r)
        * Complex.exp (Complex.I * ((y : ℂ) * (lam r : ℂ)))) y := by
  classical
  refine HasDerivAt.fun_sum ?_
  intro r _
  have h0 : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun z : ℝ => Complex.I * ((z : ℂ) * (lam r : ℂ)))
      (Complex.I * (lam r : ℂ)) y := by
    have := ((h0.mul_const ((lam r : ℂ))).const_mul (Complex.I))
    simpa using this
  have h2 : HasDerivAt (fun z : ℝ => Complex.exp (Complex.I * ((z : ℂ) * (lam r : ℂ))))
      (Complex.I * (lam r : ℂ) * Complex.exp (Complex.I * ((y : ℂ) * (lam r : ℂ)))) y := by
    simpa [mul_comm] using h1.cexp
  have := h2.const_mul (a r)
  convert this using 1
  ring

/-- **The literal three-sample pair-kernel identity** for the mode expansion and
its `x`-derivative channel. -/
theorem augDet3_channelPair_eq_pairKernel {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ) :
    augDet3 (∑ r ∈ s, a r • modeVector x (lam r))
        (∑ t ∈ s, (Complex.I * (lam t : ℂ) * a t) • modeVector x (lam t)) m
      = Complex.I * ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2),
          pairKernel a lam
            (fun r t => augDet3 (modeVector x (lam r)) (modeVector x (lam t)) m) p.1 p.2 :=
  (antisymBilin_augDet3 m).channelPair_eq_pairKernel s a lam (fun r => modeVector x (lam r))

/-- **The literal four-sample pair-kernel identity** (the version required by the
contrastive-derivative channel pair, whose two pole responses `m`, `m′` span the
two nuisance rows). -/
theorem augDet4_channelPair_eq_pairKernel {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (x : Fin 4 → ℝ) (p q : Fin 4 → ℂ) :
    augDet4 (∑ r ∈ s, a r • modeVector x (lam r))
        (∑ t ∈ s, (Complex.I * (lam t : ℂ) * a t) • modeVector x (lam t)) p q
      = Complex.I * ∑ z ∈ (s ×ˢ s).filter (fun z => z.1 < z.2),
          pairKernel a lam
            (fun r t => augDet4 (modeVector x (lam r)) (modeVector x (lam t)) p q) z.1 z.2 :=
  (antisymBilin_augDet4 p q).channelPair_eq_pairKernel s a lam (fun r => modeVector x (lam r))

end

end RiemannAnalytic
