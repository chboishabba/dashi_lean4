/-
# The self-forcing slot of a helical triad is a signed square

The open Round 105 wall asks for a cutoff-uniform bound on the *positive part*
of the network forcing `F_τ` of the Waleffe amplitude.  This file computes the
part of `F_τ` produced by the triad **by itself** — the contribution to `f_k`
of the two convolution terms `(p,q)` and `(q,p)` with `p + q = k` — and shows
that on helical (Beltrami) modes it is not merely bounded but *exactly* a
signed square:

  `Re⟪f_k^{(p,q)} , u_p × u_q⟫ = (λ_q − λ_p) ‖P_k(u_p × u_q)‖²`.

The derivation is the literal rotational normal form, proved here and not
assumed:

* the vector triple product identity on `ℂ³` (`cross_cross`);
* the Fourier rotational form of the advective pair,
  `i(u_p·q)u_q + i(u_q·p)u_p = ω_p×u_q + ω_q×u_p + i k (u_p·u_q)`
  with `ω_j = i j × u_j` (`pair_rotational_form`), an *identity*: no
  transversality is needed for it;
* the Leray projection kills the longitudinal residue `i k (u_p·u_q)`
  (`leray_longitudinal`);
* the Beltrami relation `i j × u_j = λ_j u_j` collapses the two rotational
  terms into the single Waleffe factor `(λ_p − λ_q) u_p × u_q`;
* `herm_leray_self` turns the resulting pairing into `‖P_k(u_p×u_q)‖²`.

Consequences for the wall.  The self slot carries a definite sign, fixed by the
helicity gap `λ_q − λ_p`; it is favourable exactly on the cells where the
Round 105 phase-damping payment is applied, and where it is adverse it is an
*explicitly computable* square rather than an unknown.  What is therefore left
inside the open budget is exclusively the **external** network forcing: the
contribution to `f_k, f_p, f_q` of convolution pairs that do not belong to the
triad.  This is the sharpest available localisation of the Round 105 wall.
-/
import RequestProject.NavierStokes.WaleffeForcingMajorant

noncomputable section

namespace ClayNS.Waleffe

/-- The bilinear (unconjugated) contraction of two complex 3-vectors. -/
def dotb (u v : Fin 3 → ℂ) : ℂ := ∑ j, u j * v j

theorem dotb_comm (u v : Fin 3 → ℂ) : dotb u v = dotb v u := by
  simp [dotb, mul_comm]

theorem dotb_smul_left (c : ℂ) (u v : Fin 3 → ℂ) :
    dotb (fun i => c * u i) v = c * dotb u v := by
  simp [dotb, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The vector triple product identity `(a×b)×c = b (a·c) − a (b·c)` on `ℂ³`. -/
theorem cross_cross (a b c : Fin 3 → ℂ) :
    cross (cross a b) c = fun i => b i * dotb a c - a i * dotb b c := by
  funext i
  fin_cases i <;> simp [cross, crossProduct, dotb, Fin.sum_univ_three] <;> ring

theorem cross_smul_left (c : ℂ) (a b : Fin 3 → ℂ) :
    cross (fun i => c * a i) b = fun i => c * cross a b i := by
  funext i
  fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem cross_antisymm (a b : Fin 3 → ℂ) : cross a b = fun i => -(cross b a i) := by
  funext i
  fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem herm_wC_wC (k : Wave) : herm (wC k) (wC k) = ((wsq k : ℝ) : ℂ) := by
  simp only [herm, wC, Fin.sum_univ_three, map_intCast]
  rw [wsq_cast]
  ring

/-- The Leray projection annihilates longitudinal vectors. -/
theorem leray_longitudinal (k : Wave) (c : ℂ) (hk : wsq k ≠ 0) :
    leray k (fun i => c * wC k i) = fun _ => 0 := by
  funext i
  have hk' : ((wsq k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [leray, herm_smul_right]
  rw [show (herm (wC k) fun i => wC k i) = ((wsq k : ℝ) : ℂ) from herm_wC_wC k]
  field_simp
  simp [wC]

theorem leray_add (k : Wave) (a b : Fin 3 → ℂ) :
    leray k (fun i => a i + b i) = fun i => leray k a i + leray k b i := by
  funext i
  simp only [leray, herm_add_right]
  ring

theorem wC_add {p q k : Wave} (h : p + q = k) : ∀ i, wC p i + wC q i = wC k i := by
  intro i
  simp only [wC, ← h]
  simp [Pi.add_apply]

/-! ## The advective pair of one triad -/

/-- The two convolution terms of the advective nonlinearity at `k = p+q` that
come from the triad itself. -/
def pairAdvection (p q : Wave) (up uq : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => (Complex.I * dotb up (wC q)) * uq i + (Complex.I * dotb uq (wC p)) * up i

/-- **Rotational normal form of the advective pair.**  With the Beltrami
relations `p × u_p = −i λ_p u_p` and `q × u_q = −i λ_q u_q` (real `λ`), the two
convolution terms of the triad collapse to the Waleffe factor times the cross
product, plus a purely longitudinal residue. -/
theorem pair_rotational_form {p q k : Wave} (hpq : p + q = k)
    (up uq : Fin 3 → ℂ) (lp lq : ℝ)
    (hp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i)
    (hq : cross (wC q) uq = fun i => (-Complex.I) * (lq : ℂ) * uq i) :
    pairAdvection p q up uq
      = fun i => ((lp : ℂ) - (lq : ℂ)) * cross up uq i
          + (Complex.I * dotb up uq) * wC k i := by
  -- the two vorticity vectors are real multiples of the modes themselves
  have hwp : cross (fun i => Complex.I * wC p i) up = fun i => (lp : ℂ) * up i := by
    rw [cross_smul_left, hp]
    funext i
    simp only
    have : Complex.I * ((-Complex.I) * (lp : ℂ) * up i) = (lp : ℂ) * up i := by
      rw [show Complex.I * ((-Complex.I) * (lp : ℂ) * up i)
          = (Complex.I * (-Complex.I)) * ((lp : ℂ) * up i) by ring]
      simp [Complex.I_mul_I]
    exact this
  have hwq : cross (fun i => Complex.I * wC q i) uq = fun i => (lq : ℂ) * uq i := by
    rw [cross_smul_left, hq]
    funext i
    simp only
    have : Complex.I * ((-Complex.I) * (lq : ℂ) * uq i) = (lq : ℂ) * uq i := by
      rw [show Complex.I * ((-Complex.I) * (lq : ℂ) * uq i)
          = (Complex.I * (-Complex.I)) * ((lq : ℂ) * uq i) by ring]
      simp [Complex.I_mul_I]
    exact this
  -- triple products
  have e1 : cross (cross (fun i => Complex.I * wC p i) up) uq
      = fun i => up i * (Complex.I * dotb (wC p) uq) - (Complex.I * wC p i) * dotb up uq := by
    rw [cross_cross]
    funext i
    rw [dotb_smul_left]
  have e2 : cross (cross (fun i => Complex.I * wC q i) uq) up
      = fun i => uq i * (Complex.I * dotb (wC q) up) - (Complex.I * wC q i) * dotb uq up := by
    rw [cross_cross]
    funext i
    rw [dotb_smul_left]
  rw [hwp] at e1
  rw [hwq] at e2
  rw [cross_smul_left] at e1 e2
  funext i
  have h1 := congrFun e1 i
  have h2 := congrFun e2 i
  have hanti : cross uq up i = -(cross up uq i) := by
    have := congrFun (cross_antisymm uq up) i
    simpa using this
  have hdc : dotb uq up = dotb up uq := dotb_comm uq up
  have hwCk := wC_add hpq i
  simp only [pairAdvection]
  rw [dotb_comm up (wC q), dotb_comm uq (wC p)]
  rw [hanti] at h2
  rw [hdc] at h2
  -- combine
  have hsum : (lp : ℂ) * cross up uq i + (lq : ℂ) * -(cross up uq i)
      = (up i * (Complex.I * dotb (wC p) uq) - Complex.I * wC p i * dotb up uq)
        + (uq i * (Complex.I * dotb (wC q) up) - Complex.I * wC q i * dotb up uq) := by
    rw [h1, h2]
  rw [← hwCk]
  linear_combination -hsum

/-- **The projected self-forcing of a helical triad is the Waleffe factor times
the projected cross product.**  The longitudinal residue of the rotational
normal form is annihilated by the Leray projection. -/
theorem leray_pairAdvection {p q k : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (up uq : Fin 3 → ℂ) (lp lq : ℝ)
    (hp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i)
    (hq : cross (wC q) uq = fun i => (-Complex.I) * (lq : ℂ) * uq i) :
    leray k (pairAdvection p q up uq)
      = fun i => ((lp : ℂ) - (lq : ℂ)) * leray k (cross up uq) i := by
  rw [pair_rotational_form hpq up uq lp lq hp hq,
    leray_add k (fun i => ((lp : ℂ) - (lq : ℂ)) * cross up uq i)
      (fun i => (Complex.I * dotb up uq) * wC k i),
    leray_smul, leray_longitudinal k (Complex.I * dotb up uq) hk]
  funext i
  simp

/-- **The self slot of the network forcing is a signed square.**  For a helical
resonant triad `k = p+q`, the contribution of the triad's own convolution pair
to the forcing of the mode `k`, paired against `u_p × u_q`, equals
`(λ_q − λ_p) ‖P_k(u_p × u_q)‖²`.

This is the exact Waleffe self-forcing law: its sign is fixed by the helicity
gap alone, and its size is an explicitly computable square.  Consequently the
only part of the Round 105 network-forcing budget that is not already computed
is the *external* forcing, i.e. the convolution pairs outside the triad. -/
theorem pair_self_forcing_signed_square {p q k : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (up uq : Fin 3 → ℂ) (lp lq : ℝ)
    (hp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i)
    (hq : cross (wC q) uq = fun i => (-Complex.I) * (lq : ℂ) * uq i) :
    (herm (fun i => -(leray k (pairAdvection p q up uq) i)) (cross up uq)).re
      = (lq - lp) * nsq (leray k (cross up uq)) := by
  have hL := leray_pairAdvection hpq hk up uq lp lq hp hq
  have hvec : (fun i => -(leray k (pairAdvection p q up uq) i))
      = fun i => (((lq : ℝ) - (lp : ℝ) : ℝ) : ℂ) * leray k (cross up uq) i := by
    funext i
    rw [hL]
    push_cast
    ring
  rw [hvec, herm_smul_left, herm_leray_self k (cross up uq) hk]
  simp

/-- The favourable/adverse dichotomy: the self slot is nonnegative exactly when
the helicity gap `λ_q − λ_p` is nonnegative. -/
theorem pair_self_forcing_nonneg {p q k : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (up uq : Fin 3 → ℂ) (lp lq : ℝ) (hgap : lp ≤ lq)
    (hp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i)
    (hq : cross (wC q) uq = fun i => (-Complex.I) * (lq : ℂ) * uq i) :
    0 ≤ (herm (fun i => -(leray k (pairAdvection p q up uq) i)) (cross up uq)).re := by
  rw [pair_self_forcing_signed_square hpq hk up uq lp lq hp hq]
  exact mul_nonneg (by linarith) (nsq_nonneg _)

end ClayNS.Waleffe
