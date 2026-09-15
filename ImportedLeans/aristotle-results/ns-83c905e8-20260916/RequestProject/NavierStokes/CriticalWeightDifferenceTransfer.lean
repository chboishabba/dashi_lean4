/-
# The weighted production is a *weight-difference* transfer

The S2b frontier asks for a bound on the literal weighted production

  `N_N = 2 ∑_k w(k) Re⟨f_k,u_k⟩`,   `f_k = −P_k ∑_{p+q=k} i (u_p·q) u_q`.

Majorising `N_N` term by term destroys the signed cancellation that makes the
quantity critical at all — the corpus records that route as refuted for a
cutoff-uniform payment.  This file does the opposite: it keeps the sign and
exhibits the exact algebraic reason the weighted production is not the
unweighted one.

For a symmetric mode set, the involution `(k,p) ↦ (k−p,−p)` of the truncated
convolution index set sends the pair contribution to minus its conjugate
(`convTerm_conj_add_flip`, already in the project).  Averaging the weighted sum
over that involution gives

```text
2 ∑_k w(k) Re⟨f_k,u_k⟩ = − ∑_{(k,p)} ( w(k) − w(k−p) ) · Re S(k,p)
```

with `S` the literal pair contribution `convTerm`.  Only the **weight
differences across a triad leg** survive: a constant weight gives zero, which is
exactly the classical energy neutrality of the truncated nonlinearity, and for
the dyadic critical weight the driver is the shell difference
`w(k) − w(k−p)`, bounded by the shell laws of `CriticalDyadicWeight.lean`.

This is an identity, not an estimate: no majorisation, no positivity, no
absorption.  It is the cancellation-preserving entry point for S2b.
-/
import RequestProject.NavierStokes.CriticalProductionAbsorption

noncomputable section

open Finset

namespace ClayNS.Waleffe

variable {modes : Finset Wave} {u : Wave → Fin 3 → ℂ}

/-- The real part of a pair contribution is odd under the convolution
involution. -/
theorem re_convTerm_convFlip (hreal : ∀ (k : Wave) (i : Fin 3), u (-k) i = (starRingEnd ℂ) (u k i))
    (htr : ∀ k : Wave, herm (wC k) (u k) = 0) (z : Wave × Wave) :
    (convTerm u (convFlip z)).re = -(convTerm u z).re := by
  have h := convTerm_conj_add_flip u hreal htr z
  have hre : ((starRingEnd ℂ) (convTerm u z) + convTerm u (convFlip z)).re = 0 := by
    rw [h]; rfl
  rw [Complex.add_re, Complex.conj_re] at hre
  linarith

/-- The weighted pairing of the field with its own projected forcing, written on
the truncated convolution index set. -/
theorem sum_weighted_herm_force_eq (w : Wave → ℝ)
    (hsupp : ∀ k : Wave, k ∉ modes → u k = 0)
    (htr : ∀ k : Wave, herm (wC k) (u k) = 0) :
    ∑ k ∈ modes, w k * (herm (modalForcing modes u k) (u k)).re
      = -∑ z ∈ convPairs modes, w z.1 * (convTerm u z).re := by
  classical
  have hforce : ∀ k ∈ modes,
      w k * (herm (modalForcing modes u k) (u k)).re
        = -(w k * (∑ p ∈ modes, convTerm u (k, p)).re) := by
    intro k _
    have hsym : (herm (modalForcing modes u k) (u k)).re
        = (herm (u k) (modalForcing modes u k)).re := by
      have h := herm_conj (modalForcing modes u k) (u k)
      rw [← h, Complex.conj_re]
    have hperp : herm (u k) (wC k) = 0 := herm_wC_right_of_transverse (htr k)
    have hv : modalForcing modes u k
        = fun i => -(advection modes u k i
            - (herm (wC k) (advection modes u k) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ)) := rfl
    have hsplit : herm (u k) (fun i => advection modes u k i
        - (herm (wC k) (advection modes u k) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ))
        = herm (u k) (advection modes u k)
          - (herm (wC k) (advection modes u k) / ((wsq k : ℝ) : ℂ)) * herm (u k) (wC k) := by
      simp only [herm, wC, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hneg : herm (u k) (fun i => -(advection modes u k i
        - (herm (wC k) (advection modes u k) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ)))
        = -herm (u k) (fun i => advection modes u k i
            - (herm (wC k) (advection modes u k) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ)) := by
      simp only [herm]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hfk : herm (u k) (modalForcing modes u k) = -herm (u k) (advection modes u k) := by
      rw [hv, hneg, hsplit, hperp, mul_zero, sub_zero]
    rw [hsym, hfk, herm_advection_eq_sum_of htr]
    simp
  have hprod : ∑ k ∈ modes, w k * (∑ p ∈ modes, convTerm u (k, p)).re
      = ∑ z ∈ modes ×ˢ modes, w z.1 * (convTerm u z).re := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
  have hdrop : ∑ z ∈ modes ×ˢ modes, w z.1 * (convTerm u z).re
      = ∑ z ∈ convPairs modes, w z.1 * (convTerm u z).re := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro z hz
      obtain ⟨h1, h2, -⟩ := mem_convPairs hz
      exact Finset.mem_product.2 ⟨h1, h2⟩
    · intro z hz hnot
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hz
      have h3 : z.1 - z.2 ∉ modes := fun h => hnot (mem_convPairs_iff.2 ⟨h1, h2, h⟩)
      have hz0 : u (z.1 - z.2) = 0 := hsupp _ h3
      simp [convTerm, hz0, herm]
  rw [Finset.sum_congr rfl hforce, Finset.sum_neg_distrib, hprod, hdrop]

/-- **The weighted production is a weight-difference transfer.**  For a symmetric
mode set carrying a supported, transverse, real field, the weighted production
depends on the weight only through the differences `w(k) − w(k−p)` across the
triad legs. -/
theorem weighted_production_eq_weightDifference (w : Wave → ℝ)
    (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hsupp : ∀ k : Wave, k ∉ modes → u k = 0)
    (htr : ∀ k : Wave, herm (wC k) (u k) = 0)
    (hreal : ∀ (k : Wave) (i : Fin 3), u (-k) i = (starRingEnd ℂ) (u k i)) :
    2 * ∑ k ∈ modes, w k * (herm (modalForcing modes u k) (u k)).re
      = -∑ z ∈ convPairs modes, (w z.1 - w (z.1 - z.2)) * (convTerm u z).re := by
  classical
  have hflip : (∑ z ∈ convPairs modes, w z.1 * (convTerm u z).re)
      = -∑ z ∈ convPairs modes, w (z.1 - z.2) * (convTerm u z).re := by
    have hbij : ∑ z ∈ convPairs modes, w (convFlip z).1 * (convTerm u (convFlip z)).re
        = ∑ z ∈ convPairs modes, w z.1 * (convTerm u z).re := by
      refine Finset.sum_nbij' convFlip convFlip ?_ ?_ ?_ ?_ ?_
      · exact fun a ha => convFlip_mem hsym ha
      · exact fun a ha => convFlip_mem hsym ha
      · exact fun a _ => convFlip_involutive a
      · exact fun a _ => convFlip_involutive a
      · exact fun a _ => rfl
    rw [← hbij, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [re_convTerm_convFlip hreal htr z]
    show w (z.1 - z.2) * -(convTerm u z).re = -(w (z.1 - z.2) * (convTerm u z).re)
    ring
  have hsum := sum_weighted_herm_force_eq (u := u) w hsupp htr
  have hsplit : ∑ z ∈ convPairs modes, (w z.1 - w (z.1 - z.2)) * (convTerm u z).re
      = (∑ z ∈ convPairs modes, w z.1 * (convTerm u z).re)
        - ∑ z ∈ convPairs modes, w (z.1 - z.2) * (convTerm u z).re := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hsum, hsplit]
  linarith [hflip]

/-- **Constant weights see nothing.**  Specialising the identity to a constant
weight recovers the energy neutrality of the truncated nonlinearity. -/
theorem weighted_production_const_eq_zero (c : ℝ)
    (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hsupp : ∀ k : Wave, k ∉ modes → u k = 0)
    (htr : ∀ k : Wave, herm (wC k) (u k) = 0)
    (hreal : ∀ (k : Wave) (i : Fin 3), u (-k) i = (starRingEnd ℂ) (u k i)) :
    ∑ k ∈ modes, c * (herm (modalForcing modes u k) (u k)).re = 0 := by
  have h := weighted_production_eq_weightDifference (u := u) (fun _ => c) hsym hsupp htr hreal
  simp only [sub_self, zero_mul, Finset.sum_const_zero, neg_zero] at h
  linarith

/-- The literal dyadic critical production, in cancellation-preserving form. -/
theorem critProductionOf_eq_weightDifference
    (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hsupp : ∀ k : Wave, k ∉ modes → u k = 0)
    (htr : ∀ k : Wave, herm (wC k) (u k) = 0)
    (hreal : ∀ (k : Wave) (i : Fin 3), u (-k) i = (starRingEnd ℂ) (u k i)) :
    critProductionOf modes u
      = -∑ z ∈ convPairs modes,
          (critWeight z.1 - critWeight (z.1 - z.2)) * (convTerm u z).re :=
  weighted_production_eq_weightDifference (u := u) critWeight hsym hsupp htr hreal

/-- **The critical production lives on the shell boundary.**  In the
weight-difference form the summand vanishes on every pair whose output and
high-leg lie in the same dyadic shell, so the whole of the literal critical
production is carried by the pairs that cross a shell boundary. -/
theorem critProductionOf_eq_shellJump_sum
    (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hsupp : ∀ k : Wave, k ∉ modes → u k = 0)
    (htr : ∀ k : Wave, herm (wC k) (u k) = 0)
    (hreal : ∀ (k : Wave) (i : Fin 3), u (-k) i = (starRingEnd ℂ) (u k i)) :
    critProductionOf modes u
      = -∑ z ∈ (convPairs modes).filter (fun z => critShell z.1 ≠ critShell (z.1 - z.2)),
          (critWeight z.1 - critWeight (z.1 - z.2)) * (convTerm u z).re := by
  classical
  rw [critProductionOf_eq_weightDifference hsym hsupp htr hreal]
  congr 1
  refine (Finset.sum_filter_of_ne ?_).symm
  intro z _ hne hshell
  apply hne
  have : critWeight z.1 = critWeight (z.1 - z.2) := by
    unfold critWeight
    rw [hshell]
  rw [this, sub_self, zero_mul]


end ClayNS.Waleffe
