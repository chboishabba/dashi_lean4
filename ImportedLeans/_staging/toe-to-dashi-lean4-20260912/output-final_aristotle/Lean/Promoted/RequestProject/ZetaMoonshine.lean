/-
# If the zeta function were moonshine

Monstrous moonshine is the statement that the modular function

```
J(τ) = j(τ) - 744 = ∑_{n} c(n) qⁿ
```

is the graded dimension of a graded module `V = ⊕ₙ Vₙ` for the Monster `M`, and that for
every `g ∈ M` the *McKay–Thompson series* `T_g(τ) = ∑ₙ tr(g | Vₙ) qⁿ` is again a distinguished
modular function.  The identity element gives back the moonshine function itself,
`T_1 = J`, because `tr(1 | Vₙ) = dim Vₙ`.

This file plays the same game with the Riemann zeta function in place of `j`, i.e. with
Dirichlet series `∑ₙ aₙ n^{-s}` in place of `q`-expansions `∑ₙ aₙ qⁿ`.  Since the coefficients
of `ζ(s) = ∑ₙ n^{-s}` are all `1`, a "moonshine module" for ζ is a graded module with
`dim Vₙ = 1` for every `n ≥ 1`, and a group acting on it must act on each `Vₙ` by a scalar.

The natural such group is the **cyclic group `ZMod N`**, acting on the one-dimensional space
`Vₙ` through the standard additive character `ψ`, by the scalar `ψ(j · n) = e^{2πi jn/N}`:

* `ZetaMoonshine.gradedTrace j n = tr(j | Vₙ) = ψ(j n)`, so `Vₙ` is the irreducible
  representation `ρ_{n mod N}` of `ZMod N` (`gradedTrace_eq_irrep`) and `dim Vₙ = 1`
  (`gradedTrace_zero_left`);
* `ZetaMoonshine.mtSeries j s = ∑ₙ tr(j | Vₙ) n^{-s}` is the McKay–Thompson series of `j`, and
  **`mtSeries_zero_eq_riemannZeta`: `T_0(s) = ζ(s)`** — the zeta function is the moonshine
  series of this module, exactly as `J = T_1` for the Monster;
* the multiplicity of the irreducible `ρ_a` in `Vₙ`, computed by the usual character-theoretic
  averaging, is `1` if `n ≡ a (mod N)` and `0` otherwise (`mult_eq_ite`), in particular a
  non-negative integer (`mult_eq_natCast`, moonshine positivity), and these multiplicities add
  up to `dim Vₙ = 1` (`sum_mult`);
* summing the isotypic pieces decomposes ζ: `ζ(s) = ∑_{a} isotypic a s` with
  `isotypic a s = ∑_{n ≡ a (N)} n^{-s}` (`riemannZeta_eq_sum_isotypic`), and every
  McKay–Thompson series is the same combination twisted by the character values
  (`mtSeries_eq_sum_isotypic`);
* twisting the isotypic pieces by a Dirichlet character mod `N` produces the Dirichlet
  `L`-functions (`sum_dirichlet_smul_isotypic`), and conversely the isotypic pieces are
  recovered from the `L`-functions by orthogonality (`isotypic_eq_sum_LSeries`).  So in this
  analogy the Dirichlet `L`-functions play the role that the `T_g` play for the Monster: they
  are the twists of ζ by the characters of the moonshine group.

Finally `N = 24` (the exponent in `Δ = η²⁴`, whose coefficients are the τ of this project) is
singled out, and the fiber of the prime `2` — the prime carrying the 46 exponents of `|M|` —
is located inside the isotypic decomposition (`two_pow_mem_isotypic`).
-/
import Mathlib

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZetaMoonshine

variable {N : ℕ} [NeZero N] {s : ℂ}

/-! ## The moonshine module of the zeta function

The group is `ZMod N`.  The module is `V = ⊕_{n ≥ 1} Vₙ` with every `Vₙ` one-dimensional,
the group element `j` acting on `Vₙ` by the scalar `ψ(j n)` where `ψ` is the standard additive
character `x ↦ e^{2πi x/N}`. -/

/-- The irreducible representation of `ZMod N` indexed by `a`: the element `j` acts by the
scalar `ψ(j a) = e^{2πi ja/N}`.  As `a` runs over `ZMod N` these are all the irreducibles. -/
noncomputable def irrep (a j : ZMod N) : ℂ := ZMod.stdAddChar (j * a)

/-- The trace of the group element `j` on the `n`-th graded piece `Vₙ` of the moonshine module.
Since `Vₙ` is one-dimensional this is just the scalar by which `j` acts. -/
noncomputable def gradedTrace (j : ZMod N) (n : ℕ) : ℂ := irrep (n : ZMod N) j

/-- The `n`-th graded piece is the irreducible representation `ρ_{n mod N}`: the analogue of
the decomposition of a moonshine module's graded pieces into irreducibles. -/
theorem gradedTrace_eq_irrep (j : ZMod N) (n : ℕ) :
    gradedTrace j n = irrep (n : ZMod N) j := rfl

/-- `tr(1 | Vₙ) = dim Vₙ = 1`: every graded piece is one-dimensional, which is why the
graded dimension series is the zeta function. -/
@[simp] theorem gradedTrace_zero_left (n : ℕ) : gradedTrace (0 : ZMod N) n = 1 := by
  simp [gradedTrace, irrep]

@[simp] theorem norm_irrep (a j : ZMod N) : ‖irrep a j‖ = 1 := by
  rw [irrep, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

@[simp] theorem norm_gradedTrace (j : ZMod N) (n : ℕ) : ‖gradedTrace j n‖ = 1 :=
  norm_irrep _ _

/-- Distinct group elements have distinct McKay–Thompson coefficient sequences: the `N`
McKay–Thompson series of the moonshine module are pairwise distinct. -/
theorem gradedTrace_injective : Function.Injective (gradedTrace : ZMod N → ℕ → ℂ) := by
  intro j₁ j₂ h
  have h1 : gradedTrace j₁ 1 = gradedTrace j₂ 1 := congrFun h 1
  simp only [gradedTrace, irrep, Nat.cast_one, mul_one] at h1
  exact ZMod.injective_stdAddChar h1

/-! ## McKay–Thompson series -/

/-- The McKay–Thompson series of the group element `j`: the Dirichlet series
`∑ₙ tr(j | Vₙ) n^{-s}` of the graded traces, the analogue of `T_g(τ) = ∑ tr(g|Vₙ)qⁿ`. -/
noncomputable def mtSeries (j : ZMod N) (s : ℂ) : ℂ := LSeries (gradedTrace j) s

theorem lSeriesSummable_gradedTrace (j : ZMod N) (hs : 1 < s.re) :
    LSeriesSummable (gradedTrace j) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => le_of_eq (norm_gradedTrace j n)) hs

/-- **The zeta function is the moonshine series.**  The McKay–Thompson series of the identity
element of the moonshine group is the Riemann zeta function, just as `T_1 = J = j - 744` for
the Monster. -/
theorem mtSeries_zero_eq_riemannZeta (hs : 1 < s.re) :
    mtSeries (0 : ZMod N) s = riemannZeta s := by
  rw [mtSeries, ← LSeries_one_eq_riemannZeta hs]
  congr 1
  funext n
  simp

/-! ## Isotypic decomposition -/

/-- The multiplicity of the irreducible representation `ρ_a` in the graded piece `Vₙ`,
computed by character-theoretic averaging over the group. -/
noncomputable def mult (a : ZMod N) (n : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j : ZMod N, (starRingEnd ℂ) (irrep a j) * gradedTrace j n

/-- The multiplicity of `ρ_a` in `Vₙ` is `1` if `n ≡ a (mod N)` and `0` otherwise. -/
theorem mult_eq_ite (a : ZMod N) (n : ℕ) :
    mult a n = if (n : ZMod N) = a then 1 else 0 := by
  classical
  have hstar : ∀ j : ZMod N, (starRingEnd ℂ) (irrep a j) * gradedTrace j n
      = ZMod.stdAddChar (j * ((n : ZMod N) - a)) := by
    intro j
    have hnorm : ‖irrep a j‖ = 1 := norm_irrep a j
    have hinv : (starRingEnd ℂ) (irrep a j) = (irrep a j)⁻¹ := by
      rw [← Complex.inv_eq_conj hnorm]
    rw [hinv, irrep, gradedTrace, irrep, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    ring_nf
  have hsum : ∑ j : ZMod N, (starRingEnd ℂ) (irrep a j) * gradedTrace j n
      = ((if (n : ZMod N) - a = 0 then (Fintype.card (ZMod N)) else 0 : ℕ) : ℂ) := by
    simp only [hstar]
    exact AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)
  rw [mult, hsum, ZMod.card]
  by_cases h : (n : ZMod N) = a
  · rw [if_pos h, if_pos (sub_eq_zero.mpr h)]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℂ) ≠ 0)
  · rw [if_neg h, if_neg (fun hc => h (sub_eq_zero.mp hc))]
    simp

/-- Moonshine positivity: every multiplicity is a non-negative integer (here `0` or `1`). -/
theorem mult_eq_natCast (a : ZMod N) (n : ℕ) :
    mult a n = ((if (n : ZMod N) = a then 1 else 0 : ℕ) : ℂ) := by
  rw [mult_eq_ite]; split <;> simp

/-- The multiplicities of the irreducibles in `Vₙ` add up to `dim Vₙ = 1`. -/
theorem sum_mult (n : ℕ) : ∑ a : ZMod N, mult a n = 1 := by
  classical
  simp [mult_eq_ite]

/-- The `a`-isotypic part of the moonshine module, as a Dirichlet series:
`∑_{n ≡ a (mod N)} n^{-s}`. -/
noncomputable def isotypic (a : ZMod N) (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => if (n : ZMod N) = a then 1 else 0) s

omit [NeZero N] in
theorem lSeriesSummable_isotypic (a : ZMod N) (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => if (n : ZMod N) = a then (1 : ℂ) else 0) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hs
  split <;> simp

omit [NeZero N] in
theorem lSeriesSummable_smul_isotypic (c : ℂ) (a : ZMod N) (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => c * (if (n : ZMod N) = a then (1 : ℂ) else 0)) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := ‖c‖) (fun n _ => ?_) hs
  split <;> simp [norm_nonneg]

/-- **The zeta function decomposes into isotypic components**: `ζ(s) = ∑_a isotypic a s`,
the analogue of decomposing the moonshine module into isotypic pieces for the group. -/
theorem riemannZeta_eq_sum_isotypic (hs : 1 < s.re) :
    riemannZeta s = ∑ a : ZMod N, isotypic a s := by
  classical
  rw [← LSeries_one_eq_riemannZeta hs]
  have hfun : (1 : ℕ → ℂ)
      = ∑ a : ZMod N, (fun n : ℕ => if (n : ZMod N) = a then (1 : ℂ) else 0) := by
    funext n
    simp
  rw [hfun, LSeries_sum (fun a _ => lSeriesSummable_isotypic a hs)]
  rfl

/-- Every McKay–Thompson series is the same combination of isotypic Dirichlet series,
twisted by the values of the corresponding character. -/
theorem mtSeries_eq_sum_isotypic (j : ZMod N) (hs : 1 < s.re) :
    mtSeries j s = ∑ a : ZMod N, irrep a j * isotypic a s := by
  classical
  have hfun : gradedTrace j
      = ∑ a : ZMod N, (fun n : ℕ => irrep a j * (if (n : ZMod N) = a then (1 : ℂ) else 0)) := by
    funext n
    simp [gradedTrace]
  rw [mtSeries, hfun, LSeries_sum (fun a _ => lSeriesSummable_smul_isotypic (irrep a j) a hs)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsmul : (fun n : ℕ => irrep a j * (if (n : ZMod N) = a then (1 : ℂ) else 0))
      = irrep a j • (fun n : ℕ => if (n : ZMod N) = a then (1 : ℂ) else 0) := rfl
  rw [hsmul, LSeries_smul]
  rfl

/-! ## The Dirichlet `L`-functions as the twists of ζ -/

/-- Twisting the isotypic components by a Dirichlet character mod `N` gives that character's
Dirichlet `L`-series: the `L`-functions are the character twists of the ζ-moonshine module. -/
theorem sum_dirichlet_smul_isotypic (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    ∑ a : ZMod N, χ a * isotypic a s = LSeries (fun n : ℕ => χ n) s := by
  classical
  have hfun : (fun n : ℕ => χ n)
      = ∑ a : ZMod N, (fun n : ℕ => χ a * (if (n : ZMod N) = a then (1 : ℂ) else 0)) := by
    funext n
    simp
  rw [hfun, LSeries_sum (fun a _ => lSeriesSummable_smul_isotypic (χ a) a hs)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsmul : (fun n : ℕ => χ a * (if (n : ZMod N) = a then (1 : ℂ) else 0))
      = χ a • (fun n : ℕ => if (n : ZMod N) = a then (1 : ℂ) else 0) := rfl
  rw [hsmul, LSeries_smul]
  rfl

/-- Conversely, by orthogonality of Dirichlet characters, each isotypic component at a unit
`a` is recovered from the `L`-functions: `isotypic a s = φ(N)⁻¹ ∑_χ χ(a⁻¹) L(χ, s)`. -/
theorem isotypic_eq_sum_LSeries {a : ZMod N} (ha : IsUnit a) (hs : 1 < s.re) :
    isotypic a s
      = (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * LSeries (fun n : ℕ => χ n) s := by
  classical
  have hswap : ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * LSeries (fun n : ℕ => χ n) s
      = ∑ b : ZMod N, (∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * χ b) * isotypic b s := by
    calc ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * LSeries (fun n : ℕ => χ n) s
        = ∑ χ : DirichletCharacter ℂ N, ∑ b : ZMod N, χ a⁻¹ * (χ b * isotypic b s) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [← sum_dirichlet_smul_isotypic χ hs, Finset.mul_sum]
      _ = ∑ b : ZMod N, ∑ χ : DirichletCharacter ℂ N, (χ a⁻¹ * χ b) * isotypic b s := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun χ _ => by ring
      _ = ∑ b : ZMod N, (∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * χ b) * isotypic b s := by
          exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  have horth : ∀ b : ZMod N, ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * χ b
      = if a = b then (N.totient : ℂ) else 0 :=
    fun b => DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  have htot : (N.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  rw [hswap]
  simp only [horth, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← mul_assoc, inv_mul_cancel₀ htot, one_mul]

/-! ## Self-similarity of the ζ-moonshine module

The component of the module on which the group acts trivially is a rescaled copy of the whole
module: `∑_{N ∣ n} n^{-s} = N^{-s} ζ(s)`.  This is the ζ-analogue of the self-reproducing
(replication) formulas satisfied by the McKay–Thompson series of the Monster. -/

theorem isotypic_zero_eq (hs : 1 < s.re) :
    isotypic (0 : ZMod N) s = (N : ℂ) ^ (-s) * riemannZeta s := by
  classical
  set f : ℕ → ℂ := fun n : ℕ => if (n : ZMod N) = 0 then (1 : ℂ) else 0 with hf
  have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b h => by
    simpa [Nat.mul_right_inj (NeZero.ne N)] using h
  have hsupp : Function.support (LSeries.term f s) ⊆ Set.range (fun m : ℕ => N * m) := by
    intro n hn
    rw [Function.mem_support, LSeries.term_def] at hn
    have hz : (n : ZMod N) = 0 := by
      by_contra hc
      exact hn (by simp [hf, hc])
    obtain ⟨m, rfl⟩ := (ZMod.natCast_eq_zero_iff n N).mp hz
    exact ⟨m, rfl⟩
  have hterm : ∀ m : ℕ,
      LSeries.term f s (N * m) = (N : ℂ) ^ (-s) * LSeries.term (1 : ℕ → ℂ) s m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.term]
    · have hNm : N * m ≠ 0 := Nat.mul_ne_zero (NeZero.ne N) hm
      have hfval : f (N * m) = 1 := by
        simp [hf]
      have hcast : ((N * m : ℕ) : ℂ) ^ s = (N : ℂ) ^ s * (m : ℂ) ^ s := by
        have h := Complex.mul_cpow_ofReal_nonneg (a := (N : ℝ)) (b := (m : ℝ))
          (by positivity) (by positivity) s
        push_cast at h ⊢
        exact h
      rw [LSeries.term_def, LSeries.term_def, if_neg hNm, if_neg hm, hfval, hcast,
        Complex.cpow_neg]
      simp [mul_comm]
  calc isotypic (0 : ZMod N) s = ∑' n : ℕ, LSeries.term f s n := rfl
    _ = ∑' m : ℕ, LSeries.term f s (N * m) := (hinj.tsum_eq hsupp).symm
    _ = ∑' m : ℕ, (N : ℂ) ^ (-s) * LSeries.term (1 : ℕ → ℂ) s m := tsum_congr hterm
    _ = (N : ℂ) ^ (-s) * LSeries (1 : ℕ → ℂ) s := tsum_mul_left
    _ = (N : ℂ) ^ (-s) * riemannZeta s := by rw [LSeries_one_eq_riemannZeta hs]

/-! ## The smallest moonshine group: `ZMod 2` and the Dirichlet eta function

For the group of order two the module has just two isotypic pieces, the even and the odd
integers, and the two McKay–Thompson series are `T_0 = ζ` and the alternating series
`T_1(s) = ∑ (-1)^n n^{-s} = (2^{1-s} - 1) ζ(s)`, i.e. minus the Dirichlet eta function. -/

section Two

theorem stdAddChar_one_two : (ZMod.stdAddChar (1 : ZMod 2)) = -1 := by
  have h2 : (ZMod.stdAddChar (1 : ZMod 2)) ^ 2 = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, show (2 : ℕ) • (1 : ZMod 2) = 0 by decide]
    exact AddChar.map_zero_eq_one _
  have hne : (ZMod.stdAddChar (1 : ZMod 2)) ≠ 1 := by
    intro h
    have h0 : ZMod.stdAddChar (1 : ZMod 2) = ZMod.stdAddChar (0 : ZMod 2) := by
      rw [h, AddChar.map_zero_eq_one]
    exact absurd (ZMod.injective_stdAddChar h0) (by decide)
  have hfac :
      ((ZMod.stdAddChar (1 : ZMod 2)) - 1) * ((ZMod.stdAddChar (1 : ZMod 2)) + 1) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- The non-trivial element of the group of order two acts on `Vₙ` by `(-1)^n`. -/
theorem gradedTrace_one_two (n : ℕ) : gradedTrace (1 : ZMod 2) n = (-1) ^ n := by
  rw [gradedTrace, irrep, one_mul]
  induction n with
  | zero => simp
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ZMod 2) = (k : ZMod 2) + 1 := by push_cast; ring
    rw [hcast, AddChar.map_add_eq_mul, ih, stdAddChar_one_two, pow_succ]

/-- **The Dirichlet eta function is the other McKay–Thompson series.**  For the moonshine group
of order two, the non-identity element gives `∑ (-1)^n n^{-s} = (2^{1-s} - 1) ζ(s)`. -/
theorem mtSeries_one_two (hs : 1 < s.re) :
    mtSeries (1 : ZMod 2) s = ((2 : ℂ) ^ (1 - s) - 1) * riemannZeta s := by
  have hsum : ∀ f : ZMod 2 → ℂ, ∑ a : ZMod 2, f a = f 0 + f 1 := by
    intro f
    simp [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  have hzeta : riemannZeta s = isotypic (0 : ZMod 2) s + isotypic (1 : ZMod 2) s := by
    rw [riemannZeta_eq_sum_isotypic (N := 2) hs, hsum]
  have hmt : mtSeries (1 : ZMod 2) s
      = isotypic (0 : ZMod 2) s - isotypic (1 : ZMod 2) s := by
    rw [mtSeries_eq_sum_isotypic 1 hs, hsum]
    have h0 : irrep (0 : ZMod 2) 1 = 1 := by simp [irrep]
    have h1 : irrep (1 : ZMod 2) 1 = -1 := by
      rw [irrep, one_mul, stdAddChar_one_two]
    rw [h0, h1]
    ring
  have hzero : isotypic (0 : ZMod 2) s = ((2 : ℕ) : ℂ) ^ (-s) * riemannZeta s :=
    isotypic_zero_eq hs
  have hpow : ((2 : ℕ) : ℂ) ^ (1 - s) = 2 * ((2 : ℕ) : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring,
      Complex.cpow_add _ _ (by norm_num : ((2 : ℕ) : ℂ) ≠ 0), Complex.cpow_one]
    norm_num
  rw [hmt, show isotypic (1 : ZMod 2) s = riemannZeta s - isotypic (0 : ZMod 2) s by
    rw [hzeta]; ring, hzero]
  push_cast at hpow ⊢
  rw [hpow]
  ring

end Two

/-! ## Partial sums: the decomposition seen on the real axis

The same decomposition truncated at `n ≤ K`, over the reals, is what the picture
`visualization/zeta-moonshine.svg` draws. -/

/-- `∑_{n = 1}^{K} n^{-s}`, the truncated zeta function on the real axis. -/
noncomputable def zetaPartialR (K : ℕ) (s : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-s)

/-- The truncated `a`-isotypic component `∑_{n ≤ K, n ≡ a (N)} n^{-s}`. -/
noncomputable def isotypicPartialR (a : ZMod N) (K : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 K).filter (fun n : ℕ => (n : ZMod N) = a), (n : ℝ) ^ (-s)

/-- The truncated zeta function is the sum of its truncated isotypic components. -/
theorem zetaPartialR_eq_sum_isotypicPartialR (K : ℕ) (t : ℝ) :
    zetaPartialR K t = ∑ a : ZMod N, isotypicPartialR a K t :=
  (Finset.sum_fiberwise (Finset.Icc 1 K) (fun n : ℕ => (n : ZMod N))
    (fun n : ℕ => (n : ℝ) ^ (-t))).symm

omit [NeZero N] in
/-- Each truncated isotypic component is non-negative. -/
theorem isotypicPartialR_nonneg (a : ZMod N) (K : ℕ) (t : ℝ) : 0 ≤ isotypicPartialR a K t :=
  Finset.sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-! ## The moonshine group of order 24

The number `24` is the exponent in `Δ = η²⁴`, the modular form whose `q`-expansion coefficients
are the Ramanujan τ studied elsewhere in this project.  Its moonshine group `ZMod 24` has 24
elements, hence 24 pairwise distinct McKay–Thompson series, the first of which is ζ. -/

section TwentyFour

/-- The group has 24 elements, so there are 24 McKay–Thompson series; they are pairwise
distinct (`gradedTrace_injective`), the one at the identity being ζ. -/
theorem card_group_24 : Fintype.card (ZMod 24) = 24 := by simp

/-- ζ is the McKay–Thompson series of the identity of the group of order 24. -/
theorem mtSeries_zero_eq_riemannZeta_24 (hs : 1 < s.re) :
    mtSeries (0 : ZMod 24) s = riemannZeta s :=
  mtSeries_zero_eq_riemannZeta hs

/-- The prime-power fiber of `2` meets only four of the twenty-four isotypic components:
every `2^k` with `k ≥ 1` is congruent to `2`, `4`, `8` or `16` mod `24`. -/
theorem two_pow_mod24_mem (k : ℕ) (hk : 1 ≤ k) :
    ((2 ^ k : ℕ) : ZMod 24) ∈ ({2, 4, 8, 16} : Finset (ZMod 24)) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h | h
    · interval_cases n
      · decide
    · have hstep : ((2 ^ (n + 1) : ℕ) : ZMod 24) = 2 * ((2 ^ n : ℕ) : ZMod 24) := by
        push_cast; ring
      have hmem := ih h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rw [hstep]
      rcases hmem with h | h | h | h <;> rw [h] <;> decide

/-- Consequently the multiplicity of `ρ_a` in the graded piece `V_{2^k}` vanishes outside those
four components. -/
theorem mult_two_pow_eq_zero_of_not_mem {a : ZMod 24} (k : ℕ) (hk : 1 ≤ k)
    (ha : a ∉ ({2, 4, 8, 16} : Finset (ZMod 24))) : mult a (2 ^ k) = 0 := by
  rw [mult_eq_ite, if_neg]
  intro h
  exact ha (h ▸ two_pow_mod24_mem k hk)

/-- The largest prime power of the Monster's order, `2^46`, sits in the isotypic component
`a = 16`. -/
theorem monster_two_pow_isotypic : ((2 ^ 46 : ℕ) : ZMod 24) = 16 := by
  push_cast
  decide

theorem mult_monster_two_pow : mult (16 : ZMod 24) (2 ^ 46) = 1 := by
  rw [mult_eq_ite, if_pos monster_two_pow_isotypic]

end TwentyFour

end ZetaMoonshine
