import Mathlib

/-!
# Triadic ("3s within 9s") p-adic kernel algebra — the formal core

This file formalises the genuine mathematical content of the *triadic / p-adic
codec formalism* developed in the source document (the "balanced-ternary
kernel algebra" sections 0–14).  The document is largely informal, but it
contains a self-contained discrete/algebraic skeleton whose crisp claims are
reproduced here as Lean theorems.

The balanced-ternary **trit** is modelled by `ZMod 3` (three states, with a
negation whose only fixed point is `0`).  The integer-valued balanced ternary
*digits* live in `{-1, 0, 1} ⊆ ℤ`.

Contents (matching the document's numbering):

* **§0.1 / 2.1** alphabet cardinality `|T| = 3` (`card_trit`).
* **§2.1 the 9-object** `C = T²`, `|C| = 9` (`card_sheet`).
* **§2.2 kernels** `K_d = T^d`, `|K_d| = 3^d` (`card_kernel`).
* **§2.2 the 9-lift** `|K_{d+2}| = 9·|K_d|` (`card_lift9`).
* **§3 ambient tetration tower** `|F_{n+1}| = |F_n|^{|F_n|}`
  (`card_funspace`, `cardTower_succ`, `cardTower_strictMono`).
* **§0.2 balanced-ternary representation** of every integer
  (`balanced_ternary_repr`).
* **§6.2 global inversion quotient** `|K_d/G| = 1 + (3^d-1)/2`, hence
  `|T²/G| = 5`, `|T³/G| = 14` (`orbitCount_two`, `orbitCount_three`,
  `orbitCount_formula`).
* **§8.4 lossless reconstruction** (`lossless_reconstruction`,
  `residual_lossless`).
* **§12 trit packing** `T⁵ ↪ {0,…,255}` since `3⁵ = 243 ≤ 256`, with packing
  efficiency `log₂(3⁵)/8 < 1` (`trit_pack_card`, `trit_pack_embedding`,
  `trit_pack_efficiency_eq`, `trit_pack_efficiency_lt_one`).
-/

namespace TriadicKernelAlgebra

open scoped BigOperators

/-! ## §0.1 / §2.1 — Balanced-ternary alphabet and the 9-object -/

/-- **Alphabet size.** The balanced-ternary trit `T` has three states. -/
theorem card_trit : Fintype.card (ZMod 3) = 3 := by decide

/-- **The 9-object (sheet).** `C = T²` has `|C| = 9`. -/
theorem card_sheet : Fintype.card (ZMod 3 × ZMod 3) = 9 := by decide

/-! ## §2.2 — Kernels `K_d = T^d` and the 9-lift -/

/-- **Kernel cardinality.** A kernel of order `d` is `K_d = T^d`, with
`|K_d| = 3^d`. -/
theorem card_kernel (d : ℕ) : Fintype.card (Fin d → ZMod 3) = 3 ^ d := by
  rw [Fintype.card_fun, card_trit, Fintype.card_fin]

/-- **The 9-lift `K_d → K_{d+2}`.** Adding two triadic axes multiplies the
kernel size by `9`: `|K_{d+2}| = 9·|K_d|`. This is the document's
"3s within 9s" generator. -/
theorem card_lift9 (d : ℕ) :
    Fintype.card (Fin (d + 2) → ZMod 3) = 9 * Fintype.card (Fin d → ZMod 3) := by
  rw [card_kernel, card_kernel]; ring

/-! ## §3 — Ambient tetration tower (unstructured potential) -/

/-- **Function-space cardinality.** If the level `F_n` has `c` states, the next
level `F_{n+1} = F_n^{F_n}` (all self-maps) has `c^c` states. -/
theorem card_funspace (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (α → α) = Fintype.card α ^ Fintype.card α :=
  Fintype.card_fun

/-- The cardinality tower `|F_n|` of the ambient tetration, anchored at
`|F_0| = 9`. -/
def cardTower : ℕ → ℕ
  | 0 => 9
  | (n + 1) => cardTower n ^ cardTower n

/-- **Tetration recurrence.** `|F_{n+1}| = |F_n|^{|F_n|}`. -/
theorem cardTower_succ (n : ℕ) : cardTower (n + 1) = cardTower n ^ cardTower n := rfl

/-
Every level of the tower is at least `9` (so at least `2`).
-/
theorem cardTower_ge_two (n : ℕ) : 2 ≤ cardTower n := by
  induction' n with n ih;
  · decide +revert;
  · exact le_trans ih ( Nat.le_self_pow ( by linarith ) _ )

/-
**The tower grows strictly** (it never stabilises).
-/
theorem cardTower_strictMono : StrictMono cardTower := by
  refine' strictMono_nat_of_lt_succ fun n => _;
  exact lt_self_pow₀ ( by linarith [ cardTower_ge_two n ] ) ( by linarith [ cardTower_ge_two n ] )

/-! ## §0.2 — Balanced-ternary representation of integers -/

/-
**Balanced-ternary representation.** Every integer `z` is a finite sum
`z = Σ_{k<N} c_k · 3^k` with each digit `c_k ∈ {-1, 0, 1}`. This is the
arithmetic backbone of the triadic residual decomposition.
-/
theorem balanced_ternary_repr (z : ℤ) :
    ∃ (N : ℕ) (c : ℕ → ℤ),
      (∀ k, c k = -1 ∨ c k = 0 ∨ c k = 1) ∧
      z = ∑ k ∈ Finset.range N, c k * 3 ^ k := by
        -- We prove this by strong induction on the natural number `z.natAbs` (or induction on |z|), or use a known Mathlib development of balanced ternary if available.
        have h_abs : ∀ n : ℕ, ∃ N : ℕ, ∃ c : ℕ → ℤ, (∀ k, c k ∈ ({-1, 0, 1} : Set ℤ)) ∧ n = ∑ k ∈ Finset.range N, c k * 3 ^ k := by
          intro n
          induction' n using Nat.strong_induction_on with n ih
          by_cases hn : n = 0
          · exact ⟨0, fun _ => 0, by norm_num, by norm_num [hn]⟩
          ·
            -- Write $n$ as $3q + r$ where $r \in \{-1, 0, 1\}$ is the balanced residue of $n$ mod 3.
            obtain ⟨q, r, hr⟩ : ∃ q r : ℤ, n = 3 * q + r ∧ r ∈ ({-1, 0, 1} : Set ℤ) := by
              exact ⟨ ( n + 1 ) / 3, ( n + 1 ) % 3 - 1, by omega, by norm_num; omega ⟩;
            -- By the induction hypothesis, $q$ has a balanced ternary representation.
            obtain ⟨N, c, hc⟩ : ∃ N : ℕ, ∃ c : ℕ → ℤ, (∀ k, c k ∈ ({-1, 0, 1} : Set ℤ)) ∧ q = ∑ k ∈ Finset.range N, c k * 3 ^ k := by
              convert ih ( Int.natAbs q ) _;
              · rw [ Int.natAbs_of_nonneg ( by rcases hr.2 with ( rfl | rfl | rfl ) <;> linarith [ Nat.pos_of_ne_zero hn ] ) ];
              · grind;
            refine' ⟨ N + 1, fun k => if k = 0 then r else c ( k - 1 ), _, _ ⟩ <;> simp_all +decide [ Finset.sum_range_succ' ];
            · grind;
            · simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, pow_succ'];
        cases' Int.eq_nat_or_neg z with h h;
        obtain rfl | rfl := h <;> obtain ⟨ N, c, hc₁, hc₂ ⟩ := h_abs ‹_› <;> [ exact ⟨ N, c, hc₁, hc₂ ⟩ ; exact ⟨ N, fun k => -c k, fun k => by specialize hc₁ k; aesop, by simp +decide [ hc₂ ] ⟩ ] ;

/-! ## §6.2 — Global inversion quotient

The group `G = ℤ₂ = {±1}` acts on the kernel `K_d = T^d` by `g · u = -u`.
The number of orbits `|K_d/G|` is realised concretely as the number of
distinct unordered pairs `{u, -u}`. -/

/-- The number of orbits `|K_d / G|` of the inversion action `u ↦ -u`,
realised as the number of distinct unordered pairs `{u, -u}`. -/
def orbitCount (d : ℕ) : ℕ :=
  (Finset.univ.image
    (fun u : Fin d → ZMod 3 => ({u, -u} : Finset (Fin d → ZMod 3)))).card

/-- **`|T²/G| = 5`** — "9 states as 5 + inversion bit". -/
theorem orbitCount_two : orbitCount 2 = 5 := by decide

/-- **`|T³/G| = 14`** — "27 states as 14 + inversion bit". -/
theorem orbitCount_three : orbitCount 3 = 14 := by decide

/-
**General inversion-quotient count.** `|K_d/G| = 1 + (3^d - 1)/2 = (3^d+1)/2`.
The only fixed point of `u ↦ -u` is the all-zero kernel, so by an orbit-counting
(Burnside) argument the number of orbits is `(3^d + 1)/2`.
-/
theorem orbitCount_formula (d : ℕ) : orbitCount d = (3 ^ d + 1) / 2 := by
  have h_orbitSize : ∀ u : Fin d → ZMod 3, ({u, -u} : Finset (Fin d → ZMod 3)).card = if u = 0 then 1 else 2 := by
    intro u;
    by_cases hu : u = 0 <;> simp +decide [ hu ];
    rw [ Finset.card_pair ];
    contrapose! hu;
    ext i; have := congr_fun hu i; norm_num at *;
    grind;
  -- By double counting, the sum of the sizes of the orbits is equal to the size of the domain.
  have h_sum_orbitSizes : ∑ u ∈ Finset.univ.image (fun u : Fin d → ZMod 3 => ({u, -u} : Finset (Fin d → ZMod 3))), u.card = 3 ^ d := by
    rw [ Finset.sum_image' ];
    rotate_left;
    use fun u => 1;
    · simp +zetaDelta at *;
      intro u; rw [ show Finset.filter ( fun j => { j, -j } = { u, -u } ) Finset.univ = { u, -u } from ?_ ] ;
      grind;
    · norm_num [ Finset.card_univ ];
  -- Since each pair {u, -u} contributes 2 to the sum except for the singleton {0}, we can split the sum into these contributions.
  have h_split_sum : ∑ u ∈ Finset.univ.image (fun u : Fin d → ZMod 3 => ({u, -u} : Finset (Fin d → ZMod 3))), u.card = ∑ u ∈ Finset.univ.image (fun u : Fin d → ZMod 3 => ({u, -u} : Finset (Fin d → ZMod 3))), if u = {0} then 1 else 2 := by
    refine' Finset.sum_congr rfl fun x hx => _;
    grind;
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ];
  split_ifs at h_sum_orbitSizes <;> simp_all +decide [ Finset.card_erase_of_mem ];
  · exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ Finset.card ( Finset.image ( fun u : Fin d → ZMod 3 => { u, -u } : ( Fin d → ZMod 3 ) → Finset ( Fin d → ZMod 3 ) ) Finset.univ ) from Finset.card_pos.mpr ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ 0 ) ⟩ ), show orbitCount d = Finset.card ( Finset.image ( fun u : Fin d → ZMod 3 => { u, -u } : ( Fin d → ZMod 3 ) → Finset ( Fin d → ZMod 3 ) ) Finset.univ ) from rfl ] ) );
  · exact absurd ( congr_arg Even h_sum_orbitSizes ) ( by norm_num [ parity_simps ] )

/-! ## §8.4 — Lossless reconstruction -/

/-- **Lossless reconstruction (abstract).** If the decoder `dec` is a left
inverse of the encoder `enc` ("`Dec` matches `Enc`"), then decoding recovers the
original datum exactly. -/
theorem lossless_reconstruction {X C : Type*} (enc : X → C) (dec : C → X)
    (h : Function.LeftInverse dec enc) (x : X) : dec (enc x) = x := h x

/-- **Residual losslessness.** Writing the value as prediction `P` plus residual
`R`, the residual admits a balanced-ternary plane decomposition
`R = Σ_{k<N} S_k · 3^k` (`S_k ∈ {-1,0,1}`); recomposing planes and adding back the
prediction returns the original value `P + R` exactly. -/
theorem residual_lossless (P R : ℤ) :
    ∃ (N : ℕ) (S : ℕ → ℤ),
      (∀ k, S k = -1 ∨ S k = 0 ∨ S k = 1) ∧
      P + ∑ k ∈ Finset.range N, S k * 3 ^ k = P + R := by
  obtain ⟨N, c, hc, hR⟩ := balanced_ternary_repr R
  exact ⟨N, c, hc, by rw [← hR]⟩

/-! ## §12 — Trit packing (5 trits per byte) -/

/-- `|T⁵| = 3⁵ = 243`. -/
theorem trit_pack_card : Fintype.card (Fin 5 → ZMod 3) = 243 := by
  rw [card_kernel]; norm_num

/-- **Trit packing.** Since `3⁵ = 243 ≤ 256` there is an injective packing
`T⁵ ↪ {0,…,255}`, storing five trits per byte losslessly. -/
theorem trit_pack_embedding : Nonempty ((Fin 5 → ZMod 3) ↪ Fin 256) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [trit_pack_card, Fintype.card_fin]; norm_num

/-- The trit-packing efficiency is `log₂(3⁵)/8 = 5·log₂(3)/8`. -/
theorem trit_pack_efficiency_eq :
    Real.logb 2 ((3 : ℝ) ^ 5) / 8 = 5 * Real.logb 2 3 / 8 := by
  rw [Real.logb_pow]; norm_num

/-
The packing has efficiency strictly below `1` byte-per-byte (overhead from
`243 < 256`): `log₂(3⁵)/8 < 1`.
-/
theorem trit_pack_efficiency_lt_one : Real.logb 2 ((3 : ℝ) ^ 5) / 8 < 1 := by
  rw [ div_lt_one, Real.logb_lt_iff_lt_rpow ] <;> norm_num

end TriadicKernelAlgebra