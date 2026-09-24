import RequestProject.FrobeniusOrbit
import RequestProject.CenterRetraction

/-!
# What would Frobenius do?  He would take the transfer.

The two halves of this project — retractions of a group onto its centre, and the Frobenius
orbit product `N(x) = x · x^p ⋯ x^(p^(k-1))` of a finite field onto its prime subfield — are
the *same construction*: the **transfer homomorphism** (Verlagerung) of a group onto a
subgroup, evaluated in two different situations.

* For a subgroup `H ≤ G` of finite index which is central (or when `G` itself is abelian) the
  transfer is the "index power" `g ↦ g ^ [G : H]`, landing in `H`.
* Taking `H = Z(G)` gives Mathlib's `MonoidHom.transferCenterPow : G →* Z(G)`.
* Taking `G = Kˣ` and `H = 𝔽ₚˣ` — here `primeUnits K p`, the units killed by `x ↦ x^(p-1)` —
  gives exactly the Frobenius orbit product, because `[Kˣ : 𝔽ₚˣ] = 1 + p + ⋯ + p^(k-1)`
  (`transfer_primeUnits_eq_frobNorm`).

Both maps therefore fail to be retractions for the same reason: on the target they are not the
identity but the *index power*, and both are repaired in the same way — compose with a power
`t` inverting the index, which is possible exactly when the index is invertible modulo the
order of the target (`pow_index_inverse`).  This gives

* `hasCenterRetraction_of_coprime_index` : if `gcd([G : Z(G)], |Z(G)|) = 1` then `G` retracts
  onto its centre.  (Consistently with `not_hasCenterRetraction_of_isPGroup`, that coprimality
  can never hold for a nonabelian finite `p`-group: `not_coprime_index_center_of_isPGroup`.)
* `exists_multiplicative_retraction_of_coprime` : if `gcd(k, p-1) = 1` then `Kˣ` retracts onto
  `𝔽ₚˣ` — the criterion `FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime` of the
  field half, obtained here from the group-theoretic engine, because
  `[Kˣ : 𝔽ₚˣ] ≡ k (mod p-1)` (`index_primeUnits_modEq`).

`what_frobenius_does` collects the dictionary in one statement.
-/

open Subgroup MonoidHom Finset

namespace FrobeniusTransfer

/-! ### The engine: undoing an index power -/

/-- **Inverting the index power.**  In a group `A` whose order is coprime to `n`, the `n`-th
power map is inverted by a power map: there is a `t` with `(a ^ n) ^ t = a` for every `a`.
(If `A` is infinite the hypothesis forces `n = 1`.) -/
theorem pow_index_inverse {A : Type*} [Group A] {n : ℕ} (h : Nat.Coprime n (Nat.card A)) :
    ∃ t : ℕ, ∀ a : A, (a ^ n) ^ t = a := by
  rcases Nat.lt_or_ge (Nat.card A) 2 with h1 | h1
  · interval_cases hA : Nat.card A
    · have hn : n = 1 := (Nat.coprime_zero_right n).1 (by simpa [hA] using h)
      exact ⟨1, fun a => by simp [hn]⟩
    · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 hA).1
      exact ⟨0, fun a => by simp [Subsingleton.elim a 1]⟩
  · obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime h h1
    refine ⟨t, fun a => ?_⟩
    rw [← pow_mul]
    conv_rhs => rw [← pow_one a]
    have hnt : n * t = Nat.card A * (n * t / Nat.card A) + 1 := by
      conv_lhs => rw [← Nat.div_add_mod (n * t) (Nat.card A)]
      omega
    rw [hnt, pow_add, pow_mul, pow_card_eq_one', one_pow, one_mul]

/-- `1 + p + ⋯ + p^(k-1) ≡ k (mod p - 1)`: the index of the prime units is congruent to the
degree. -/
theorem geom_sum_modEq (p k : ℕ) (hp : 1 ≤ p) : (∑ i ∈ range k, p ^ i) ≡ k [MOD p - 1] := by
  have hpow : ∀ i : ℕ, p ^ i ≡ 1 [MOD p - 1] := by
    intro i
    have h1 : p ≡ 1 [MOD p - 1] := by
      rcases Nat.eq_or_lt_of_le hp with h | h
      · simp [← h]
      · unfold Nat.ModEq
        rw [Nat.mod_eq_sub_mod (by omega), Nat.sub_sub_self (by omega)]
    simpa using h1.pow i
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simpa using ih.add (hpow n)

/-! ### The group side: the transfer onto the centre -/

section GroupSide

variable {G : Type*} [Group G]

/-- On the centre the transfer `G →* Z(G)` is the index power `z ↦ z ^ [G : Z(G)]`. -/
theorem transferCenterPow_restrict [(center G).FiniteIndex] (z : center G) :
    transferCenterPow G (z : G) = z ^ (center G).index := by
  apply Subtype.ext
  rw [transferCenterPow_apply]
  push_cast
  rfl

/-- The transfer onto the centre is a retraction exactly when the index power is trivial on the
centre. -/
theorem transferCenterPow_isRetraction_iff [(center G).FiniteIndex] :
    (∀ z : center G, transferCenterPow G (z : G) = z) ↔
      ∀ z : center G, z ^ ((center G).index - 1) = 1 := by
  have hpos : 1 ≤ (center G).index := Nat.one_le_iff_ne_zero.2 FiniteIndex.index_ne_zero
  constructor
  · intro h z
    have hz := h z
    rw [transferCenterPow_restrict] at hz
    have hz2 : z ^ ((center G).index - 1) * z = 1 * z := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hpos]; exact hz
    exact mul_right_cancel hz2
  · intro h z
    rw [transferCenterPow_restrict, ← Nat.sub_add_cancel hpos, pow_succ, h z, one_mul]

/-- **The repaired transfer.**  If the index of the centre is coprime to the order of the
centre, then a power of the transfer is a genuine retraction of `G` onto `Z(G)`. -/
theorem hasCenterRetraction_of_coprime_index [Finite G]
    (h : Nat.Coprime (center G).index (Nat.card (center G))) : HasCenterRetraction G := by
  obtain ⟨t, ht⟩ := pow_index_inverse (A := center G) h
  refine ⟨(powMonoidHom t).comp (transferCenterPow G), fun z => ?_⟩
  simp only [MonoidHom.comp_apply, transferCenterPow_restrict z, powMonoidHom_apply]
  exact ht z

/-- Consequently, when the index of the centre is coprime to its order, the centre is a direct
factor of `G`. -/
theorem center_isComplement_of_coprime_index [Finite G]
    (h : Nat.Coprime (center G).index (Nat.card (center G))) :
    ∃ N : Subgroup G, IsComplement' N (center G) :=
  (hasCenterRetraction_iff_isComplement G).1 (hasCenterRetraction_of_coprime_index h)

/-- For a nonabelian finite `p`-group the coprimality of the repair criterion always fails —
as it must, since such a group has no retraction onto its centre at all. -/
theorem not_coprime_index_center_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (hnc : ¬ ∀ a b : G, a * b = b * a) :
    ¬ Nat.Coprime (center G).index (Nat.card (center G)) := fun h =>
  not_hasCenterRetraction_of_isPGroup hG hnc (hasCenterRetraction_of_coprime_index h)

end GroupSide

/-! ### The same engine for a subgroup of an abelian group -/

section CommSide

variable {G : Type*} [CommGroup G]

/-- In an abelian group the transfer onto a subgroup of finite index is the index power. -/
theorem transfer_comm_eq_pow (H : Subgroup G) [H.FiniteIndex] (g : G) :
    ((transfer (MonoidHom.id H) g : H) : G) = g ^ H.index := by
  rw [MonoidHom.transfer_eq_pow (MonoidHom.id H) g
    (fun k g₀ _ => by rw [mul_comm g₀⁻¹ (g ^ k), mul_assoc, inv_mul_cancel, mul_one])]
  rfl

/-- **The repaired transfer, abelian version.**  If `[G : H]` is coprime to `|H|` then a power
of the transfer is a retraction of `G` onto `H`. -/
theorem exists_retraction_of_coprime_index (H : Subgroup G) [H.FiniteIndex]
    (h : Nat.Coprime H.index (Nat.card H)) : ∃ r : G →* H, ∀ z : H, r z = z := by
  obtain ⟨t, ht⟩ := pow_index_inverse (A := H) h
  refine ⟨(powMonoidHom t).comp (transfer (MonoidHom.id H)), fun z => ?_⟩
  have hz : (transfer (MonoidHom.id H) (z : G) : H) = z ^ H.index := by
    apply Subtype.ext
    rw [transfer_comm_eq_pow]
    push_cast
    rfl
  simp only [MonoidHom.comp_apply, hz, powMonoidHom_apply]
  exact ht z

end CommSide

/-! ### The field side: the Frobenius orbit product is the transfer onto `𝔽ₚˣ` -/

section FieldSide

open FrobeniusPrimeSubfield

variable (K : Type*) [Field K] (p : ℕ)

/-- The units of the prime subfield, as a subgroup of `Kˣ`: the kernel of `x ↦ x ^ (p-1)`. -/
def primeUnits : Subgroup Kˣ := (powMonoidHom (p - 1) : Kˣ →* Kˣ).ker

variable {K p}

theorem mem_primeUnits_iff {x : Kˣ} : x ∈ primeUnits K p ↔ x ^ (p - 1) = 1 := Iff.rfl

/-- A unit lies in `primeUnits K p` exactly when it is fixed by the Frobenius, i.e. lies in the
prime subfield. -/
theorem mem_primeUnits_iff_pow_char [Fact p.Prime] {x : Kˣ} :
    x ∈ primeUnits K p ↔ (x : K) ^ p = (x : K) := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  rw [mem_primeUnits_iff]
  constructor
  · intro h
    have : ((x ^ (p - 1) : Kˣ) : K) = 1 := by rw [h]; rfl
    push_cast at this
    calc (x : K) ^ p = (x : K) ^ (p - 1) * (x : K) := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
      _ = (x : K) := by rw [this, one_mul]
  · intro h
    apply Units.ext
    push_cast
    exact pow_sub_one_eq_one_of_pow_char_eq_self h x.ne_zero

variable [Fintype K] [Fact p.Prime] {k : ℕ}

/-- `𝔽ₚˣ` has `p - 1` elements. -/
theorem card_primeUnits (hK : Nat.card K = p ^ k) : Nat.card (primeUnits K p) = p - 1 := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hcard : Nat.card Kˣ = p ^ k - 1 := by rw [Nat.card_units, hK]
  have hdvd : (p - 1) ∣ Nat.card Kˣ := by
    rw [hcard]
    simpa using Nat.sub_dvd_pow_sub_pow p 1 k
  exact card_ker_pow_of_dvd Kˣ hdvd (by omega)

/-- **The index of `𝔽ₚˣ` in `Kˣ` is the Frobenius orbit length count**
`1 + p + ⋯ + p^(k-1)`. -/
theorem index_primeUnits (hK : Nat.card K = p ^ k) :
    (primeUnits K p).index = ∑ i ∈ range k, p ^ i := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hcard : Nat.card Kˣ = p ^ k - 1 := by rw [Nat.card_units, hK]
  have h1 : (primeUnits K p).index * (p - 1) = p ^ k - 1 := by
    rw [← card_primeUnits (p := p) hK, Subgroup.index_mul_card, hcard]
  have h2 : (∑ i ∈ range k, p ^ i) * (p - 1) = p ^ k - 1 := geom_sum_mul_pred p k (by omega)
  have : (primeUnits K p).index * (p - 1) = (∑ i ∈ range k, p ^ i) * (p - 1) := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

instance primeUnits_finiteIndex : (primeUnits K p).FiniteIndex := by
  have : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) (fun _ _ h => Units.ext h)
  infer_instance

/-- **The dictionary.**  The Frobenius orbit product `N(x) = x · x^p ⋯ x^(p^(k-1))` *is* the
transfer homomorphism of `Kˣ` onto the subgroup `𝔽ₚˣ`. -/
theorem transfer_primeUnits_eq_frobNorm (hK : Nat.card K = p ^ k) (x : Kˣ) :
    (((transfer (MonoidHom.id (primeUnits K p)) x : primeUnits K p) : Kˣ) : K)
      = frobNorm p k (x : K) := by
  have h := transfer_comm_eq_pow (primeUnits K p) x
  have h2 : (((transfer (MonoidHom.id (primeUnits K p)) x : primeUnits K p) : Kˣ) : K)
      = ((x ^ (primeUnits K p).index : Kˣ) : K) := by rw [h]
  rw [h2, frobNorm_eq_pow, index_primeUnits hK]
  push_cast
  rfl

/-- The index of `𝔽ₚˣ` is congruent to the degree `k` modulo `p - 1`; so on the prime subfield
the transfer is the `k`-th power map, exactly as for the orbit product. -/
theorem index_primeUnits_modEq (hK : Nat.card K = p ^ k) :
    (primeUnits K p).index ≡ k [MOD p - 1] := by
  rw [index_primeUnits hK]
  exact geom_sum_modEq p k ((Fact.out (p := p.Prime)).one_lt.le)

/-- The repair criterion for the field side is `gcd(k, p-1) = 1`, since the index is congruent
to `k` modulo `p - 1`. -/
theorem coprime_index_primeUnits_iff (hK : Nat.card K = p ^ k) :
    Nat.Coprime (primeUnits K p).index (p - 1) ↔ Nat.Coprime k (p - 1) := by
  have h := index_primeUnits_modEq (p := p) hK
  unfold Nat.Coprime
  rw [Nat.gcd_comm _ (p - 1), Nat.gcd_comm k (p - 1), Nat.gcd_rec, Nat.gcd_rec (p - 1) k, h]

/-- **The multiplicative repair, from the transfer.**  If `gcd(k, p-1) = 1` then a power of the
Frobenius orbit product is a retraction of `Kˣ` onto `𝔽ₚˣ`. -/
theorem exists_multiplicative_retraction_of_coprime (hK : Nat.card K = p ^ k)
    (hk : Nat.Coprime k (p - 1)) :
    ∃ r : Kˣ →* primeUnits K p, ∀ z : primeUnits K p, r z = z := by
  refine exists_retraction_of_coprime_index (primeUnits K p) ?_
  rw [card_primeUnits hK]
  exact (coprime_index_primeUnits_iff hK).2 hk

end FieldSide

/-! ### The two halves in one statement -/

/-- **What Frobenius does.**  For a finite field `K` with `p ^ k` elements and any finite group
`G`, one and the same construction — the transfer — produces:

1. the map `G →* Z(G)`, which on the centre is the index power `z ↦ z ^ [G : Z(G)]`;
2. the map `Kˣ →* 𝔽ₚˣ`, which *is* the Frobenius orbit product `x ↦ x · x^p ⋯ x^(p^(k-1))`;

and in both cases the failure to be a retraction is repaired by a power of the map as soon as
the index is coprime to the order of the target. -/
theorem what_frobenius_does {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] [Fintype K] {p k : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ k) :
    (∀ z : center G, transferCenterPow G (z : G) = z ^ (center G).index) ∧
    (∀ x : Kˣ, (((transfer (MonoidHom.id (primeUnits K p)) x : primeUnits K p) : Kˣ) : K)
        = FrobeniusPrimeSubfield.frobNorm p k (x : K)) ∧
    (Nat.Coprime (center G).index (Nat.card (center G)) → HasCenterRetraction G) ∧
    (Nat.Coprime k (p - 1) →
      ∃ r : Kˣ →* primeUnits K p, ∀ z : primeUnits K p, r z = z) :=
  ⟨transferCenterPow_restrict, transfer_primeUnits_eq_frobNorm hK,
    hasCenterRetraction_of_coprime_index, exists_multiplicative_retraction_of_coprime hK⟩

end FrobeniusTransfer
