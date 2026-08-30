{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Finite-sum lemmas for the Bishop constructive reals.
--
-- These are the elementary block/telescope facts about `∑₀` that a
-- constructive Riemann integral needs.  Everything here is proved from the
-- vendored constructive real library; no postulate, no opaque `Set` field
-- and no receipt is used.
--
-- Provenance of the imported carrier: Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer 1985; Agda formalisation by Zachary
-- Murray (arXiv:2205.08354), continued by Viktor Csimma, vendored at
-- `vendor/bishop`.
------------------------------------------------------------------------

module DASHI.Analysis.BishopFiniteSumLemmas where

open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n)
import Data.Nat.Properties as ℕP
open import Data.Integer.Base as ℤ using (ℤ; +_; +≤+)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; *≤*)
import Data.Integer.Properties as ℤP
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; sym; subst; trans)

open import Real
open import RealProperties

------------------------------------------------------------------------
-- Embedding of the naturals, defined recursively so that the successor law
-- is definitional.

natToℝ : ℕ → ℝ
natToℝ zero = 0ℝ
natToℝ (suc n) = natToℝ n + 1ℝ

0≤1ℝ : 0ℝ ≤ 1ℝ
0≤1ℝ = p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (*≤* (+≤+ z≤n))

0≤natToℝ : ∀ n → 0ℝ ≤ natToℝ n
0≤natToℝ zero = ≤-refl
0≤natToℝ (suc n) =
  ≤-respˡ-≃ (+-identityˡ 0ℝ) (+-mono-≤ (0≤natToℝ n) 0≤1ℝ)

------------------------------------------------------------------------
-- Pointwise congruence.

∑₀-congruent :
  ∀ {f g : ℕ → ℝ} → (∀ i → f i ≃ g i) → ∀ n → ∑₀ f n ≃ ∑₀ g n
∑₀-congruent f≃g zero = ≃-refl
∑₀-congruent f≃g (suc n) = +-cong (∑₀-congruent f≃g n) (f≃g n)

------------------------------------------------------------------------
-- Splitting a sum at an arbitrary index.

∑₀-shift-split :
  ∀ (f : ℕ → ℝ) (m p : ℕ) →
  ∑₀ f (m ℕ.+ p) ≃ ∑₀ f m + ∑₀ (λ k → f (m ℕ.+ k)) p
∑₀-shift-split f m zero =
  subst (λ z → ∑₀ f z ≃ ∑₀ f m + 0ℝ) (sym (ℕP.+-identityʳ m))
    (≃-symm (+-identityʳ (∑₀ f m)))
∑₀-shift-split f m (suc p) =
  subst (λ z → ∑₀ f z ≃ ∑₀ f m + (∑₀ (λ k → f (m ℕ.+ k)) p + f (m ℕ.+ p)))
    (sym (ℕP.+-suc m p))
    (≃-trans
      (+-congˡ (f (m ℕ.+ p)) (∑₀-shift-split f m p))
      (+-assoc (∑₀ f m) (∑₀ (λ k → f (m ℕ.+ k)) p) (f (m ℕ.+ p))))

------------------------------------------------------------------------
-- Decomposition of a sum of length n * p into n blocks of length p.

∑₀-block :
  ∀ (f : ℕ → ℝ) (n p : ℕ) →
  ∑₀ f (n ℕ.* p) ≃ ∑₀ (λ i → ∑₀ (λ k → f (i ℕ.* p ℕ.+ k)) p) n
∑₀-block f zero p = ≃-refl
∑₀-block f (suc n) p =
  subst
    (λ z → ∑₀ f z ≃ ∑₀ (λ i → ∑₀ (λ k → f (i ℕ.* p ℕ.+ k)) p) n
                    + ∑₀ (λ k → f (n ℕ.* p ℕ.+ k)) p)
    (ℕP.+-comm (n ℕ.* p) p)
    (≃-trans (∑₀-shift-split f (n ℕ.* p) p)
      (+-congˡ (∑₀ (λ k → f (n ℕ.* p ℕ.+ k)) p) (∑₀-block f n p)))

------------------------------------------------------------------------
-- Triangle inequality for finite sums.

∑₀-abs :
  ∀ (f : ℕ → ℝ) (n : ℕ) → ∣ ∑₀ f n ∣ ≤ ∑₀ (λ i → ∣ f i ∣) n
∑₀-abs f zero = ≤-reflexive (nonNegx⇒∣x∣≃x (0≤x⇒nonNegx ≤-refl))
∑₀-abs f (suc n) =
  ≤-trans (∣x+y∣≤∣x∣+∣y∣ (∑₀ f n) (f n))
    (+-mono-≤ (∑₀-abs f n) ≤-refl)

------------------------------------------------------------------------
-- A constant bound on the summands gives a linear bound on the sum.

∑₀-const-bound :
  ∀ (f : ℕ → ℝ) (c : ℝ) → (∀ i → f i ≤ c) → ∀ n → ∑₀ f n ≤ natToℝ n * c
∑₀-const-bound f c bound zero = ≤-reflexive (≃-symm (*-zeroˡ c))
∑₀-const-bound f c bound (suc n) =
  ≤-respʳ-≃ step (+-mono-≤ (∑₀-const-bound f c bound n) (bound n))
  where
  step : natToℝ n * c + c ≃ (natToℝ n + 1ℝ) * c
  step = ≃-symm
    (≃-trans (*-distribʳ-+ c (natToℝ n) 1ℝ)
      (+-congʳ (natToℝ n * c) (*-identityˡ c)))

------------------------------------------------------------------------
-- Sums commute with differences.

∑₀-sub :
  ∀ (f g : ℕ → ℝ) (n : ℕ) →
  ∑₀ (λ i → f i - g i) n ≃ ∑₀ f n - ∑₀ g n
∑₀-sub f g zero = ≃-symm (+-inverseʳ 0ℝ)
∑₀-sub f g (suc n) = ≃-trans
  (+-congˡ (f n - g n) (∑₀-sub f g n))
  (solve 4 (λ a b c d → (a ⊖ b) ⊕ (c ⊖ d) ⊜ (a ⊕ c) ⊖ (b ⊕ d))
    ≃-refl (∑₀ f n) (∑₀ g n) (f n) (g n))
  where open ℝ-Solver

------------------------------------------------------------------------
-- The natural-number embedding agrees with the rational embedding.

natToℝ-⋆ : ∀ n → natToℝ n ≃ (+ n ℚ./ 1) ⋆
natToℝ-⋆ zero = ≃-refl
natToℝ-⋆ (suc n) = ≃-trans
  (+-congˡ 1ℝ (natToℝ-⋆ n))
  (≃-trans (≃-symm (⋆-distrib-+ (+ n ℚ./ 1) 1ℚᵘ))
           (⋆-cong (ℚ.*≡* eqn)))
  where
  eqn : (+ n ℤ.* + 1 ℤ.+ + 1 ℤ.* + 1) ℤ.* + 1 ≡ + suc n ℤ.* + 1
  eqn = trans (ℤP.*-identityʳ _)
        (trans (cong₂ ℤ._+_ (ℤP.*-identityʳ (+ n)) (ℤP.*-identityʳ (+ 1)))
        (trans (sym (ℤP.pos-+ n 1))
        (trans (cong +_ (ℕP.+-comm n 1))
               (sym (ℤP.*-identityʳ (+ suc n))))))

------------------------------------------------------------------------
-- Sum of a constant, and pulling a scalar out of a sum.

∑₀-const : ∀ (c : ℝ) n → ∑₀ (λ _ → c) n ≃ natToℝ n * c
∑₀-const c zero = ≃-symm (*-zeroˡ c)
∑₀-const c (suc n) = ≃-trans (+-congˡ c (∑₀-const c n))
  (≃-symm (≃-trans (*-distribʳ-+ c (natToℝ n) 1ℝ)
                   (+-congʳ (natToℝ n * c) (*-identityˡ c))))

∑₀-scale : ∀ (c : ℝ) (f : ℕ → ℝ) n → ∑₀ (λ i → c * f i) n ≃ c * ∑₀ f n
∑₀-scale c f zero = ≃-symm (*-zeroʳ c)
∑₀-scale c f (suc n) = ≃-trans (+-congˡ (c * f n) (∑₀-scale c f n))
  (≃-symm (*-distribˡ-+ c (∑₀ f n) (f n)))

-- The same bound, needed only on the indices that actually occur.

∑₀-const-bound-lt :
  ∀ (f : ℕ → ℝ) (c : ℝ) (n : ℕ) →
  (∀ i → i ℕ.< n → f i ≤ c) → ∑₀ f n ≤ natToℝ n * c
∑₀-const-bound-lt f c zero bound = ≤-reflexive (≃-symm (*-zeroˡ c))
∑₀-const-bound-lt f c (suc n) bound =
  ≤-respʳ-≃ step
    (+-mono-≤ (∑₀-const-bound-lt f c n
                 (λ i i<n → bound i (ℕP.<-trans i<n (ℕP.n<1+n n))))
              (bound n (ℕP.n<1+n n)))
  where
  step : natToℝ n * c + c ≃ (natToℝ n + 1ℝ) * c
  step = ≃-symm
    (≃-trans (*-distribʳ-+ c (natToℝ n) 1ℝ)
      (+-congʳ (natToℝ n * c) (*-identityˡ c)))
