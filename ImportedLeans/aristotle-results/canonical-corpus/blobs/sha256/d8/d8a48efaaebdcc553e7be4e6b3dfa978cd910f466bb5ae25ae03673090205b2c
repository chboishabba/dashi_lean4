-- A collection of extra properties about naturals, integers, and rationals
-- that were useful in constructing the rest of the library.

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_; case_of_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod as ℤD hiding (_/_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step; n<1+n)
import Data.Nat.DivMod as ℕD
open import Data.Nat.Solver renaming (module +-*-Solver to ℕ-Solver)
open import Level using (0ℓ)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _/_; 0ℚᵘ; 1ℚᵘ; ↥_; ↧_; ↧ₙ_; _<_; *<*)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base

import NonReflectiveQ as ℚ-Solver
import NonReflectiveZ as ℤ-Solver

open import Data.List

_≢0 : ℕ → Set
n ≢0 = n ≢ 0

open ℚᵘ

∣p-q∣≃∣q-p∣ : ∀ p q -> ℚ.∣ p ℚ.- q ∣ ℚ.≃ ℚ.∣ q ℚ.- p ∣
∣p-q∣≃∣q-p∣ p q = begin
  ℚ.∣ p ℚ.- q ∣       ≈⟨ ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (p ℚ.- q)) ⟩
  ℚ.∣ ℚ.- (p ℚ.- q) ∣ ≈⟨ ℚP.∣-∣-cong (solve 2 (λ p q ->
                         (⊝ (p ⊖ q)) ⊜ (q ⊖ p)) ℚP.≃-refl p q) ⟩
  ℚ.∣ q ℚ.- p ∣        ∎
  where
    open ℚP.≃-Reasoning
    open ℚ-Solver

m≤∣m∣ : ∀ m -> m ℤ.≤ + ℤ.∣ m ∣
m≤∣m∣ (+_ n) = ℤP.≤-refl
m≤∣m∣ (-[1+_] n) = ℤ.-≤+

antidensity-ℤ : ¬(∃ λ (n : ℤ) -> + 0 ℤ.< n × n ℤ.< + 1)
antidensity-ℤ (.(+[1+ n ]) , ℤ.+<+ {n = suc n} m<n , ℤ.+<+ (ℕ.s≤s ()))

p≤∣p∣ : ∀ p -> p ℚ.≤ ℚ.∣ p ∣
p≤∣p∣ (mkℚᵘ (+_ n) denominator-2) = ℚP.≤-refl
p≤∣p∣ (mkℚᵘ (-[1+_] n) denominator-2) = ℚ.*≤* ℤ.-≤+

archimedean-ℚ : ∀ p r -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r ℚ.< ((+ N) ℤ.* ↥ p) ℚ./ (↧ₙ p)
archimedean-ℚ (mkℚᵘ +[1+ g ] q-1) (mkℚᵘ u v-1) posp =
  let p = suc g; q = suc q-1; v = suc v-1
      r = (u ℤ.* + q) %ℕ (p ℕ.* v); t = (u ℤ.* + q) /ℕ (p ℕ.* v)
      open ℤ-Solver
      eq1 = a≡a%ℕn+[a/ℕn]*n (u ℤ.* + q) (p ℕ.* v)
      lt1 = ℤP.+-monoˡ-< (t ℤ.* + (p ℕ.* v)) (ℤ.+<+ (n%ℕd<d (u ℤ.* + q) (p ℕ.* v)))
      eq2 = solve 3 (λ p v t -> ((p ⊗ v) ⊕ (t ⊗ (p ⊗ v))) ⊜ ((Κ (+ 1) ⊕ t) ⊗ (p ⊗ v))) refl (+ p) (+ v) t
      le1 = ℤP.*-monoʳ-≤-nonNeg (+ p ℤ.* + v) {{ℤ.nonNeg}} (m≤∣m∣ (+ 1 ℤ.+ t))
      le2 = ℤP.*-monoʳ-≤-nonNeg (+ p ℤ.* + v) {{ℤ.nonNeg}} (ℤ.+≤+ (ℤP.∣i+j∣≤∣i∣+∣j∣ (+ 1) t))
      eq3 = sym (ℤP.*-assoc (+ suc ℤ.∣ t ∣) (+ p) (+ v))

      lt2 = subst (ℤ._< + (p ℕ.* v) ℤ.+ t ℤ.* + (p ℕ.* v)) (sym eq1) lt1
      lt3 = subst (u ℤ.* + q ℤ.<_) eq2 lt2
      lt4 = ℤP.<-≤-trans lt3 le1
      lt5 = ℤP.<-≤-trans lt4 le2
      proof = subst (u ℤ.* + q ℤ.<_) eq3 lt5
  in suc ℤ.∣ t ∣ , ℚ.*<* proof

abstract
  fast-archimedean-ℚ : ∀ p r -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r ℚ.< ((+ N) ℤ.* ↥ p) ℚ./ (↧ₙ p)
  fast-archimedean-ℚ = archimedean-ℚ

q≤r⇒+p/r≤+p/q : ∀ p q r ⦃ q≢0 : ℕ.NonZero q ⦄ ⦃ r≢0 : ℕ.NonZero r ⦄ -> q ℕ.≤ r -> (+ p / r) ℚ.≤ (+ p / q)
q≤r⇒+p/r≤+p/q p (suc k₁) (suc k₂) q≤r = ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg (+ p) {{ℤ.nonNeg}} (ℤ.+≤+ q≤r))


q<r⇒+p/r<+p/q : ∀ p q r ⦃ p≢0 : ℕ.NonZero p ⦄ ⦃ q≢0 : ℕ.NonZero q ⦄ ⦃ r≢0 : ℕ.NonZero r ⦄ -> q ℕ.< r -> (+ p / r) ℚ.< (+ p / q)
q<r⇒+p/r<+p/q (suc k₁) (suc k₂) (suc k₃) q<r = ℚ.*<* (ℤP.*-monoˡ-<-pos (+ suc k₁) {{_}} (ℤ.+<+ q<r))

p≤q⇒p/r≤q/r : ∀ (p q : ℤ) -> ∀ (r : ℕ) ⦃ r≢0 : ℕ.NonZero r ⦄ -> p ℤ.≤ q -> (p / r) ℚ.≤ (q / r)
p≤q⇒p/r≤q/r p q (suc k₁) p≤q = ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg (+ suc k₁) {{ℤ.nonNeg}} p≤q)

p<q⇒p/r<q/r : (p q : ℤ) (r : ℕ) ⦃ r≢0 : ℕ.NonZero r ⦄ → p ℤ.< q → (p / r) ℚ.< (q / r)
p<q⇒p/r<q/r p q (suc r-1) p<q = ℚ.*<* (ℤP.*-monoʳ-<-pos (+ suc r-1) {{_}} p<q)

lemma-den : ∀ N-1 q-1 → suc ((q-1 ℕ.+ N-1) ℕ.+ q-1 ℕ.* N-1) ≡ suc N-1 ℕ.* suc q-1
lemma-den N-1 q-1 = let open ℕ-Solver in solve 2 (λ a b → (con 1 :+ ((b :+ a) :+ (b :* a))) := (con 1 :+ a) :* (con 1 :+ b)) refl N-1 q-1

lemma-archimedean-eq2 : ∀ N-1 p-1 q-1 → (suc N-1 ℕ.* suc p-1) ℕ.* 1 ℕ.* suc q-1 ≡ suc p-1 ℕ.* (suc q-1 ℕ.* suc N-1)
lemma-archimedean-eq2 N-1 p-1 q-1 = let N = suc N-1; p = suc p-1; q = suc q-1; open ≡-Reasoning in begin
  (N ℕ.* p) ℕ.* 1 ℕ.* q               ≡⟨ cong (λ x → x ℕ.* q) (ℕP.*-identityʳ (N ℕ.* p)) ⟩
  (N ℕ.* p) ℕ.* q                       ≡⟨ ℕP.*-assoc N p q ⟩
  N ℕ.* (p ℕ.* q)                       ≡⟨ cong (N ℕ.*_) (ℕP.*-comm p q) ⟩
  N ℕ.* (q ℕ.* p)                       ≡⟨ sym (ℕP.*-assoc N q p) ⟩
  (N ℕ.* q) ℕ.* p                       ≡⟨ ℕP.*-comm (N ℕ.* q) p ⟩
  p ℕ.* (N ℕ.* q)                       ≡⟨ cong (p ℕ.*_) (ℕP.*-comm N q) ⟩
  p ℕ.* (q ℕ.* N)                       ∎

lemma-eq1 : ∀ n N-1 → (n ℕ.+ 0) ℕ.* suc N-1 ≡ n ℕ.* suc N-1
lemma-eq1 n N-1 = cong (λ x → x ℕ.* suc N-1) (ℕP.+-identityʳ n)

lemma-eq1-neg : ∀ n N-1 → (n ℕ.+ 0) ℕ.* suc N-1 ℕ.+ N-1 ≡ n ℕ.* suc N-1 ℕ.+ N-1
lemma-eq1-neg n N-1 = cong (λ x → x ℕ.+ N-1) (lemma-eq1 n N-1)

archimedean-ℚ₂ : ∀ (p : ℚᵘ) -> ∀ (r : ℤ) -> ℚ.Positive p -> ∃ λ (N-1 : ℕ) -> r / (suc N-1) ℚ.< p
archimedean-ℚ₂ (mkℚᵘ (+_ zero) q-1) r ()
archimedean-ℚ₂ (mkℚᵘ (+_ (suc p-1)) q-1) r posp/q = N-1 , lt1
  where
    p = suc p-1; q = suc q-1; origP = mkℚᵘ (+ p) q-1
    N-1 = proj₁ (fast-archimedean-ℚ origP (r / 1) posp/q)
    N = suc N-1
    rq<Np+1 : (r ℤ.* + q) ℤ.< ((+ N-1 ℤ.* + p) ℤ.* + 1)
    rq<Np+1 = case proj₂ (fast-archimedean-ℚ origP (r / 1) posp/q) of λ where (ℚ.*<* p) → p
    rq<Np : (r ℤ.* + q) ℤ.< (+ N-1 ℤ.* + p)
    rq<Np = subst (λ y → (r ℤ.* + q) ℤ.< y) (ℤP.*-identityʳ (+ N-1 ℤ.* + p)) rq<Np+1
    r<pN-1 : (r ℤ.* + q) ℤ.< (+ p ℤ.* + N-1)
    r<pN-1 = subst (λ y → (r ℤ.* + q) ℤ.< y) (ℤP.*-comm (+ N-1) (+ p)) rq<Np
    +pN-1<+pN : (+ p ℤ.* + N-1) ℤ.< (+ p ℤ.* + N)
    +pN-1<+pN = ℤP.*-monoˡ-<-pos (+ p) {{posp/q}} (ℤ.+<+ (ℕP.n<1+n N-1))
    lt1 : r / N ℚ.< origP
    lt1 = ℚ.*<* (ℤP.<-trans r<pN-1 +pN-1<+pN)

abstract
  fast-archimedean-ℚ₂ : ∀ (p : ℚᵘ) -> ∀ (r : ℤ) -> ℚ.Positive p -> ∃ λ (N-1 : ℕ) -> r / (suc N-1) ℚ.< p
  fast-archimedean-ℚ₂ = archimedean-ℚ₂

p<q⇒0<q-p : ∀ p q -> p ℚ.< q -> 0ℚᵘ ℚ.< q ℚ.- p
p<q⇒0<q-p p q p<q = begin-strict
  0ℚᵘ     ≃⟨ ℚP.≃-sym (ℚP.+-inverseʳ p) ⟩
  p ℚ.- p <⟨ ℚP.+-monoˡ-< (ℚ.- p) p<q ⟩
  q ℚ.- p  ∎
  where open ℚP.≤-Reasoning

∣∣p∣-∣q∣∣≤∣p-q∣ : ∀ p q -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
∣∣p∣-∣q∣∣≤∣p-q∣ p q = [ left p q , right p q ]′ (ℚP.≤-total ℚ.∣ q ∣ ℚ.∣ p ∣)
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

    left : ∀ p q -> ℚ.∣ q ∣ ℚ.≤ ℚ.∣ p ∣ -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
    left p q hyp = begin
      ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣             ≃⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp) ⟩
      ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣                   ≃⟨ ℚP.+-congˡ (ℚ.- ℚ.∣ q ∣) (ℚP.∣-∣-cong (solve 2 (λ p q ->
                                               p ⊜ (p ⊖ q ⊕ q)) ℚP.≃-refl p q)) ⟩
      ℚ.∣ p ℚ.- q ℚ.+ q ∣ ℚ.- ℚ.∣ q ∣       ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- ℚ.∣ q ∣) (ℚP.∣p+q∣≤∣p∣+∣q∣ (p ℚ.- q) q) ⟩
      ℚ.∣ p ℚ.- q ∣ ℚ.+ ℚ.∣ q ∣ ℚ.- ℚ.∣ q ∣ ≃⟨ solve 2 (λ x y -> x ⊕ y ⊖ y ⊜ x)
                                              ℚP.≃-refl ℚ.∣ p ℚ.- q ∣ ℚ.∣ q ∣ ⟩
      ℚ.∣ p ℚ.- q ∣ ∎

    right : ∀ p q -> ℚ.∣ p ∣ ℚ.≤ ℚ.∣ q ∣ -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
    right p q hyp = begin
      ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ≃⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣))) (ℚP.∣-∣-cong
                                  (solve 2 (λ p q -> ⊝ (p ⊖ q) ⊜ (q ⊖ p)) ℚP.≃-refl ℚ.∣ p ∣ ℚ.∣ q ∣)) ⟩
      ℚ.∣ ℚ.∣ q ∣ ℚ.- ℚ.∣ p ∣ ∣ ≤⟨ left q p hyp ⟩
      ℚ.∣ q ℚ.- p ∣            ≃⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (q ℚ.- p))) (ℚP.∣-∣-cong
                                  (solve 2 (λ p q -> ⊝ (q ⊖ p) ⊜ (p ⊖ q)) ℚP.≃-refl p q)) ⟩
      ℚ.∣ p ℚ.- q ∣  ∎

least-ℤ>ℚ : ∀ (p : ℚᵘ) -> ∃ λ (K : ℤ) ->
            p ℚ.< K / 1 × ∀ (n : ℤ) -> p ℚ.< n / 1 -> K ℤ.≤ n
least-ℤ>ℚ p/q = let p = ↥ p/q; q = ↧ₙ p/q; r = p %ℕ q; t = p /ℕ q in + 1 ℤ.+ t , greater , least
  where
    open ℤP.≤-Reasoning
    open ℤ-Solver
    greater : p/q ℚ.< (+ 1 ℤ.+ (↥ p/q /ℕ ↧ₙ p/q)) / 1
    greater = let p = ↥ p/q; q = ↧ₙ p/q; r = p %ℕ q; t = p /ℕ q in ℚ.*<* (begin-strict
      p ℤ.* + 1           ≡⟨ trans (ℤP.*-identityʳ p) (a≡a%ℕn+[a/ℕn]*n p q) ⟩
      + r ℤ.+ t ℤ.* + q   <⟨ ℤP.+-monoˡ-< (t ℤ.* (+ q)) (ℤ.+<+ (n%ℕd<d p q)) ⟩
      + q ℤ.+ t ℤ.* + q   ≡⟨ solve 2 (λ q t -> q ⊕ t ⊗ q ⊜ (Κ (+ 1) ⊕ t) ⊗ q) _≡_.refl (+ q) t ⟩
      (+ 1 ℤ.+ t) ℤ.* + q  ∎)

    least : ∀ (n : ℤ) -> p/q ℚ.< n / 1 -> + 1 ℤ.+ (↥ p/q /ℕ ↧ₙ p/q) ℤ.≤ n
    least n p/q<n = ℤP.≮⇒≥ (λ {hyp -> antidensity-ℤ (n ℤ.- (↥ p/q /ℕ ↧ₙ p/q) , zero<n-t hyp , n-t<1 hyp)})
      where
        zero<n-t : n ℤ.< + 1 ℤ.+ (↥ p/q /ℕ ↧ₙ p/q) -> + 0 ℤ.< n ℤ.- (↥ p/q /ℕ ↧ₙ p/q)
        zero<n-t hyp = let p = ↥ p/q; q = ↧ₙ p/q; r = p %ℕ q; t = p /ℕ q in ℤP.*-cancelʳ-<-nonNeg (+ q) (begin-strict
          + 0 ℤ.* + q                     ≡⟨ ℤP.*-zeroˡ (+ q) ⟩
          + 0                             ≤⟨ ℤ.+≤+ ℕ.z≤n ⟩
          + r                             ≡⟨ solve 3 (λ r t q -> r ⊜ (r ⊕ t ⊗ q ⊖ t ⊗ q)) _≡_.refl (+ r) t (+ q) ⟩
          + r ℤ.+ t ℤ.* + q ℤ.- t ℤ.* + q ≡⟨ cong (λ x -> x ℤ.- t ℤ.* + q) (sym (a≡a%ℕn+[a/ℕn]*n p q)) ⟩
          p ℤ.- t ℤ.* + q                 <⟨ ℤP.+-monoˡ-< (ℤ.- (t ℤ.* + q)) (subst (ℤ._< n ℤ.* + q) (ℤP.*-identityʳ p) (ℚP.drop-*<* p/q<n)) ⟩
          n ℤ.* + q ℤ.- t ℤ.* + q         ≡⟨ solve 3 (λ n t q -> n ⊗ q ⊖ t ⊗ q ⊜ (n ⊖ t) ⊗ q) _≡_.refl n t (+ q) ⟩
          (n ℤ.- t) ℤ.* + q                ∎)

        n-t<1 : n ℤ.< + 1 ℤ.+ (↥ p/q /ℕ ↧ₙ p/q) -> n ℤ.- (↥ p/q /ℕ ↧ₙ p/q) ℤ.< + 1
        n-t<1 hyp = let t = ↥ p/q /ℕ ↧ₙ p/q in begin-strict
          n ℤ.- t         <⟨ ℤP.+-monoˡ-< (ℤ.- t) hyp ⟩
          + 1 ℤ.+ t ℤ.- t ≡⟨ solve 1 (λ t -> Κ (+ 1) ⊕ t ⊖ t ⊜ Κ (+ 1)) _≡_.refl t ⟩
          + 1              ∎

2ℚᵘ : ℚᵘ
2ℚᵘ = + 2 / 1

1/n≤1 : ∀ (n : ℕ) -> .{{_ : ℕ.NonZero n}} -> (+ 1 / n) ℚ.≤ 1ℚᵘ
1/n≤1 (suc k₁) = ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg (+ 1) {{ℤ.nonNeg}} {+ 1} {+ n} (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n))) where n = suc k₁

p≤r⇒p/q≤r/q : ∀ (p r : ℤ) -> ∀ (q : ℕ) -> .{{_ : ℕ.NonZero q}} -> p ℤ.≤ r -> (p / q) ℚ.≤ (r / q)
p≤r⇒p/q≤r/q p r (suc k₁) p≤r = let q = suc k₁ in ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg (+ q) {{ℤ.nonNeg}} p≤r)

p-q≤j⁻¹⇒p≤q : ∀ {p q : ℚᵘ} ->
              (∀ (j : ℕ) -> .{{_ : ℕ.NonZero j}} -> p ℚ.- q ℚ.≤ (+ 1 / j)) -> p ℚ.≤ q
p-q≤j⁻¹⇒p≤q {p} {q} hyp = ℚP.≮⇒≥ λ q<p -> let arch = fast-archimedean-ℚ₂ (p ℚ.- q) (+ 1) (ℚ.positive (p<q⇒0<q-p q p q<p)); j = suc (proj₁ arch) in
                      ℚP.<⇒≱ (proj₂ arch) (hyp j)

p-j⁻¹≤q⇒p≤q : ∀ {p q : ℚᵘ} -> (∀ (j : ℕ) -> .{{_ : ℕ.NonZero j}} -> p ℚ.- (+ 1 / j) ℚ.≤ q) -> p ℚ.≤ q
p-j⁻¹≤q⇒p≤q {p} {q} hyp = p-q≤j⁻¹⇒p≤q λ { (suc k₁) -> let j = suc k₁ in begin
  p ℚ.- q                         ≃⟨ solve 3 (λ p q j⁻¹ ->
                                     (p ⊖ q) ⊜ (p ⊖ j⁻¹ ⊖ q ⊕ j⁻¹))
                                     ℚP.≃-refl p q (+ 1 / j) ⟩
  p ℚ.- + 1 / j ℚ.- q ℚ.+ + 1 / j ≤⟨ ℚP.+-monoˡ-≤ (+ 1 / j) (ℚP.+-monoˡ-≤ (ℚ.- q) (hyp j)) ⟩
  q ℚ.- q ℚ.+ + 1 / j             ≃⟨ solve 2 (λ q j⁻¹ -> (q ⊖ q ⊕ j⁻¹) ⊜ j⁻¹) ℚP.≃-refl q (+ 1 / j) ⟩
  + 1 / j  ∎}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

ℚ-*-mono-≤ : ∀ {p q r s} -> .{{ℚ.NonNegative p}} -> .{{ℚ.NonNegative r}} ->
             p ℚ.≤ q -> r ℚ.≤ s -> p ℚ.* r ℚ.≤ q ℚ.* s
ℚ-*-mono-≤ {p} {q} {r} {s} p≤q r≤s = begin
   p ℚ.* r ≤⟨ ℚP.*-monoˡ-≤-nonNeg r p≤q ⟩
   q ℚ.* r ≤⟨ ℚP.*-monoʳ-≤-nonNeg q {{ℚ.nonNegative (ℚP.≤-trans (ℚP.nonNegative⁻¹ p) p≤q)}} r≤s ⟩
  q ℚ.* s  ∎
  where open ℚP.≤-Reasoning

ℚ≠-helper : ∀ p -> p ℚ.> 0ℚᵘ ⊎ p ℚ.< 0ℚᵘ -> p ℚ.≄ 0ℚᵘ
ℚ≠-helper p hyp1 = [ (λ p>0 p≃0 -> ℚP.<-irrefl (ℚP.≃-sym p≃0) p>0) , (λ p<0 p≃0 -> ℚP.<-irrefl p≃0 p<0) ]′ hyp1

m<n*m : ∀ {m n} -> 0 ℕ.< m -> 1 ℕ.< n -> m ℕ.< n ℕ.* m
m<n*m {m} {n} 0<m 1<n = subst (m ℕ.<_) (ℕP.*-comm m n) (ℕP.m<m*n m n {{ℕ.>-nonZero 0<m}} 1<n)

∣p∣≃p⊔-p : ∀ p -> ℚ.∣ p ∣ ℚ.≃ p ℚ.⊔ (ℚ.- p)
∣p∣≃p⊔-p p = [ left , right ]′ (ℚP.≤-total 0ℚᵘ p)
  where
    left : 0ℚᵘ ℚ.≤ p -> ℚ.∣ p ∣ ℚ.≃ p ℚ.⊔ ℚ.- p
    left 0≤p = let ∣p∣≃p = ℚP.0≤p⇒∣p∣≃p 0≤p in
      ℚP.≃-trans ∣p∣≃p (ℚP.≃-sym (ℚP.p≥q⇒p⊔q≃p
        (ℚP.≤-respʳ-≃ ∣p∣≃p (ℚP.≤-respʳ-≃ (ℚP.∣-p∣≃∣p∣ p) (p≤∣p∣ (ℚ.- p))))))

    right : p ℚ.≤ 0ℚᵘ -> ℚ.∣ p ∣ ℚ.≃ p ℚ.⊔ ℚ.- p
    right p≤0 = let ∣p∣≃-p = ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ p)) (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ p≤0)) in
      ℚP.≃-trans ∣p∣≃-p (ℚP.≃-sym (ℚP.p≤q⇒p⊔q≃q (ℚP.≤-respʳ-≃ ∣p∣≃-p (p≤∣p∣ p))))

≤⇒≡∨< : ∀ (m n : ℕ) -> m ℕ.≤ n -> m ≡ n ⊎ m ℕ.< n
≤⇒≡∨< zero zero m≤n = inj₁ _≡_.refl
≤⇒≡∨< zero (suc n) m≤n = inj₂ ℕP.0<1+n
≤⇒≡∨< (suc m) (suc n) (ℕ.s≤s m≤n) = [ (λ m≡n -> inj₁ (cong suc m≡n)) , (λ m<n -> inj₂ (ℕ.s≤s m<n)) ]′ (≤⇒≡∨< m n m≤n)

≤∨> : ∀ p q -> p ℚ.≤ q ⊎ q ℚ.< p  
≤∨> p q with p ℚP.≤? q
... | .Bool.true because ofʸ p₁ = inj₁ p₁
... | .Bool.false because ofⁿ ¬p = inj₂ (ℚP.≰⇒> ¬p)

½+½≃1 : (+ 1 / 2) ℚ.+ (+ 1 / 2) ℚ.≃ 1ℚᵘ
½+½≃1 = ℚ.*≡* refl

½r+½r≃r : ∀ r -> (+ 1 / 2) ℚ.* r ℚ.+ (+ 1 / 2) ℚ.* r ℚ.≃ r
½r+½r≃r r = begin-equality
  (+ 1 / 2) ℚ.* r ℚ.+ (+ 1 / 2) ℚ.* r
    ≃⟨ ℚP.≃-sym (ℚP.*-distribʳ-+ r (+ 1 / 2) (+ 1 / 2)) ⟩
  ((+ 1 / 2) ℚ.+ (+ 1 / 2)) ℚ.* r
    ≃⟨ ℚP.*-congʳ {x = r} ½+½≃1 ⟩
  1ℚᵘ ℚ.* r
    ≃⟨ ℚP.*-identityˡ r ⟩
  r ∎
  where open ℚP.≤-Reasoning

½r≃r-½r : ∀ r -> (+ 1 / 2) ℚ.* r ℚ.≃ r ℚ.- (+ 1 / 2) ℚ.* r
½r≃r-½r r = ℚP.≃-sym (begin-equality
   r ℚ.- (+ 1 / 2) ℚ.* r
     ≃⟨ ℚP.+-comm r (ℚ.- ((+ 1 / 2) ℚ.* r)) ⟩
   (ℚ.- ((+ 1 / 2) ℚ.* r)) ℚ.+ r
     ≃⟨ ℚP.+-congʳ (ℚ.- ((+ 1 / 2) ℚ.* r)) (ℚP.≃-sym (½r+½r≃r r)) ⟩
   (ℚ.- ((+ 1 / 2) ℚ.* r)) ℚ.+ ((+ 1 / 2) ℚ.* r ℚ.+ (+ 1 / 2) ℚ.* r)
     ≃⟨ ℚP.≃-sym (ℚP.+-assoc (ℚ.- ((+ 1 / 2) ℚ.* r)) ((+ 1 / 2) ℚ.* r) ((+ 1 / 2) ℚ.* r)) ⟩
   ((ℚ.- ((+ 1 / 2) ℚ.* r)) ℚ.+ (+ 1 / 2) ℚ.* r) ℚ.+ (+ 1 / 2) ℚ.* r
     ≃⟨ ℚP.+-congˡ ((+ 1 / 2) ℚ.* r) (ℚP.+-inverseˡ ((+ 1 / 2) ℚ.* r)) ⟩
   0ℚᵘ ℚ.+ (+ 1 / 2) ℚ.* r
     ≃⟨ ℚP.+-identityˡ ((+ 1 / 2) ℚ.* r) ⟩
   (+ 1 / 2) ℚ.* r ∎)
  where open ℚP.≤-Reasoning

p+q>r⇒p>2⁻¹r∨q>2⁻¹r : ∀ p q r -> p ℚ.+ q ℚ.> r -> p ℚ.> (+ 1 / 2) ℚ.* r ⊎ q ℚ.> (+ 1 / 2) ℚ.* r
p+q>r⇒p>2⁻¹r∨q>2⁻¹r p q r p+q>r = [ (λ hyp -> inj₁ (lem hyp)) , (λ hyp -> inj₂ hyp) ]′ (≤∨> q ((+ 1 / 2) ℚ.* r))
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

    lem : q ℚ.≤ (+ 1 / 2) ℚ.* r -> p ℚ.> (+ 1 / 2) ℚ.* r
    lem hyp = begin-strict
      (+ 1 / 2) ℚ.* r                             ≃⟨ ½r≃r-½r r ⟩
      r ℚ.- (+ 1 / 2) ℚ.* r                       <⟨ ℚP.+-monoˡ-< (ℚ.- ((+ 1 / 2) ℚ.* r)) p+q>r ⟩
      (p ℚ.+ q) ℚ.- (+ 1 / 2) ℚ.* r               ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- (+ 1 / 2 ℚ.* r)) (ℚP.+-monoʳ-≤ p hyp) ⟩
      (p ℚ.+ (+ 1 / 2) ℚ.* r) ℚ.- (+ 1 / 2) ℚ.* r ≃⟨ solve 2 (λ p 2⁻¹r -> (p ⊕ 2⁻¹r ⊖ 2⁻¹r) ⊜ p) ℚP.≃-refl p ((+ 1 / 2) ℚ.* r) ⟩
      p                                            ∎

0<q-p⇒p<q : ∀ p q -> 0ℚᵘ ℚ.< q ℚ.- p -> p ℚ.< q
0<q-p⇒p<q p q 0<q-p = begin-strict
  p               ≃⟨ ℚP.≃-sym (ℚP.+-identityʳ p) ⟩
  p ℚ.+ 0ℚᵘ       <⟨ ℚP.+-monoʳ-< p 0<q-p ⟩
  p ℚ.+ (q ℚ.- p) ≃⟨ solve 2 (λ p q -> (p ⊕ (q ⊖ p)) ⊜ q) ℚP.≃-refl p q ⟩
  q                ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

p-q≥j⁻¹⇒p≥q : ∀ {p q : ℚᵘ} ->
              (∀ (j : ℕ) -> .{{_ : ℕ.NonZero j}} -> p ℚ.- q ℚ.≥ (+ 1 / j)) -> p ℚ.≥ q
p-q≥j⁻¹⇒p≥q {p} {q} hyp = ℚP.≮⇒≥ (λ p<q -> let arch = fast-archimedean-ℚ₂ (q ℚ.- p) (+ 1) (ℚ.positive (p<q⇒0<q-p p q p<q))
                                                    ; j = suc (proj₁ arch) in
                          ℚP.<-irrefl ℚP.≃-refl (begin-strict
  0ℚᵘ           <⟨ ℚP.positive⁻¹ _ ⟩
  + 1 / j       ≤⟨ hyp j ⟩
  p ℚ.- q       ≃⟨ solve 2 (λ p q -> (p ⊖ q) ⊜ (⊝ (q ⊖ p))) ℚP.≃-refl p q ⟩
  ℚ.- (q ℚ.- p) <⟨ ℚP.neg-mono-< (proj₂ arch) ⟩
  ℚ.- (+ 1 / j) <⟨ ℚP.negative⁻¹ _ ⟩
  0ℚᵘ            ∎))
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

0<n⇒n≢0 : ∀ n -> 0 ℕ.< n -> n ≢0
0<n⇒n≢0 (suc n-1) 0<n = λ ()

m<1+n⇒m≤n : ∀ m n -> m ℕ.< suc n -> m ℕ.≤ n
m<1+n⇒m≤n m n (ℕ.s≤s m≤n) = m≤n

p≤q+j⁻¹⇒p≤q : ∀ {p q} -> (∀ j -> .{{_ : ℕ.NonZero j}} -> p ℚ.≤ q ℚ.+ (+ 1 / j)) -> p ℚ.≤ q
p≤q+j⁻¹⇒p≤q {p} {q} hyp = p-q≤j⁻¹⇒p≤q (λ {(suc j-1) -> let j = suc j-1 in begin
  p ℚ.- q             ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- q) (hyp j) ⟩
  q ℚ.+ + 1 / j ℚ.- q ≃⟨ solve 2 (λ q j⁻¹ -> (q ⊕ j⁻¹ ⊖ q) ⊜ j⁻¹) ℚP.≃-refl q (+ 1 / j) ⟩
  + 1 / j              ∎})
  where
    open ℚP.≤-Reasoning
    open import NonReflectiveQ

