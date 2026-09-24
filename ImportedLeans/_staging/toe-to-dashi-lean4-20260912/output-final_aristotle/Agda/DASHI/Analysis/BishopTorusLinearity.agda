{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Linearity of the constructed Haar integral on the n-torus.
--
-- `DASHI.Analysis.BishopTorusHaar` builds the normalized, positive,
-- monotone, translation invariant iterated integral on [0,1]^n.  A Haar
-- integral must in addition be a *linear* functional; this module supplies
-- the two missing laws, additivity and scalar homogeneity, by induction on
-- the number of coordinates from the one-dimensional statements
-- (`integral-add`, `integral-scale`).
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopTorusLinearity where

open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup)
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤProp
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as PE
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Real
open import RealProperties
open import ExtraProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopRiemannIntegralAdditivity
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopIntegralLinearity
open import DASHI.Analysis.BishopTorusHaar

------------------------------------------------------------------------
-- A joint modulus for a sum.

private
  dbl : ℕ → ℕ
  dbl j = ℕ.pred (2 ℕ.* suc j)

sumVecModulus : ∀ {n} (f g : Vec ℝ n → ℝ) →
  VecModulus f → VecModulus g → VecModulus (λ v → f v + g v)
sumVecModulus {n} f g mf mg = record { δ = δs ; δ-cont = cont }
  where
  open ℤSolver.+-*-Solver

  δf = VecModulus.δ mf
  δg = VecModulus.δ mg

  δs : ℕ → ℕ
  δs j = δf (dbl j) ℕ.⊔ δg (dbl j)

  halves : ∀ j →
    (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ + (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ ≤ (+ 1 ℚ./ suc j) ⋆
  halves j = ≤-reflexive (≃-trans
    (≃-symm (⋆-distrib-+ (+ 1 ℚ./ (2 ℕ.* suc j)) (+ 1 ℚ./ (2 ℕ.* suc j))))
    (⋆-cong (ℚ.*≡* (solve 1 (λ z →
      (con (+ 1) :* (con (+ 2) :* z) :+ con (+ 1) :* (con (+ 2) :* z)) :* z
        := con (+ 1) :* (con (+ 2) :* z :* (con (+ 2) :* z)))
      refl (+ suc j)))))

  cont : ∀ (j : ℕ) (u v : Vec ℝ n) →
    (∀ i → ∣ lookup u i - lookup v i ∣ ≤ (+ 1 ℚ./ suc (δs j)) ⋆) →
    ∣ (f u + g u) - (f v + g v) ∣ ≤ (+ 1 ℚ./ suc j) ⋆
  cont j u v hyp = ≤-trans t₁ (≤-trans t₂ (≤-trans t₃ (halves j)))
    where
    open ℝ-Solver

    hf : ∀ i → ∣ lookup u i - lookup v i ∣ ≤ (+ 1 ℚ./ suc (δf (dbl j))) ⋆
    hf i = ≤-trans (hyp i) (p≤q⇒p⋆≤q⋆ _ _
      (q≤r⇒+p/r≤+p/q 1 (suc (δf (dbl j))) (suc (δs j))
        (s≤s (ℕP.m≤m⊔n (δf (dbl j)) (δg (dbl j))))))

    hg : ∀ i → ∣ lookup u i - lookup v i ∣ ≤ (+ 1 ℚ./ suc (δg (dbl j))) ⋆
    hg i = ≤-trans (hyp i) (p≤q⇒p⋆≤q⋆ _ _
      (q≤r⇒+p/r≤+p/q 1 (suc (δg (dbl j))) (suc (δs j))
        (s≤s (ℕP.m≤n⊔m (δf (dbl j)) (δg (dbl j))))))

    t₁ : ∣ (f u + g u) - (f v + g v) ∣ ≤ ∣ (f u - f v) + (g u - g v) ∣
    t₁ = ≤-reflexive (∣-∣-cong (ℝ-Solver.solve 4
      (λ a b c d → (a ⊕ c) ⊖ (b ⊕ d) ⊜ (a ⊖ b) ⊕ (c ⊖ d))
      ≃-refl (f u) (f v) (g u) (g v)))

    t₂ : ∣ (f u - f v) + (g u - g v) ∣ ≤ ∣ f u - f v ∣ + ∣ g u - g v ∣
    t₂ = ∣x+y∣≤∣x∣+∣y∣ (f u - f v) (g u - g v)

    t₃ : ∣ f u - f v ∣ + ∣ g u - g v ∣
           ≤ (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ + (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆
    t₃ = +-mono-≤ (VecModulus.δ-cont mf (dbl j) u v hf)
                  (VecModulus.δ-cont mg (dbl j) u v hg)

------------------------------------------------------------------------
-- A joint modulus for a scalar multiple.

scaleVecModulusAux : ∀ {n} (c : ℝ) (f : Vec ℝ n → ℝ) → VecModulus f →
  (N-1 : ℕ) → ∣ c ∣ ≤ (+ suc N-1 ℚ./ 1) ⋆ →
  VecModulus (λ v → c * f v)
scaleVecModulusAux {n} c f mf N-1 cBound = record
  { δ      = λ j → δ (j ℕ.+ N-1 ℕ.* suc j)
  ; δ-cont = cont
  }
  where
  open VecModulus mf

  cont : ∀ (j : ℕ) (u v : Vec ℝ n) →
    (∀ i → ∣ lookup u i - lookup v i ∣
             ≤ (+ 1 ℚ./ suc (δ (j ℕ.+ N-1 ℕ.* suc j))) ⋆) →
    ∣ c * f u - c * f v ∣ ≤ (+ 1 ℚ./ suc j) ⋆
  cont j u v hyp = ≤-respˡ-≃ (≃-symm split) (≤-respʳ-≃ collapse bound)
    where
    open ℝ-Solver

    j′ : ℕ
    j′ = j ℕ.+ N-1 ℕ.* suc j

    split : ∣ c * f u - c * f v ∣ ≃ ∣ c ∣ * ∣ f u - f v ∣
    split = ≃-trans
      (∣-∣-cong (ℝ-Solver.solve 3 (λ a b d → a ⊗ b ⊖ a ⊗ d ⊜ a ⊗ (b ⊖ d))
        ≃-refl c (f u) (f v)))
      (∣x*y∣≃∣x∣*∣y∣ c (f u - f v))

    bound : ∣ c ∣ * ∣ f u - f v ∣
              ≤ (+ suc N-1 ℚ./ 1) ⋆ * (+ 1 ℚ./ suc j′) ⋆
    bound = *-mono-≤ (nonNeg∣x∣ c) (nonNeg∣x∣ (f u - f v)) cBound
      (δ-cont j′ u v hyp)

    collapse : (+ suc N-1 ℚ./ 1) ⋆ * (+ 1 ℚ./ suc j′) ⋆ ≃ (+ 1 ℚ./ suc j) ⋆
    collapse = ≃-trans (≃-symm (⋆-distrib-* (+ suc N-1 ℚ./ 1) (+ 1 ℚ./ suc j′)))
      (⋆-cong (ratEq))
      where
      ratEq : (+ suc N-1 ℚ./ 1) ℚ.* (+ 1 ℚ./ suc j′) ℚ.≃ (+ 1 ℚ./ suc j)
      ratEq = ℚ.*≡* step
        where
        step : (+ suc N-1 ℤ.* + 1) ℤ.* + suc j
                 ≡ + 1 ℤ.* + (1 ℕ.* suc (j ℕ.+ N-1 ℕ.* suc j))
        step = PE.trans (PE.cong (ℤ._* + suc j) (ℤProp.*-identityʳ (+ suc N-1)))
               (PE.trans (PE.sym (ℤProp.pos-* (suc N-1) (suc j)))
                      (PE.sym (PE.trans (ℤProp.*-identityˡ (+ (1 ℕ.* suc j′)))
                                  (PE.cong +_ (ℕP.*-identityˡ (suc j′))))))

scaleVecModulus : ∀ {n} (c : ℝ) (f : Vec ℝ n → ℝ) → VecModulus f →
  VecModulus (λ v → c * f v)
scaleVecModulus c f mf =
  scaleVecModulusAux c f mf (ℕ.pred (K ∣ c ∣)) (x≤Kx ∣ c ∣)

------------------------------------------------------------------------
-- Additivity of the torus integral.

torusIntegral-add : ∀ {n} (f g : Vec ℝ n → ℝ)
  (mf : VecModulus f) (mg : VecModulus g)
  (ms : VecModulus (λ v → f v + g v)) →
  torusIntegral (λ v → f v + g v) ms
    ≃ torusIntegral f mf + torusIntegral g mg
torusIntegral-add {zero}  f g mf mg ms = ≃-refl
torusIntegral-add {suc n} f g mf mg ms = ≃-trans align
  (integral-add F G (headMod f mf) (headMod g mg))
  where
  F G : ℝ → ℝ
  F x = torusIntegral (λ v → f (x ∷ v)) (consMod f mf x)
  G x = torusIntegral (λ v → g (x ∷ v)) (consMod g mg x)

  inner : ∀ x → torusIntegral (λ v → f (x ∷ v) + g (x ∷ v))
                  (consMod (λ v → f v + g v) ms x)
                  ≃ F x + G x
  inner x = torusIntegral-add (λ v → f (x ∷ v)) (λ v → g (x ∷ v))
    (consMod f mf x) (consMod g mg x)
    (consMod (λ v → f v + g v) ms x)

  align : torusIntegral (λ v → f v + g v) ms
            ≃ integral (λ x → F x + G x)
                (sumModulus F G (headMod f mf) (headMod g mg))
  align = integral-cong
    (λ x → torusIntegral (λ v → f (x ∷ v) + g (x ∷ v))
             (consMod (λ v → f v + g v) ms x))
    (λ x → F x + G x)
    (headMod (λ v → f v + g v) ms)
    (sumModulus F G (headMod f mf) (headMod g mg))
    inner

------------------------------------------------------------------------
-- Homogeneity of the torus integral.

torusIntegral-scale : ∀ {n} (c : ℝ) (f : Vec ℝ n → ℝ)
  (mf : VecModulus f) (mcf : VecModulus (λ v → c * f v)) →
  torusIntegral (λ v → c * f v) mcf ≃ c * torusIntegral f mf
torusIntegral-scale {zero}  c f mf mcf = ≃-refl
torusIntegral-scale {suc n} c f mf mcf = ≃-trans align
  (integral-scale c F (headMod f mf) (scaleModulus c F (headMod f mf)))
  where
  F : ℝ → ℝ
  F x = torusIntegral (λ v → f (x ∷ v)) (consMod f mf x)

  inner : ∀ x → torusIntegral (λ v → c * f (x ∷ v))
                  (consMod (λ v → c * f v) mcf x)
                  ≃ c * F x
  inner x = torusIntegral-scale c (λ v → f (x ∷ v)) (consMod f mf x)
    (consMod (λ v → c * f v) mcf x)

  align : torusIntegral (λ v → c * f v) mcf
            ≃ integral (λ x → c * F x) (scaleModulus c F (headMod f mf))
  align = integral-cong
    (λ x → torusIntegral (λ v → c * f (x ∷ v))
             (consMod (λ v → c * f v) mcf x))
    (λ x → c * F x)
    (headMod (λ v → c * f v) mcf)
    (scaleModulus c F (headMod f mf))
    inner

------------------------------------------------------------------------
-- Sums and scalar multiples of coordinatewise periodic functions are
-- coordinatewise periodic, so the integrands form a vector space.

sumVecPeriodic : ∀ {n} (f g : Vec ℝ n → ℝ) →
  VecPeriodic f → VecPeriodic g → VecPeriodic (λ v → f v + g v)
sumVecPeriodic {zero} f g pf pg = _
sumVecPeriodic {suc n} f g (pfT , pfH) (pgT , pgH) =
  (λ x → sumVecPeriodic (λ v → f (x ∷ v)) (λ v → g (x ∷ v)) (pfT x) (pgT x))
  , (λ x v → +-cong (pfH x v) (pgH x v))

scaleVecPeriodic : ∀ {n} (c : ℝ) (f : Vec ℝ n → ℝ) →
  VecPeriodic f → VecPeriodic (λ v → c * f v)
scaleVecPeriodic {zero} c f pf = _
scaleVecPeriodic {suc n} c f (pfT , pfH) =
  (λ x → scaleVecPeriodic c (λ v → f (x ∷ v)) (pfT x))
  , (λ x v → *-congˡ (pfH x v))

------------------------------------------------------------------------
-- The torus integral is a product measure: an integrand that splits as a
-- product of a function of the first coordinate and a function of the
-- remaining ones has factorizing integral.  (For a lattice gauge measure
-- this is the statement that distinct links are independent.)

torusIntegral-product : ∀ {n} (g : ℝ → ℝ) (mg : UniformModulus g)
  (h : Vec ℝ n → ℝ) (mh : VecModulus h)
  (mp : VecModulus {suc n} (λ w → g (Vec.head w) * h (Vec.tail w))) →
  torusIntegral (λ w → g (Vec.head w) * h (Vec.tail w)) mp
    ≃ integral g mg * torusIntegral h mh
torusIntegral-product {n} g mg h mh mp =
  ≃-trans alignInner (≃-trans pullOut (*-comm H (integral g mg)))
  where
  H : ℝ
  H = torusIntegral h mh

  F : Vec ℝ (suc n) → ℝ
  F w = g (Vec.head w) * h (Vec.tail w)

  inner : ∀ x → torusIntegral (λ v → g x * h v) (consMod F mp x) ≃ H * g x
  inner x = ≃-trans (torusIntegral-scale (g x) h mh (consMod F mp x))
                    (*-comm (g x) H)

  alignInner : torusIntegral F mp ≃ integral (λ x → H * g x) (scaleModulus H g mg)
  alignInner = integral-cong
    (λ x → torusIntegral (λ v → g x * h v) (consMod F mp x))
    (λ x → H * g x)
    (headMod F mp) (scaleModulus H g mg) inner

  pullOut : integral (λ x → H * g x) (scaleModulus H g mg) ≃ H * integral g mg
  pullOut = integral-scale H g mg (scaleModulus H g mg)
