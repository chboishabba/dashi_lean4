{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- A constructed normalized invariant (Haar) integral on the n-torus.
--
-- `DASHI.Analysis.BishopCircleHaar` constructs a normalized, additive,
-- monotone, translation invariant integral on the circle group R/Z over the
-- Bishop reals.  A lattice gauge measure is a *product* of copies of the
-- Haar measure of the structure group, one per link, so what the lattice
-- construction actually needs is the Haar integral of a finite product of
-- copies of the group.  This module builds it for the n-fold product of
-- circles, for every n, by iterated integration:
--
--   * `VecModulus`         -- a joint modulus of uniform continuity for a
--                             function of n real variables (sup metric);
--   * `torusIntegral`      -- the iterated integral over [0,1]^n;
--   * `torusIntegral-close`, `torusIntegral-cong`, `torusIntegral-mod-irrelevant`
--                          -- the comparison estimate and its consequences;
--   * `torusIntegral-const`, `torusIntegral-one` -- normalisation;
--   * `torusIntegral-nonNeg`, `torusIntegral-mono` -- positivity/order;
--   * `torus-invariant`    -- invariance under translation by an arbitrary
--                             element of the torus, for integrands periodic
--                             in each coordinate.
--
-- Postulate-free, over the constructed (not postulated) Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopTorusHaar where

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; zipWith; replicate)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; subst₂)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopPeriodicShift
open import DASHI.Analysis.BishopCircleInvariance
open import DASHI.Analysis.BishopCircleNodeShift
open import DASHI.Analysis.BishopCircleHaar

------------------------------------------------------------------------
-- Small helpers.

eqDist : ∀ {x y : ℝ} → x ≃ y → ∀ (d : ℕ) → ∣ x - y ∣ ≤ (+ 1 ℚ./ suc d) ⋆
eqDist {x} {y} x≃y d = ≤-respˡ-≃
  (≃-symm (≃-trans (∣-∣-cong (≃-trans (+-congˡ (- y) x≃y) (+-inverseʳ y)))
                   (nonNegx⇒∣x∣≃x nonNeg0)))
  (0≤width d)

zeroDist : ∀ (x : ℝ) (d : ℕ) → ∣ x - x ∣ ≤ (+ 1 ℚ./ suc d) ⋆
zeroDist x d = eqDist (≃-refl {x}) d

------------------------------------------------------------------------
-- A joint modulus of uniform continuity in n variables, for the sup metric.

record VecModulus {n : ℕ} (f : Vec ℝ n → ℝ) : Set where
  field
    δ      : ℕ → ℕ
    δ-cont : ∀ (j : ℕ) (u v : Vec ℝ n) →
             (∀ i → ∣ lookup u i - lookup v i ∣ ≤ (+ 1 ℚ./ suc (δ j)) ⋆) →
             ∣ f u - f v ∣ ≤ (+ 1 ℚ./ suc j) ⋆

-- Fixing the first variable.

consMod : ∀ {n} (f : Vec ℝ (suc n) → ℝ) → VecModulus f → (x : ℝ) →
  VecModulus (λ v → f (x ∷ v))
consMod f mf x = record
  { δ      = VecModulus.δ mf
  ; δ-cont = λ j u v hyp →
      VecModulus.δ-cont mf j (x ∷ u) (x ∷ v) (cases j u v hyp)
  }
  where
  cases : ∀ j u v →
    (∀ i → ∣ lookup u i - lookup v i ∣ ≤ (+ 1 ℚ./ suc (VecModulus.δ mf j)) ⋆) →
    ∀ i → ∣ lookup (x ∷ u) i - lookup (x ∷ v) i ∣
            ≤ (+ 1 ℚ./ suc (VecModulus.δ mf j)) ⋆
  cases j u v hyp zero    = zeroDist x (VecModulus.δ mf j)
  cases j u v hyp (suc i) = hyp i

-- A function with a joint modulus respects equality of Bishop reals.

vec-cong : ∀ {n} (f : Vec ℝ n → ℝ) → VecModulus f → ∀ (u v : Vec ℝ n) →
  (∀ i → lookup u i ≃ lookup v i) → f u ≃ f v
vec-cong f mf u v u≃v = ∣x-y∣≤k⁻¹⇒x≃y (f u) (f v) bound
  where
  bound : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} → ∣ f u - f v ∣ ≤ (+ 1 ℚ./ k) ⋆
  bound (suc j) = VecModulus.δ-cont mf j u v
    (λ i → eqDist (u≃v i) (VecModulus.δ mf j))

-- Fixing all but the first variable is not needed; what is needed is that
-- the partial integral is uniformly continuous in the remaining variable,
-- which is proved together with the construction below.

------------------------------------------------------------------------
-- The iterated integral and its comparison estimate, defined together.

mutual

  torusIntegral : ∀ {n} (f : Vec ℝ n → ℝ) → VecModulus f → ℝ
  torusIntegral {zero}  f mf = f []
  torusIntegral {suc n} f mf =
    integral (λ x → torusIntegral (λ v → f (x ∷ v)) (consMod f mf x))
             (headMod f mf)

  headMod : ∀ {n} (f : Vec ℝ (suc n) → ℝ) (mf : VecModulus f) →
    UniformModulus (λ x → torusIntegral (λ v → f (x ∷ v)) (consMod f mf x))
  headMod {n} f mf = record
    { δ      = VecModulus.δ mf
    ; δ-cont = λ j x y hyp →
        torusIntegral-close (λ v → f (x ∷ v)) (λ v → f (y ∷ v))
          (consMod f mf x) (consMod f mf y) ((+ 1 ℚ./ suc j) ⋆)
          (λ v → VecModulus.δ-cont mf j (x ∷ v) (y ∷ v) (cases j x y hyp v))
    }
    where
    cases : ∀ j x y →
      ∣ x - y ∣ ≤ (+ 1 ℚ./ suc (VecModulus.δ mf j)) ⋆ →
      ∀ (v : Vec ℝ n) i →
      ∣ lookup (x ∷ v) i - lookup (y ∷ v) i ∣
        ≤ (+ 1 ℚ./ suc (VecModulus.δ mf j)) ⋆
    cases j x y hyp v zero    = hyp
    cases j x y hyp v (suc i) = zeroDist (lookup v i) (VecModulus.δ mf j)

  torusIntegral-close : ∀ {n} (f g : Vec ℝ n → ℝ)
    (mf : VecModulus f) (mg : VecModulus g) (ε : ℝ) →
    (∀ v → ∣ f v - g v ∣ ≤ ε) →
    ∣ torusIntegral f mf - torusIntegral g mg ∣ ≤ ε
  torusIntegral-close {zero}  f g mf mg ε bound = bound []
  torusIntegral-close {suc n} f g mf mg ε bound = integral-close
    (λ x → torusIntegral (λ v → f (x ∷ v)) (consMod f mf x))
    (λ x → torusIntegral (λ v → g (x ∷ v)) (consMod g mg x))
    (headMod f mf) (headMod g mg) ε
    (λ x → torusIntegral-close (λ v → f (x ∷ v)) (λ v → g (x ∷ v))
             (consMod f mf x) (consMod g mg x) ε (λ v → bound (x ∷ v)))

------------------------------------------------------------------------
-- Consequences of the comparison estimate.

torusIntegral-cong : ∀ {n} (f g : Vec ℝ n → ℝ)
  (mf : VecModulus f) (mg : VecModulus g) →
  (∀ v → f v ≃ g v) → torusIntegral f mf ≃ torusIntegral g mg
torusIntegral-cong f g mf mg f≃g =
  ∣x-y∣≤k⁻¹⇒x≃y (torusIntegral f mf) (torusIntegral g mg) bound
  where
  bound : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} →
    ∣ torusIntegral f mf - torusIntegral g mg ∣ ≤ (+ 1 ℚ./ k) ⋆
  bound (suc j) = torusIntegral-close f g mf mg ((+ 1 ℚ./ suc j) ⋆)
    (λ v → ≤-respˡ-≃
      (≃-symm (≃-trans (∣-∣-cong (≃-trans (+-congˡ (- g v) (f≃g v))
                                          (+-inverseʳ (g v))))
                       (nonNegx⇒∣x∣≃x nonNeg0)))
      (0≤width j))

torusIntegral-mod-irrelevant : ∀ {n} (f : Vec ℝ n → ℝ)
  (m₁ m₂ : VecModulus f) → torusIntegral f m₁ ≃ torusIntegral f m₂
torusIntegral-mod-irrelevant f m₁ m₂ =
  torusIntegral-cong f f m₁ m₂ (λ _ → ≃-refl)

------------------------------------------------------------------------
-- Normalisation.

constVecModulus : ∀ {n} (c : ℝ) → VecModulus {n} (λ _ → c)
constVecModulus c = record
  { δ      = λ _ → 0
  ; δ-cont = λ j u v _ → ≤-respˡ-≃
      (≃-symm (≃-trans (∣-∣-cong (+-inverseʳ c)) (nonNegx⇒∣x∣≃x nonNeg0)))
      (0≤width j)
  }

torusIntegral-const : ∀ {n} (c : ℝ) (m : VecModulus {n} (λ _ → c)) →
  torusIntegral {n} (λ _ → c) m ≃ c
torusIntegral-const {zero}  c m = ≃-refl
torusIntegral-const {suc n} c m = ≃-trans inner (integral-const c)
  where
  inner : torusIntegral {suc n} (λ _ → c) m
            ≃ integral (λ _ → c) (constModulus c)
  inner = uniqueness-of-limits
    (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ k → riemannSum-cong
        (λ x → torusIntegral (λ v → c) (consMod (λ _ → c) m x))
        (λ _ → c)
        (λ x → torusIntegral-const {n} c (consMod (λ _ → c) m x)) k)
      (riemannSum-isConvergent
        (λ x → torusIntegral (λ v → c) (consMod (λ _ → c) m x))
        (headMod (λ _ → c) m)))
    (riemannSum-converges (λ _ → c) (constModulus c))

torusIntegral-one : ∀ {n} → torusIntegral {n} (λ _ → 1ℝ) (constVecModulus 1ℝ) ≃ 1ℝ
torusIntegral-one {n} = torusIntegral-const {n} 1ℝ (constVecModulus 1ℝ)

------------------------------------------------------------------------
-- Order properties.

torusIntegral-mono : ∀ {n} (f g : Vec ℝ n → ℝ)
  (mf : VecModulus f) (mg : VecModulus g) →
  (∀ v → f v ≤ g v) → torusIntegral f mf ≤ torusIntegral g mg
torusIntegral-mono {zero}  f g mf mg f≤g = f≤g []
torusIntegral-mono {suc n} f g mf mg f≤g = integral-mono
  (λ x → torusIntegral (λ v → f (x ∷ v)) (consMod f mf x))
  (λ x → torusIntegral (λ v → g (x ∷ v)) (consMod g mg x))
  (headMod f mf) (headMod g mg)
  (λ x → torusIntegral-mono (λ v → f (x ∷ v)) (λ v → g (x ∷ v))
           (consMod f mf x) (consMod g mg x) (λ v → f≤g (x ∷ v)))

torusIntegral-nonNeg : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  (∀ v → 0ℝ ≤ f v) → 0ℝ ≤ torusIntegral f mf
torusIntegral-nonNeg {n} f mf 0≤f = ≤-respˡ-≃
  (torusIntegral-const {n} 0ℝ (constVecModulus 0ℝ))
  (torusIntegral-mono (λ _ → 0ℝ) f (constVecModulus 0ℝ) mf 0≤f)

------------------------------------------------------------------------
-- Periodicity in every coordinate, and translation invariance.

VecPeriodic : ∀ {n} (f : Vec ℝ n → ℝ) → Set
VecPeriodic {zero}  f = ⊤
VecPeriodic {suc n} f =
  (∀ x → VecPeriodic (λ v → f (x ∷ v)))
    × (∀ x v → f ((x + 1ℝ) ∷ v) ≃ f (x ∷ v))

-- translation of the argument
shiftVec : ∀ {n} → Vec ℝ n → Vec ℝ n → Vec ℝ n
shiftVec v a = zipWith _+_ v a

-- Translating the argument by a constant vector does not change the modulus.

shiftVecModulus : ∀ {n} (f : Vec ℝ n → ℝ) → VecModulus f → (a : Vec ℝ n) →
  VecModulus (λ v → f (shiftVec v a))
shiftVecModulus f mf a = record
  { δ      = VecModulus.δ mf
  ; δ-cont = λ j u v hyp →
      VecModulus.δ-cont mf j (shiftVec u a) (shiftVec v a)
        (λ i → ≤-respˡ-≃ (∣-∣-cong (≃-symm (diff i u v))) (hyp i))
  }
  where
  diff : ∀ i u v →
    lookup (shiftVec u a) i - lookup (shiftVec v a) i ≃ lookup u i - lookup v i
  diff i u v = subst₂ (λ p q → p - q ≃ lookup u i - lookup v i)
    (sym (lookup-zipWith _+_ i u a)) (sym (lookup-zipWith _+_ i v a))
    (shift-diff (lookup u i) (lookup v i) (lookup a i))

torus-invariant : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  VecPeriodic f → (a : Vec ℝ n) →
  (mfa : VecModulus (λ v → f (shiftVec v a))) →
  torusIntegral (λ v → f (shiftVec v a)) mfa ≃ torusIntegral f mf
torus-invariant {zero} f mf per [] mfa = ≃-refl
torus-invariant {suc n} f mf (perTail , perHead) (a ∷ as) mfa =
  ≃-trans step₁ (≃-trans step₂ step₃)
  where
  -- the integrand of the outer integral, before and after the shift
  G : ℝ → ℝ
  G x = torusIntegral (λ v → f (x ∷ v)) (consMod f mf x)

  mG : UniformModulus G
  mG = headMod f mf

  Ga : ℝ → ℝ
  Ga x = torusIntegral (λ v → f (shiftVec (x ∷ v) (a ∷ as)))
                       (consMod (λ v → f (shiftVec v (a ∷ as))) mfa x)

  mGa : UniformModulus Ga
  mGa = headMod (λ v → f (shiftVec v (a ∷ as))) mfa

  -- 1-periodicity of the partial integral
  Gper : ∀ x → G (x + 1ℝ) ≃ G x
  Gper x = torusIntegral-cong (λ v → f ((x + 1ℝ) ∷ v)) (λ v → f (x ∷ v))
    (consMod f mf (x + 1ℝ)) (consMod f mf x) (λ v → perHead x v)

  -- the inner integral is invariant under the shift of the tail
  inner : ∀ x → Ga x ≃ G (x + a)
  inner x = torus-invariant (λ v → f ((x + a) ∷ v)) (consMod f mf (x + a))
    (perTail (x + a)) as
    (consMod (λ v → f (shiftVec v (a ∷ as))) mfa x)

  step₁ : torusIntegral (λ v → f (shiftVec v (a ∷ as))) mfa
            ≃ integral (λ x → G (x + a)) (shiftModulus G mG a)
  step₁ = uniqueness-of-limits
    (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ k → riemannSum-cong Ga (λ x → G (x + a)) inner k)
      (riemannSum-isConvergent Ga mGa))
    (riemannSum-converges (λ x → G (x + a)) (shiftModulus G mG a))

  step₂ : integral (λ x → G (x + a)) (shiftModulus G mG a) ≃ integral G mG
  step₂ = integral-realShift G mG Gper a

  step₃ : integral G mG ≃ torusIntegral f mf
  step₃ = ≃-refl

-- The canonical form of the invariance statement: the Haar integral of a
-- coordinatewise periodic uniformly continuous function on the n-torus is
-- unchanged by translation by an arbitrary point of the torus.

torus-invariant-canonical : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  VecPeriodic f → (a : Vec ℝ n) →
  torusIntegral (λ v → f (shiftVec v a)) (shiftVecModulus f mf a)
    ≃ torusIntegral f mf
torus-invariant-canonical f mf per a =
  torus-invariant f mf per a (shiftVecModulus f mf a)

-- Translates of a coordinatewise periodic function are coordinatewise
-- periodic, so translation acts on the space of integrands.

shiftVecPeriodic : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  VecPeriodic f → (a : Vec ℝ n) → VecPeriodic (λ v → f (shiftVec v a))
shiftVecPeriodic {zero} f mf per [] = tt
shiftVecPeriodic {suc n} f mf (perTail , perHead) (a ∷ as) = tail , head
  where
  tail : ∀ x → VecPeriodic (λ v → f ((x + a) ∷ shiftVec v as))
  tail x = shiftVecPeriodic (λ v → f ((x + a) ∷ v))
    (consMod f mf (x + a)) (perTail (x + a)) as

  head : ∀ x v → f (((x + 1ℝ) + a) ∷ shiftVec v as)
                   ≃ f ((x + a) ∷ shiftVec v as)
  head x v = ≃-trans
    (vec-cong f mf (((x + 1ℝ) + a) ∷ shiftVec v as)
                   (((x + a) + 1ℝ) ∷ shiftVec v as) swapAt)
    (perHead (x + a) (shiftVec v as))
    where
    swapAt : ∀ i → lookup (((x + 1ℝ) + a) ∷ shiftVec v as) i
                     ≃ lookup (((x + a) + 1ℝ) ∷ shiftVec v as) i
    swapAt zero = ℝ-Solver.solve 3
      (λ u w z → (u ⊕ w) ⊕ z ⊜ (u ⊕ z) ⊕ w) ≃-refl x 1ℝ a
      where open ℝ-Solver
    swapAt (suc i) = ≃-refl
