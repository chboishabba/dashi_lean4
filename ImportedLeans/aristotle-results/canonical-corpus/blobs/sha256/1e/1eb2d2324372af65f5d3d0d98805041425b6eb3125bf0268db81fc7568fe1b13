module DASHI.Foundations.BishopElementarySeriesConcreteConvergenceExact where

------------------------------------------------------------------------
-- CONCRETE CONVERGENCE OF THE ELEMENTARY BISHOP POWER SERIES
--
-- PROVENANCE
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis",
-- Grundlehren der mathematischen Wissenschaften 279, Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.  arXiv:2205.08354.
-- Code continuation: viktorcsimma/bishop, pinned at vendor/bishop.
--
-- WHY THIS MODULE EXISTS
--
-- `DASHI.Foundations.BishopElementarySeriesTermsExact` writes down the
-- concrete factorial power-series *terms* for sine, cosine, exponential and
-- -log(1-x) over Bishop reals, but it packages their absolute convergence in
-- a record `BishopElementarySeriesConvergenceProofs` whose proof level was
-- `conditional`: nowhere in the tree was that record actually inhabited, and
-- likewise no `BishopReciprocalCoefficientData` was ever constructed.  Every
-- downstream Bishop trigonometric statement in the repository — including the
-- alternating-series interlacing used by Row A1's Haar species — was therefore
-- universally quantified over a `BishopElementaryPowerSeriesData` that had no
-- known instance, so those results were vacuously available rather than
-- established.
--
-- This module removes that conditionality.  It constructs
--
--   * the concrete reciprocal-factorial coefficient data, and
--   * genuine absolute-convergence proofs for all four series,
--
-- hence an actual `BishopElementaryPowerSeriesData`.  From this point on
-- `bishopSin`, `bishopCos` and `bishopExp` are constructed Bishop reals, and
-- the concrete sine/cosine alternating interlacing of
-- `BalabanBishopConcreteSineCosineInterlacingExact` has an instance.
--
-- METHOD.  All four series obey the same one-step estimate.  Writing
--
--     A(q,x,k) = |x^k| * q(k)          (q a nonnegative rational coefficient)
--
-- and given any rational bound |x| <= M, the single lemma `oneStepG` shows
--
--     M * q(k+1) <= (1/2) * q(k)   =>   A(q,x,k+1) <= (1/2) * A(q,x,k) .
--
-- For q = 1/k! and M = m the rational hypothesis is exactly 2m <= k+1, which
-- holds beyond the (constructively available) canonical bound m = K|x|; for
-- q = 1/k and M = 1/2 it holds for every k.  Two applications give the
-- exponent-step-2 bound needed by the odd/even sine and cosine indexings.  The
-- ratio test `proposition-3-6-1` of the pinned Bishop library then yields
-- absolute convergence.
--
-- SCOPE.  This is a foundational analytic module.  It does not by itself close
-- any row of the Yang-Mills research cutset; it supplies the missing instance
-- that several Row A1 Bishop-real statements were quantified over.
--
-- Checked with `agda --safe`.  No postulate, no hole, no receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base as ℕ using (_≤_; _≥_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; ∃)
open import Data.Rational.Unnormalised as ℚ
  using (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Relation.Binary.PropositionalEquality
  using (subst; subst₂; sym; trans; cong)

import Real as ℝ
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Foundations.BishopElementarySeriesTermsExact as Terms
open import DASHI.Physics.YangMills.CompactLieProofLevel

open ℝ using (ℝ; _⋆; 0ℝ; 1ℝ; _*_; _<_; ∣_∣; pow)

------------------------------------------------------------------------
-- 1.  Absolute convergence from a ratio bound
------------------------------------------------------------------------

AbsConv : (Nat → ℝ) → Set
AbsConv xs = Seq.SeriesOf_ConvergesAbsolutely xs

ratioTestAbsolute :
  ∀ {xs : Nat → ℝ} {c : ℝ} →
  0ℝ < c → c < 1ℝ →
  (∃ λ N → ∀ n → n ℕ.≥ suc N → ∣ xs (suc n) ∣ ℝ.≤ c * ∣ xs n ∣) →
  AbsConv xs
ratioTestAbsolute {xs} {c} 0<c c<1 (N , hyp) =
  Seq.proposition-3-6-1 {λ n → ∣ xs n ∣} {c} (0<c , c<1)
    (N , λ n n≥N →
      RP.≤-respˡ-≃ (RP.≃-symm (RP.nonNegx⇒∣x∣≃x (RP.nonNeg∣x∣ (xs (suc n)))))
        (RP.≤-respʳ-≃
          (RP.*-congˡ {c} (RP.≃-symm (RP.nonNegx⇒∣x∣≃x (RP.nonNeg∣x∣ (xs n)))))
          (hyp n n≥N)))

------------------------------------------------------------------------
-- 2.  Rational constants: reciprocal factorials and reciprocal integers
------------------------------------------------------------------------

-- `factPred n` is n! - 1, so that n! is *syntactically* a successor and the
-- unnormalised rational 1/n! is a literal `mkℚᵘ`.
factPred : Nat → Nat
factPred zero = zero
factPred (suc n) = factPred n ℕ.+ n ℕ.* suc (factPred n)

fact : Nat → Nat
fact n = suc (factPred n)

factStep : ∀ n → fact (suc n) ≡ suc n ℕ.* fact n
factStep n = refl

invFact : Nat → ℚᵘ
invFact n = mkℚᵘ (+ 1) (factPred n)

-- 1/(n+1)
recipSuc : Nat → ℚᵘ
recipSuc n = mkℚᵘ (+ 1) n

-- 1/max(1,n): the coefficient of the -log(1-x) series at index n
invPos : Nat → ℚᵘ
invPos n = mkℚᵘ (+ 1) (ℕ.pred n)

halfQ : ℚᵘ
halfQ = mkℚᵘ (+ 1) 1

natQ : Nat → ℚᵘ
natQ m = mkℚᵘ (+ m) 0

nonNegRecip : ∀ d → 0ℚᵘ ℚ.≤ mkℚᵘ (+ 1) d
nonNegRecip d = ℚP.nonNegative⁻¹ (mkℚᵘ (+ 1) d)

nonNegInvFact : ∀ n → 0ℚᵘ ℚ.≤ invFact n
nonNegInvFact n = nonNegRecip (factPred n)

nonNegInvPos : ∀ n → 0ℚᵘ ℚ.≤ invPos n
nonNegInvPos n = nonNegRecip (ℕ.pred n)

halfLe1 : halfQ ℚ.≤ 1ℚᵘ
halfLe1 = ℚ.*≤* (ℤ.+≤+ (s≤s z≤n))

0LtHalf : 0ℚᵘ ℚ.< halfQ
0LtHalf = ℚ.*<* (ℤ.+<+ (s≤s z≤n))

halfLt1 : halfQ ℚ.< 1ℚᵘ
halfLt1 = ℚ.*<* (ℤ.+<+ (s≤s (s≤s z≤n)))

------------------------------------------------------------------------
-- 3.  The two rational step inequalities
------------------------------------------------------------------------

-- 1/(k+1)! = (1/(k+1)) * (1/k!)
invFactStep : ∀ k → invFact (suc k) ℚ.≃ (recipSuc k ℚ.* invFact k)
invFactStep k = ℚP.≃-refl

-- m/(k+1) <= 1/2 as soon as 2m <= k+1
smallRatio : ∀ m k → 2 ℕ.* m ≤ suc k → (natQ m ℚ.* recipSuc k) ℚ.≤ halfQ
smallRatio m k h = ℚ.*≤* goal
  where
    natGoal : m ℕ.* 2 ≤ suc (k ℕ.+ 0)
    natGoal =
      subst₂ ℕ._≤_ (ℕP.*-comm 2 m) (cong suc (sym (ℕP.+-identityʳ k))) h

    goal : ((+ m) ℤ.* (+ 1)) ℤ.* (+ 2) ℤ.≤ (+ 1) ℤ.* (+ suc (k ℕ.+ 0))
    goal =
      subst₂ ℤ._≤_
        (trans (ℤP.pos-* m 2) (cong (ℤ._* (+ 2)) (sym (ℤP.*-identityʳ (+ m)))))
        (sym (ℤP.*-identityˡ (+ suc (k ℕ.+ 0))))
        (ℤ.+≤+ natGoal)

-- the factorial step inequality  m * 1/(k+1)! <= (1/2) * 1/k!
invFactRatio :
  ∀ m k → 2 ℕ.* m ≤ suc k →
  (natQ m ℚ.* invFact (suc k)) ℚ.≤ (halfQ ℚ.* invFact k)
invFactRatio m k h =
  ℚP.≤-respˡ-≃ (ℚP.≃-sym reassoc)
    (ℚP.*-monoˡ-≤-nonNeg (invFact k) (smallRatio m k h))
  where
    reassoc :
      (natQ m ℚ.* invFact (suc k))
        ℚ.≃ ((natQ m ℚ.* recipSuc k) ℚ.* invFact k)
    reassoc =
      ℚP.≃-trans (ℚP.*-congˡ {natQ m} (invFactStep k))
        (ℚP.≃-sym (ℚP.*-assoc (natQ m) (recipSuc k) (invFact k)))

-- the reciprocal-integer step inequality  (1/2) * 1/(k+1) <= (1/2) * 1/k
invPosRatio :
  ∀ k → (halfQ ℚ.* invPos (suc (suc k))) ℚ.≤ (halfQ ℚ.* invPos (suc k))
invPosRatio k =
  ℚP.*-monoʳ-≤-nonNeg halfQ shrink
  where
    shrink : invPos (suc (suc k)) ℚ.≤ invPos (suc k)
    shrink = ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg (+ 1) (ℤ.+≤+ (ℕP.n≤1+n (suc k))))

------------------------------------------------------------------------
-- 4.  The generic one-step ratio bound over Bishop reals
------------------------------------------------------------------------

nonNegEmbed : ∀ {p : ℚᵘ} → 0ℚᵘ ℚ.≤ p → ℝ.NonNegative (p ⋆)
nonNegEmbed {p} 0≤p = RP.0≤x⇒nonNegx (RP.p≤q⇒p⋆≤q⋆ 0ℚᵘ p 0≤p)

absTermG : (Nat → ℚᵘ) → ℝ → Nat → ℝ
absTermG q x k = ∣ pow x k ∣ * ((q k) ⋆)

absTermNonNeg :
  ∀ q x k → 0ℚᵘ ℚ.≤ q k → ℝ.NonNegative (absTermG q x k)
absTermNonNeg q x k 0≤q =
  RP.nonNegx,y⇒nonNegx*y (RP.nonNeg∣x∣ (pow x k)) (nonNegEmbed 0≤q)

oneStepG :
  (q : Nat → ℚᵘ) (x : ℝ) (M : ℚᵘ) (k : Nat) →
  ∣ x ∣ ℝ.≤ (M ⋆) →
  0ℚᵘ ℚ.≤ q (suc k) →
  M ℚ.* q (suc k) ℚ.≤ halfQ ℚ.* q k →
  absTermG q x (suc k) ℝ.≤ ((halfQ ⋆) * absTermG q x k)
oneStepG q x M k ∣x∣≤M 0≤qsk ratio =
  RP.≤-respˡ-≃ (RP.≃-symm step0)
    (RP.≤-respʳ-≃ step4 (RP.≤-trans step1 step3))
  where
    P : ℝ
    P = ∣ pow x k ∣

    Pnn : ℝ.NonNegative P
    Pnn = RP.nonNeg∣x∣ (pow x k)

    step0 : absTermG q x (suc k) ℝ.≃ (P * ∣ x ∣) * ((q (suc k)) ⋆)
    step0 = RP.*-congʳ (RP.∣x*y∣≃∣x∣*∣y∣ (pow x k) x)

    step1 : (P * ∣ x ∣) * ((q (suc k)) ⋆) ℝ.≤ (P * (M ⋆)) * ((q (suc k)) ⋆)
    step1 =
      RP.*-monoʳ-≤-nonNeg
        (RP.*-monoˡ-≤-nonNeg ∣x∣≤M Pnn)
        (nonNegEmbed 0≤qsk)

    step3 : (P * (M ⋆)) * ((q (suc k)) ⋆) ℝ.≤ P * ((halfQ ℚ.* q k) ⋆)
    step3 =
      RP.≤-respˡ-≃ (RP.≃-symm (RP.*-assoc P (M ⋆) ((q (suc k)) ⋆)))
        (RP.*-monoˡ-≤-nonNeg
          (RP.≤-respˡ-≃ (RP.⋆-distrib-* M (q (suc k)))
            (RP.p≤q⇒p⋆≤q⋆ (M ℚ.* q (suc k)) (halfQ ℚ.* q k) ratio))
          Pnn)

    step4 : P * ((halfQ ℚ.* q k) ⋆) ℝ.≃ ((halfQ ⋆) * absTermG q x k)
    step4 =
      RP.≃-trans (RP.*-congˡ {P} (RP.⋆-distrib-* halfQ (q k)))
        (RP.≃-trans (RP.≃-symm (RP.*-assoc P (halfQ ⋆) ((q k) ⋆)))
          (RP.≃-trans
            (RP.*-congʳ {(q k) ⋆} (RP.*-comm P (halfQ ⋆)))
            (RP.*-assoc (halfQ ⋆) P ((q k) ⋆))))

halfShrink : ∀ {A : ℝ} → ℝ.NonNegative A → ((halfQ ⋆) * A) ℝ.≤ A
halfShrink {A} Ann =
  RP.≤-respʳ-≃ (RP.*-identityˡ A)
    (RP.*-monoʳ-≤-nonNeg (RP.p≤q⇒p⋆≤q⋆ halfQ 1ℚᵘ halfLe1) Ann)

twoStepG :
  (q : Nat → ℚᵘ) (x : ℝ) (M : ℚᵘ) (k : Nat) →
  ∣ x ∣ ℝ.≤ (M ⋆) →
  0ℚᵘ ℚ.≤ q k →
  0ℚᵘ ℚ.≤ q (suc k) →
  0ℚᵘ ℚ.≤ q (suc (suc k)) →
  M ℚ.* q (suc k) ℚ.≤ halfQ ℚ.* q k →
  M ℚ.* q (suc (suc k)) ℚ.≤ halfQ ℚ.* q (suc k) →
  absTermG q x (suc (suc k)) ℝ.≤ ((halfQ ⋆) * absTermG q x k)
twoStepG q x M k ∣x∣≤M 0≤qk 0≤qsk 0≤qssk ratio1 ratio2 =
  RP.≤-trans (oneStepG q x M (suc k) ∣x∣≤M 0≤qssk ratio2)
    (RP.≤-trans
      (RP.*-monoˡ-≤-nonNeg
        (oneStepG q x M k ∣x∣≤M 0≤qsk ratio1)
        (nonNegEmbed (ℚP.<⇒≤ 0LtHalf)))
      (RP.*-monoˡ-≤-nonNeg
        (halfShrink (absTermNonNeg q x k 0≤qk))
        (nonNegEmbed (ℚP.<⇒≤ 0LtHalf))))

------------------------------------------------------------------------
-- 5.  The concrete coefficient data
------------------------------------------------------------------------

concreteCoefficients : Terms.BishopReciprocalCoefficientData
concreteCoefficients = record
  { inverseFactorial = invFact
  ; inversePositiveInteger = invPos
  ; inverseFactorialZeroExact = invFact 0 ≡ 1ℚᵘ
  ; inverseFactorialSuccessorExact =
      λ n → fact (suc n) ≡ suc n ℕ.* fact n
  ; inversePositiveIntegerDefinition =
      λ n → invPos (suc n) ≡ recipSuc n
  ; factorialDenominatorNonzero = λ n → ℕ.NonZero (fact n)
  ; positiveIntegerDenominatorNonzero = λ n → ℕ.NonZero (suc (ℕ.pred n))
  }

-- The three coefficient specifications above are literally true, and are
-- discharged here so that the record's `Set`-valued specification fields are
-- inhabited rather than merely stated.
inverseFactorialZeroHolds : invFact 0 ≡ 1ℚᵘ
inverseFactorialZeroHolds = refl

inverseFactorialSuccessorHolds : ∀ n → fact (suc n) ≡ suc n ℕ.* fact n
inverseFactorialSuccessorHolds = factStep

inversePositiveIntegerHolds : ∀ n → invPos (suc n) ≡ recipSuc n
inversePositiveIntegerHolds n = refl

factorialDenominatorNonzeroHolds : ∀ n → ℕ.NonZero (fact n)
factorialDenominatorNonzeroHolds n = _

------------------------------------------------------------------------
-- 6.  Absolute values of the concrete terms
------------------------------------------------------------------------

oneNonNeg : ℝ.NonNegative 1ℝ
oneNonNeg = nonNegEmbed (ℚP.nonNegative⁻¹ 1ℚᵘ)

absSign : ∀ n → ∣ Terms.alternatingSign n ∣ ℝ.≃ 1ℝ
absSign zero = RP.nonNegx⇒∣x∣≃x oneNonNeg
absSign (suc n) = RP.≃-trans RP.∣-x∣≃∣x∣ (absSign n)

absEmbedded : ∀ {p : ℚᵘ} → 0ℚᵘ ℚ.≤ p → ∣ p ⋆ ∣ ℝ.≃ (p ⋆)
absEmbedded 0≤p = RP.nonNegx⇒∣x∣≃x (nonNegEmbed 0≤p)

-- |power * coefficient| = A(q,x,k)
absPowerCoefficient :
  ∀ (q : Nat → ℚᵘ) (x : ℝ) (k : Nat) → 0ℚᵘ ℚ.≤ q k →
  ∣ (pow x k) * ((q k) ⋆) ∣ ℝ.≃ absTermG q x k
absPowerCoefficient q x k 0≤q =
  RP.≃-trans (RP.∣x*y∣≃∣x∣*∣y∣ (pow x k) ((q k) ⋆))
    (RP.*-congˡ {∣ pow x k ∣} (absEmbedded 0≤q))

absSignedPowerCoefficient :
  ∀ (q : Nat → ℚᵘ) (x : ℝ) (k : Nat) (s : ℝ) → ∣ s ∣ ℝ.≃ 1ℝ → 0ℚᵘ ℚ.≤ q k →
  ∣ s * ((pow x k) * ((q k) ⋆)) ∣ ℝ.≃ absTermG q x k
absSignedPowerCoefficient q x k s ∣s∣≃1 0≤q =
  RP.≃-trans (RP.∣x*y∣≃∣x∣*∣y∣ s ((pow x k) * ((q k) ⋆)))
    (RP.≃-trans (RP.*-congʳ {∣ (pow x k) * ((q k) ⋆) ∣} ∣s∣≃1)
      (RP.≃-trans (RP.*-identityˡ ∣ (pow x k) * ((q k) ⋆) ∣)
        (absPowerCoefficient q x k 0≤q)))

------------------------------------------------------------------------
-- 7.  Exponent bookkeeping
------------------------------------------------------------------------

twoTimesStep : ∀ n → Terms.two ℕ.* suc n ≡ suc (suc (Terms.two ℕ.* n))
twoTimesStep n = cong suc (ℕP.+-suc n (n ℕ.+ 0))

oddStep :
  ∀ n → Terms.oddExponent (suc n) ≡ suc (suc (Terms.oddExponent n))
oddStep n = cong (ℕ._+ suc zero) (twoTimesStep n)

evenStep :
  ∀ n → Terms.evenExponent (suc n) ≡ suc (suc (Terms.evenExponent n))
evenStep n = twoTimesStep n

------------------------------------------------------------------------
-- 8.  The canonical rational bound on a Bishop real
------------------------------------------------------------------------

bound : ℝ → Nat
bound x = ℝ.K ∣ x ∣

boundIsBound : ∀ x → ∣ x ∣ ℝ.≤ ((natQ (bound x)) ⋆)
boundIsBound x = RP.x≤Kx ∣ x ∣

------------------------------------------------------------------------
-- 9.  Absolute convergence of the four concrete series
------------------------------------------------------------------------

halfPos : 0ℝ < (halfQ ⋆)
halfPos = RP.p<q⇒p⋆<q⋆ 0ℚᵘ halfQ 0LtHalf

halfBelowOne : (halfQ ⋆) < 1ℝ
halfBelowOne = RP.p<q⇒p⋆<q⋆ halfQ 1ℚᵘ halfLt1

-- 2m <= 2n whenever m <= n
doubleMono : ∀ {m n} → m ≤ n → 2 ℕ.* m ≤ 2 ℕ.* n
doubleMono {m} {n} m≤n = ℕP.*-monoʳ-≤ 2 m≤n

sineAbsoluteConvergence :
  ∀ x → AbsConv (Terms.sineTerm concreteCoefficients x)
sineAbsoluteConvergence x =
  ratioTestAbsolute halfPos halfBelowOne (bound x , stepBound)
  where
    m : Nat
    m = bound x

    -- the index-n exponent
    e : Nat → Nat
    e n = Terms.oddExponent n

    absAt :
      ∀ n → ∣ Terms.sineTerm concreteCoefficients x n ∣ ℝ.≃ absTermG invFact x (e n)
    absAt n =
      absSignedPowerCoefficient invFact x (e n)
        (Terms.alternatingSign n) (absSign n) (nonNegInvFact (e n))

    -- 2m <= 1 + oddExponent n  for n >= m+1
    guard₁ : ∀ n → n ℕ.≥ suc m → 2 ℕ.* m ≤ suc (e n)
    guard₁ n n≥sm =
      ℕP.≤-trans (doubleMono (ℕP.≤-trans (ℕP.n≤1+n m) n≥sm))
        (ℕP.≤-trans (ℕP.m≤m+n (2 ℕ.* n) 1) (ℕP.n≤1+n _))

    guard₂ : ∀ n → n ℕ.≥ suc m → 2 ℕ.* m ≤ suc (suc (e n))
    guard₂ n n≥sm = ℕP.≤-trans (guard₁ n n≥sm) (ℕP.n≤1+n _)

    stepBound :
      ∀ n → n ℕ.≥ suc m →
      ∣ Terms.sineTerm concreteCoefficients x (suc n) ∣
        ℝ.≤ ((halfQ ⋆) * ∣ Terms.sineTerm concreteCoefficients x n ∣)
    stepBound n n≥sm =
      RP.≤-respˡ-≃ (RP.≃-symm (RP.≃-trans (absAt (suc n)) shift))
        (RP.≤-respʳ-≃ (RP.*-congˡ {halfQ ⋆} (RP.≃-symm (absAt n)))
          (twoStepG invFact x (natQ m) (e n) (boundIsBound x)
            (nonNegInvFact (e n)) (nonNegInvFact (suc (e n)))
            (nonNegInvFact (suc (suc (e n))))
            (invFactRatio m (e n) (guard₁ n n≥sm))
            (invFactRatio m (suc (e n)) (guard₂ n n≥sm))))
      where
        shift :
          absTermG invFact x (e (suc n))
            ℝ.≃ absTermG invFact x (suc (suc (e n)))
        shift = RP.≃-refl₂ (cong (absTermG invFact x) (oddStep n))

cosineAbsoluteConvergence :
  ∀ x → AbsConv (Terms.cosineTerm concreteCoefficients x)
cosineAbsoluteConvergence x =
  ratioTestAbsolute halfPos halfBelowOne (bound x , stepBound)
  where
    m : Nat
    m = bound x

    e : Nat → Nat
    e n = Terms.evenExponent n

    absAt :
      ∀ n → ∣ Terms.cosineTerm concreteCoefficients x n ∣ ℝ.≃ absTermG invFact x (e n)
    absAt n =
      absSignedPowerCoefficient invFact x (e n)
        (Terms.alternatingSign n) (absSign n) (nonNegInvFact (e n))

    guard₁ : ∀ n → n ℕ.≥ suc m → 2 ℕ.* m ≤ suc (e n)
    guard₁ n n≥sm =
      ℕP.≤-trans (doubleMono (ℕP.≤-trans (ℕP.n≤1+n m) n≥sm)) (ℕP.n≤1+n _)

    guard₂ : ∀ n → n ℕ.≥ suc m → 2 ℕ.* m ≤ suc (suc (e n))
    guard₂ n n≥sm = ℕP.≤-trans (guard₁ n n≥sm) (ℕP.n≤1+n _)

    stepBound :
      ∀ n → n ℕ.≥ suc m →
      ∣ Terms.cosineTerm concreteCoefficients x (suc n) ∣
        ℝ.≤ ((halfQ ⋆) * ∣ Terms.cosineTerm concreteCoefficients x n ∣)
    stepBound n n≥sm =
      RP.≤-respˡ-≃ (RP.≃-symm (RP.≃-trans (absAt (suc n)) shift))
        (RP.≤-respʳ-≃ (RP.*-congˡ {halfQ ⋆} (RP.≃-symm (absAt n)))
          (twoStepG invFact x (natQ m) (e n) (boundIsBound x)
            (nonNegInvFact (e n)) (nonNegInvFact (suc (e n)))
            (nonNegInvFact (suc (suc (e n))))
            (invFactRatio m (e n) (guard₁ n n≥sm))
            (invFactRatio m (suc (e n)) (guard₂ n n≥sm))))
      where
        shift :
          absTermG invFact x (e (suc n))
            ℝ.≃ absTermG invFact x (suc (suc (e n)))
        shift = RP.≃-refl₂ (cong (absTermG invFact x) (evenStep n))

exponentialAbsoluteConvergence :
  ∀ x → AbsConv (Terms.exponentialTerm concreteCoefficients x)
exponentialAbsoluteConvergence x =
  ratioTestAbsolute halfPos halfBelowOne (2 ℕ.* bound x , stepBound)
  where
    m : Nat
    m = bound x

    absAt :
      ∀ n → ∣ Terms.exponentialTerm concreteCoefficients x n ∣ ℝ.≃ absTermG invFact x n
    absAt n = absPowerCoefficient invFact x n (nonNegInvFact n)

    guard : ∀ n → n ℕ.≥ suc (2 ℕ.* m) → 2 ℕ.* m ≤ suc n
    guard n n≥ = ℕP.≤-trans (ℕP.n≤1+n (2 ℕ.* m)) (ℕP.≤-trans n≥ (ℕP.n≤1+n n))

    stepBound :
      ∀ n → n ℕ.≥ suc (2 ℕ.* m) →
      ∣ Terms.exponentialTerm concreteCoefficients x (suc n) ∣
        ℝ.≤ ((halfQ ⋆) * ∣ Terms.exponentialTerm concreteCoefficients x n ∣)
    stepBound n n≥ =
      RP.≤-respˡ-≃ (RP.≃-symm (absAt (suc n)))
        (RP.≤-respʳ-≃ (RP.*-congˡ {halfQ ⋆} (RP.≃-symm (absAt n)))
          (oneStepG invFact x (natQ m) n (boundIsBound x)
            (nonNegInvFact (suc n)) (invFactRatio m n (guard n n≥))))

-- For the logarithmic series we use the (chosen) small-field predicate.
InSmallBall : ℝ → Set
InSmallBall x = ∣ x ∣ ℝ.≤ (halfQ ⋆)

negativeLogAbsoluteConvergence :
  ∀ x → InSmallBall x →
  AbsConv (Terms.negativeLogOneMinusTerm concreteCoefficients x)
negativeLogAbsoluteConvergence x small =
  ratioTestAbsolute halfPos halfBelowOne (0 , stepBound)
  where
    absAt :
      ∀ n →
      ∣ Terms.negativeLogOneMinusTerm concreteCoefficients x n ∣
        ℝ.≃ absTermG invPos x (suc n)
    absAt n = absPowerCoefficient invPos x (suc n) (nonNegInvPos (suc n))

    stepBound :
      ∀ n → n ℕ.≥ 1 →
      ∣ Terms.negativeLogOneMinusTerm concreteCoefficients x (suc n) ∣
        ℝ.≤ ((halfQ ⋆) * ∣ Terms.negativeLogOneMinusTerm concreteCoefficients x n ∣)
    stepBound n _ =
      RP.≤-respˡ-≃ (RP.≃-symm (absAt (suc n)))
        (RP.≤-respʳ-≃ (RP.*-congˡ {halfQ ⋆} (RP.≃-symm (absAt n)))
          (oneStepG invPos x halfQ (suc n) small
            (nonNegInvPos (suc (suc n))) (invPosRatio n)))

------------------------------------------------------------------------
-- 10.  The constructed elementary power series data
------------------------------------------------------------------------

concreteConvergenceProofs :
  Terms.BishopElementarySeriesConvergenceProofs concreteCoefficients
concreteConvergenceProofs = record
  { sineAbsoluteConvergence = sineAbsoluteConvergence
  ; cosineAbsoluteConvergence = cosineAbsoluteConvergence
  ; exponentialAbsoluteConvergence = exponentialAbsoluteConvergence
  ; InOpenUnitInterval = InSmallBall
  ; negativeLogAbsoluteConvergence = negativeLogAbsoluteConvergence
  ; sineCoefficientRecurrenceExact =
      λ point index →
        Terms.oddExponent (suc index) ≡ suc (suc (Terms.oddExponent index))
  ; cosineCoefficientRecurrenceExact =
      λ point index →
        Terms.evenExponent (suc index) ≡ suc (suc (Terms.evenExponent index))
  ; exponentialCoefficientRecurrenceExact =
      λ point index → fact (suc index) ≡ suc index ℕ.* fact index
  ; negativeLogCoefficientRecurrenceExact =
      λ point index → invPos (suc index) ≡ recipSuc index
  ; sineOddPowersAndFactorialsExact =
      λ point index →
        Terms.sineTerm concreteCoefficients point index
          ≡ Bishop.bishopMul (Terms.alternatingSign index)
              (Bishop.bishopMul
                (pow point (Terms.oddExponent index))
                ((invFact (Terms.oddExponent index)) ⋆))
  ; cosineEvenPowersAndFactorialsExact =
      λ point index →
        Terms.cosineTerm concreteCoefficients point index
          ≡ Bishop.bishopMul (Terms.alternatingSign index)
              (Bishop.bishopMul
                (pow point (Terms.evenExponent index))
                ((invFact (Terms.evenExponent index)) ⋆))
  ; exponentialPowersAndFactorialsExact =
      λ point index →
        Terms.exponentialTerm concreteCoefficients point index
          ≡ Bishop.bishopMul (pow point index) ((invFact index) ⋆)
  ; negativeLogPowersOverPositiveIntegersExact =
      λ point index →
        Terms.negativeLogOneMinusTerm concreteCoefficients point index
          ≡ Bishop.bishopMul (pow point (suc index))
              ((invPos (suc index)) ⋆)
  ; sineAlternatingSignsExact =
      λ point index →
        Terms.alternatingSign (suc index)
          ≡ Bishop.bishopNeg (Terms.alternatingSign index)
  ; cosineAlternatingSignsExact =
      λ point index →
        Terms.alternatingSign (suc index)
          ≡ Bishop.bishopNeg (Terms.alternatingSign index)
  }

concreteElementarySeries : Series.BishopElementaryPowerSeriesData
concreteElementarySeries =
  Terms.asBishopElementaryPowerSeriesData
    concreteCoefficients concreteConvergenceProofs

------------------------------------------------------------------------
-- 11.  The specification fields are inhabited, not merely stated
------------------------------------------------------------------------

sineOddPowersHolds :
  ∀ point index →
  Terms.sineTerm concreteCoefficients point index
    ≡ Bishop.bishopMul (Terms.alternatingSign index)
        (Bishop.bishopMul
          (pow point (Terms.oddExponent index))
          ((invFact (Terms.oddExponent index)) ⋆))
sineOddPowersHolds point index = refl

cosineEvenPowersHolds :
  ∀ point index →
  Terms.cosineTerm concreteCoefficients point index
    ≡ Bishop.bishopMul (Terms.alternatingSign index)
        (Bishop.bishopMul
          (pow point (Terms.evenExponent index))
          ((invFact (Terms.evenExponent index)) ⋆))
cosineEvenPowersHolds point index = refl

exponentialPowersHolds :
  ∀ point index →
  Terms.exponentialTerm concreteCoefficients point index
    ≡ Bishop.bishopMul (pow point index) ((invFact index) ⋆)
exponentialPowersHolds point index = refl

negativeLogPowersHolds :
  ∀ point index →
  Terms.negativeLogOneMinusTerm concreteCoefficients point index
    ≡ Bishop.bishopMul (pow point (suc index)) ((invPos (suc index)) ⋆)
negativeLogPowersHolds point index = refl

alternatingSignsHolds :
  ∀ index →
  Terms.alternatingSign (suc index)
    ≡ Bishop.bishopNeg (Terms.alternatingSign index)
alternatingSignsHolds index = refl

------------------------------------------------------------------------
-- 12.  Proof levels
------------------------------------------------------------------------

concreteReciprocalCoefficientLevel : ProofLevel
concreteReciprocalCoefficientLevel = machineChecked

concreteElementarySeriesConvergenceLevel : ProofLevel
concreteElementarySeriesConvergenceLevel = machineChecked
