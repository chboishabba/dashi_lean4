{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- A constructive Riemann integral on [0,1] over the Bishop reals.
--
-- The Yang-Mills lane of this repository needs a normalised invariant
-- integral on a compact group (Haar measure); no integration theory at all
-- exists in the vendored constructive analysis library, in the Agda standard
-- library, or elsewhere in DASHI.  This module builds the first genuinely
-- missing brick: for every function with a modulus of uniform continuity the
-- sequence of uniform Riemann sums on [0,1] is a Cauchy sequence of Bishop
-- reals, hence converges, and the limit is *defined* to be the integral.
--
-- Everything here is proved.  There is no postulate, no opaque `Set` field,
-- no receipt and no appeal to an external authority.
------------------------------------------------------------------------

module DASHI.Analysis.BishopRiemannIntegral where

open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_; +≤+)
import Data.Integer.Properties as ℤP
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; *≤*; *≡*)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas

------------------------------------------------------------------------
-- Uniform partitions of [0,1].
--
-- The index `m` stands for a partition of [0,1] into `suc m` cells of width
-- `1/(suc m)`; the sample points are the left endpoints.

width : ℕ → ℚᵘ
width m = + 1 ℚ./ suc m

node : ℕ → ℕ → ℝ
node m i = (+ i ℚ./ suc m) ⋆

riemannSum : (ℝ → ℝ) → ℕ → ℝ
riemannSum f m = (width m) ⋆ * ∑₀ (λ i → f (node m i)) (suc m)

-- `refine m q` is the partition obtained by cutting every cell of the
-- partition `m` into `suc q` equal pieces.  The defining equation below holds
-- definitionally, which is what makes the block decomposition of sums apply
-- without any coercion.

refine : ℕ → ℕ → ℕ
refine m q = q ℕ.+ m ℕ.* suc q

refine-suc : ∀ m q → suc (refine m q) ≡ suc m ℕ.* suc q
refine-suc m q = refl

------------------------------------------------------------------------
-- Two rational identities, proved by integer ring arithmetic.

⋆-distrib-sub : ∀ p q → (p ℚ.- q) ⋆ ≃ p ⋆ - q ⋆
⋆-distrib-sub p q =
  ≃-trans (⋆-distrib-+ p (ℚ.- q)) (+-congʳ (p ⋆) (⋆-distrib-neg q))

private
  open ℤSolver.+-*-Solver

  posMul : ∀ m n → + (m ℕ.* n) ≡ + m ℤ.* + n
  posMul m n = ℤP.pos-* m n

  -- (1/(n·s)) · (s/1) = 1/n
  widthℤ : ∀ (n s : ℕ) →
    (+ 1 ℤ.* + s) ℤ.* + n ≡ + 1 ℤ.* + ((n ℕ.* s) ℕ.* 1)
  widthℤ n s = trans (cong (ℤ._* + n) (ℤP.*-identityˡ (+ s)))
    (trans (sym (posMul s n))
    (trans (cong +_ (ℕP.*-comm s n))
    (trans (cong +_ (sym (ℕP.*-identityʳ (n ℕ.* s))))
           (sym (ℤP.*-identityˡ (+ ((n ℕ.* s) ℕ.* 1)))))))

  -- ((i·s+k)/(n·s)) - (i/n) = k/(n·s)
  nodeℤ : ∀ (I K N S : ℤ) →
    ((I ℤ.* S ℤ.+ K) ℤ.* N ℤ.+ (ℤ.- I) ℤ.* (N ℤ.* S)) ℤ.* (N ℤ.* S)
      ≡ K ℤ.* ((N ℤ.* S) ℤ.* N)
  nodeℤ = solve 4
    (λ I K N S →
      ((I :* S :+ K) :* N :+ (:- I) :* (N :* S)) :* (N :* S)
        := K :* ((N :* S) :* N))
    refl

------------------------------------------------------------------------
-- The weight of a refined partition, times the number of subcells, is the
-- weight of the original partition.

width-refine : ∀ m q → (width (refine m q)) ⋆ * natToℝ (suc q) ≃ (width m) ⋆
width-refine m q =
  ≃-trans (*-congˡ (natToℝ-⋆ (suc q)))
  (≃-trans (≃-symm (⋆-distrib-* (width (refine m q)) (+ suc q ℚ./ 1)))
           (⋆-cong (ℚ.*≡* (widthℤ (suc m) (suc q)))))

------------------------------------------------------------------------
-- The distance between a refined node and the node it refines.

node-refine : ∀ m q i k →
  node (refine m q) (i ℕ.* suc q ℕ.+ k) - node m i
    ≃ (+ k ℚ./ suc (refine m q)) ⋆
node-refine m q i k = ≃-symm
  (≃-trans (⋆-cong eq) (⋆-distrib-sub (+ (i ℕ.* suc q ℕ.+ k) ℚ./ suc (refine m q))
                                      (+ i ℚ./ suc m)))
  where
  eq : (+ k ℚ./ suc (refine m q))
         ℚ.≃ ((+ (i ℕ.* suc q ℕ.+ k) ℚ./ suc (refine m q)) ℚ.- (+ i ℚ./ suc m))
  eq = ℚP.≃-sym (ℚ.*≡* step)
    where
    n = suc m
    s = suc q
    step : ((+ (i ℕ.* s ℕ.+ k)) ℤ.* + n ℤ.+ (ℤ.- (+ i)) ℤ.* + (n ℕ.* s))
             ℤ.* + (n ℕ.* s)
           ≡ + k ℤ.* + ((n ℕ.* s) ℕ.* n)
    step = trans (cong₂ (λ z w → (z ℤ.* + n ℤ.+ (ℤ.- (+ i)) ℤ.* w) ℤ.* w) e1 e2)
           (trans (nodeℤ (+ i) (+ k) (+ n) (+ s))
                  (cong (λ w → + k ℤ.* w) (sym e3)))
      where
      e1 : + (i ℕ.* s ℕ.+ k) ≡ + i ℤ.* + s ℤ.+ + k
      e1 = trans (ℤP.pos-+ (i ℕ.* s) k) (cong (ℤ._+ + k) (posMul i s))

      e2 : + (n ℕ.* s) ≡ + n ℤ.* + s
      e2 = posMul n s

      e3 : + ((n ℕ.* s) ℕ.* n) ≡ (+ n ℤ.* + s) ℤ.* + n
      e3 = trans (posMul (n ℕ.* s) n) (cong (ℤ._* + n) e2)

------------------------------------------------------------------------
-- A refined node is close to the node it refines.

node-close : ∀ m q d i k → k ℕ.< suc q → d ℕ.≤ m →
  ∣ node (refine m q) (i ℕ.* suc q ℕ.+ k) - node m i ∣ ≤ (+ 1 ℚ./ suc d) ⋆
node-close m q d i k k<s d≤m =
  ≤-respˡ-≃ (∣-∣-cong (≃-symm (node-refine m q i k)))
    (≤-respˡ-≃ (∣p∣⋆≃∣p⋆∣ (+ k ℚ./ suc (refine m q)))
      (p≤q⇒p⋆≤q⋆ ℚ.∣ + k ℚ./ suc (refine m q) ∣ (+ 1 ℚ./ suc d) qle))
  where
  natBound : k ℕ.* suc d ℕ.≤ suc m ℕ.* suc q
  natBound = ℕP.≤-trans (ℕP.*-mono-≤ (ℕP.≤-pred k<s) (s≤s d≤m))
    (subst (λ z → q ℕ.* suc m ℕ.≤ z) (ℕP.*-comm (suc q) (suc m))
      (ℕP.*-monoˡ-≤ (suc m) (ℕP.n≤1+n q)))

  qle : ℚ.∣ + k ℚ./ suc (refine m q) ∣ ℚ.≤ (+ 1 ℚ./ suc d)
  qle = ℚ.*≤* (subst₂ ℤ._≤_ (posMul k (suc d))
                            (sym (ℤP.*-identityˡ (+ (suc m ℕ.* suc q))))
                            (+≤+ natBound))

------------------------------------------------------------------------
-- Positivity of the cell width, and the fact that the cells of a partition
-- of [0,1] add up to 1.

0≤width : ∀ r → 0ℝ ≤ (+ 1 ℚ./ suc r) ⋆
0≤width r = p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 ℚ./ suc r) (ℚP.nonNegative⁻¹ _)

private
  widthUnitℤ : ∀ (n : ℕ) → (+ 1 ℤ.* + n) ℤ.* + 1 ≡ + 1 ℤ.* + (n ℕ.* 1)
  widthUnitℤ n = trans (ℤP.*-identityʳ (+ 1 ℤ.* + n))
    (trans (ℤP.*-identityˡ (+ n))
    (trans (cong +_ (sym (ℕP.*-identityʳ n)))
           (sym (ℤP.*-identityˡ (+ (n ℕ.* 1))))))

width-unit : ∀ m → (width m) ⋆ * natToℝ (suc m) ≃ 1ℝ
width-unit m =
  ≃-trans (*-congˡ (natToℝ-⋆ (suc m)))
  (≃-trans (≃-symm (⋆-distrib-* (width m) (+ suc m ℚ./ 1)))
           (⋆-cong (ℚ.*≡* (widthUnitℤ (suc m)))))

------------------------------------------------------------------------
-- A modulus of uniform continuity, indexed by naturals: `δ j` is a partition
-- index such that points at distance at most `1/(suc (δ j))` have values at
-- distance at most `1/(suc j)`.

record UniformModulus (f : ℝ → ℝ) : Set where
  field
    δ      : ℕ → ℕ
    δ-cont : ∀ (j : ℕ) (x y : ℝ) →
             ∣ x - y ∣ ≤ (+ 1 ℚ./ suc (δ j)) ⋆ →
             ∣ f x - f y ∣ ≤ (+ 1 ℚ./ suc j) ⋆

------------------------------------------------------------------------
-- The key estimate: refining a partition changes the Riemann sum by at most
-- the modulus of continuity of the function.

module _ (f : ℝ → ℝ) (mc : UniformModulus f) where
  open UniformModulus mc

  refinement-bound : ∀ j m q → δ j ℕ.≤ m →
    ∣ riemannSum f (refine m q) - riemannSum f m ∣ ≤ (+ 1 ℚ./ suc j) ⋆
  refinement-bound j m q hδ =
    ≤-respˡ-≃ (∣-∣-cong (≃-symm main-eq)) (≤-respˡ-≃ (≃-symm absEq) final)
    where
    open ℝ-Solver

    s n : ℕ
    s = suc q
    n = suc m

    w ε : ℝ
    w = (width (refine m q)) ⋆
    ε = (+ 1 ℚ./ suc j) ⋆

    g h : ℕ → ℝ
    g i = f (node (refine m q) i)
    h i = f (node m i)

    A B inner : ℕ → ℝ
    A i = ∑₀ (λ k → g (i ℕ.* s ℕ.+ k)) s
    B i = ∑₀ (λ k → h i) s
    inner i = ∑₀ (λ k → g (i ℕ.* s ℕ.+ k) - h i) s

    S : ℝ
    S = ∑₀ inner n

    E1 : riemannSum f (refine m q) ≃ w * ∑₀ A n
    E1 = *-congˡ (∑₀-block g n s)

    E2 : riemannSum f m ≃ w * ∑₀ B n
    E2 = ≃-symm
      (≃-trans (*-congˡ (∑₀-congruent (λ i → ∑₀-const (h i) s) n))
      (≃-trans (*-congˡ (∑₀-scale (natToℝ s) h n))
      (≃-trans (≃-symm (*-assoc w (natToℝ s) (∑₀ h n)))
               (*-congʳ (width-refine m q)))))

    E3 : w * S ≃ w * ∑₀ A n - w * ∑₀ B n
    E3 = ≃-trans
      (*-congˡ (≃-trans
        (∑₀-congruent
          (λ i → ∑₀-sub (λ k → g (i ℕ.* s ℕ.+ k)) (λ _ → h i) s) n)
        (∑₀-sub A B n)))
      (ℝ-Solver.solve 3 (λ a b c → a ⊗ (b ⊖ c) ⊜ a ⊗ b ⊖ a ⊗ c)
        ≃-refl w (∑₀ A n) (∑₀ B n))

    main-eq : riemannSum f (refine m q) - riemannSum f m ≃ w * S
    main-eq = ≃-trans (+-cong E1 (-‿cong E2)) (≃-symm E3)

    absEq : ∣ w * S ∣ ≃ w * ∣ S ∣
    absEq = ≃-trans (∣x*y∣≃∣x∣*∣y∣ w S)
      (*-congʳ (nonNegx⇒∣x∣≃x (0≤x⇒nonNegx (0≤width (refine m q)))))

    innerBound : ∀ i → ∣ inner i ∣ ≤ natToℝ s * ε
    innerBound i = ≤-trans (∑₀-abs (λ k → g (i ℕ.* s ℕ.+ k) - h i) s)
      (∑₀-const-bound-lt (λ k → ∣ g (i ℕ.* s ℕ.+ k) - h i ∣) ε s
        (λ k k<s → δ-cont j (node (refine m q) (i ℕ.* s ℕ.+ k)) (node m i)
                     (node-close m q (δ j) i k k<s hδ)))

    Sbound : ∣ S ∣ ≤ natToℝ n * (natToℝ s * ε)
    Sbound = ≤-trans (∑₀-abs inner n)
      (∑₀-const-bound (λ i → ∣ inner i ∣) (natToℝ s * ε) innerBound n)

    collapse : w * (natToℝ n * (natToℝ s * ε)) ≃ ε
    collapse = ≃-trans
      (ℝ-Solver.solve 4 (λ a b c d → a ⊗ (b ⊗ (c ⊗ d)) ⊜ ((a ⊗ c) ⊗ b) ⊗ d)
        ≃-refl w (natToℝ n) (natToℝ s) ε)
      (≃-trans (*-congʳ (*-congʳ (width-refine m q)))
      (≃-trans (*-congʳ (width-unit m)) (*-identityˡ ε)))

    final : w * ∣ S ∣ ≤ ε
    final = ≤-respʳ-≃ collapse
      (*-monoˡ-≤-nonNeg Sbound (0≤x⇒nonNegx (0≤width (refine m q))))

------------------------------------------------------------------------
-- Common refinements: `refine m₁ m₂` and `refine m₂ m₁` are the same
-- partition.

comm-refine : ∀ m₁ m₂ → refine m₁ m₂ ≡ refine m₂ m₁
comm-refine m₁ m₂ = ℕP.suc-injective (ℕP.*-comm (suc m₁) (suc m₂))

------------------------------------------------------------------------
-- The Riemann sums of a uniformly continuous function form a Cauchy
-- sequence, hence converge.  The limit is the integral.

module _ (f : ℝ → ℝ) (mc : UniformModulus f) where
  open UniformModulus mc

  riemannSum-isCauchy : (λ m → riemannSum f m) isCauchy
  riemannSum-isCauchy = cauchy* main
    where
    open ℤSolver.+-*-Solver

    main : ∀ k → .{{_ : ℕ.NonZero k}} →
      ∃ λ Mₖ-1 → ∀ m₁ m₂ → m₁ ℕ.≥ suc Mₖ-1 → m₂ ℕ.≥ suc Mₖ-1 →
      ∣ riemannSum f m₁ - riemannSum f m₂ ∣ ≤ (+ 1 ℚ./ k) ⋆
    main (suc k-1) = δ j , sub
      where
      k = suc k-1
      j = ℕ.pred (2 ℕ.* k)

      halves : (+ 1 ℚ./ (2 ℕ.* k)) ⋆ + (+ 1 ℚ./ (2 ℕ.* k)) ⋆ ≤ (+ 1 ℚ./ k) ⋆
      halves = ≤-reflexive (≃-trans
        (≃-symm (⋆-distrib-+ (+ 1 ℚ./ (2 ℕ.* k)) (+ 1 ℚ./ (2 ℕ.* k))))
        (⋆-cong (ℚ.*≡* (solve 1 (λ z →
          (con (+ 1) :* (con (+ 2) :* z) :+ con (+ 1) :* (con (+ 2) :* z)) :* z
            := con (+ 1) :* (con (+ 2) :* z :* (con (+ 2) :* z)))
          refl (+ k)))))

      sub : ∀ m₁ m₂ → m₁ ℕ.≥ suc (δ j) → m₂ ℕ.≥ suc (δ j) →
        ∣ riemannSum f m₁ - riemannSum f m₂ ∣ ≤ (+ 1 ℚ./ k) ⋆
      sub m₁ m₂ h₁ h₂ = ≤-trans t₁ (≤-trans t₂ (≤-trans t₃ halves))
        where
        M = refine m₁ m₂

        b₁ : ∣ riemannSum f M - riemannSum f m₁ ∣ ≤ (+ 1 ℚ./ (2 ℕ.* k)) ⋆
        b₁ = refinement-bound f mc j m₁ m₂ (ℕP.<⇒≤ h₁)

        b₂ : ∣ riemannSum f M - riemannSum f m₂ ∣ ≤ (+ 1 ℚ./ (2 ℕ.* k)) ⋆
        b₂ = subst
          (λ z → ∣ riemannSum f z - riemannSum f m₂ ∣ ≤ (+ 1 ℚ./ (2 ℕ.* k)) ⋆)
          (comm-refine m₂ m₁)
          (refinement-bound f mc j m₂ m₁ (ℕP.<⇒≤ h₂))

        t₁ : ∣ riemannSum f m₁ - riemannSum f m₂ ∣
               ≤ ∣ (riemannSum f m₁ - riemannSum f M)
                   + (riemannSum f M - riemannSum f m₂) ∣
        t₁ = ≤-reflexive (∣-∣-cong (ℝ-Solver.solve 3
          (λ a b c → a ⊖ b ⊜ a ⊖ c ⊕ (c ⊖ b)) ≃-refl
          (riemannSum f m₁) (riemannSum f m₂) (riemannSum f M)))
          where open ℝ-Solver

        t₂ : ∣ (riemannSum f m₁ - riemannSum f M)
               + (riemannSum f M - riemannSum f m₂) ∣
               ≤ ∣ riemannSum f m₁ - riemannSum f M ∣
                 + ∣ riemannSum f M - riemannSum f m₂ ∣
        t₂ = ∣x+y∣≤∣x∣+∣y∣ (riemannSum f m₁ - riemannSum f M)
                            (riemannSum f M - riemannSum f m₂)

        t₃ : ∣ riemannSum f m₁ - riemannSum f M ∣
               + ∣ riemannSum f M - riemannSum f m₂ ∣
               ≤ (+ 1 ℚ./ (2 ℕ.* k)) ⋆ + (+ 1 ℚ./ (2 ℕ.* k)) ⋆
        t₃ = +-mono-≤
          (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (riemannSum f M) (riemannSum f m₁)) b₁)
          b₂

  riemannSum-isConvergent : (λ m → riemannSum f m) isConvergent
  riemannSum-isConvergent = cauchy⇒convergent riemannSum-isCauchy

  -- The integral of f over [0,1].
  integral : ℝ
  integral = proj₁ riemannSum-isConvergent

  -- ... and the theorem that the uniform Riemann sums converge to it.
  riemannSum-converges : (λ m → riemannSum f m) ConvergesTo integral
  riemannSum-converges = proj₂ riemannSum-isConvergent

------------------------------------------------------------------------
-- Nondegeneracy: constants are integrable and integrate to themselves.  In
-- particular the total mass of [0,1] is 1.

constModulus : (c : ℝ) → UniformModulus (λ _ → c)
constModulus c = record
  { δ      = λ _ → 0
  ; δ-cont = λ j x y _ →
      ≤-respˡ-≃ (≃-symm (≃-trans (∣-∣-cong (+-inverseʳ c))
                                 (nonNegx⇒∣x∣≃x nonNeg0)))
                (0≤width j)
  }

riemannSum-const : ∀ (c : ℝ) m → riemannSum (λ _ → c) m ≃ c
riemannSum-const c m =
  ≃-trans (*-congˡ (∑₀-const c (suc m)))
  (≃-trans (≃-symm (*-assoc ((width m) ⋆) (natToℝ (suc m)) c))
  (≃-trans (*-congʳ (width-unit m)) (*-identityˡ c)))

integral-const : ∀ (c : ℝ) → integral (λ _ → c) (constModulus c) ≃ c
integral-const c = uniqueness-of-limits
  (riemannSum-converges (λ _ → c) (constModulus c))
  (xₙ≃c⇒xₙ→c (λ n → riemannSum-const c n))

integral-one : integral (λ _ → 1ℝ) (constModulus 1ℝ) ≃ 1ℝ
integral-one = integral-const 1ℝ
