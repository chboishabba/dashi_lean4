import Integration.EisensteinJZeroLocalEulerExact
import Mathlib.FieldTheory.Finite.Basic

namespace Dashi.EisensteinJZeroInertPrimeEulerExact

/-- Affine points of the same `j=0` cubic after reduction to `F_p`. -/
def JZeroAffinePoint (p : Nat) :=
  {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + 1}

/-- For `p ≡ 2 (mod 3)`, this exponent is the inverse of cubing modulo
`p-1`: if `p = 3k+2`, then `3(2k+1)=2(p-1)+1`. -/
def inertCubeRootExponent (p : Nat) : Nat := 2 * (p / 3) + 1

private theorem inert_prime_shape (p : Nat) (hmod : p % 3 = 2) :
    p = 3 * (p / 3) + 2 := by
  have h := Nat.mod_add_div p 3
  omega

private theorem inert_cube_exponent_identity (p : Nat) (hmod : p % 3 = 2) :
    inertCubeRootExponent p * 3 = 2 * (p - 1) + 1 := by
  have hp := inert_prime_shape p hmod
  simp only [inertCubeRootExponent]
  omega

/-- The explicit inverse-to-cubing formula on an inert prime field. -/
def inertCubeRoot (p : Nat) (a : ZMod p) : ZMod p :=
  a ^ inertCubeRootExponent p

/-- Cubing the explicit root returns the original field element.  The nonzero
case is exactly Fermat's theorem plus `3e = 2(p-1)+1`; zero is immediate. -/
theorem inertCubeRoot_cube
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) (a : ZMod p) :
    (inertCubeRoot p a) ^ 3 = a := by
  by_cases ha : a = 0
  · simp [inertCubeRoot, ha]
  · have hfermat : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
    have hexp := inert_cube_exponent_identity p hmod
    simp only [inertCubeRoot]
    rw [← pow_mul, hexp]
    calc
      a ^ (2 * (p - 1) + 1)
          = (a ^ (p - 1)) ^ 2 * a := by
              rw [pow_add, pow_mul]
      _ = a := by rw [hfermat]; simp

/-- Applying the explicit inverse after cubing also returns the input. -/
theorem inertCubeRoot_cube_left
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) (a : ZMod p) :
    inertCubeRoot p (a ^ 3) = a := by
  by_cases ha : a = 0
  · simp [inertCubeRoot, ha]
  · have hfermat : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
    have hexp := inert_cube_exponent_identity p hmod
    simp only [inertCubeRoot]
    rw [← pow_mul]
    have hcomm : 3 * inertCubeRootExponent p = 2 * (p - 1) + 1 := by
      simpa [Nat.mul_comm] using hexp
    rw [hcomm]
    calc
      a ^ (2 * (p - 1) + 1)
          = (a ^ (p - 1)) ^ 2 * a := by
              rw [pow_add, pow_mul]
      _ = a := by rw [hfermat]; simp

/-- Cubing is therefore an explicit equivalence of `F_p` whenever
`p ≡ 2 (mod 3)`. -/
noncomputable def cubeMapEquiv
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) : ZMod p ≃ ZMod p where
  toFun x := x ^ 3
  invFun := inertCubeRoot p
  left_inv := inertCubeRoot_cube_left p hmod
  right_inv := inertCubeRoot_cube p hmod

/-- The headline finite-field permutation theorem. -/
theorem cubeMap_bijective
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) :=
  (cubeMapEquiv p hmod).bijective

/-- Every `y ∈ F_p` determines exactly one affine point because cubing is a
bijection: solve `x³ = y²-1`. -/
noncomputable def yEquivAffinePoint
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    ZMod p ≃ JZeroAffinePoint p where
  toFun y := by
    let x := (cubeMapEquiv p hmod).symm (y ^ 2 - 1)
    refine ⟨(x, y), ?_⟩
    have hx : x ^ 3 = y ^ 2 - 1 := by
      simpa [x, cubeMapEquiv] using
        (cubeMapEquiv p hmod).apply_symm_apply (y ^ 2 - 1)
    rw [hx]
    ring
  invFun P := P.1.2
  left_inv y := rfl
  right_inv P := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      have hcube : (cubeMapEquiv p hmod) P.1.1 = P.1.2 ^ 2 - 1 := by
        change P.1.1 ^ 3 = P.1.2 ^ 2 - 1
        have hp := P.2
        linear_combination -hp
      rw [← hcube, (cubeMapEquiv p hmod).symm_apply_apply]
    · rfl

/-- The affine point set has exactly `p` elements for every inert prime. -/
theorem affinePointCount_inert
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    Fintype.card (JZeroAffinePoint p) = p := by
  letI : NeZero p := ⟨Fact.out.ne_zero⟩
  calc
    Fintype.card (JZeroAffinePoint p)
        = Fintype.card (ZMod p) :=
          Fintype.card_congr (yEquivAffinePoint p hmod).symm
    _ = p := ZMod.card p

/-- Projective point count for the reduced `j=0` curve. -/
def jZeroProjectivePointCount (p : Nat) [Fintype (JZeroAffinePoint p)] : Nat :=
  Fintype.card (JZeroAffinePoint p) + 1

/-- Signed Frobenius trace `a_p = p+1-#E(F_p)`. -/
def jZeroFrobeniusTrace (p : Nat) [Fintype (JZeroAffinePoint p)] : Int :=
  (p : Int) + 1 - (jZeroProjectivePointCount p : Int)

/-- Coefficients `(1,-a_p,p)` of the local Euler polynomial. -/
def jZeroLocalEulerPolynomial (p : Nat) [Fintype (JZeroAffinePoint p)] :
    Int × Int × Int :=
  (1, -jZeroFrobeniusTrace p, (p : Int))

/-- Every inert prime has exactly `p+1` projective points on this same curve. -/
theorem projectivePointCount_inert
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroProjectivePointCount p = p + 1 := by
  simp only [jZeroProjectivePointCount, affinePointCount_inert p hmod]

/-- Hence the Frobenius trace vanishes for the entire inert residue family. -/
theorem frobeniusTrace_inert
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroFrobeniusTrace p = 0 := by
  rw [jZeroFrobeniusTrace, projectivePointCount_inert p hmod]
  norm_num

/-- And the complete inert-prime local Euler polynomial is `1 + pT²`. -/
theorem localEulerPolynomial_inert
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroLocalEulerPolynomial p = (1, 0, (p : Int)) := by
  rw [jZeroLocalEulerPolynomial, frobeniusTrace_inert p hmod]
  simp

/-- The earlier literal `p=5` row is now a specialization of the family theorem. -/
theorem five_row_recovered :
    jZeroLocalEulerPolynomial 5 = (1, 0, 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact localEulerPolynomial_inert 5 (by norm_num)

/-- Claim-strength boundary after the elementary all-inert proof.  No Hecke
character is used: split-prime trace normalization and the global elliptic
Euler product remain the next distinct arithmetic obligations. -/
structure InertPrimeEulerBoundary where
  cubePermutationAllInertPrimesPaid : Bool := true
  affineCountAllInertPrimesPaid : Bool := true
  traceZeroAllInertPrimesPaid : Bool := true
  localEulerAllInertPrimesPaid : Bool := true
  splitPrimeTraceFormulaPaid : Bool := false
  heckeCharacterNormalizationPaid : Bool := false
  globalEllipticHeckeLSeriesIdentityPaid : Bool := false

/-- Exact frontier after paying the full inert family. -/
def canonicalBoundary : InertPrimeEulerBoundary := {}

end Dashi.EisensteinJZeroInertPrimeEulerExact
