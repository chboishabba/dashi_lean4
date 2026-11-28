import Synthesis.MillenniumHodgeDicksonCoupledCharacterExact
import Synthesis.MillenniumHodgeRankSixEvenSignOrientationExact

/-!
Actual degree-seven Dickson source Q0: six simultaneous quadratic root
addresses, signed derivative coordinates and their coupled product.
This constructs the affine algebraic incidence BIDI, not the Chow pushforward
or nonvanishing of its transcendental cycle-class projection.
-/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

def derivativeCoordinate (a s : ℚ) : ℚ := -4*s-3*a^2+3*a+1

def derivativeInverse (a d : ℚ) : ℚ := (-3*a^2+3*a+1-d)/4

theorem derivative_inverse_left (a s : ℚ) :
    derivativeInverse a (derivativeCoordinate a s)=s := by
  unfold derivativeInverse derivativeCoordinate
  ring

theorem derivative_inverse_right (a d : ℚ) :
    derivativeCoordinate a (derivativeInverse a d)=d := by
  unfold derivativeInverse derivativeCoordinate
  ring

/-- Literal Q0 identity with its original y+a^7/y address, not an
abstract independently chosen quadratic equation. -/
theorem derivative_discriminant_residual (a y s : ℚ) :
    derivativeCoordinate a s ^ 2-Q0Discriminant a y =
      -8*(Q0 a s-y-a^7/y) := by
  unfold derivativeCoordinate Q0Discriminant Q0
  ring

theorem Q0_root_iff_signed_discriminant (a y s : ℚ) :
    Q0 a s = y+a^7/y ↔
      derivativeCoordinate a s ^ 2=Q0Discriminant a y := by
  have h := derivative_discriminant_residual a y s
  constructor <;> intro he <;> linarith

theorem rootPartner_derivative (a s : ℚ) :
    derivativeCoordinate a (rootPartner (-2) (-3*a^2+3*a+1) s) =
      -derivativeCoordinate a s := by
  unfold derivativeCoordinate rootPartner
  ring

/-- The actual six-fold coupled algebraic equations. y≠0 is required
at every original Laurent address. The signed product is a source
coordinate, not discarded by taking its square. -/
def CoupledRoots (a y : Address → ℚ) (δ : ℚ) :=
  {s : Address → ℚ //
    (∀ i,Q0 (a i) (s i)=y i+(a i)^7/y i) ∧
    (∏ i,derivativeCoordinate (a i) (s i))=δ}

def CoupledDiscriminants (a y : Address → ℚ) (δ : ℚ) :=
  {d : Address → ℚ //
    (∀ i,(d i)^2=Q0Discriminant (a i) (y i)) ∧
    (∏ i,d i)=δ}

def coupledRootDerivativeEquiv (a y : Address → ℚ) (δ : ℚ) :
    CoupledRoots a y δ ≃ CoupledDiscriminants a y δ where
  toFun s := ⟨fun i => derivativeCoordinate (a i) (s.1 i),
    fun i => (Q0_root_iff_signed_discriminant _ _ _).mp (s.2.1 i),s.2.2⟩
  invFun d := ⟨fun i => derivativeInverse (a i) (d.1 i),by
    constructor
    · intro i
      apply (Q0_root_iff_signed_discriminant _ _ _).mpr
      rw [derivative_inverse_right]
      exact d.2.1 i
    · simp only [derivative_inverse_right]
      exact d.2.2⟩
  left_inv s := Subtype.ext (funext fun i => derivative_inverse_left _ _)
  right_inv d := Subtype.ext (funext fun i => derivative_inverse_right _ _)

/-- Exact BIDI of the nonzero product fibre: a root sign change is
allowed precisely when its six signs multiply to one. -/
theorem signed_product_fibre_iff (d e : Address → ℚ) (δ : ℚ)
    (hd : (∏ i,d i)=δ) (hδ : δ≠0) :
    (∏ i,e i*d i)=δ ↔ (∏ i,e i)=1 := by
  rw [Finset.prod_mul_distrib,hd]
  constructor
  · intro h
    exact (mul_right_cancel₀ hδ (by simpa using h : (∏ i,e i)*δ=1*δ))
  · intro h
    rw [h,one_mul]

theorem signed_product_square_necessary (a y : Address → ℚ) (δ : ℚ)
    (d : CoupledDiscriminants a y δ) :
    δ^2=∏ i,Q0Discriminant (a i) (y i) := by
  rw [← d.2.2,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  exact d.2.1 i

end
end DASHI.Hodge.DicksonCoupled
