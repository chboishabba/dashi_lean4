import Mathlib
import Integration.DASHITOE.Core
import Integration.DASHITOE.K27TransverseDuadCharacterCut
import Integration.DASHITOE.WittenCSWZWMonsterChiralCut

/-!
Source-matched algebraic leaves from Agda #1554 (P0AM–AO).
This is a companion to the existing K27 / Witten / TOE owners, not a
continuum Einstein solver or an actual Monster representation.
Source-written; no kernel receipt is asserted for this commit.
-/
namespace DASHITOE.HopfMonsterSourceCut

/-- The direct periodic Hopf seed has a common normal factor s = sqrt S.
The prescribed tangential derivative coefficient is 2*j/s. The result is
the scalar multiplier of the identity after contraction with H inverse. -/
theorem seedJumpMultiplier (s j : ℚ) (hs : s ≠ 0) :
    s / 2 * (2 * j / s) = j := by
  field_simp <;> ring

/-- Pure-tension scalar seam factor after the conformal change.
t is kappa*T, u is the positive conformal factor. -/
theorem conformalJumpMultiplier (u t : ℚ) (hu : u ≠ 0) :
    ((-t / 3) + (t / 3 * (u - u ^ 2)) / u) / u = -t / 3 := by
  field_simp <;> ring

/-- Exact algebra of the decaying lower and upper boundary barriers.
e is the chosen eta value, d is the small barrier amplitude. -/
theorem lowerBarrierResidual (t d e : ℚ) :
    -t*d*e/3 + t/3*((1-d*e)-(1-d*e)^2) = -t*d^2*e^2/3 := by ring

theorem upperBarrierResidual (t d e : ℚ) :
    t*d*e/3 + t/3*((1+d*e-2*d^2*e^2)-(1+d*e-2*d^2*e^2)^2) =
      t*d^2*e^2*(1+4*d*e-4*d^2*e^2)/3 := by ring

/-- Published M2 linear exterior carrier, half copy and natural parity.
These are exact arithmetic checks, not exterior action construction. -/
def halfEven : Nat := 4 * Nat.choose 24 2 + 4 * Nat.choose 24 4
def halfOdd : Nat := Nat.choose 24 1 + 6 * Nat.choose 24 3 + Nat.choose 24 5

theorem halfParity : halfEven = 43608 ∧ halfOdd = 54672 := by
  decide

theorem naturalFullParity :
    300 + 2 * halfEven = 87516 ∧ 24 + 2 * halfOdd = 109368 := by decide

theorem dressedFullParity :
    300 + halfEven + halfOdd = 98580 ∧
    24 + halfEven + halfOdd = 98304 := by decide

/-- Selected rank-eight block cycle with arbitrary real degree-preserving
order-three flavour mixing, not every C3 action or the full Monster. -/
theorem selectedTriadicCharacterNoGo (m : ℤ) : 96 - 24*m ≠ 54 := by omega

/-- On the chosen zero-KK tower the AdS3 dimension starts at three.
Arithmetic consequence of the source separated operator; no PDE proof. -/
theorem zeroKKMassPositive (n : Nat) : 3 ≤ (n+1)*(n+3) := by
  nlinarith [Nat.zero_le n]

/-- Reuse the original signed-duad and chiral CS/WZW negative controls. -/
theorem originalComparisonControls :
    (36 : ℤ) ≠ 20 ∧ (5 : ℕ) ≠ 1 :=
  ⟨DASHIK27Transverse.atlas2ACharacterMismatch,
   DASHIWittenCSWZW.noDirectChiralBlockIdentification⟩

/-- The original TOE grade rule forbids a coordinate-only donor
from promoting the physical Monster edge. -/
theorem coordinateDonorDoesNotPromote :
    composeGrade .sharedCarrier .conjecturalStructural = .conjecturalStructural := rfl

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Polynomial graph metric equality along the full chosen affine path.
The variables are scalar evaluations on two original tangents, not
an asserted Lorentzian manifold or integrated action. -/
theorem kkGraphPath (g dg a b da db f k df dk r dr t : ℚ) :
    g + t*dg + (r+t*dr)*((f+t*df)+(a+t*da))*((k+t*dk)+(b+t*db)) =
    g + t*dg + (r+t*dr)*((a+f)+t*(da+df))*((b+k)+t*(db+dk)) := by ring

/-- Original AK warp lapse equation, after selecting its first integral. -/
theorem periodicWarpLapse (c h b v : ℚ)
    (hv : v^2 = c^2*b^2-h^2) :
    b^2*(-12*h^2)-12*b^2*v^2+12*c^2*b^4 = 0 := by
  rw [hv]
  ring

/-- Warp variation of the same reduced EH density at unit normal lapse. -/
theorem periodicWarpEulerLagrange (c h b v w : ℚ)
    (hv : v^2 = c^2*b^2-h^2) (hw : w = c^2*b) :
    2*b*(-12*h^2)-24*b*v^2-24*b^2*w+48*c^2*b^3 = 0 := by
  rw [hv, hw]
  ring

/-- The boundary term obtained by varying the same warped EH action,
including the periodic pure-tension surface action. -/
theorem periodicWarpSeam (b t : ℚ) :
    -24*b^2*(-t*b/3)-8*t*b^3 = 0 := by ring

/-- Integrated bulk total derivative b^3 b' yields the supplied relation
between warp moments and tension. This lemma pays only its algebraic
consequence, not the integration or the continuum variation. -/
theorem periodicWarpReducedPotential (c h I2 I4 t : ℚ)
    (ht : t = 3*(4*c^2*I4-3*h^2*I2)) :
    24*c^2*I4-12*h^2*I2-2*t = 6*h^2*I2 := by
  rw [ht]
  ring

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Signed null endpoints in the same KK graph quadratic. -/
theorem kkSignedNullEndpoints (q r a p : ℚ) (hq : q = -r*p^2) :
    q+r*((p-a)+a)^2 = 0 ∧ q+r*((-p-a)+a)^2 = 0 := by
  rw [hq]
  constructor <;> ring

theorem kkSignedEndpointRecovery (a p : ℚ) :
    ((p-a)+(-p-a))/2 = -a ∧ ((p-a)-(-p-a))/2 = p := by
  constructor <;> ring

/-- Any nonnegative positive-fibre penalty preserves the base causal
inequality. Conversely the original horizontal lift has zero penalty.
This is ordered-field algebra for the selected pointwise cone. -/
theorem kkConeProjects (q r w : ℚ) (hr : 0 ≤ r)
    (h : q+r*w^2 ≤ 0) : q ≤ 0 := by
  have hp : 0 ≤ r*w^2 := mul_nonneg hr (sq_nonneg w)
  linarith

theorem kkHorizontalCausalLift (q r : ℚ) (h : q ≤ 0) :
    q+r*(0:ℚ)^2 ≤ 0 := by simpa using h

/-- Finite null probes in a source-orthonormal frame recover each
time-space cross term and diagonal relation, then each spatial cross
term. The global metric and measured frame are not supplied here. -/
theorem oppositeNullProbes (a b c : ℚ)
    (hp : a+2*b+c=0) (hm : a-2*b+c=0) :
    b=0 ∧ c = -a := by constructor <;> linarith

theorem mixedNullProbe (a b : ℚ)
    (h : a + (3/5:ℚ)^2*(-a) + (4/5:ℚ)^2*(-a) +
      2*(3/5:ℚ)*(4/5:ℚ)*b = 0) : b=0 := by linarith

/-- A selected positive time coordinate does not make a two-time
quadratic causal set convex. -/
theorem twoTimeConeNonconvexControl :
    -(1:ℤ)^2-2^2+2^2 < 0 ∧
    -(1:ℤ)^2-(-2)^2+2^2 < 0 ∧
    0 < -(2:ℤ)^2-0^2+4^2 := by norm_num

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Original selected six-neighbour impulse readout. The signed centre
and marked neighbour recover both coupling and mass squared. -/
theorem selectedImpulseProbeInverse (k m : ℚ) :
    (k, - (-(m+6*k)) - 6*k) = (k,m) := by
  congr 1 <;> ring

theorem selectedImpulseProbeRightInverse (neighbor center : ℚ) :
    (neighbor, -((-center-6*neighbor)+6*neighbor)) = (neighbor,center) := by
  congr 1 <;> ring

/-- The principal symbol in the calibrated clock chart follows after
removing the lower-order mass and dividing by the measured c².
This is only the coefficient identity, not a wave convergence proof. -/
theorem selectedPhysicalPrincipal (c ω x y z m : ℚ) :
    (-ω^2+c^2*(x^2+y^2+z^2)+m)-m =
      -ω^2+c^2*(x^2+y^2+z^2) := by ring

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Real and imaginary components of the ORIGINAL selected amplitudes
(1,b+i*d), after a late real rotation of the pointer. This is a
conditioned amplitude identity, not an unconditioned signal. -/
theorem lateRotationWeightSum (c s b d : ℚ)
    (h : c*c+s*s=1) :
    (c+b*s)^2+(d*s)^2+(-s+b*c)^2+(d*c)^2 = 1+b*b+d*d := by
  calc
    _ = (c*c+s*s)*(1+b*b+d*d) := by ring
    _ = _ := by rw [h]; ring

/-- Each already registered branch has the same unconditioned norm
after a complete final measurement. -/
theorem lateRotationBranchNorm (c s : ℚ) (h : c*c+s*s=1) :
    c^2+s^2=1 ∧ (-s)^2+c^2=1 := by
  constructor <;> nlinarith

/-- ABL's incoherent positive denominator does not imply nonzero
coherent weak overlap. Original source amplitudes (1,-1). -/
theorem ablPositiveWeakOverlapZero :
    (0:ℚ) < 1^2+(-1)^2 ∧ (1:ℚ)+(-1)=0 := by norm_num

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Cross-multiplied normalized conditional derivative and inverse.
No derivative or positive denominator is inferred from this algebra. -/
theorem conditionalResponseNumerator (a b da db : ℚ) :
    da*(a+b)-a*(da+db)=da*b-a*db := by ring

theorem conditionalResponseReconstruct (a b da db : ℚ) :
    (da*b-a*db)+a*(da+db)=da*(a+b) := by ring

theorem binarySelectionCovariance (p x y a b : ℚ) :
    p*x*a+(1-p)*y*b-(p*x+(1-p)*y)*(p*a+(1-p)*b) =
      p*(1-p)*(x-y)*(a-b) := by ring

/-- The two polynomial families for the original 5^3 torus:
ordinary endpoint count versus shortest-path count divided by d!.
Not a native proof of the graph enumeration correspondence. -/
theorem periodFiveThreeCoordination (z : ℚ) :
    (1+2*z+2*z^2)^3 =
      1+6*z+18*z^2+32*z^3+36*z^4+24*z^5+8*z^6 := by ring

theorem periodFiveThreePathEGF (z : ℚ) :
    (1+2*z+z^2)^3 = (1+z)^6 := by ring

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Original six marked axis channels, now with unequal pair couplings. -/
theorem anisotropicMassInverse (x y z m : ℚ) :
    - (-(m+2*x+2*y+2*z))-2*x-2*y-2*z=m := by ring

theorem anisotropicMassRightInverse (x y z center : ℚ) :
    - ((-center-2*x-2*y-2*z)+2*x+2*y+2*z)=center := by ring

/-- The calibrated six-direction stencil determines all its coefficients
from the symmetric principal matrix. Positivity is a separate condition. -/
theorem sixDirectionPrincipalInverse (x y z u v w : ℚ) :
    (x+u+v-u-v, y+u+w-u-w, z+v+w-v-w, u,v,w) =
      (x,y,z,u,v,w) := by
  have hx : x+u+v-u-v=x := by ring
  have hy : y+u+w-u-w=y := by ring
  have hz : z+v+w-v-w=z := by ring
  rw [hx, hy, hz]

/-- Equal principal quadratic need not identify the fourth moment. -/
theorem oppositeDiagonalSamePrincipal (x y : ℚ) :
    (x+y)^2+(x-y)^2=2*(x^2+y^2) := by ring

theorem oppositeDiagonalQuarticResidual (x y : ℚ) :
    (x+y)^4+(x-y)^4-2*(x^4+y^4)=12*x^2*y^2 := by ring

/-- Two signed shortest paths cancel. A positive diagonal can make
the full stiffness positive without removing this cancellation. -/
theorem signedDiamondCancellation : (1:ℚ)*1+1*(-1)=0 := by norm_num

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Real and imaginary polarization on the selected rational-complex
coordinate. The imaginary sign uses conjugate-linear first argument.
The existing Bishop complex span compiler remains the transport owner. -/
theorem complexRealPolarization (a b c d : ℚ) :
    ((a+c)^2+(b+d)^2)-((a-c)^2+(b-d)^2) = 4*(a*c+b*d) := by ring

theorem complexImagPolarization (a b c d : ℚ) :
    ((a-d)^2+(b+c)^2)-((a+d)^2+(b-c)^2) = -4*(a*d-b*c) := by ring

/-- Coordinate kinetic density fixes the scale of the inverse metric,
not just its cone. Algebraic scalar factor at a nondegenerate density. -/
theorem actionDensityReopens (rho v k : ℚ) (hv : v ≠ 0) :
    v*(-rho/v) = -rho ∧ v*(k/v) = k := by
  constructor <;> field_simp

/-- The layered flux corrector, with the effective coefficient already
defined by the reciprocal mean. No general homogenization theorem. -/
theorem layeredFluxMean (p a b ke : ℚ)
    (h : ke*(p*a+(1-p)*b)=1) :
    p*(ke*a)+(1-p)*(ke*b)=1 := by
  calc
    _ = ke*(p*a+(1-p)*b) := by ring
    _ = 1 := h

end DASHITOE.HopfMonsterSourceCut
