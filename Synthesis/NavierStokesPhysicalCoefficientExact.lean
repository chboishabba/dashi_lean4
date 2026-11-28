import Synthesis.NavierStokesCoerciveNonlinearRootExact
import Mathlib

/-! Source formulas: Alpöge–Buckmaster ad53419, CertCell/StatementDefs
(labelTime, labelAzimuth, labelFlip), Cert/ExtendedCoerciveDefs
(baseDensity). Classical integer algebra and weighted quadratic bounds.
These are literal formula specializations, not imports of the upstream
certificate or assertions of its inhabitation. -/
namespace Synthesis
noncomputable section

abbrev NSLabel := ℤ × ℤ

def nsLabelTime (i : NSLabel) : ℤ := 2*i.2-i.1
def nsLabelAzimuth (m : ℤ) (i : NSLabel) : ℤ := i.1*m
def nsLabelHarmonic (m : ℤ) (i : NSLabel) : NSLabel :=
  (nsLabelTime i,nsLabelAzimuth m i)
def nsLabelFlip (i : NSLabel) : NSLabel := (-i.1,i.2-i.1)

theorem nsLabelFlipInvolutive (i : NSLabel) :
    nsLabelFlip (nsLabelFlip i) = i := by
  rcases i with ⟨a,b⟩
  apply Prod.ext <;> simp [nsLabelFlip] <;> ring

theorem nsLabelFlipTransport (m : ℤ) (i : NSLabel) :
    nsLabelHarmonic m (nsLabelFlip i) =
      (nsLabelTime i,-nsLabelAzimuth m i) := by
  apply Prod.ext <;> simp [nsLabelHarmonic,nsLabelFlip,nsLabelTime,nsLabelAzimuth] <;> ring

theorem nsLabelAdd (m : ℤ) (i j : NSLabel) :
    nsLabelHarmonic m (i.1+j.1,i.2+j.2) =
      (nsLabelTime i+nsLabelTime j,nsLabelAzimuth m i+nsLabelAzimuth m j) := by
  apply Prod.ext <;> simp [nsLabelHarmonic,nsLabelTime,nsLabelAzimuth] <;> ring

theorem nsLabelInjective (m : ℤ) (hm : m ≠ 0) :
    Function.Injective (nsLabelHarmonic m) := by
  intro i j h
  have ha : i.1*m = j.1*m := congrArg Prod.snd h
  have ht : 2*i.2-i.1 = 2*j.2-j.1 := congrArg Prod.fst h
  have h1 : i.1 = j.1 := mul_right_cancel₀ hm ha
  apply Prod.ext h1
  omega

theorem nsLabelZero (m : ℤ) (hm : m ≠ 0) (i : NSLabel) :
    nsLabelHarmonic m i = (0,0) ↔ i = (0,0) := by
  constructor
  · intro h
    apply nsLabelInjective m hm
    simpa [nsLabelHarmonic,nsLabelTime,nsLabelAzimuth] using h
  · rintro rfl
    simp [nsLabelHarmonic,nsLabelTime,nsLabelAzimuth]

/-- Exact inverse lattice, with parity retained; no quotient by C3. -/
theorem nsLabelLatticeBidi (m t a : ℤ) :
    (∃ i : NSLabel, nsLabelHarmonic m i = (t,a)) ↔
      ∃ n : ℤ, a = n*m ∧ 2 ∣ t+n := by
  constructor
  · rintro ⟨i,hi⟩
    have ht : 2*i.2-i.1 = t := congrArg Prod.fst hi
    have ha : i.1*m = a := congrArg Prod.snd hi
    refine ⟨i.1,ha.symm,i.2,?_⟩
    omega
  · rintro ⟨n,ha,b,hb⟩
    refine ⟨(n,b),?_⟩
    apply Prod.ext
    · change 2*b-n = t
      omega
    · exact ha.symm

/-- Literal upstream five-channel baseDensity with the two
second-derivative weight norms as scalar inputs. -/
def nsBaseDensity (d z c w dd dz x2 xc x1 xo x0 : ℝ) : ℝ :=
  (d-c)*x2^2+(1-d)*xc^2+(1/4-z)*xo^2+
    (z-dd-c*w)*x1^2-dz*x0^2

/-- Exact signed perturbation of all five channels. No nonnegative
assumption on the coefficients. -/
theorem nsBaseDensityDifference
    (d z c w dd dz d' z' c' w' dd' dz' x2 xc x1 xo x0 : ℝ) :
    nsBaseDensity d z c w dd dz x2 xc x1 xo x0 -
      nsBaseDensity d' z' c' w' dd' dz' x2 xc x1 xo x0 =
    ((d-d')-(c-c'))*x2^2-(d-d')*xc^2-(z-z')*xo^2+
      ((z-z')-(dd-dd')-(c*w-c'*w'))*x1^2-(dz-dz')*x0^2 := by
  unfold nsBaseDensity
  ring

/-- Allocate the actual negative velocity channel against an independently
proved weighted Hardy/Poincare estimate; it cannot simply be dropped. -/
theorem nsBaseDensityLower
    (d z c w dd dz x2 xc x1 xo x0 a b : ℝ)
    (ha : a ≤ d-c) (hb : a ≤ 1-d)
    (hc : a ≤ 1/4-z) (hd : a ≤ z-dd-c*w)
    (he : dz*x0^2 ≤ b*(x2^2+xc^2+x1^2+xo^2)) :
    (a-b)*(x2^2+xc^2+x1^2+xo^2) ≤
      nsBaseDensity d z c w dd dz x2 xc x1 xo x0 := by
  have h1 := mul_le_mul_of_nonneg_right ha (sq_nonneg x2)
  have h2 := mul_le_mul_of_nonneg_right hb (sq_nonneg xc)
  have h3 := mul_le_mul_of_nonneg_right hc (sq_nonneg xo)
  have h4 := mul_le_mul_of_nonneg_right hd (sq_nonneg x1)
  unfold nsBaseDensity
  nlinarith only [h1,h2,h3,h4,he]

/-- Reverse solve a common lower coefficient margin. The four upper/lower
faces are simultaneous; incompatible weight choices are excluded. -/
theorem nsBaseCoefficientBudget (d z c w dd a : ℝ) :
    (a ≤ d-c ∧ a ≤ 1-d ∧ a ≤ 1/4-z ∧ a ≤ z-dd-c*w) ↔
    (c+a ≤ d ∧ d ≤ 1-a ∧ dd+c*w+a ≤ z ∧ z ≤ 1/4-a) := by
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem nsBaseCoefficientFeasible (c w dd a : ℝ) :
    (∃ d z : ℝ, c+a ≤ d ∧ d ≤ 1-a ∧
      dd+c*w+a ≤ z ∧ z ≤ 1/4-a) ↔
    c+2*a ≤ 1 ∧ dd+c*w+2*a ≤ 1/4 := by
  constructor
  · rintro ⟨d,z,h1,h2,h3,h4⟩
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨h1,h2⟩
    exact ⟨c+a,dd+c*w+a,le_rfl,by linarith,le_rfl,by linarith⟩

end
end Synthesis
