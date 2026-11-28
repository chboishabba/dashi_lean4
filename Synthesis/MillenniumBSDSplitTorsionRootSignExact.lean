import Synthesis.MillenniumBSDActualDoublingArithmeticExact

/-!
Original split cubic after shifting one root to zero:
Y²=u(u+a)(u+b). Translation by that root's two-torsion point
has U=ab/u, V=-abY/u². The three tangent square roots transform
by (+,-,-), the literal Weil pairing sign row. These are coordinate
identities on the nonexceptional chart; the actual point group and
Galois-character comparison must consume them.
-/
namespace DASHI.BSD.SplitTangent
variable {F : Type*} [Field F] [CharZero F]

def shiftedSlope (a b u Y : F) :=
  (3*u^2+2*(a+b)*u+a*b)/(2*Y)
def rootZero (a b u Y : F) := (a*b-u^2)/(2*Y)
def rootA (a b u Y : F) := -(u^2+2*a*u+a*b)/(2*Y)
def rootB (a b u Y : F) := -(u^2+2*b*u+a*b)/(2*Y)

theorem tangentRoots_closed (a b u Y : F)
    (hu : u ≠ 0) (ha : u+a ≠ 0) (hb : u+b ≠ 0) (hy : Y ≠ 0)
    (hc : Y^2=u*(u+a)*(u+b)) :
    Y/u-shiftedSlope a b u Y=rootZero a b u Y ∧
    Y/(u+a)-shiftedSlope a b u Y=rootA a b u Y ∧
    Y/(u+b)-shiftedSlope a b u Y=rootB a b u Y := by
  unfold shiftedSlope rootZero rootA rootB
  constructor
  · field_simp [hu,hy] <;> nlinarith [hc]
  constructor
  · field_simp [ha,hy] <;> nlinarith [hc]
  · field_simp [hb,hy] <;> nlinarith [hc]

def torsionU (a b u : F) := a*b/u
def torsionV (a b u Y : F) := -(a*b*Y/u^2)

/-- The translated coordinates stay on the same original curve.
Applying the translation twice returns the original point. -/
theorem shiftedTorsion_geometry (a b u Y : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0)
    (hc : Y^2=u*(u+a)*(u+b)) :
    (torsionV a b u Y)^2 =
      torsionU a b u*(torsionU a b u+a)*(torsionU a b u+b) ∧
    torsionU a b (torsionU a b u)=u ∧
    torsionV a b (torsionU a b u) (torsionV a b u Y)=Y := by
  unfold torsionU torsionV
  constructor
  · field_simp [ha,hb,hu] <;> ring_nf at hc ⊢
    linear_combination (a^2*b^2)*hc
  constructor <;> field_simp [ha,hb,hu] <;> ring

theorem shiftedTorsion_rootSigns (a b u Y : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (hy : Y ≠ 0) :
    rootZero a b (torsionU a b u) (torsionV a b u Y)=rootZero a b u Y ∧
    rootA a b (torsionU a b u) (torsionV a b u Y) = -rootA a b u Y ∧
    rootB a b (torsionU a b u) (torsionV a b u Y) = -rootB a b u Y := by
  unfold rootZero rootA rootB torsionU torsionV
  constructor
  · field_simp [ha,hb,hu,hy] <;> ring
  constructor <;> field_simp [ha,hb,hu,hy] <;> ring

/-- Exact chord intersection giving the coordinate translation law.
The negative third intersection is the translated point. -/
theorem shiftedTorsion_chord (a b u Y t : F) (hu : u ≠ 0)
    (hc : Y^2=u*(u+a)*(u+b)) :
    t*(t+a)*(t+b)-(Y/u*t)^2=t*(t-u)*(t-torsionU a b u) := by
  unfold torsionU
  field_simp [hu]
  ring_nf at hc ⊢
  linear_combination -t^2*hc

end DASHI.BSD.SplitTangent
