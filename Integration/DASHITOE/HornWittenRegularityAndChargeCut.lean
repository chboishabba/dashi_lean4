import Mathlib

/-!
# Horned SU3 vs Witten SU3_1: perfectness and norm regularity max-cut

ORIGINAL SOURCES:
Hatcher, Algebraic Topology, Example 2B.2: injective group-tower
m_w=[m_{w0},m_{w1}] for the classical Alexander horned complement.
Classical group theory: homomorphisms into abelian groups annihilate
commutators (trivial abelianization of the perfect horn group).
Elementary unitary operator-norm estimate:
 ||[X,Y]-1|| <= 2 ||X-1|| ||Y-1||.
Lacki/Zaugg 1989: SU2_4 -> SU3_1 conformal extension and its pointed
C3 fusion *of chiral simple-object labels*.
Sibling Agda PR #1247 fixes a NON-CENTRAL matrix W in SU3; this
unmerged matrix/Agda proof is not imported into this Lean module.

This file proves mathematical envelope and abelian-target consequences
under explicit recursive/horn-map hypotheses. It does NOT construct
the wild embedding, uniformly short geometric loops, a bounded
connection, a representation of a VOA into a physical gauge theory,
or kernel-certified analytic holonomy.
-/

namespace DASHIHornWittenRegularity

/-- The scalar envelope after n layers of a full binary
commutator tree, assuming leaves have common operator gap <= eps.
Its use as a matrix bound requires the external UNITARY commutator
norm lemma and the original group's physical meridian relation. -/
def commutatorEnvelope (eps : ℚ) : ℕ → ℚ
  | 0 => eps
  | n + 1 =>
      2 * commutatorEnvelope eps n * commutatorEnvelope eps n

/-- 1/2 is the nonzero fixed point of the elementary quadratic
envelope. At any depth, a root gap >1/2 rules out every leaf
having gap <=1/2, conditional on the group/holonomy correspondence. -/
theorem halfIsFixedAtEveryDepth (n : ℕ) :
    commutatorEnvelope (1 / 2 : ℚ) n = 1 / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [commutatorEnvelope, ih]
      norm_num

/-- Finite-depth strict obstruction. In application,
h is obtained from the analytic unitary commutator estimate
and the assumption of 2^n uniformly small leaves. -/
theorem noSelectedRootWithAllSmallLeaves
    (delta : ℚ) (n : ℕ) (hdelta : 1 / 2 < delta)
    (hbound : delta ≤ commutatorEnvelope (1 / 2 : ℚ) n) : False := by
  rw [halfIsFixedAtEveryDepth] at hbound
  exact not_lt_of_ge hbound hdelta

/-- A group homomorphism into an ABELIAN gauge-charge group kills
every commutator, regardless of the chosen non-abelian source group.
This is the actual obstruction to interpreting SU3_1 pointed C3
fusion labels as a direct group character on horn meridians. -/
theorem commutatorMapsTrivially
    {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (x y : G) :
    f (x * y * x⁻¹ * y⁻¹) = 1 := by
  simp [map_mul, mul_comm, mul_left_comm, mul_assoc]

/-- If every selected meridian is a commutator of its children,
then any abelian-target charge maps EVERY meridian to identity.
To deduce f is globally trivial one also needs the original
Hatcher theorem that those meridians generate the group. -/
theorem hornMeridiansHaveTrivialAbelianCharge
    {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A)
    (m child0 child1 : ℕ → G)
    (hrec : ∀ w : ℕ,
      m w = child0 w * child1 w * (child0 w)⁻¹ * (child1 w)⁻¹)
    (w : ℕ) : f (m w) = 1 := by
  rw [hrec w]
  exact commutatorMapsTrivially f (child0 w) (child1 w)

/-- Concrete C3-charge statement, with no phase/braiding promoted
from SU3_1 as an actual horned SU3 matrix or state. -/
theorem pointedZMod3CommutatorIsZero (a b : ZMod 3) :
    a + b - a - b = 0 := by
  abel

/-- Original selected cyclotomic trace from sibling #1247:
tr(W)=a+b*zeta3; its coefficients are not those of any scalar
SU(3) centre representative 3,3*zeta3,3*zeta3^2.
These coefficients are a source-labelled fixture, NOT a
kernel reconstruction of W's 3x3 matrix. -/
def rootTraceRational : ℚ :=
  176093404722400 / 181846007130841
def rootTraceZeta : ℚ :=
  -(19836986431118 / 181846007130841)

theorem selectedRootTraceIsNotCentre :
    (rootTraceRational, rootTraceZeta) ≠ ((3 : ℚ), 0) ∧
    (rootTraceRational, rootTraceZeta) ≠ ((0 : ℚ), 3) ∧
    (rootTraceRational, rootTraceZeta) ≠ ((-3 : ℚ), -3) := by
  norm_num [rootTraceRational, rootTraceZeta]


/-- Original #1247 exact Galois character gives the REAL trace coefficient.
For zeta3=-1/2+i sqrt(3)/2 the real trace is a-b/2.
These numbers are source data; no new physical SU3 connection is asserted. -/
def selectedRootRealTrace : ℚ :=
  rootTraceRational - rootTraceZeta / 2

/-- For a 3×3 UNITARY W, the known standard norm theorem is
    ||W-I||_F²=6-2 Re(tr W) and
    ||W-I||_op² >= (||W-I||_F²)/3.
The real/complex norm inequality is an external geometry lemma,
NOT kernel-established by this purely rational arithmetic module. -/
def selectedRootOpGapSquaredLower : ℚ :=
  (6 - 2 * selectedRootRealTrace) / 3

/-- Exact selected-source lower bound using no numerical eigensolver. -/
theorem selectedRootGapCertificate :
    selectedRootRealTrace = 221179426799 / 216225930001 ∧
    selectedRootOpGapSquaredLower =
      854996726408 / 648677790003 ∧
    (1 : ℚ) < selectedRootOpGapSquaredLower := by
  norm_num [selectedRootRealTrace, selectedRootOpGapSquaredLower,
    rootTraceRational, rootTraceZeta]

/-- CONDITIONAL full-depth finite no-go: given the analytical
    source matrix inequality (the selected q is <= delta²), a
    certified nonnegative operator gap delta and the source tree's
    all-leaf epsilon=1/2 upper estimate, contradiction follows
    at ANY finite depth. The geometric all-leaf bound is UNPAID. -/
theorem halfLengthCutoffContradiction
    (delta : ℚ) (n : ℕ)
    (hgapNonneg : 0 ≤ delta)
    (hsourceNorm : selectedRootOpGapSquaredLower ≤ delta ^ 2)
    (hsmallLeaves : delta ≤ commutatorEnvelope (1 / 2 : ℚ) n) :
    False := by
  rw [halfIsFixedAtEveryDepth] at hsmallLeaves
  have hq : (1 : ℚ) < selectedRootOpGapSquaredLower :=
    selectedRootGapCertificate.2.2
  nlinarith [sq_nonneg delta]

/-- Exact countermodel coefficient: a loop of radius r=1/n
    repeated n² times encloses oriented area pi*N*r²=pi
    while its geometric diameter 2/n tends to zero and its
    arclength grows as 2 pi n. This is a smooth NON-FLAT
    background-curvature fixture, not a horn meridian. -/
theorem highWindingSmallDiameterCanHaveFixedFlux (n : ℚ)
    (hn : n ≠ 0) :
    n ^ 2 * (1 / n) ^ 2 = 1 := by
  field_simp
  ring

theorem highWindingLoopLengthGrows (n : ℚ)
    (hn : n ≠ 0) : n ^ 2 * (1 / n) = n := by
  field_simp
  ring

end DASHIHornWittenRegularity
