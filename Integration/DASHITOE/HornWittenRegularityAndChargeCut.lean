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


/-- Finite-depth monotone envelope on the WHOLE interval 0<=eps<=1/2,
not just at the epsilon=1/2 fixed point. This is pure rational
arithmetic and does not prove its input is a geometric holonomy. -/
theorem envelopeInHalfInterval (eps : ℚ)
    (heps0 : 0 ≤ eps) (hepsHalf : eps ≤ 1 / 2) :
    ∀ n : ℕ, 0 ≤ commutatorEnvelope eps n ∧
      commutatorEnvelope eps n ≤ 1 / 2 := by
  intro n
  induction n with
  | zero =>
      exact ⟨heps0, hepsHalf⟩
  | succ n ih =>
      let x : ℚ := commutatorEnvelope eps n
      have hx0 : 0 ≤ x := ih.1
      have hxHalf : x ≤ 1 / 2 := ih.2
      have hprod : 0 ≤ (1 / 2 - x) * (1 / 2 + x) := by
        exact mul_nonneg (sub_nonneg.mpr hxHalf) (by linarith)
      change 0 ≤ 2 * x * x ∧ 2 * x * x ≤ 1 / 2
      constructor
      · positivity
      · nlinarith [hprod]

/-- Exactly the target physical acceptance interface.
M is a SOURCE-BOUNDED compatible connection 1-form norm,
ell is a SOURCE-PROVED uniform length bound on genuine
marked meridians at a COMPLETE Hatcher depth n,
and htree is the analytic iterated unitary commutator
bound after parallel-transport conjugation. The caller
must provide these actual geometric/analytic witnesses;
this arithmetic proof cannot create them. -/
theorem selectedRootFiniteGeometricLengthNoGo
    (M ell delta : ℚ) (n : ℕ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell)
    (hlengthCut : M * ell ≤ 1 / 2)
    (hunitaryTrace : selectedRootOpGapSquaredLower ≤ delta ^ 2)
    (hdeltaNonneg : 0 ≤ delta)
    (hsourceTree : delta ≤ commutatorEnvelope (M * ell) n) :
    False := by
  have hsmall : 0 ≤ M * ell := mul_nonneg hM hell
  have hhalf : commutatorEnvelope (M * ell) n ≤ 1 / 2 :=
    (envelopeInHalfInterval (M * ell) hsmall hlengthCut n).2
  have hq : (1 : ℚ) < selectedRootOpGapSquaredLower :=
    selectedRootGapCertificate.2.2
  have hgapHalf : delta ≤ 1 / 2 := le_trans hsourceTree hhalf
  nlinarith


/-- The OTHER worker's selected #1247 SU3 Wilson W is not conjugate
to ANY element of the STANDARD real icosahedral inclusion
A5 < SO(3) < SU(3): its cyclotomic zeta coefficient b is nonzero,
hence Im Tr(W)=b*sqrt(3)/2 is nonzero; every real SO3 matrix has
real trace and complex SU3 conjugation preserves trace.
The Lie/character implication is source mathematics, not formalized
here as an SU3 matrix equivalence; this theorem certifies b ≠ 0. -/
theorem selectedWilsonTraceNotRealInIcosahedralSense :
    rootTraceZeta ≠ 0 := by
  norm_num [rootTraceZeta]

/-- Exact rational certificate for the NONZERO imaginary trace:
(Im Tr W)^2 = 3 b^2/4 >0, conditional only on the original source
unit complex zeta3 phase. -/
theorem selectedWilsonImaginaryTraceSquarePositive :
    0 < (3 / 4 : ℚ) * rootTraceZeta ^ 2 := by
  have hb : rootTraceZeta ≠ 0 :=
    selectedWilsonTraceNotRealInIcosahedralSense
  have hs : 0 < rootTraceZeta ^ 2 := sq_pos_of_ne_zero hb
  positivity


end DASHIHornWittenRegularity
