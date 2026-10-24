import Mathlib

/-!
# Curved Wilson transport through a marked Hatcher binary branch

For arbitrary CURVED source gauge connections the π₁ commutator
relation does NOT imply equality of Wilson matrices. Let eta(w)
BOUND THE ACTUAL geometric parent-holonomy versus the commutator
of its genuinely based/transported children. Then the exact
unitary commutator Lipschitz factor 2 gives the source-gated
inequality d(U_parent) <= eta(w)+2*d(U_chosen_child).

This module proves the recurrence and a finite rejection interface,
under explicitly provided local-error premises. Constructing the
source homotopy, its nonabelian-Stokes curvature bound, real metric
loop lengths, a selected physical connection and literal Hatcher
Z-block remains OPEN. Original Hatcher topology, independent original
Agda horn #1244 and neutrino #1247 sources retain authorship.
Native Lean kernel/typecheck unavailable in this environment.
-/

namespace DASHIHornCurvedDefect

/-- Prefix addresses: the error is incurred at each actual parent
while descending along the chosen child bits. -/
def branchErrorEnvelope (eta : List Bool → ℚ) :
    List Bool → List Bool → ℚ → ℚ
  | [], _, leaf => leaf
  | b :: rest, base, leaf =>
      eta base + 2 * branchErrorEnvelope eta rest (b :: base) leaf

/-- No FLATNESS is assumed here, because the missing geometric
homotopy curvature estimate appears as an EXPLICIT hstep. -/
theorem oneBranchWithCurvatureDefects
    {G : Type*} (U : List Bool → G) (d : G → ℚ)
    (eta : List Bool → ℚ)
    (hstep : ∀ (base : List Bool) (b : Bool),
      d (U base) ≤ eta base + 2 * d (U (b :: base)))
    (path : List Bool) :
    d (U []) ≤
      branchErrorEnvelope eta path [] (d (U path.reverse)) := by
  have haux : ∀ (p base : List Bool),
      d (U base) ≤ branchErrorEnvelope eta p base
          (d (U (p.reverse ++ base))) := by
    intro p
    induction p with
    | nil =>
        intro base
        simp [branchErrorEnvelope]
    | cons b rest ih =>
        intro base
        have hs := hstep base b
        have hr := ih (b :: base)
        calc
          d (U base) ≤ eta base + 2 * d (U (b :: base)) := hs
          _ ≤ eta base + 2 *
                branchErrorEnvelope eta rest (b :: base)
                  (d (U (rest.reverse ++ b :: base))) := by
                    linarith
          _ = branchErrorEnvelope eta (b :: rest) base
                (d (U ((b :: rest).reverse ++ base))) := by
                    simp [branchErrorEnvelope, List.reverse_cons,
                      List.append_assoc]
  simpa using haux path []

/-- Source-selected W has a previously certified strict norm-gap >1.
If a TRUE geometric/curvature defect and leaf length budget force
the weighted envelope <=1, the proposed physical connection is
incompatible with that W. The actual eta is NOT inferred from pi1. -/
theorem curvedSourceGeometricRejection
    {G : Type*} (U : List Bool → G) (d : G → ℚ)
    (eta : List Bool → ℚ)
    (hstep : ∀ (base : List Bool) (b : Bool),
      d (U base) ≤ eta base + 2 * d (U (b :: base)))
    (path : List Bool) (leafBound : ℚ)
    (hroot : 1 < d (U []))
    (hLeaf : d (U path.reverse) ≤ leafBound)
    (hEnvelopeMono : ∀ (base p : List Bool) (a b : ℚ),
      a ≤ b → branchErrorEnvelope eta p base a ≤
        branchErrorEnvelope eta p base b)
    (hCap : branchErrorEnvelope eta path [] leafBound ≤ 1) :
    False := by
  have hp := oneBranchWithCurvatureDefects U d eta hstep path
  have hb := hEnvelopeMono [] path _ _ hLeaf
  have hc : d (U []) ≤ 1 := le_trans hp (le_trans hb hCap)
  exact (not_lt_of_ge hc hroot)

/-- Heterogeneous defect envelope monotonicity, with no extra
postulate; the proof relies only on nonnegative factor 2. -/
theorem envelopeMonotone (eta : List Bool → ℚ)
    (p base : List Bool) (x y : ℚ) (hxy : x ≤ y) :
    branchErrorEnvelope eta p base x ≤
      branchErrorEnvelope eta p base y := by
  induction p generalizing base with
  | nil => simpa [branchErrorEnvelope] using hxy
  | cons b rest ih =>
      simp only [branchErrorEnvelope]
      have h := ih (b :: base)
      linarith

/-- Pure exact rational regression for the curved-source acceptance
fixture eta_k=(1/100)*(1/3)^k, length_n=(1/3)^n and M=100 at depth12
lives in the exact Python consumer. This theorem is not an actual
Stokes-area certificate or the historical horn's chosen spatial metric. -/

end DASHIHornCurvedDefect
