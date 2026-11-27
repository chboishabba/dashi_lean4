import Integration.Griess1990Moufang81ActualAlbertOrder13
import Integration.AlbertScalarTraceless
import Mathlib

/-!
# ACTUAL traceless 26D Albert module under Griess's order13 automorphism

Original source for Griess g and the 27D Albert:
R. L. Griess Jr., J. Algebra 131 (1990), 281-293,
DOI 10.1016/0021-8693(90)90176-O.

Do not reintroduce a cardinality proxy `26=2*13`.
We restrict the SAME native rational Albert automorphism via the
ACTUAL trace functional diag0+diag1+diag2, using explicitly selected
basis vectors e0-e1, e1-e2, and the 24 off-diagonal octonion axes.
Thus Q27 = Q·unit ⊕ ker(trace), dim ker(trace)=26.

Independent exact Python checked this very coordinate embedding,
the inherited 26D operator, and the stronger 27D rational charpoly:
  χ27 = (X−1)^3 Φ13(X)^2;
so the 26D traceless restriction has
  χ26 = (X−1)^2 Φ13(X)^2,
fixed dimension2 and two 12D rational cyclotomic blocks.
Every nonidentity power has trace 0 on this *actual* 26D module.
The 26D deductions use classical linear algebra and cyclotomic
irreducibility, not brute symbolic expansion of a 26x26 determinant.

Proof boundary: all finite Lean theorem targets below are SOURCE
WRITTEN but UNCOMPILED. This is not a F4 automorphism-group
classification, a selected Monster VOA 3B mode or a physical action.
Ibrahim A027907 shares arithmetic 26=2*13 but has no authority to
identify the corresponding representations.
-/

namespace Integration.Griess1990AlbertOrder13Traceless26

open Integration.Griess1990Moufang81ActualAlbertOrder13
open Integration.Griess1990RationalTrialityMatrixWitness

/-- Actual native rational Albert trace in the already established
coordinate order. -/
def coordinateTrace (v : Fin 27 → ℚ) : ℚ :=
  v 0 + v 1 + v 2

/-- The exact selected rational traceless basis:
[e0-e1, e1-e2, off12(8), off20(8), off01(8)]. -/
def tracelessBasis (j : Fin 26) (i : Fin 27) : ℚ :=
  if j = 0 then
    (if i = 0 then 1 else if i = 1 then -1 else 0)
  else if j = 1 then
    (if i = 1 then 1 else if i = 2 then -1 else 0)
  else
    if i.val = j.val + 1 then 1 else 0

/-- Explicit inverse coordinates on the actual kernel of trace. -/
def projectTraceless (v : Fin 27 → ℚ) (j : Fin 26) : ℚ :=
  if j = 0 then v 0
  else if j = 1 then -(v 2)
  else v (Fin.ofNat 27 (j.val + 1))

def injectTraceless (v : Fin 26 → ℚ) : Fin 27 → ℚ :=
  fun i => ∑ j : Fin 26, tracelessBasis j i * v j

theorem each_basis_trace_zero :
    ∀ j : Fin 26, coordinateTrace (tracelessBasis j) = 0 := by
  native_decide

theorem projection_is_left_inverse_on_basis :
    ∀ j : Fin 26,
      projectTraceless (tracelessBasis j) =
        (fun k : Fin 26 => if k = j then (1 : ℚ) else 0) := by
  native_decide

/-- The selected explicit 26x26 linear operator, NOT a 240-point
permutation or an arbitrary isomorphic 26D set. -/
def nativeTracelessOrder13 : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j =>
    projectTraceless
      (applyWitness nativeOrder13Matrix (tracelessBasis j)) i

/-- Exact preservation of the native Albert trace by the
already actual 27D Jordan automorphism. -/
theorem native_order_thirteen_preserves_trace_on_basis :
    ∀ j : Fin 27,
      coordinateTrace (fun i => nativeOrder13Matrix i j) =
        coordinateTrace (fun i => if i = j then (1 : ℚ) else 0) := by
  native_decide

/-- Check the 26 tracezero basis vectors. Extension to all rational
linear combinations follows from bilinearity, and avoids trying
to decision-evaluate an infinite universal Q-vector quantifier. -/
theorem traceless_action_is_same_native_action_on_basis :
    ∀ j : Fin 26,
      injectTraceless (fun i => nativeTracelessOrder13 i j) =
      applyWitness nativeOrder13Matrix (tracelessBasis j) := by
  native_decide

theorem native_traceless_order_thirteen :
    nativeTracelessOrder13 ^ 13 = 1 := by
  native_decide

/-- Cheaper trace fingerprint than a 26x26 characteristic
polynomial: the root-of-unity order13 and fixed dimension2
determine χ26 over Q by irreducibility of Φ13. -/
theorem native_traceless_trace_nonidentity_powers :
    ∀ k : Fin 12,
      Matrix.trace (nativeTracelessOrder13 ^ (k.val + 1)) = 0 := by
  native_decide

end Integration.Griess1990AlbertOrder13Traceless26
