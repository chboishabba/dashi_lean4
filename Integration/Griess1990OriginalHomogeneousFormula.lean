import Integration.Griess1990RationalTrialityFiniteProduct
import Mathlib

/-!
# Griess 1990 ORIGINAL homogeneous product, in the rational tau-real basis

External original mathematical author: Robert L. Griess Jr.,
"A Moufang loop, the exceptional Jordan algebra, and a cubic form in
27 variables", J. Algebra 131 (1990), 281--293,
DOI 10.1016/0021-8693(90)90176-O.

Original formula in an F3^3 homogeneous basis:
   e_x * e_y = (-2)^(-c(x,y)) * omega^(g(x,y)) e_(x+y)
where c=0 if dependent, 1 otherwise and
g=-x1*x2*y3-x3*y1*y2+x2*x3*y1+x1*y2*y3 (mod 3).
The source cyclotomic field has omega^2+omega+1=0.

This independently reconstructs all 729 source basis products using
ONLY FOUR homogeneous products per pair of tau-real basis vectors.
The published formula, real structure and source normalisation are
thus explicit in Lean, rather than a textual attribution attached
to a long hard-coded source tensor. A finite formula-to-table theorem
below is the remaining source-equivalence payment.

We deliberately reuse the source table and native rational Albert
carrier already on Lean #52, not reinventing octonions, F4, a spatial
P3^3 lattice or the Monster VOA Griess algebra.

IMPORTANT: proof statements are SOURCE-WRITTEN, NOT kernel checked.
No valid Lean receipt is claimed until Lake/Lean actually accepts them.
-/

namespace Integration.Griess1990OriginalHomogeneousFormula

open Integration.Griess1990RationalTrialityFiniteProduct

abbrev Cyclo := ℚ × ℚ

def oneC : Cyclo := (1, 0)
def zeroC : Cyclo := (0, 0)
def omegaC : Cyclo := (0, 1)
def omega2C : Cyclo := (-1, -1)

/-- Exact Q(omega), omega² = -1-omega. -/
def cycloMul (x y : Cyclo) : Cyclo :=
  (x.1*y.1 - x.2*y.2,
   x.1*y.2 + x.2*y.1 - x.2*y.2)

def cycloScale (t : ℚ) (x : Cyclo) : Cyclo :=
  (t*x.1, t*x.2)

/-- Grades are lexicographic x=(x1,x2,x3) with integer digits 0,1,2. -/
def gradeAdd (x y : Fin 27) : Fin 27 :=
  Fin.ofNat 27
    (9*((x.val/9 + y.val/9)%3) +
     3*((x.val/3%3 + y.val/3%3)%3) +
     ((x.val%3 + y.val%3)%3))

def gradeNeg (x : Fin 27) : Fin 27 :=
  Fin.ofNat 27
    (9*((3 - x.val/9)%3) +
     3*((3 - x.val/3%3)%3) +
     ((3 - x.val%3)%3))

/-- In F3^3 two grades are dependent precisely if one is zero
or the nonzero grades differ by one of the two nonzero scalars. -/
def gradeDependent (x y : Fin 27) : Bool :=
  (x == 0) || (y == 0) || (x == y) || (gradeNeg x == y)

/-- The explicit source phase g, using -q mod3 = (2q) mod3. -/
def gPhase (x y : Fin 27) : Nat :=
  let a := x.val/9
  let b := x.val/3%3
  let c := x.val%3
  let u := y.val/9
  let v := y.val/3%3
  let t := y.val%3
  (2*(a*b*t+c*u*v)+b*c*u+a*v*t)%3

def phasePower : Nat → Cyclo
  | 0 => oneC
  | 1 => omegaC
  | _ => omega2C

/-- Exactly (-2)^(-c(x,y))*omega^g: independent coefficient -1/2,
not -2. -/
def homogeneousCoefficient (x y : Fin 27) : Cyclo :=
  cycloScale (if gradeDependent x y then 1 else (-1/2 : ℚ))
    (phasePower (gPhase x y))

/-- The 13 antipodal grade representatives of (F3^3 \\ {0})/(±1),
in the original tau-real/source-coordinate order. -/
def antipodalRepresentative : Fin 13 → Fin 27 :=
  ![1,3,4,5,9,10,11,12,13,14,15,16,17]

/-- Each tau-real source basis vector is supported on at most two
homogeneous grades; the first is e0 and each subsequent pair is
u_a=e_a+e_-a, v_a=omega e_a+omega² e_-a. -/
def modeGrade (i : Fin 27) (t : Fin 2) : Fin 27 :=
  if i = 0 then 0 else
    let a := antipodalRepresentative (Fin.ofNat 13 ((i.val-1)/2))
    if t = 0 then a else gradeNeg a

def modeCoefficient (i : Fin 27) (t : Fin 2) : Cyclo :=
  if i = 0 then
    if t = 0 then oneC else zeroC
  else if (i.val-1)%2 = 0 then oneC
  else if t = 0 then omegaC else omega2C

/-- Four products (two-by-two homogeneous supports), not 27² terms. -/
def homogeneousProductAt (i j a : Fin 27) : Cyclo :=
  ∑ t : Fin 2, ∑ u : Fin 2,
    if gradeAdd (modeGrade i t) (modeGrade j u) = a then
      cycloMul (cycloMul (modeCoefficient i t)
        (modeCoefficient j u))
        (homogeneousCoefficient (modeGrade i t) (modeGrade j u))
    else zeroC

/-- Convert the source tau-real vector to the actual rational coefficient
coordinates (A,B) of the representative e_a coefficient A+B omega.
The conjugate e_-a coefficient is forced by the source real structure. -/
def originalSourceCoefficient (i j k : Fin 27) : ℚ :=
  if k = 0 then
    (homogeneousProductAt i j 0).1
  else
    let a := antipodalRepresentative (Fin.ofNat 13 ((k.val-1)/2))
    let v := homogeneousProductAt i j a
    if (k.val-1)%2 = 0 then v.1 else v.2

/-- This closes the SOURCE FORMULA -> previously independently computed
tau-real structure table boundary once kernel checked.
It is NOT a replacement for the separately named native-algebra
729-basis isomorphism theorem; both are necessary. -/
theorem original_formula_equals_source_tensor :
    ∀ i j k : Fin 27,
      originalSourceCoefficient i j k = sourceTensor i j k := by
  native_decide

/-- Source order-three identity and inverse homogeneous grading checks. -/
theorem grade_order_three :
    ∀ x : Fin 27, gradeAdd x (gradeAdd x x) = 0 := by
  native_decide

theorem grade_opposite :
    ∀ x : Fin 27, gradeAdd x (gradeNeg x) = 0 := by
  native_decide

end Integration.Griess1990OriginalHomogeneousFormula
