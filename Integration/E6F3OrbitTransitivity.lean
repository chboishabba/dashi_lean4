import Integration.E6PGSp4ExteriorSquare
import Mathlib

/-!
# Six-generator transitivity on the F3^5 quadratic strata

The existing reduced E6 simple reflections preserve the standard quadratic
form.  Instead of enumerating the full generated 51,840-element matrix group,
this owner saturates one finite seed under the six generators.

Exact finite saturation reaches every point of each nonzero quadratic stratum:

* nonzero Q=0: 80 points;
* Q=1: 90 points;
* Q=2: 72 points.

Thus transitivity is paid independently of the still-separate full group-order
closure theorem.
-/

namespace Integration.E6F3OrbitTransitivity

open Integration.E6F3ExteriorSquare
open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction
open Integration.E6PGSp4ExteriorSquare

/-- E6 reflection action on the Q=1 shell. -/
def reflectQ1 (s : E6SimpleReflection) (z : StandardQ1) : StandardQ1 :=
  ⟨reflectV5 s z.1, by
    rw [reflectV5_preserves_quadratic, z.2]⟩

/-- E6 reflection action on the Q=2 shell. -/
def reflectQ2 (s : E6SimpleReflection) (z : StandardQ2) : StandardQ2 :=
  ⟨reflectV5 s z.1, by
    rw [reflectV5_preserves_quadratic, z.2]⟩

/-- One generator-saturation step. -/
def expandOrbit {α : Type*} [Fintype α] [DecidableEq α]
    (act : E6SimpleReflection → α → α) (S : Finset α) : Finset α :=
  S ∪ Finset.univ.biUnion (fun g : E6SimpleReflection => S.image (act g))

/-- Bounded saturation from one seed. -/
def orbitN {α : Type*} [Fintype α] [DecidableEq α]
    (act : E6SimpleReflection → α → α) (seed : α) : Nat → Finset α
  | 0 => {seed}
  | n + 1 => expandOrbit act (orbitN act seed n)

/-- Concrete nonzero Q=0 seed `(0,1,1,2,0)`. -/
def nullSeed : StandardNull :=
  ⟨![0,1,1,2,0], by native_decide⟩

/-- Concrete Q=1 seed `(1,0,0,0,0)`. -/
def q1Seed : StandardQ1 :=
  ⟨![1,0,0,0,0], by native_decide⟩

/-- Concrete Q=2 seed `(1,1,0,0,0)`. -/
def q2Seed : StandardQ2 :=
  ⟨![1,1,0,0,0], by native_decide⟩

/-- Nine rounds suffice for the 80-point null orbit. -/
def nullOrbit : Finset StandardNull :=
  orbitN reflectStandardNull nullSeed 9

/-- Nine rounds suffice for the 90-point norm-one orbit. -/
def q1Orbit : Finset StandardQ1 :=
  orbitN reflectQ1 q1Seed 9

/-- Twenty-one rounds suffice for the 72-point E6 root/norm-two orbit. -/
def q2Orbit : Finset StandardQ2 :=
  orbitN reflectQ2 q2Seed 21

/-- The six simple reflections reach all 80 nonzero null vectors. -/
theorem null_orbit_full : nullOrbit = Finset.univ := by
  native_decide

/-- The same generators reach all 90 norm-one vectors. -/
theorem q1_orbit_full : q1Orbit = Finset.univ := by
  native_decide

/-- The same generators reach all 72 norm-two/root vectors. -/
theorem q2_orbit_full : q2Orbit = Finset.univ := by
  native_decide

theorem null_orbit_card : nullOrbit.card = 80 := by
  rw [null_orbit_full]
  exact standardNull_card

theorem q1_orbit_card : q1Orbit.card = 90 := by
  rw [q1_orbit_full]
  exact standardQ1_card

theorem q2_orbit_card : q2Orbit.card = 72 := by
  rw [q2_orbit_full]
  exact standardQ2_card

/-- Pointwise reachability form: every null point belongs to the generated
finite saturation of the selected seed. -/
theorem null_reachable (z : StandardNull) : z ∈ nullOrbit := by
  rw [null_orbit_full]
  simp

theorem q1_reachable (z : StandardQ1) : z ∈ q1Orbit := by
  rw [q1_orbit_full]
  simp

theorem q2_reachable (z : StandardQ2) : z ∈ q2Orbit := by
  rw [q2_orbit_full]
  simp

structure Boundary where
  sameSixE6GeneratorsConsumed : Bool
  nullOrbitTransitivePaid : Bool
  q1OrbitTransitivePaid : Bool
  q2OrbitTransitivePaid : Bool
  nullOrbitSize80Paid : Bool
  q1OrbitSize90Paid : Bool
  q2OrbitSize72Paid : Bool
  fullGeneratedGroupOrderNeededForTransitivity : Bool
  rawT4PunctureIdentifiedWithNullOrbit : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sameSixE6GeneratorsConsumed := true
  nullOrbitTransitivePaid := true
  q1OrbitTransitivePaid := true
  q2OrbitTransitivePaid := true
  nullOrbitSize80Paid := true
  q1OrbitSize90Paid := true
  q2OrbitSize72Paid := true
  fullGeneratedGroupOrderNeededForTransitivity := false
  rawT4PunctureIdentifiedWithNullOrbit := false

end Integration.E6F3OrbitTransitivity
