import Integration.MonsterFifteen
import AgdaMirror.MonsterWalk
import Cuisine.SafetyFabric

/-!
# Census of the corpus's `Ultrametric` instances

`Ultrametric.agda` is one of the corpus's structural hubs (in-degree 73 in the
Agda import graph).  The record is a socket: it says only that a `Nat`-valued
distance is reflexive-zero, symmetric and satisfies the strong triangle
inequality.  Consumers build instances all over the corpus and never compare
them, so it is not visible from the source whether "the ultrametric" means one
geometry or many.

This file settles the question for every live instance in the Lean cutset.  The
answer is that they are all one geometry — the prefix/agreement distance of
`Integration.Address` — pulled back along various maps, with exactly one
exception, which is not an ultrametric at all:

| instance | source | verdict |
|---|---|---|
| `AgdaMirror.MonsterProjection15.UMask15` | `MonsterUltrametric15.agda` | prefix geometry (`d15_eq_prefix`) |
| `Synthesis.MonsterFibre.USSP` | transported onto the 15-prime fibre | prefix geometry (`dSSP_eq_dist`) |
| `Integration.MonsterFifteen.fabricUltrametric` | ternary hyperfabric | prefix geometry by definition |
| `Integration.Address.Addr.ultrametric` | `SSP369Ultrametric.agda` | the geometry itself |
| `Cuisine.SafetyFabric.USafety` | a culture-domain instance | pullback of the prefix geometry (`dSafety_eq_prefix`) |
| `AgdaMirror.MonsterWalk.UMask` | `Monster/Ultrametric.agda` | **not** an ultrametric; and provably not a prefix geometry (`walk_not_prefix`) |

The last row is the interesting one.  The Agda `Monster.Ultrametric` module
*postulates* the strong triangle law for its first-difference distance; the
mirror already disproves the postulate (`dMask_ultratriangle_false`).  Here we
draw the structural consequence: because the prefix distance satisfies the law,
no relabelling whatsoever can present the walk distance as a prefix distance.
So the corpus contains two genuinely different "Monster distances", one sound
and one built on a false postulate, and they are not isomorphic.
-/

namespace Integration.UltrametricCensus

open Integration.Address
open Integration.MonsterFifteen
open AgdaMirror.MonsterProjection15 (Mask15 d15 dMask lcpLen)
open Synthesis.MonsterFibre (dSSP maskListEquiv)

/-! ## The supplied length-15 mask carrier -/

/-- A supplied length-15 mask read as a depth-15 boolean address. -/
def mask15Addr (m : Mask15) : Addr 15 Bool := maskListEquiv.symm m

/-- **The supplied `UMask15` is the depth-15 prefix geometry.** -/
theorem d15_eq_prefix (m m' : Mask15) :
    d15 m m' = Addr.dist (mask15Addr m) (mask15Addr m') := by
  have hm : List.ofFn (mask15Addr m) = m.val :=
    congrArg Subtype.val (maskListEquiv.apply_symm_apply m)
  have hm' : List.ofFn (mask15Addr m') = m'.val :=
    congrArg Subtype.val (maskListEquiv.apply_symm_apply m')
  show dMask m.val m'.val = _
  rw [← hm, ← hm']
  simp only [dMask, List.length_ofFn, Addr.dist, Addr.agreeA]
  rw [lcpLen_ofFn 15]

/-- …and the record itself carries that distance. -/
theorem UMask15_d_eq_prefix :
    AgdaMirror.MonsterProjection15.UMask15.d =
      fun m m' => Addr.dist (mask15Addr m) (mask15Addr m') := by
  funext m m'; exact d15_eq_prefix m m'

/-! ## A domain instance: the cuisine safety field -/

open Cuisine.SafetyFabric (SafetyField dSafety doubtMask USafety)

/-- **The culture-domain safety ultrametric is the prefix geometry, pulled back
along the doubt mask.**  So a cuisine-layer construction, the Monster 15-prime
mask layer and the ternary address geometry are one metric object; the only
domain-specific content is the map `doubtMask`. -/
theorem dSafety_eq_prefix (x y : SafetyField) :
    dSafety x y = Addr.dist (maskAddr (doubtMask x)) (maskAddr (doubtMask y)) :=
  dSSP_eq_dist _ _

theorem USafety_d_eq_prefix :
    USafety.d = fun x y => Addr.dist (maskAddr (doubtMask x)) (maskAddr (doubtMask y)) := by
  funext x y; exact dSafety_eq_prefix x y

/-! ## The exception: the walk distance -/

/-- **The `Monster` walk distance is not a prefix geometry.**  Not merely "the
obvious map fails": no map at all into any depth-`n` address space over any
alphabet presents it as a prefix distance, because the prefix distance satisfies
the strong triangle law and the walk distance does not.  (The Agda module
postulates that law; the mirror's `dMask_ultratriangle_false` refutes it.) -/
theorem walk_not_prefix {n : ℕ} {α : Type} [DecidableEq α] [Inhabited α] :
    ¬ ∃ f : AgdaMirror.MonsterWalk.Mask → Addr n α,
        ∀ x y, AgdaMirror.MonsterWalk.dMask x y = Addr.dist (f x) (f y) := by
  rintro ⟨f, hf⟩
  refine AgdaMirror.MonsterWalk.dMask_ultratriangle_false (fun x y z => ?_)
  rw [hf x z, hf x y, hf y z]
  exact Addr.dist_ultratriangle (f x) (f y) (f z)

/-- The same obstruction stated against the two sound Monster geometries: the
walk distance is not the length-15 mask distance under any relabelling. -/
theorem walk_not_mask15 :
    ¬ ∃ f : AgdaMirror.MonsterWalk.Mask → Mask15,
        ∀ x y, AgdaMirror.MonsterWalk.dMask x y = d15 (f x) (f y) := by
  rintro ⟨f, hf⟩
  exact walk_not_prefix (α := Bool) (n := 15)
    ⟨fun m => mask15Addr (f m), fun x y => (hf x y).trans (d15_eq_prefix _ _)⟩

/-! ## Summary -/

/-- The census as one checked conjunction: four instances are the prefix
geometry, and the fifth provably is not. -/
theorem ultrametric_census :
    (∀ m m' : Mask15, d15 m m' = Addr.dist (mask15Addr m) (mask15Addr m')) ∧
      (∀ x y, dSSP x y = Addr.dist (maskAddr x) (maskAddr y)) ∧
      (∀ x y : SafetyField,
          dSafety x y = Addr.dist (maskAddr (doubtMask x)) (maskAddr (doubtMask y))) ∧
      (∀ F G, fabricDist F G = Addr.dist (fabricAddr F) (fabricAddr G)) ∧
      ¬ ∃ f : AgdaMirror.MonsterWalk.Mask → Addr 15 Bool,
          ∀ x y, AgdaMirror.MonsterWalk.dMask x y = Addr.dist (f x) (f y) :=
  ⟨d15_eq_prefix, dSSP_eq_dist, dSafety_eq_prefix, fun _ _ => rfl, walk_not_prefix⟩

end Integration.UltrametricCensus
