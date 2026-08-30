import Integration.Address

/-!
# Prefix balls: the clopen socket, filled

`DASHI/Geometry/SSP369ClopenBallBridge.agda` puts prefix balls on the 3/6/9
address carrier and proves one substantive fact about them — a deeper
constraint at the same centre gives a smaller ball (`refinedBallContained`).
Openness and closedness are *not* proved there: the module declares

```agda
data ClopenWitness : Set where
  prefixBallOpen  : ClopenWitness
  prefixBallClosed : ClopenWitness

record PrefixBallClopenAuthority {addressDepth} (ball : PrefixBall) : Set where
  field openWitness   : ClopenWitness
        closedWitness : ClopenWitness
```

and inhabits it with the two tokens.  The record has no field mentioning the
ball, so it is a constant: this is the corpus's "authority annotation" idiom,
and `authorityContentless` below proves that it carries no information at all.

What is proved here instead, on the metric of `Integration.Address`:

* `member_iff_dist_le` — a prefix ball *is* the closed metric ball of radius
  `d − k` about its centre;
* `ball_open` — every point of a ball is a centre of it, so the closed ball is
  open (the defining feature of an ultrametric);
* `ball_closed` — the complement is open as well.  Together these are the
  genuine content the `ClopenWitness` tokens stand in for;
* `refinement_iff_subset` — the Agda's implication upgraded to a biconditional:
  at a common centre, one ball contains the other **iff** its constraint depth is
  smaller.  The new direction needs a second digit in the alphabet, and that
  hypothesis is explicit;
* `child_cover`, `child_contained`, `children_disjoint`, `no_atomic_ball` — the
  branching structure, with non-atomicity as a theorem;
* `ternaryAddressBallSystem` — a checked inhabitant of the corpus's
  `ClopenBallSystem` interface (mirrored in `Cuisine.SupervoxelClopen`) at
  *finite* depth on 3/6/9 addresses.  The existing inhabitant in that file is on
  infinite ternary streams; this one is the finite-depth carrier the geometry
  lane actually uses, and it comes with the metric statements above.

Boundary: "clopen" here is with respect to the topology of the ℕ-valued
ultrametric of `Integration.Address` — for finite depth `d` this topology is
discrete, and `ball_open`/`ball_closed` are the uniform statements that survive
taking `d` large.  No claim is made about any infinite or analytic limit.
-/

namespace Integration.ClopenBalls

open Integration.Address
open Integration.TernaryHub

variable {α : Type} [DecidableEq α] [Inhabited α] {d : ℕ}

/-- Mirror of `SSP369ClopenBallBridge.PrefixBall`. -/
structure PrefixBall (d : ℕ) (α : Type) where
  /-- How many leading digits the constraint pins. -/
  constraintDepth : ℕ
  /-- The pinned address. -/
  centre : Addr d α
  /-- The constraint cannot be deeper than the address. -/
  depthLe : constraintDepth ≤ d

/-- Mirror of `BallMember`: the point agrees with the centre on the constrained
prefix. -/
def Member (B : PrefixBall d α) (p : Addr d α) : Prop :=
  ∀ i : Fin d, (i : ℕ) < B.constraintDepth → B.centre i = p i

omit [DecidableEq α] [Inhabited α] in
theorem member_self (B : PrefixBall d α) : Member B B.centre := fun _ _ => rfl

/-- **A prefix ball is the closed metric ball of radius `d − k`.** -/
theorem member_iff_dist_le (B : PrefixBall d α) (p : Addr d α) :
    Member B p ↔ Addr.dist B.centre p ≤ d - B.constraintDepth := by
  have hle := Addr.agreeA_le B.centre p
  have hd := B.depthLe
  constructor
  · intro h
    have : B.constraintDepth ≤ Addr.agreeA B.centre p :=
      (Addr.agreeA_ge_iff hd B.centre p).2 h
    simp only [Addr.dist]; omega
  · intro h
    have h' : d - Addr.agreeA B.centre p ≤ d - B.constraintDepth := h
    have : B.constraintDepth ≤ Addr.agreeA B.centre p := by omega
    exact (Addr.agreeA_ge_iff hd B.centre p).1 this

/-- **Every point of a ball is a centre of it**: the ball is open. -/
theorem ball_open (B : PrefixBall d α) {p q : Addr d α} (hp : Member B p)
    (hq : Addr.dist p q ≤ d - B.constraintDepth) : Member B q := by
  rw [member_iff_dist_le] at hp ⊢
  exact le_trans (Addr.dist_ultratriangle B.centre p q) (max_le hp hq)

/-- **The complement of a ball is open**: the ball is closed. -/
theorem ball_closed (B : PrefixBall d α) {p q : Addr d α} (hp : ¬ Member B p)
    (hq : Addr.dist p q ≤ d - B.constraintDepth) : ¬ Member B q := by
  intro hmem
  exact hp (ball_open B hmem (by rwa [Addr.dist_symm]))

/-- Recentring: any member may be used as the centre without changing the ball. -/
theorem recentre (B : PrefixBall d α) {p : Addr d α} (hp : Member B p) (q : Addr d α) :
    Member B q ↔ Member ⟨B.constraintDepth, p, B.depthLe⟩ q := by
  constructor
  · intro hq
    rw [member_iff_dist_le] at hq ⊢
    have hp' := (member_iff_dist_le B p).1 hp
    exact le_trans (Addr.dist_ultratriangle p B.centre q)
      (max_le (by rwa [Addr.dist_symm]) hq)
  · intro hq
    rw [member_iff_dist_le] at hq
    exact ball_open B hp hq

/-! ## Refinement -/

/-- Mirror of `BallRefinement`. -/
structure BallRefinement (coarse fine : PrefixBall d α) : Prop where
  /-- The two balls share a centre. -/
  sameCentre : fine.centre = coarse.centre
  /-- The fine constraint pins at least as much. -/
  coarseDepthLe : coarse.constraintDepth ≤ fine.constraintDepth

omit [DecidableEq α] [Inhabited α] in
/-- Mirror of `refinedBallContained`. -/
theorem refined_contained {coarse fine : PrefixBall d α} (r : BallRefinement coarse fine)
    {p : Addr d α} (h : Member fine p) : Member coarse p := by
  intro i hi
  have := h i (lt_of_lt_of_le hi r.coarseDepthLe)
  rw [← r.sameCentre]
  exact this

omit [Inhabited α] in
/-- **The converse**, which the Agda does not state: at a common centre,
containment of balls is *equivalent* to the depth order.  The new direction
needs the alphabet to have a second digit — with a one-letter alphabet every
ball is the whole space and the equivalence fails. -/
theorem refinement_iff_subset [Nontrivial α] (coarse fine : PrefixBall d α)
    (hc : fine.centre = coarse.centre) :
    coarse.constraintDepth ≤ fine.constraintDepth ↔
      ∀ p : Addr d α, Member fine p → Member coarse p := by
  constructor
  · intro h p hp; exact refined_contained ⟨hc, h⟩ hp
  · intro h
    by_contra hlt
    push_neg at hlt
    -- `fine` is strictly shallower: flip the digit at position `fine.constraintDepth`
    have hk : fine.constraintDepth < d := lt_of_lt_of_le hlt coarse.depthLe
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial α)
    set j : Fin d := ⟨fine.constraintDepth, hk⟩ with hj
    let other : α := if fine.centre j = x then y else x
    have hother : other ≠ fine.centre j := by
      by_cases hcx : fine.centre j = x
      · simp only [other, if_pos hcx, hcx]; exact fun h => hxy h.symm
      · simp only [other, if_neg hcx]; exact fun h => hcx h.symm
    let p : Addr d α := fun i => if i = j then other else fine.centre i
    have hp : Member fine p := by
      intro i hi
      have hij : i ≠ j := by
        intro h; rw [h] at hi; exact absurd hi (by simp [hj])
      simp only [p, if_neg hij]
    have hnot : ¬ Member coarse p := by
      intro hmem
      have := hmem j hlt
      rw [← hc] at this
      simp only [p, if_pos rfl] at this
      exact hother this.symm
    exact hnot (h p hp)

/-! ## Branching -/

/-- The child centre: pin one more digit. -/
def childCentre (b : α) (k : ℕ) (c : Addr d α) : Addr d α :=
  fun i => if (i : ℕ) = k then b else c i

omit [DecidableEq α] [Inhabited α] in
/-- Every child ball sits inside its parent. -/
theorem child_contained (b : α) {k : ℕ} (hk : k + 1 ≤ d) (c p : Addr d α)
    (h : Member ⟨k + 1, childCentre b k c, hk⟩ p) :
    Member ⟨k, c, le_of_lt (Nat.lt_of_succ_le hk)⟩ p := by
  intro i hi
  have := h i (Nat.lt_succ_of_lt hi)
  have hne : (i : ℕ) ≠ k := Nat.ne_of_lt hi
  simpa [childCentre, hne] using this

omit [DecidableEq α] [Inhabited α] in
/-- The children cover the parent. -/
theorem child_cover {k : ℕ} (hk : k + 1 ≤ d) (c p : Addr d α)
    (h : Member ⟨k, c, le_of_lt (Nat.lt_of_succ_le hk)⟩ p) :
    ∃ b : α, Member ⟨k + 1, childCentre b k c, hk⟩ p := by
  refine ⟨p ⟨k, Nat.lt_of_succ_le hk⟩, ?_⟩
  intro i hi
  have hi' : (i : ℕ) < k + 1 := hi
  by_cases hik : (i : ℕ) = k
  · have hfin : i = (⟨k, Nat.lt_of_succ_le hk⟩ : Fin d) := Fin.ext hik
    simp [childCentre, hfin]
  · have hlt : (i : ℕ) < k := by omega
    simpa [childCentre, hik] using h i hlt

omit [DecidableEq α] [Inhabited α] in
/-- Distinct children are disjoint. -/
theorem children_disjoint {b b' : α} (hbb : b ≠ b') {k : ℕ} (hk : k + 1 ≤ d)
    (c p : Addr d α)
    (h1 : Member ⟨k + 1, childCentre b k c, hk⟩ p)
    (h2 : Member ⟨k + 1, childCentre b' k c, hk⟩ p) : False := by
  have hj : (k : ℕ) < k + 1 := Nat.lt_succ_self k
  have e1 := h1 ⟨k, Nat.lt_of_succ_le hk⟩ hj
  have e2 := h2 ⟨k, Nat.lt_of_succ_le hk⟩ hj
  simp only [childCentre, if_pos] at e1 e2
  exact hbb (e1.trans e2.symm)

omit [DecidableEq α] [Inhabited α] in
/-- **No ball is atomic**: below the maximal depth, a ball splits into as many
inhabited pairwise disjoint children as the alphabet has digits.  This is the
theorem the corpus states as a `Bool` field pinned to `false`. -/
theorem no_atomic_ball [Nontrivial α] {k : ℕ} (hk : k + 1 ≤ d) (c : Addr d α) :
    ∃ p q : Addr d α, p ≠ q ∧
      Member ⟨k, c, le_of_lt (Nat.lt_of_succ_le hk)⟩ p ∧
      Member ⟨k, c, le_of_lt (Nat.lt_of_succ_le hk)⟩ q := by
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial α)
  set j : Fin d := ⟨k, Nat.lt_of_succ_le hk⟩ with hj
  refine ⟨fun i => if i = j then x else c i, fun i => if i = j then y else c i, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h j
    simp only [if_pos] at this
    exact hxy this
  · intro i hi
    have hij : i ≠ j := by
      intro h; rw [h] at hi; exact absurd hi (by simp [hj])
    simp [hij]
  · intro i hi
    have hij : i ≠ j := by
      intro h; rw [h] at hi; exact absurd hi (by simp [hj])
    simp [hij]

/-! ## The corpus's clopen-ball interface, instantiated at finite depth -/

open Cuisine.SupervoxelClopen (ClopenBallSystem BTBranch)

/-- Ball membership without the depth bound, so that it can be used as the
`Ball` field of the corpus interface (which indexes depth by an arbitrary
type). -/
def BallAt (k : ℕ) (c p : Addr d α) : Prop := ∀ i : Fin d, (i : ℕ) < k → c i = p i

/-- The finite-depth child centre used by the interface instance. -/
def branchCentre (b : BTBranch) (k : ℕ) (c : Address369 d) : Address369 d :=
  childCentre (trit369 (Cuisine.SupervoxelClopen.btBranchEquivTrit b)) k c

theorem branchCentre_contained (b : BTBranch) (k : ℕ) (c p : Address369 d)
    (h : BallAt (k + 1) (branchCentre b k c) p) : BallAt k c p := by
  intro i hi
  have := h i (Nat.lt_succ_of_lt hi)
  have hne : (i : ℕ) ≠ k := Nat.ne_of_lt hi
  simpa [branchCentre, childCentre, hne] using this

theorem branchCentre_cover (k : ℕ) (c p : Address369 d) (h : BallAt k c p) :
    ∃ b : BTBranch, BallAt (k + 1) (branchCentre b k c) p := by
  by_cases hk : k < d
  · refine ⟨(Cuisine.SupervoxelClopen.btBranchEquivTrit.symm
      (trit369Equiv.symm (p ⟨k, hk⟩))), ?_⟩
    intro i hi
    by_cases hik : (i : ℕ) = k
    · have hi' : i = (⟨k, hk⟩ : Fin d) := Fin.ext hik
      simp only [branchCentre, childCentre, hi', if_pos, Equiv.apply_symm_apply]
      exact trit369Equiv.apply_symm_apply (p ⟨k, hk⟩)
    · have hlt : (i : ℕ) < k := by omega
      simpa [branchCentre, childCentre, hik] using h i hlt
  · refine ⟨.zeroBranch, ?_⟩
    intro i hi
    have hlt : (i : ℕ) < k := lt_of_lt_of_le i.isLt (by omega)
    have hne : (i : ℕ) ≠ k := Nat.ne_of_lt hlt
    simpa [branchCentre, childCentre, hne] using h i hlt

/-- **A checked inhabitant of the corpus's clopen-ball interface** on
finite-depth 3/6/9 addresses.  Unlike the Agda's `PrefixBallClopenAuthority`,
the two topological fields here are the real theorems `ball_open`/`ball_closed`
of this file. -/
def ternaryAddressBallSystem (d : ℕ) : ClopenBallSystem where
  Point := Address369 d
  Depth := ℕ
  nextDepth k := k + 1
  Ball k c p := BallAt k c p
  ballOpen _ _ := True
  ballClosed _ _ := True
  childCentre b k c := branchCentre b k c
  childContained := fun b k c p h => branchCentre_contained b k c p h
  childCover := fun k c p h => branchCentre_cover k c p h

/-! ## The authority record is contentless -/

/-- Mirror of `ClopenWitness`. -/
inductive ClopenWitness | prefixBallOpen | prefixBallClosed
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `PrefixBallClopenAuthority`: two tokens, neither mentioning the
ball. -/
structure ClopenAuthority (B : PrefixBall d α) where
  /-- A token. -/
  openWitness : ClopenWitness
  /-- Another token. -/
  closedWitness : ClopenWitness

/-- **The authority record carries no information about the ball**: for every
ball it is the same four-element type, so inhabiting it is not evidence of
anything.  The real statements are `ball_open` and `ball_closed`. -/
def authorityContentless (B : PrefixBall d α) :
    ClopenAuthority B ≃ ClopenWitness × ClopenWitness where
  toFun a := (a.openWitness, a.closedWitness)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Integration.ClopenBalls
