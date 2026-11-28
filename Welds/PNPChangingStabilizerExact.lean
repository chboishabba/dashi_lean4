import Welds.RecursiveHyperfabricQuotientExact
import Welds.PNPHyperfabricActualEpochPackingExact

namespace RecursiveHyperfabricQuotient

-- A finite refinement is a partition of original lifts, not a new
-- quotient mass convention. Counts are constant on a certified orbit.
theorem uniform_mass_partition {I X : Type*} [DecidableEq X]
    (ids : Finset I) (parts : I → Finset X) (O : Finset X)
    (unit mass : Nat)
    (cover : O.card = ∑ i ∈ ids, (parts i).card)
    (hm : mass = O.card * unit) :
    (∑ i ∈ ids, (parts i).card * unit) = mass := by
  rw [← Finset.sum_mul, ← cover, ← hm]

-- Build the actual original member from an old representative. The
-- caller supplies the action's validity and key transport.
def refineLift {G X K : Type*} [Group G] [MulAction G X] [MulAction G K]
    (key : X → K) (equivariant : ∀ a : G, ∀ x, key (a • x) = a • key x)
    (x : X) (k : K) (a : G) (h : a • key x = k) :
    {y : X // key y = k} :=
  ⟨a • x,(equivariant a x).trans h⟩

-- An actual original-lift partition by a finer key; this equivalence
-- witnesses disjointness and coverage rather than assuming cardinality.
def SplitFibre {X K L : Type*} (fine : X → L) (coarse : L → K) (k : K) :=
  Σ l : {l : L // coarse l = k}, {x : X // fine x = l.val}

def splitFibreEquiv {X K L : Type*} (fine : X → L) (coarse : L → K)
    (k : K) : {x : X // coarse (fine x) = k} ≃ SplitFibre fine coarse k where
  toFun x := ⟨⟨fine x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun p := ⟨p.2.val,by rw [p.2.property]; exact p.1.property⟩
  left_inv x := by cases x; rfl
  right_inv p := by
    rcases p with ⟨⟨l,hl⟩,⟨x,hx⟩⟩
    subst l
    rfl

-- Two-orbit separation, not merely the choice of an anchor.
def TwoOrbitHit {G X I : Type*} [Group G] [MulAction G X]
    (coord : X → I → Bool) (R : Set I) (x y : X) : Prop :=
  ∀ a b : G, ∃ i ∈ R, coord (a • x) i ≠ coord (b • y) i

theorem twoOrbitHit_iff {G X I : Type*} [Group G] [MulAction G X]
    (coord : X → I → Bool) (R : Set I) (x y : X) :
    TwoOrbitHit (G:=G) coord R x y ↔
      ∀ a : G, OrbitHit (G:=G) coord R (a • x) y := Iff.rfl

theorem twoOrbitHit_representatives {G X I : Type*} [Group G] [MulAction G X]
    (coord : X → I → Bool) (R : Set I) (x y : X) (a b : G)
    (h : TwoOrbitHit (G:=G) coord R x y) :
    TwoOrbitHit (G:=G) coord R (a • x) (b • y) := by
  intro c d
  simpa only [mul_smul] using h (c*a) (d*b)

-- Actual consumer distinction remains a separate requirement.
theorem twoOrbit_consumer_distinct {G X Y : Type*} [Group G] [MulAction G X]
    (f : X → Y) (inv : ∀ a : G, ∀ x, f (a • x) = f x)
    (x y : X) (h : f x ≠ f y) (a b : G) :
    f (a • x) ≠ f (b • y) := by simpa only [inv] using h

-- A finite exact future-state quotient needs a congruence for the next
-- transition; consumer agreement alone only certifies the current readout.
structure Dynamics {X K Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) (advance : X → X) (reduced : K → K) where
  commutes : ∀ x, q.contract (advance x) = reduced (q.contract x)

theorem iterate_commutes {X K Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) (advance : X → X) (reduced : K → K)
    (h : Dynamics q advance reduced) (n : Nat) (x : X) :
    q.contract ((advance^[n]) x) = (reduced^[n]) (q.contract x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h.commutes]

theorem iterate_consumer {X K Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) (advance : X → X) (reduced : K → K)
    (h : Dynamics q advance reduced) (n : Nat) (x : X) :
    g ((reduced^[n]) (q.contract x)) = f ((advance^[n]) x) := by
  rw [← iterate_commutes q advance reduced h n x]
  exact q.consumerClosed _

end RecursiveHyperfabricQuotient
