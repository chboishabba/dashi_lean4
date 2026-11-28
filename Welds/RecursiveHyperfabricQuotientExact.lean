import Welds.PNPSignedOrbitBoundaryExact
import Welds.PNPResidualGeometryBridgeExact

namespace RecursiveHyperfabricQuotient

/-- Keys are inhabited; a section is not a two-sided inverse on the
original carrier. Original lift validity belongs in X (a subtype). -/
structure Step (X K Y : Type*) (f : X → Y) (g : K → Y) where
  contract : X → K
  lift : K → X
  sectionExact : ∀ k, contract (lift k) = k
  consumerClosed : ∀ x, g (contract x) = f x

def Step.id (X Y : Type*) (f : X → Y) : Step X X Y f f :=
  ⟨id,id,fun _ => rfl,fun _ => rfl⟩

def Step.comp {X K L Y : Type*} {f : X → Y} {g : K → Y} {h : L → Y}
    (q : Step X K Y f g) (r : Step K L Y g h) : Step X L Y f h where
  contract x := r.contract (q.contract x)
  lift l := q.lift (r.lift l)
  sectionExact l := by rw [q.sectionExact,r.sectionExact]
  consumerClosed x := (r.consumerClosed _).trans (q.consumerClosed x)

theorem Step.sameKey {X K Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) {x y : X} (e : q.contract x = q.contract y) :
    f x = f y :=
  (q.consumerClosed x).symm.trans ((congrArg g e).trans (q.consumerClosed y))

theorem Step.liftConsumer {X K Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) (k : K) : f (q.lift k) = g k := by
  rw [← q.consumerClosed,q.sectionExact]

theorem Step.consumerRange {X K Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) : Set.range f = Set.range g := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨q.contract x,q.consumerClosed x⟩
  · rintro ⟨k,rfl⟩
    exact ⟨q.lift k,q.liftConsumer k⟩

-- Instantiate the diagonal gauge without losing order of nonabelian multiplication.
def diagonal {G Y : Type*} [Group G] (f : G × G → Y)
    (invariant : ∀ a x y : G, f (a*x,a*y) = f (x,y)) :
    Step (G × G) G Y f (fun k => f (k,1)) where
  contract p := p.2⁻¹*p.1
  lift k := (k,1)
  sectionExact k := by simp
  consumerClosed p := by
    simpa using invariant p.2⁻¹ p.1 p.2

-- S1: any same-key counterfactual is irrelevant to the actual consumer.
theorem noSameKeyRival {X K S Y : Type*} {f : X → Y} {g : K → Y}
    (q : Step X K Y f g) (valid : Set X) (state : X → Nat → S)
    (x y : X) (t : Nat) (e : q.contract x = q.contract y) :
    y ∉ PNPHyperfabricOwnedEvents.ReachableDivergentSet valid state f x t := by
  intro hy
  exact hy.2.2 (q.sameKey e.symm)

-- Every representative must be tested, not just a chosen canonical lift.
def OrbitHit {I X G : Type*} [Group G] [MulAction G X]
    (coord : X → I → Bool) (R : Set I) (x y : X) : Prop :=
  ∀ a : G, ∃ i ∈ R, coord x i ≠ coord (a • y) i

theorem orbitHit_iff_noAgree {I X G : Type*} [Group G] [MulAction G X]
    (coord : X → I → Bool) (R : Set I) (x y : X) :
    OrbitHit (G:=G) coord R x y ↔
      ¬ ∃ a : G, ∀ i ∈ R, coord x i = coord (a • y) i := by
  classical
  constructor
  · rintro h ⟨a,ha⟩
    obtain ⟨i,hi,hne⟩ := h a
    exact hne (ha i hi)
  · intro h a
    by_contra hn
    apply h
    refine ⟨a,?_⟩
    intro i hi
    by_contra hne
    exact hn ⟨i,hi,hne⟩

-- Receipt costs compose; they are not inferred from rank or quotient size.
structure Receipt where
  discovery : Nat
  applyCost : Nat
  liftCost : Nat
  auditCost : Nat
  failedCost : Nat
  deriving DecidableEq

def Receipt.total (r : Receipt) : Nat :=
  r.discovery+r.applyCost+r.liftCost+r.auditCost+r.failedCost

def Receipt.add (a b : Receipt) : Receipt :=
  ⟨a.discovery+b.discovery,a.applyCost+b.applyCost,a.liftCost+b.liftCost,
   a.auditCost+b.auditCost,a.failedCost+b.failedCost⟩

theorem Receipt.add_total (a b : Receipt) :
    (a.add b).total = a.total+b.total := by
  simp [Receipt.add,Receipt.total]
  omega

structure PaidStep {X K Y : Type*} (f : X → Y) (g : K → Y)
    (Physical : Nat → Prop) where
  quotient : Step X K Y f g
  receipt : Receipt
  physical : Physical receipt.total

-- Resource transport requires an actual concatenation theorem for
-- the chosen execution model, not merely logical operation estimates.
def PaidStep.comp {X K L Y : Type*} {f : X → Y} {g : K → Y} {h : L → Y}
    {P : Nat → Prop} (concat : ∀ a b, P a → P b → P (a+b))
    (q : PaidStep f g P) (r : PaidStep g h P) : PaidStep f h P where
  quotient := q.quotient.comp r.quotient
  receipt := q.receipt.add r.receipt
  physical := by
    rw [Receipt.add_total]
    exact concat _ _ q.physical r.physical

-- A compact code reader is not a decision observer. The latter has
-- its own exact relation to the original candidate's returned bit.
theorem guarded_flip_noCorrect {D : Type*} (sat dec : D → Bool) (d : D)
    (decisionFlip : sat d = !(dec d)) (correct : sat d = dec d) : False := by
  cases h : dec d <;> simp [h] at decisionFlip correct <;> simp_all

end RecursiveHyperfabricQuotient
