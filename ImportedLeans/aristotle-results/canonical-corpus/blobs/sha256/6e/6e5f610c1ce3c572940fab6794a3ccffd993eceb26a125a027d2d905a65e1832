import Integration.MonsterFifteen
import Integration.SSPWeave

/-!
# Where the Boolean observer loses information — and where it does not

`Synthesis.Hyperfabric.support_not_hom` says the Boolean support map is not a
homomorphism from the ternary XOR to boolean OR.  Filed as a bare negative, that
row reads as "the 15-prime layer does not preserve algebra", which is not what it
shows: it is a statement about the last arrow of

    signed ternary state → symmetry action → coarse Boolean observer,

and the earlier arrows do preserve algebra (`Integration.SSPWeave`).  This file
scopes the negative correctly and supplies the positive statements around it.

## What the support map actually is

`support t = decide (t ≠ neg)` — the indicator of "not the `tritXor` identity"
(`tritXor_idL`), i.e. the *native-chart* nonzero test.  It is therefore **not**
polarity-invariant (`support_not_polarity_invariant`); the polarity-invariant
Boolean observer is the magnitude test `polarPresence t = decide (t ≠ zer)`,
whose origin is the polarity-fixed state.  This is the same chart split as in
`Integration.PhaseQuotient.triXor_chart_dichotomy`, one level up.

## The positive results

* `polarPresence_orbit` — `polarPresence` is **exactly** the quotient map of the
  polarity involution: two digits have the same magnitude iff they are equal or
  polarity-opposite.  So the Boolean mask layer is the orbit space of the `ℤ/2`
  symmetry, not an arbitrary coarsening.
* `polarPresence_equivariant`, `laneAction_descends` — the SSP orientation action
  **descends** along that observer, with the induced action trivial: the square
  `π (g · x) = ḡ · π x` commutes, with `ḡ = id`.  This is a genuine equivariance
  theorem for the symmetry action, in contrast to the failure for the binary law.
* `polarPresenceMask_nonexpansive` — and the induced map of fabrics is
  non-expansive for the same prefix geometry as `supportMask`.

## The negative, correctly scoped

* `support_no_descent`, `polarPresence_no_descent` — **no** binary Boolean
  operation whatsoever makes either observer a homomorphism for `tritXor`; this
  strictly strengthens `support_not_hom`, which refutes only boolean OR.
* `no_equivariant_section` — the lost information is exactly the sign: no section
  of the magnitude observer is polarity-equivariant.

## The signed layer that keeps what the observer forgets

Mirroring `DASHI/Biology/SignedMultiplicityObstructionExact.agda`: the signed
difference `delta A B i = A i - B i` over `ℤ`, its three-way orientation, the
anti-symmetry `delta_swap`/`orientation_swap`, the proof that Boolean presence
forgets multiplicity (`presence_lossy`), and `defectOrientationHub` /
`defectToFibreOrientation_equiv`: the defect orientation carrier **is** the
ternary hub and **is** the SSP `FibreOrientation` carrier, with reversal matching
the hub polarity.  So the relational/signed data is exactly the layer on which
the preserved SSP algebra lives.
-/

namespace Integration.ObserverQuotient

open Integration.Levels
open Integration.TernaryHub
open Integration.Address
open Integration.SSPWeave
open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.TritBridge (tritXor)
open Synthesis.Hyperfabric (Fabric support supportMask)
open Synthesis.MonsterFibre (MaskSSP dSSP)
open Integration.MonsterFifteen (fabricDist maskAddr dSSP_eq_dist)

/-! ## The two Boolean observers -/

/-- The corpus's support map is the indicator of "not the `tritXor` identity":
`neg` is the identity of `tritXor` (`AgdaMirror.TritBridge.tritXor_idL`). -/
theorem support_is_native_nonzero :
    (∀ t : Trit, tritXor .neg t = t) ∧ (∀ t : Trit, support t = decide (t ≠ Trit.neg)) :=
  ⟨AgdaMirror.TritBridge.tritXor_idL, fun _ => rfl⟩

/-- **The support map is not polarity-invariant**: its origin is the additive
identity of the native chart, not the fixed point of the polarity involution. -/
theorem support_not_polarity_invariant : ¬ ∀ t : Trit, support (Trit.inv t) = support t := by
  intro h; exact absurd (h .pos) (by decide)

/-- The polarity-invariant Boolean observer: the magnitude test, whose origin is
the polarity-fixed digit `zer`. -/
def polarPresence (t : Trit) : Bool := decide (t ≠ Trit.zer)

theorem polarPresence_inv (t : Trit) : polarPresence (Trit.inv t) = polarPresence t := by
  cases t <;> rfl

/-- **The magnitude observer is exactly the quotient by the polarity
involution**: two digits have the same image iff they lie in the same orbit. -/
theorem polarPresence_orbit (x y : Trit) :
    polarPresence x = polarPresence y ↔ (y = x ∨ y = Trit.inv x) := by
  revert x y; decide

theorem polarPresence_surjective : Function.Surjective polarPresence := by decide

/-! ## The symmetry action descends; the binary law does not -/

/-- The SSP orientation action read on `Trit` through `laneStateHub`. -/
def tritAction (g : FibreOrientation) (t : Trit) : Trit :=
  laneTritEquiv (laneAction g (laneTritEquiv.symm t))

theorem tritAction_inverse (t : Trit) : tritAction .inverse t = Trit.inv t := by
  cases t <;> rfl

theorem tritAction_comp (q p : FibreOrientation) (t : Trit) :
    tritAction (composeOrientation q p) t = tritAction q (tritAction p t) := by
  revert q p t; decide

/-- **The equivariance square.**  The magnitude observer intertwines the SSP
orientation action with the induced action on masks, which is the identity: the
symmetry descends to the coarse layer, and descends trivially. -/
theorem polarPresence_equivariant (g : FibreOrientation) (t : Trit) :
    polarPresence (tritAction g t) = id (polarPresence t) := by
  revert g t; decide

/-- The descent is *forced*: the induced action making the square commute is
unique, because the observer is surjective. -/
theorem laneAction_descends (g : FibreOrientation) (f : Bool → Bool)
    (hf : ∀ t, polarPresence (tritAction g t) = f (polarPresence t)) : f = id := by
  funext b
  obtain ⟨t, ht⟩ := polarPresence_surjective b
  rw [← ht, ← hf t, polarPresence_equivariant]

/-- **The information that is lost is exactly the sign**: no section of the
magnitude observer can be polarity-equivariant, since equivariance over the
trivial action would make the chosen preimage a fixed point. -/
theorem no_equivariant_section :
    ¬ ∃ s : Bool → Trit, (∀ b, polarPresence (s b) = b) ∧ (∀ b, Trit.inv (s b) = s b) := by
  rintro ⟨s, hsec, hequiv⟩
  have h1 := hsec true
  have h2 := hequiv true
  generalize s true = t at h1 h2
  revert h1 h2
  cases t <;> decide

/-- **The observer-loss boundary, in its strongest form for `support`**: not only
is boolean OR not the induced operation — *no* binary Boolean operation is. -/
theorem support_no_descent :
    ¬ ∃ f : Bool → Bool → Bool, ∀ a b : Trit, support (tritXor a b) = f (support a) (support b) := by
  rintro ⟨f, hf⟩
  have h1 := hf .zer .zer
  have h2 := hf .zer .pos
  rw [show support (tritXor Trit.zer Trit.zer) = true from by decide,
    show support Trit.zer = true from by decide] at h1
  rw [show support (tritXor Trit.zer Trit.pos) = false from by decide,
    show support Trit.zer = true from by decide,
    show support Trit.pos = true from by decide] at h2
  rw [← h1] at h2
  exact Bool.noConfusion h2

/-- The same for the magnitude observer: the polarity-invariant Boolean layer
does not carry the ternary operation either.  Both Boolean observers lose the
algebra; only the signed/ternary layer retains it. -/
theorem polarPresence_no_descent :
    ¬ ∃ f : Bool → Bool → Bool,
      ∀ a b : Trit, polarPresence (tritXor a b) = f (polarPresence a) (polarPresence b) := by
  rintro ⟨f, hf⟩
  have h1 := hf .neg .neg
  have h2 := hf .pos .pos
  rw [show polarPresence (tritXor Trit.neg Trit.neg) = true from by decide,
    show polarPresence Trit.neg = true from by decide] at h1
  rw [show polarPresence (tritXor Trit.pos Trit.pos) = false from by decide,
    show polarPresence Trit.pos = true from by decide] at h2
  rw [← h1] at h2
  exact Bool.noConfusion h2

/-! ## The fabric level -/

/-- The magnitude mask of a hyperfabric. -/
def polarPresenceMask (F : Fabric) : MaskSSP := fun p => polarPresence (F p)

/-- The magnitude mask is invariant under the pointwise polarity action, so the
`ℤ/2` symmetry of the fabric layer descends trivially to the mask layer. -/
theorem polarPresenceMask_inv (F : Fabric) :
    polarPresenceMask (fun p => Trit.inv (F p)) = polarPresenceMask F := by
  funext p; exact polarPresence_inv (F p)

/-- Like `supportMask`, the magnitude mask is non-expansive for the depth-15
prefix geometry. -/
theorem polarPresenceMask_nonexpansive (F G : Fabric) :
    dSSP (polarPresenceMask F) (polarPresenceMask G) ≤ fabricDist F G := by
  rw [dSSP_eq_dist]
  exact Addr.dist_mono_map polarPresence _ _

/-- …and it is not injective either: the collapse of the sign is genuine at the
fabric level. -/
theorem polarPresenceMask_not_injective : ¬ Function.Injective polarPresenceMask := by
  intro h
  have : (fun _ => Trit.pos : Fabric) = (fun _ => Trit.neg) := h rfl
  exact absurd (congrFun this SSP.p2) (by decide)

/-! ## The signed layer -/

/-- Mirror of `SignedMultiplicityObstructionExact.Multiplicity`. -/
abbrev Multiplicity (I : Type) := I → ℕ

/-- Mirror of `delta`: the signed relational difference of two multiplicity
functions. -/
def delta {I : Type} (A B : Multiplicity I) (i : I) : ℤ := (A i : ℤ) - (B i : ℤ)

/-- Mirror of `DefectOrientation`. -/
inductive DefectOrientation | negativeDefect | balancedDefect | positiveDefect
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `orientationOfInteger`. -/
def orientationOfInt (z : ℤ) : DefectOrientation :=
  if z < 0 then .negativeDefect else if z = 0 then .balancedDefect else .positiveDefect

/-- Mirror of `reverseOrientation`. -/
def reverseOrientation : DefectOrientation → DefectOrientation
  | .negativeDefect => .positiveDefect
  | .balancedDefect => .balancedDefect
  | .positiveDefect => .negativeDefect

theorem reverseOrientation_involutive (o : DefectOrientation) :
    reverseOrientation (reverseOrientation o) = o := by cases o <;> rfl

theorem orientationOfInt_neg (z : ℤ) :
    orientationOfInt (-z) = reverseOrientation (orientationOfInt z) := by
  unfold orientationOfInt
  rcases lt_trichotomy z 0 with h | h | h
  · rw [if_neg (show ¬ (-z < 0) by omega), if_neg (show ¬ (-z = 0) by omega), if_pos h]
    rfl
  · subst h; decide
  · rw [if_pos (show -z < 0 by omega), if_neg (show ¬ (z < 0) by omega),
      if_neg (show ¬ (z = 0) by omega)]
    rfl

/-- Mirror of `deltaSwap`: the signed difference is anti-symmetric. -/
theorem delta_swap {I : Type} (A B : Multiplicity I) (i : I) :
    delta B A i = - delta A B i := by simp [delta]

/-- Mirror of `orientationSwap`: swapping the two objects reverses the
orientation. -/
theorem orientation_swap {I : Type} (A B : Multiplicity I) (i : I) :
    orientationOfInt (delta B A i) = reverseOrientation (orientationOfInt (delta A B i)) := by
  rw [delta_swap, orientationOfInt_neg]

/-- Mirror of `oneAndTwoHaveSamePresence` / `oneAndTwoHaveNonzeroSignedDefect`:
the Boolean presence shadow forgets multiplicity, while the signed defect does
not. -/
theorem presence_lossy :
    (decide (1 ≠ 0) = decide (2 ≠ 0)) ∧ ((1 : ℤ) - (2 : ℤ) ≠ 0) := by
  refine ⟨rfl, by decide⟩

/-- **Level iv**: the defect orientation carrier is the ternary hub, with
reversal the hub polarity. -/
def defectOrientationHub : Transport DefectOrientation Trit reverseOrientation Trit.inv where
  map :=
    { toFun := fun o => match o with
        | .negativeDefect => .neg | .balancedDefect => .zer | .positiveDefect => .pos
      invFun := fun t => match t with
        | .neg => .negativeDefect | .zer => .balancedDefect | .pos => .positiveDefect
      left_inv := by decide
      right_inv := by decide }
  equivariant := by decide

/-- **Level iii/iv**: the defect orientation carrier is also the SSP
`FibreOrientation` carrier — the bridge the Agda writes as
`toSSPFibreOrientation` — and reversal corresponds to exchanging the forward and
inverse orientations. -/
def defectToFibreOrientation : DefectOrientation ≃ FibreOrientation where
  toFun
    | .negativeDefect => .inverse | .balancedDefect => .mediated | .positiveDefect => .forward
  invFun
    | .inverse => .negativeDefect | .mediated => .balancedDefect | .forward => .positiveDefect
  left_inv := by decide
  right_inv := by decide

/-- The exchange of `forward` and `inverse` on the SSP orientation carrier. -/
def fibreFlip : FibreOrientation → FibreOrientation
  | .inverse => .forward | .mediated => .mediated | .forward => .inverse

theorem defectToFibreOrientation_equiv (o : DefectOrientation) :
    defectToFibreOrientation (reverseOrientation o) = fibreFlip (defectToFibreOrientation o) := by
  revert o; decide

/-- The flip is the sign-reversal of the orientation monoid's `ℤ/2` quotient
away from the unit, and it fixes the unit: so the signed defect layer and the
SSP transport layer share both carrier and involution. -/
theorem fibreFlip_sign (g : FibreOrientation) (h : g ≠ .mediated) :
    orientationSign (fibreFlip g) = orientationSign g + 1 := by
  revert g; decide

/-! ## Summary -/

/-- The corrected observer row: the symmetry action is preserved all the way down
to the Boolean layer, the binary ternary law is preserved by neither Boolean
observer, and the exact loss is the sign. -/
theorem observer_loss_summary :
    (∀ (g : FibreOrientation) (t : Trit),
        polarPresence (tritAction g t) = id (polarPresence t)) ∧
      (∀ x y : Trit, polarPresence x = polarPresence y ↔ (y = x ∨ y = Trit.inv x)) ∧
      (¬ ∃ f : Bool → Bool → Bool,
        ∀ a b : Trit, support (tritXor a b) = f (support a) (support b)) ∧
      (¬ ∃ f : Bool → Bool → Bool,
        ∀ a b : Trit, polarPresence (tritXor a b) = f (polarPresence a) (polarPresence b)) ∧
      (¬ ∀ t : Trit, support (Trit.inv t) = support t) :=
  ⟨polarPresence_equivariant, polarPresence_orbit, support_no_descent,
    polarPresence_no_descent, support_not_polarity_invariant⟩

end Integration.ObserverQuotient
