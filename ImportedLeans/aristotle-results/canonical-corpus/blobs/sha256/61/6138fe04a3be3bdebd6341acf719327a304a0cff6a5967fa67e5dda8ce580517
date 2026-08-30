import Integration.ClaimTransport

/-!
# Claim-transport geometry, stated as an interface, and what it reconciles with

## Why this file exists

The Level-III probe (`Integration.ClaimTransport`) reached a negative verdict:
the warrant that licenses a claim to cross a stage boundary is definitionally an
instance of the existing determination owner, and its failure is definitionally
the existing `Collision` datum, so no fifth generic owner was created.

An independently developed formulation is cited in the surrounding
correspondence: an Agda module `FormalClaimTransportGeometryExact`, said to
define claim transport as *factorisation through a retained representation*,
to make *collision / non-descent* the obstruction, and to instantiate the same
construction on a concrete bridge with a commuting translation square while
keeping semantic soundness, historical fidelity and conservativity as separate
coordinates.

**Provenance, stated up front.**  That Agda module is **not present in this
cutset.**  A whole-tree search for `ClaimTransport` (any case) and for the
bridge's name finds no Agda file, and neither do the archived tarballs.  See
`§5` and `Integration.MirrorDrift` for the machine-readable record.  Therefore
this file does **not** mirror it, does not quote it, and asserts nothing about
what it contains or whether it elaborates.

What can honestly be done without the source is the *reconciliation shape*:
state the described geometry as an **interface** — a formulation is a
transport geometry when its transportability predicate is factorisation through
the retained representation and its obstruction is exactly the failure of that —
and prove that **any two inhabitants of the interface over the same
representation and claim agree** (`two_formulations_agree`).  That converts the
reconciliation question into a single checkable condition: *does the other
development satisfy this interface?*  If it does, the two verdicts coincide by
theorem; if it does not, the mismatch is exactly the failing interface field.

No new owner is introduced: `leanGeometry` shows the existing
`Determines`/`Collision` pair already inhabits the interface, and
`interface_is_the_existing_owner` records that the interface's two predicates
are the existing ones.

## Contents

* `§1` factorisation and non-descent: `Factors`, `factors_iff_determines`,
  `nonDescent_blocks_transport`, `not_factors_iff_nonempty_collision`;
* `§2` the correspondence with the probe's `Warrant`;
* `§3` the interface and `two_formulations_agree`;
* `§4` the separate-coordinates point, proved generically: an **exactly
  commuting translation square** confers neither semantic soundness nor
  fidelity, and soundness for one semantic coordinate does not transfer to
  another;
* `§5` the provenance datum for the cited, absent source.

Every carrier below is `Bool`, `Unit`, `ℕ` or an arbitrary type.  Nothing here
is a claim about any domain, and nothing here is a claim about Agda.
-/

namespace Integration.ClaimTransportGeometry

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.ClaimTransport

variable {S R A B : Type}

/-! ## §1 Factorisation through the retained representation -/

/-- **The transport condition, in factorisation form.**  The claim `claim`
factors through the retained representation `rep`: there is a reading of the
representation that already computes the claim. -/
def Factors (rep : S → R) (claim : S → A) : Prop :=
  ∃ f : R → A, ∀ s, claim s = f (rep s)

/-- Factorisation gives determination. -/
theorem determines_of_factors {rep : S → R} {claim : S → A} (h : Factors rep claim) :
    Determines rep claim := by
  obtain ⟨f, hf⟩ := h
  intro x y hxy
  rw [hf x, hf y, hxy]

/-- And determination gives factorisation, by choosing a representative in each
fibre.  (`Nonempty A` only names a value off the image of `rep`.) -/
theorem factors_of_determines [Nonempty A] {rep : S → R} {claim : S → A}
    (h : Determines rep claim) : Factors rep claim := by
  classical
  refine ⟨fun r => if hr : ∃ s, rep s = r then claim hr.choose else Classical.arbitrary A,
    fun s => ?_⟩
  have hex : ∃ s', rep s' = rep s := ⟨s, rfl⟩
  show claim s = if hr : ∃ s', rep s' = rep s then claim hr.choose else Classical.arbitrary A
  rw [dif_pos hex]
  exact (h _ _ hex.choose_spec).symm

/-- **The two readings of the transport condition coincide.**  "The claim
factors through the retained representation" and "the representation determines
the claim" are the same condition; naming the first creates no object. -/
theorem factors_iff_determines [Nonempty A] (rep : S → R) (claim : S → A) :
    Factors rep claim ↔ Determines rep claim :=
  ⟨determines_of_factors, factors_of_determines⟩

/-- **Non-descent blocks transport.**  A collision of the representation against
the claim refutes every factorisation.  No `Nonempty` hypothesis is needed in
this direction. -/
theorem nonDescent_blocks_transport {rep : S → R} {claim : S → A}
    (w : Collision rep claim) : ¬ Factors rep claim := by
  rintro ⟨f, hf⟩
  exact w.separate (by rw [hf w.left, hf w.right, w.collide])

/-- A failure of determination *is* a collision. -/
theorem nonempty_collision_of_not_determines {rep : S → R} {claim : S → A}
    (h : ¬ Determines rep claim) : Nonempty (Collision rep claim) := by
  classical
  simp only [Determines, not_forall] at h
  obtain ⟨x, y, hxy, hne⟩ := h
  exact ⟨{ left := x, right := y
           distinct := fun hxy' => hne (by rw [hxy'])
           collide := hxy
           separate := hne }⟩

/-- **The obstruction is exactly non-descent.**  Transport fails precisely when a
collision exists; there is no third possibility and no residual obstruction
class. -/
theorem not_factors_iff_nonempty_collision [Nonempty A] (rep : S → R) (claim : S → A) :
    ¬ Factors rep claim ↔ Nonempty (Collision rep claim) := by
  constructor
  · intro h
    exact nonempty_collision_of_not_determines (fun hd => h (factors_of_determines hd))
  · rintro ⟨w⟩
    exact nonDescent_blocks_transport w

/-! ## §2 Correspondence with the probe's warrant -/

/-- **The probe's `Warrant` is this file's `Factors`, for the pulled-back
claim.**  The warrant that licenses `S → M → N` to answer a question about `S`
is factorisation of that question through the retained representation
`qM ∘ r₁`. -/
theorem warrant_iff_factors_pullback [Nonempty A] (r₁ : S → B) (qM : B → A) (q : S → A) :
    Warrant r₁ qM q ↔ Factors (fun s => qM (r₁ s)) q :=
  (factors_iff_determines _ _).symm

/-- Transport in factorisation form: the downstream local claim plus a
factorisation of the final question through the retained representation
licenses the composite. -/
theorem transport_of_factorisation {N : Type} {r₁ : S → B} {r₂ : B → N} {qM : B → A}
    {q : S → A} (h₂ : Determines r₂ qM) (hf : Factors (fun s => qM (r₁ s)) q) :
    Determines (compose r₁ r₂) q :=
  transport_of_warrant h₂ (determines_of_factors hf)

/-- And a non-descent witness for the pulled-back claim blocks that transport. -/
theorem nonDescent_blocks_warrant {r₁ : S → B} {qM : B → A} {q : S → A}
    (w : Collision (fun s => qM (r₁ s)) q) : ¬ Warrant r₁ qM q :=
  warrant_failure_is_a_collision w

/-! ## §3 The interface, and the agreement theorem -/

/-- **A claim-transport geometry over `rep`, `claim`.**  A formulation qualifies
when its transportability predicate is factorisation through the retained
representation, and its obstruction predicate holds exactly when
transportability fails.

The two `iff` fields are the whole content of the interface: they are what a
second, independently written development has to satisfy for its verdicts to be
the verdicts proved here. -/
structure TransportGeometry (S R A : Type) where
  /-- The retained representation. -/
  rep : S → R
  /-- The claim under transport. -/
  claim : S → A
  /-- The formulation's own transportability predicate. -/
  transportable : Prop
  /-- The formulation's own obstruction predicate. -/
  obstructed : Prop
  /-- Transportability is factorisation through the retained representation. -/
  transportable_iff_factors : transportable ↔ Factors rep claim
  /-- The obstruction is exactly the failure of transport. -/
  obstructed_iff_blocked : obstructed ↔ ¬ transportable

/-- **Any two formulations satisfying the interface agree.**  Two developments
that both call transport "factorisation through the retained representation"
license exactly the same transports — a correspondence theorem, not a
transcription. -/
theorem two_formulations_agree (g h : TransportGeometry S R A)
    (hrep : g.rep = h.rep) (hclaim : g.claim = h.claim) :
    g.transportable ↔ h.transportable := by
  rw [g.transportable_iff_factors, h.transportable_iff_factors, hrep, hclaim]

/-- The same for the obstruction: the two developments' non-descent conditions
coincide. -/
theorem obstructions_agree (g h : TransportGeometry S R A)
    (hrep : g.rep = h.rep) (hclaim : g.claim = h.claim) :
    g.obstructed ↔ h.obstructed := by
  rw [g.obstructed_iff_blocked, h.obstructed_iff_blocked,
    two_formulations_agree g h hrep hclaim]

/-- **The existing owners inhabit the interface.**  Determination is the
transportability predicate and the existing `Collision` datum is the
obstruction, so the interface adds no object to the spine. -/
noncomputable def leanGeometry [Nonempty A] (rep : S → R) (claim : S → A) :
    TransportGeometry S R A where
  rep := rep
  claim := claim
  transportable := Determines rep claim
  obstructed := Nonempty (Collision rep claim)
  transportable_iff_factors := (factors_iff_determines rep claim).symm
  obstructed_iff_blocked :=
    ⟨fun ⟨w⟩ hd => (nonDescent_blocks_transport w) (factors_of_determines hd),
     fun h => nonempty_collision_of_not_determines h⟩

/-- Read off: the interface's two predicates, on the Lean side, are literally
the frozen owners. -/
theorem interface_is_the_existing_owner [Nonempty A] (rep : S → R) (claim : S → A) :
    (leanGeometry rep claim).transportable = Determines rep claim ∧
      (leanGeometry rep claim).obstructed = Nonempty (Collision rep claim) :=
  ⟨rfl, rfl⟩

/-- Consequently: *if* a second development satisfies the interface over the
same representation and claim, its transport verdicts are the determination
verdicts already proved.  This is the reconciliation statement, with its
hypothesis explicit — it is not an assertion about any particular other
development. -/
theorem other_formulation_reduces_to_determination [Nonempty A]
    (g : TransportGeometry S R A) : g.transportable ↔ Determines g.rep g.claim := by
  rw [g.transportable_iff_factors, factors_iff_determines]

/-! ## §4 Separate coordinates: an exact square is not soundness -/

/-- A translation square: a source dynamics, a target dynamics, and a
translation that commutes with them **exactly**. -/
structure TranslationSquare (S T : Type) where
  /-- The source-side step. -/
  src : S → S
  /-- The target-side step. -/
  tgt : T → T
  /-- The translation. -/
  tr : S → T
  /-- The square commutes on the nose. -/
  commutes : ∀ s, tr (src s) = tgt (tr s)

/-- **An exactly commuting translation square confers no semantic soundness.**
The square below commutes definitionally, and the translation still collides two
states that the semantic reading separates.

So "the translation is a homomorphism" and "the translation preserves the
consumer's question" are independent coordinates: proof-translation strength
does not buy semantic adequacy. -/
theorem commuting_square_does_not_give_soundness :
    ∃ (sq : TranslationSquare Bool Unit) (sem : Bool → Bool),
      (∀ s, sq.tr (sq.src s) = sq.tgt (sq.tr s)) ∧ ¬ Determines sq.tr sem := by
  refine ⟨{ src := id, tgt := id, tr := fun _ => (), commutes := fun _ => rfl }, id,
    fun _ => rfl, ?_⟩
  intro h
  exact Bool.false_ne_true (h false true rfl)

/-- The obstruction in the previous theorem is again the existing datum. -/
theorem commuting_square_obstruction_is_a_collision :
    Nonempty (Collision (fun _ : Bool => ()) (id : Bool → Bool)) :=
  ⟨{ left := false, right := true, distinct := Bool.false_ne_true, collide := rfl,
     separate := Bool.false_ne_true }⟩

/-- **Soundness for one semantic coordinate does not transfer to another.**  A
translation can determine one reading of the source and fail another, so
"semantically sound" is meaningless without naming the coordinate.  (This is the
consumer-relativity of the frozen owner, instantiated on a square.) -/
theorem soundness_does_not_transfer_between_coordinates :
    ∃ (tr : ℕ → ℕ) (sem₁ sem₂ : ℕ → ℕ), Determines tr sem₁ ∧ ¬ Determines tr sem₂ := by
  refine ⟨fun n => n % 2, fun n => n % 2, id, fun _ _ h => h, ?_⟩
  intro h
  have : (0 : ℕ) = 2 := h 0 2 rfl
  omega

/-- Packaged: an exact square, sound for one coordinate, unsound for another —
the three properties are pairwise independent, which is why a bridge must carry
them as separate fields rather than one strength ordering. -/
theorem square_soundness_fidelity_independent :
    ∃ (sq : TranslationSquare ℕ ℕ) (sem₁ sem₂ : ℕ → ℕ),
      (∀ s, sq.tr (sq.src s) = sq.tgt (sq.tr s)) ∧
        Determines sq.tr sem₁ ∧ ¬ Determines sq.tr sem₂ := by
  refine ⟨{ src := id, tgt := id, tr := fun n => n % 2, commutes := fun _ => rfl },
    fun n => n % 2, id, fun _ => rfl, fun _ _ h => h, ?_⟩
  intro h
  have : (0 : ℕ) = 2 := h 0 2 rfl
  omega

/-! ## §5 The provenance datum for the cited source -/

/-- Whether a cited source surface is available in this cutset. -/
inductive SourceStatus
  /-- The file exists in the tree and can be read. -/
  | presentInCutset
  /-- The file is cited but is not in the tree, so nothing may be transcribed
  from it. -/
  | absentFromCutset
  deriving DecidableEq, Repr

/-- A citation of a source surface, with its availability. -/
structure CitedSource where
  /-- The module name as cited. -/
  module : String
  /-- Whether it is available here. -/
  status : SourceStatus
  /-- What was searched for, in words. -/
  note : String

/-- The cited independent formulation, recorded as absent. -/
def formalClaimTransportGeometryExact : CitedSource where
  module := "FormalClaimTransportGeometryExact.agda"
  status := .absentFromCutset
  note := "Whole-tree case-insensitive search for `claimtransport` and for the \
           bridge instance's name returns no Agda file, and the archived \
           tarballs contain none either.  Nothing in this module is \
           transcribed from it, and no claim is made about its contents."

/-- Machine-readable: the citation is unresolved in this cutset. -/
theorem cited_source_absent :
    formalClaimTransportGeometryExact.status = SourceStatus.absentFromCutset := rfl

end Integration.ClaimTransportGeometry
