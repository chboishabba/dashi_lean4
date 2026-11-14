import Mathlib

/-!
# Deterministic Lean proof-world core

A theorem corpus is a graph of *certified* implication paths. Source/QID/OEIS
coordinates only suggest candidates. A certified path contains actual Lean
proof terms, so graph reachability never manufactures a theorem.

Authoritative source declarations remain distinct from theorem equivalence.
Use Agda2Lean.Manifest for direct dependency and axiom-closure audits.
-/

namespace Integration.JMD.CertifiedWorld

structure SourceIdentity where
  repository : String
  revision : String
  declaration : String
  attribution : String
  deriving DecidableEq, Repr, BEq

inductive Authority where
  | candidate
  | checked
  deriving DecidableEq, Repr, BEq

structure CandidateRelation where
  origin : SourceIdentity
  destination : SourceIdentity
  relationshipHint : String
  externalCoordinate : Option String := none
  authority : Authority := .candidate
  candidateOnly : authority = .candidate

theorem candidate_not_checked (candidate : CandidateRelation) :
    candidate.authority ≠ .checked := by
  intro h
  have hc := candidate.candidateOnly
  rw [h] at hc
  cases hc

/-- A checked Lean implication owns its proof, and both source identities. -/
structure CertifiedImplication (P Q : Prop) where
  origin : SourceIdentity
  destination : SourceIdentity
  implication : P → Q

def identity (source : SourceIdentity) (P : Prop) :
    CertifiedImplication P P :=
  ⟨source, source, fun p => p⟩

def compose {P Q R : Prop}
    (left : CertifiedImplication P Q)
    (right : CertifiedImplication Q R) :
    CertifiedImplication P R :=
  ⟨left.origin, right.destination,
    fun p => right.implication (left.implication p)⟩

theorem compose_correct {P Q R : Prop}
    (left : CertifiedImplication P Q)
    (right : CertifiedImplication Q R) (hp : P) :
    (compose left right).implication hp =
      right.implication (left.implication hp) := rfl

theorem compose_preserves_source {P Q R : Prop}
    (left : CertifiedImplication P Q)
    (right : CertifiedImplication Q R) :
    (compose left right).origin = left.origin := rfl

theorem compose_preserves_destination {P Q R : Prop}
    (left : CertifiedImplication P Q)
    (right : CertifiedImplication Q R) :
    (compose left right).destination = right.destination := rfl

structure CertifiedEquivalence (P Q : Prop) where
  leftIdentity : SourceIdentity
  rightIdentity : SourceIdentity
  forward : P → Q
  backward : Q → P

def equivalenceForward {P Q : Prop} (e : CertifiedEquivalence P Q) :
    CertifiedImplication P Q :=
  ⟨e.leftIdentity, e.rightIdentity, e.forward⟩

def equivalenceBackward {P Q : Prop} (e : CertifiedEquivalence P Q) :
    CertifiedImplication Q P :=
  ⟨e.rightIdentity, e.leftIdentity, e.backward⟩

/-- Keep both identities instead of quotienting declarations by a heuristic. -/
structure WorldPair (P Q : Prop) where
  left : SourceIdentity
  right : SourceIdentity
  relation : CertifiedEquivalence P Q
  leftMatches : left = relation.leftIdentity
  rightMatches : right = relation.rightIdentity

def worldPair {P Q : Prop} (e : CertifiedEquivalence P Q) : WorldPair P Q :=
  ⟨e.leftIdentity, e.rightIdentity, e, rfl, rfl⟩

theorem worldPair_left {P Q : Prop} (e : CertifiedEquivalence P Q) :
    (worldPair e).left = e.leftIdentity := rfl

theorem worldPair_right {P Q : Prop} (e : CertifiedEquivalence P Q) :
    (worldPair e).right = e.rightIdentity := rfl

/-- Certificate-carrying transitive paths, with every donor attribution. -/
inductive VerifiedPath : Prop → Prop → Type where
  | reflexive (P : Prop) (source : SourceIdentity) : VerifiedPath P P
  | link {P Q : Prop} (proof : CertifiedImplication P Q) : VerifiedPath P Q
  | concatenate {P Q R : Prop} :
      VerifiedPath P Q → VerifiedPath Q R → VerifiedPath P R

def VerifiedPath.prove {P Q : Prop} : VerifiedPath P Q → P → Q
  | .reflexive _ _ => fun p => p
  | .link cert => cert.implication
  | .concatenate left right => fun p => right.prove (left.prove p)

def VerifiedPath.provenance {P Q : Prop} : VerifiedPath P Q → List SourceIdentity
  | .reflexive _ source => [source]
  | .link cert => [cert.origin, cert.destination]
  | .concatenate left right => left.provenance ++ right.provenance

theorem concatenate_correct {P Q R : Prop}
    (left : VerifiedPath P Q) (right : VerifiedPath Q R)
    (hp : P) :
    (VerifiedPath.concatenate left right).prove hp =
      right.prove (left.prove hp) := rfl

theorem concatenate_provenance {P Q R : Prop}
    (left : VerifiedPath P Q) (right : VerifiedPath Q R) :
    (VerifiedPath.concatenate left right).provenance =
      left.provenance ++ right.provenance := rfl

/-- A negative control: an external coordinate by itself is not a proof. -/
theorem wikidata_oeis_does_not_certify
    (candidate : CandidateRelation) :
    candidate.authority = .candidate :=
  candidate.candidateOnly

/-- Proof-composition regression: no axiom or source-name match is needed. -/
theorem implication_three_step {P Q R S : Prop}
    (f : P → Q) (g : Q → R) (h : R → S) : P → S :=
  fun p => h (g (f p))

end Integration.JMD.CertifiedWorld
