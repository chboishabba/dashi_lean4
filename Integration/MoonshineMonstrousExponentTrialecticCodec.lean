import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.TernaryHub
import Integration.ResidualQuotient
import Integration.Kernel.Quotient
import Mathlib

namespace Integration.MoonshineMonstrousExponentTrialecticCodec

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.TernaryHub
open Integration.Kernel.Quotient

/-!
# Attributed monstrous-exponent trialectic -> consumer-indexed 369 codec

External arithmetic input:
John F. R. Duncan and Holly Swisher,
"Modular Functions and the Monstrous Exponents" (2026),
arXiv:2602.09135.

The p>3 triples below mirror the attributed Agda owner
`MonsterOrderExponentCorrectionExact`.  The ternary presence quantizer,
dependent residual codec, consumer routing, and selective residuals are DASHI
repository constructions.  In particular:

* the arithmetic triple is not identified with a 369 cube;
* its three source roles are not identified with relational participant A/B/C;
* finite ternary coding does not imply recovery of arithmetic magnitude.
-/

/-! ## §1 Attributed arithmetic triple -/

structure ArithmeticTriple where
  A : Nat
  B : Nat
  C : Nat
  deriving DecidableEq, Repr

/-- The p>3 Duncan--Swisher modular contribution triple.  p=2 and p=3 are
exceptional and deliberately excluded from this table. -/
def modularContribution : SSPPrime → Option ArithmeticTriple
  | .p2 | .p3 => none
  | .p5  => some ⟨3, 5, 1⟩
  | .p7  => some ⟨2, 4, 0⟩
  | .p11 => some ⟨2, 0, 0⟩
  | .p13 => some ⟨1, 2, 0⟩
  | .p17 | .p19 | .p23 | .p29 | .p31 | .p41 | .p47 | .p59 | .p71 =>
      some ⟨1, 0, 0⟩

def p5Triple  : ArithmeticTriple := ⟨3, 5, 1⟩
def p7Triple  : ArithmeticTriple := ⟨2, 4, 0⟩
def p11Triple : ArithmeticTriple := ⟨2, 0, 0⟩
def p13Triple : ArithmeticTriple := ⟨1, 2, 0⟩

theorem p5_table  : modularContribution .p5  = some p5Triple := rfl
theorem p7_table  : modularContribution .p7  = some p7Triple := rfl
theorem p11_table : modularContribution .p11 = some p11Triple := rfl
theorem p13_table : modularContribution .p13 = some p13Triple := rfl

def exponentSum (t : ArithmeticTriple) : Nat := t.A + t.B + t.C

theorem p5_sum : exponentSum p5Triple = 9 := rfl
theorem p7_sum : exponentSum p7Triple = 6 := rfl
theorem p11_sum : exponentSum p11Triple = 2 := rfl
theorem p13_sum : exponentSum p13Triple = 3 := rfl

/-! ## §2 Coarse T3 presence surface -/

structure Surface3 where
  x : SSPTrit
  y : SSPTrit
  z : SSPTrit
  deriving DecidableEq, Repr

def presenceTrit : Nat → SSPTrit
  | 0 => .zero
  | _ + 1 => .posOne

def surface (t : ArithmeticTriple) : Surface3 :=
  ⟨presenceTrit t.A, presenceTrit t.B, presenceTrit t.C⟩

theorem p7_p13_surface_collision : surface p7Triple = surface p13Triple := rfl
theorem p7_p13_sum_distinct : exponentSum p7Triple ≠ exponentSum p13Triple := by decide

/-! ## §3 Dependent residual reopening -/

def PresenceResidual : SSPTrit → Type
  | .negOne => Empty
  | .zero => Unit
  | .posOne => Nat

def presenceResidual : (n : Nat) → PresenceResidual (presenceTrit n)
  | 0 => ()
  | n + 1 => n

def reopenPresence : (s : SSPTrit) → PresenceResidual s → Nat
  | .negOne, e => nomatch e
  | .zero, _ => 0
  | .posOne, n => n + 1

theorem reopen_presence_exact (n : Nat) :
    reopenPresence (presenceTrit n) (presenceResidual n) = n := by
  cases n <;> rfl

def TripleResidual (s : Surface3) : Type :=
  PresenceResidual s.x × PresenceResidual s.y × PresenceResidual s.z

def tripleResidual (t : ArithmeticTriple) : TripleResidual (surface t) :=
  ⟨presenceResidual t.A, presenceResidual t.B, presenceResidual t.C⟩

def reopenTriple (s : Surface3) (r : TripleResidual s) : ArithmeticTriple :=
  ⟨reopenPresence s.x r.1, reopenPresence s.y r.2.1, reopenPresence s.z r.2.2⟩

theorem reopen_triple_exact (t : ArithmeticTriple) :
    reopenTriple (surface t) (tripleResidual t) = t := by
  rcases t with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> rfl

abbrev ArithmeticCode := Sigma TripleResidual

def encodeTriple (t : ArithmeticTriple) : ArithmeticCode :=
  ⟨surface t, tripleResidual t⟩

def decodeTriple : ArithmeticCode → ArithmeticTriple
  | ⟨s,r⟩ => reopenTriple s r

theorem decode_encode_triple (t : ArithmeticTriple) :
    decodeTriple (encodeTriple t) = t :=
  reopen_triple_exact t

theorem encodeTriple_injective : Function.Injective encodeTriple := by
  intro left right h
  rw [← decode_encode_triple left, ← decode_encode_triple right, h]

/-! ## §4 Consumer-relative descent -/

/-- Presence consumers descend through the coarse T3 surface. -/
theorem presence_descends :
    DescendsThrough surface surface :=
  ⟨id, fun _ => rfl⟩

/-- The Monster-exponent sum does not descend through presence alone. -/
theorem exponent_sum_does_not_descend :
    ¬ DescendsThrough exponentSum surface :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    p7_p13_surface_collision
    p7_p13_sum_distinct

/-- Nor does the full contribution triple. -/
theorem full_triple_does_not_descend :
    ¬ DescendsThrough id surface :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    p7_p13_surface_collision
    (by decide)

/-- The exact residual code is sufficient for every declared consumer. -/
theorem every_consumer_descends_through_exact_code
    {Outcome : Type} (consumer : ArithmeticTriple → Outcome) :
    DescendsThrough consumer encodeTriple :=
  ⟨fun code => consumer (decodeTriple code), fun t => by simp [decode_encode_triple]⟩

/-! ## §5 Consumer-indexed routing -/

inductive ArithmeticCodecConsumerClass
  | presencePatternOnly
  | exponentSumConsumer
  | fullContributionConsumer
  deriving DecidableEq, Repr

inductive ArithmeticCodecRetention
  | retainCoarseT3Only
  | retainCoarseT3PlusArithmeticResidual
  | retainFullArithmeticTripleCode
  deriving DecidableEq, Repr

def routeArithmeticConsumer : ArithmeticCodecConsumerClass → ArithmeticCodecRetention
  | .presencePatternOnly => .retainCoarseT3Only
  | .exponentSumConsumer => .retainCoarseT3PlusArithmeticResidual
  | .fullContributionConsumer => .retainFullArithmeticTripleCode

theorem presence_route : routeArithmeticConsumer .presencePatternOnly =
    .retainCoarseT3Only := rfl

theorem sum_route : routeArithmeticConsumer .exponentSumConsumer =
    .retainCoarseT3PlusArithmeticResidual := rfl

theorem full_route : routeArithmeticConsumer .fullContributionConsumer =
    .retainFullArithmeticTripleCode := rfl

/-! ## §6 Role-indexed selective residuals -/

inductive ModularContributionRole
  | frickeComparison
  | levelPComparison
  | levelP2Comparison
  deriving DecidableEq, Repr

def roleSurface : ModularContributionRole → Surface3 → SSPTrit
  | .frickeComparison, s => s.x
  | .levelPComparison, s => s.y
  | .levelP2Comparison, s => s.z

def roleMagnitude : ModularContributionRole → ArithmeticTriple → Nat
  | .frickeComparison, t => t.A
  | .levelPComparison, t => t.B
  | .levelP2Comparison, t => t.C

def SelectedRoleResidual (role : ModularContributionRole) (s : Surface3) : Type :=
  PresenceResidual (roleSurface role s)

structure SelectedRoleCode (role : ModularContributionRole) where
  selectedSurface : Surface3
  selectedResidual : SelectedRoleResidual role selectedSurface

def selectedRoleResidual (role : ModularContributionRole) (t : ArithmeticTriple) :
    SelectedRoleResidual role (surface t) :=
  match role with
  | .frickeComparison => presenceResidual t.A
  | .levelPComparison => presenceResidual t.B
  | .levelP2Comparison => presenceResidual t.C

def encodeSelectedRole (role : ModularContributionRole) (t : ArithmeticTriple) :
    SelectedRoleCode role :=
  ⟨surface t, selectedRoleResidual role t⟩

def decodeSelectedRoleMagnitude (role : ModularContributionRole) :
    SelectedRoleCode role → Nat
  | ⟨s,r⟩ => reopenPresence (roleSurface role s) r

theorem decode_encode_selected_role
    (role : ModularContributionRole) (t : ArithmeticTriple) :
    decodeSelectedRoleMagnitude role (encodeSelectedRole role t) =
      roleMagnitude role t := by
  rcases t with ⟨a,b,c⟩
  cases role <;> simp [encodeSelectedRole, selectedRoleResidual,
    decodeSelectedRoleMagnitude, roleSurface, roleMagnitude, surface]
  all_goals cases ‹Nat› <;> rfl

theorem role_magnitude_descends_through_selected_code
    (role : ModularContributionRole) :
    DescendsThrough (roleMagnitude role) (encodeSelectedRole role) :=
  ⟨decodeSelectedRoleMagnitude role, decode_encode_selected_role role⟩

/-! ## §7 Necessity evidence is role-sensitive -/

theorem fricke_magnitude_does_not_descend :
    ¬ DescendsThrough (roleMagnitude .frickeComparison) surface :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    p7_p13_surface_collision
    (by decide)

theorem level_p_magnitude_does_not_descend :
    ¬ DescendsThrough (roleMagnitude .levelPComparison) surface :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    p7_p13_surface_collision
    (by decide)

/-- The current attributed p>3 table gives no same-surface collision separating
two positive C magnitudes: only p5 has C>0.  Therefore no analogous necessity
claim is manufactured here. -/
inductive SquareLevelNecessityWitnessConstructed : Prop

theorem square_level_necessity_not_claimed :
    ¬ SquareLevelNecessityWitnessConstructed := by
  intro h
  cases h

/-! ## §8 Boundary -/

structure Boundary where
  attributedPAboveThreeTripleOwned : Bool
  coarseT3PresenceSurfaceOwned : Bool
  explicitP7P13CollisionOwned : Bool
  dependentResidualReopensExactly : Bool
  exactCodeSeparating : Bool
  presenceConsumerDescends : Bool
  exponentSumDoesNotDescend : Bool
  fullTripleDoesNotDescend : Bool
  everyConsumerDescendsThroughExactCode : Bool
  consumerIndexedRoutingOwned : Bool
  selectedRoleResidualSuffices : Bool
  frickeResidualNecessityOwned : Bool
  levelPResidualNecessityOwned : Bool
  squareLevelResidualNecessityOwned : Bool
  arithmeticTripleIs369SemanticIdentity : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  attributedPAboveThreeTripleOwned := true
  coarseT3PresenceSurfaceOwned := true
  explicitP7P13CollisionOwned := true
  dependentResidualReopensExactly := true
  exactCodeSeparating := true
  presenceConsumerDescends := true
  exponentSumDoesNotDescend := true
  fullTripleDoesNotDescend := true
  everyConsumerDescendsThroughExactCode := true
  consumerIndexedRoutingOwned := true
  selectedRoleResidualSuffices := true
  frickeResidualNecessityOwned := true
  levelPResidualNecessityOwned := true
  squareLevelResidualNecessityOwned := false
  arithmeticTripleIs369SemanticIdentity := false

end Integration.MoonshineMonstrousExponentTrialecticCodec
