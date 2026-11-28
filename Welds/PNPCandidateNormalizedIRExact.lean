import Welds.PNPActualInventoryClosureExact

namespace PNPCandidateNormalizedIR
open PNPStackEmittedList PNPActualInventoryClosure PNPActualPrimeRun
open PNPActualPrimeLayout

structure Rule where
  source : Nat
  read : Nat
  target : Nat
  write : Nat
  move : Nat
  deriving DecidableEq

structure IR where
  states : Nat
  alphabet : Nat
  initial : Nat
  accepting : Nat
  rules : List Rule
  deriving DecidableEq

def flattenRules : List Rule → List Nat
  | [] => []
  | r::rs => r.source::r.read::r.target::r.write::r.move::flattenRules rs

def flatten (p : IR) : List Nat :=
  p.states::p.alphabet::p.initial::p.accepting::p.rules.length::flattenRules p.rules

def decodeRows : Nat → List Nat → Option (List Rule)
  | 0,[] => some []
  | k+1,q::a::p::b::d::xs => (decodeRows k xs).map (List.cons ⟨q,a,p,b,d⟩)
  | _,_ => none

def parse : List Nat → Option IR
  | Q::A::q::p::k::xs => (decodeRows k xs).map (IR.mk Q A q p)
  | _ => none

theorem decodeRows_flat (rs : List Rule) :
    decodeRows rs.length (flattenRules rs) = some rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    cases r
    simp [decodeRows,flattenRules,ih]

theorem parse_flat (p : IR) : parse (flatten p) = some p := by
  cases p
  simp [parse,flatten,decodeRows_flat]

def Rule.legal (Q A : Nat) (r : Rule) : Prop :=
  r.source<Q ∧ r.read<A ∧ r.target<Q ∧ r.write<A ∧ r.move<3

def Valid (p : IR) : Prop :=
  0<p.states ∧ 0<p.alphabet ∧ p.initial<p.states ∧ p.accepting<p.states ∧
  ∀ r∈p.rules,r.legal p.states p.alphabet

def selectRule : List Rule → Nat → Nat → Option Rule
  | [],_,_ => none
  | r::rs,q,a => if r.source=q ∧ r.read=a then some r else selectRule rs q a

theorem selected_mem (rs : List Rule) (q a : Nat) (r : Rule)
    (h : selectRule rs q a = some r) : r∈rs := by
  induction rs with
  | nil => simp [selectRule] at h
  | cons s ss ih =>
    by_cases e : s.source=q ∧ s.read=a
    · simp [selectRule,e] at h
      subst r
      simp
    · exact List.mem_cons_of_mem _ (ih (by simpa [selectRule,e] using h))

def direction : Nat → Move
  | 0 => .left
  | 1 => .stay
  | _ => .right

def instruction (r : Rule) : Instruction := ⟨r.target,r.write,direction r.move⟩

def table (p : IR) (q a : Nat) : Option Instruction :=
  (selectRule p.rules q a).map instruction

theorem first_duplicate (r s : Rule) (rs : List Rule) (hq : r.source=s.source)
    (ha : r.read=s.read) :
    selectRule (r::s::rs) s.source s.read = some r := by
  simp [selectRule,hq,ha]

theorem legal_table (p : IR) (h : Valid p) : LegalTable p.states p.alphabet (table p) := by
  intro q a i hq ha hi
  unfold table at hi
  cases e : selectRule p.rules q a with
  | none => simp [e] at hi
  | some r =>
    simp [e] at hi
    subst i
    have v := h.2.2.2.2 r (selected_mem _ _ _ _ e)
    exact ⟨v.2.2.1,v.2.2.2.1⟩

def emitProgram (p : IR) : List PNPStackEmittedList.Edge :=
  compile p.states p.alphabet (table p)

theorem parsedPrimeMacro (p : IR) (h : Valid p) (q : Nat) (c : PNPStackFractran.Config)
    (hq : q<p.states) (ha : c.scanned<p.alphabet)
    (hl : ∀ d∈c.left,d<p.alphabet) :
    ∃ k, integerRun p.states p.alphabet (emitProgram p) k
      (integerState p.states p.alphabet
        ⟨mainTag (.q q),PNPActualWordBisim.dataOf (max 2 p.alphabet) c⟩) =
      some (integerState p.states p.alphabet
        (PNPActualWordBisim.sourceResult (max 2 p.alphabet) q (table p) c)) := by
  exact primeMacroExact p.states p.alphabet q (table p) c h.2.1 hq ha hl
    (fun i hi => (legal_table p h q c.scanned i hq ha hi).1)

-- Shared flat list format: Q,A,initial,accept,count, then five Nat
-- fields per rule. Agda exports actual normalized enumeration indices.
-- parse_flat is a native format roundtrip; equality to an external
-- Agda export is a per-artifact interchange check, not a cross-kernel
-- proof unless the producer's validity theorem is also established.
end PNPCandidateNormalizedIR
