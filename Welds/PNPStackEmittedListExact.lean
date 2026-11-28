import Mathlib
import Welds.PNPStackFractranExact

namespace PNPStackEmittedList

-- The five data lanes and one-hot symbolic phase tags are the actual
-- fixed stack compiler's layout. Digits here are blank-first; the
-- original candidate parser must transport the alphabet into this form.
inductive Phase where
  | q (q : Nat)
  | read (q : Nat)
  | quot (q a : Nat)
  | action (q a : Nat)
  | restoreAction (q a : Nat)
  | leftShift (q : Nat)
  | restoreLeft (q : Nat)
  | leftPop (q : Nat)
  | leftQuot (q a : Nat)
  | rightLen (q : Nat)
  | rightRestore (q : Nat)
  | leftLen (q : Nat)
  | halt (q : Nat)
  deriving DecidableEq

structure Tag where
  phase : Phase
  mid : Bool
  deriving DecidableEq

inductive Move where
  | left | stay | right
  deriving DecidableEq

structure Instruction where
  target : Nat
  write : Nat
  move : Move

abbrev Data := Fin 5 → Nat
def L : Fin 5 := 0
def R : Fin 5 := 1
def U : Fin 5 := 2
def llen : Fin 5 := 3
def rlen : Fin 5 := 4

def lane (i : Fin 5) (a : Nat) : Data := fun j => if j=i then a else 0
def mainTag (p : Phase) : Tag := ⟨p,false⟩
def midTag (p : Phase) : Tag := ⟨p,true⟩

structure Body where
  dst : Tag
  take : Data
  give : Data

structure Edge where
  src : Tag
  body : Body

def go (p : Phase) : Body := ⟨mainTag p,0,0⟩
def takeGive (p : Phase) (x : Fin 5) (a : Nat) (y : Fin 5) (b : Nat) : Body :=
  ⟨mainTag p,lane x a,lane y b⟩

structure Transfer where
  x : Fin 5
  a : Nat
  y : Fin 5
  b : Nat

def actionSpec (table : Nat → Nat → Option Instruction) (q a : Nat) :
    Fin 5 × Nat × Phase :=
  match table q a with
  | none => (R,a,.halt q)
  | some i =>
    match i.move with
    | .right => (L,i.write,.rightLen i.target)
    | .left => (R,i.write,.leftShift i.target)
    | .stay => (R,i.write,.q i.target)

def transfer (B : Nat) (table : Nat → Nat → Option Instruction) : Phase → Option Transfer
  | .read _ => some ⟨R,B,U,1⟩
  | .quot _ _ => some ⟨U,1,R,1⟩
  | .action q a => some ⟨(actionSpec table q a).1,1,U,B⟩
  | .restoreAction q a => some ⟨U,1,(actionSpec table q a).1,1⟩
  | .leftShift _ => some ⟨R,1,U,B⟩
  | .restoreLeft _ => some ⟨U,1,R,1⟩
  | .leftPop _ => some ⟨L,B,U,1⟩
  | .leftQuot _ _ => some ⟨U,1,L,1⟩
  | _ => none

-- Each dispatch list is descending in the *normalized* digit, including
-- digit zero as fallback. The original alphabet may have blank elsewhere.
def exits (digits : List Nat) (table : Nat → Nat → Option Instruction) :
    Phase → List Body
  | .q q => [go (.read q)]
  | .read q => digits.map (fun a => ⟨mainTag (.quot q a),lane R a,0⟩)
  | .quot q a => [go (.action q a)]
  | .action q a => [go (.restoreAction q a)]
  | .restoreAction q a =>
      let (x,b,dst) := actionSpec table q a
      [⟨mainTag dst,0,lane x b⟩]
  | .leftShift q => [go (.restoreLeft q)]
  | .restoreLeft q => [go (.leftPop q)]
  | .leftPop q => digits.map (fun a => takeGive (.leftQuot q a) L a R a)
  | .leftQuot q _ => [go (.leftLen q)]
  | .rightLen q => [takeGive (.rightRestore q) rlen 2 llen 1,
                      ⟨mainTag (.q q),0,lane llen 1⟩]
  | .rightRestore q => [⟨mainTag (.q q),0,lane rlen 1⟩]
  | .leftLen q => [takeGive (.q q) llen 1 rlen 1,⟨mainTag (.q q),0,lane rlen 1⟩]
  | .halt _ => []

def loopBody (p : Phase) (t : Transfer) : Body :=
  ⟨midTag p,lane t.x t.a,lane t.y t.b⟩

def phaseList (B : Nat) (digits : List Nat) (table : Nat → Nat → Option Instruction)
    (p : Tag) : List Body :=
  match transfer B table p.phase,p.mid with
  | some t,false => loopBody p.phase t :: exits digits table p.phase
  | some _,true => [go p.phase]
  | none,false => exits digits table p.phase
  | none,true => []

def tagged (p : Tag) (bs : List Body) : List Edge := bs.map (Edge.mk p)

def outgoing (p : Tag) : List Edge → List Edge
  | [] => []
  | r::rs => if r.src=p then r::outgoing p rs else outgoing p rs

theorem outgoing_append (p : Tag) (a b : List Edge) :
    outgoing p (a++b)=outgoing p a++outgoing p b := by
  induction a with
  | nil => rfl
  | cons r rs ih => by_cases h : r.src=p <;> simp [outgoing,h,ih]

theorem outgoing_tagged (p q : Tag) (bs : List Body) :
    outgoing p (tagged q bs) = if q=p then tagged q bs else [] := by
  induction bs with
  | nil => simp [tagged,outgoing]
  | cons b bs ih => by_cases h : q=p <;> simp [tagged,outgoing,h,ih]

def emit (body : Tag → List Body) : List Tag → List Edge
  | [] => []
  | p::ps => tagged p (body p) ++ emit body ps

theorem emitted_outgoing (body : Tag → List Body) (ps : List Tag)
    (hn : ps.Nodup) (p : Tag) :
    outgoing p (emit body ps) = if p∈ps then tagged p (body p) else [] := by
  induction ps with
  | nil => simp [emit,outgoing]
  | cons q qs ih =>
    have h := List.nodup_cons.mp hn
    rw [emit,outgoing_append,outgoing_tagged,ih h.2]
    by_cases e : q=p
    · subst q
      simp [h.1]
    · by_cases hp : p∈qs
      · simp [e,Ne.symm e,hp]
      · simp [e,Ne.symm e,hp]

def phases (Q A : Nat) : List Phase :=
  (List.range Q).flatMap fun q =>
    [.q q,.read q,.leftShift q,.restoreLeft q,.leftPop q,.rightLen q,
      .rightRestore q,.leftLen q,.halt q] ++
      (List.range A).flatMap (fun a => [.quot q a,.action q a,.restoreAction q a,.leftQuot q a])

def inventory (Q A : Nat) : List Tag :=
  ((phases Q A).flatMap fun p => [mainTag p,midTag p]).eraseDups

-- The full grouped program is finite and emitted from the actual
-- source transition table, without an execution horizon.
def compile (Q A : Nat) (table : Nat → Nat → Option Instruction) : List Edge :=
  emit (phaseList (max 2 A) (List.range A).reverse table) (inventory Q A)

theorem compile_outgoing (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Tag) (hp : p∈inventory Q A) :
    outgoing p (compile Q A table) =
      tagged p (phaseList (max 2 A) (List.range A).reverse table p) := by
  unfold compile
  rw [emitted_outgoing]
  · simp [hp]
  · exact List.nodup_eraseDups _

theorem emitted_loop (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer)
    (hm : mainTag p ∈ inventory Q A) (hh : midTag p ∈ inventory Q A)
    (h : transfer (max 2 A) table p=some t) :
    outgoing (mainTag p) (compile Q A table) =
      tagged (mainTag p) (loopBody p t :: exits (List.range A).reverse table p) ∧
    outgoing (midTag p) (compile Q A table) =
      tagged (midTag p) [go p] := by
  rw [compile_outgoing Q A table _ hm,compile_outgoing Q A table _ hh]
  simp [phaseList,mainTag,midTag,h]

-- Native control guard and first selection for all five lanes, without
-- reducing a high-priority guard to an incorrect cancelled rational.
structure State where
  tag : Tag
  data : Data

def enabled (r : Edge) (s : State) : Prop :=
  r.src=s.tag ∧ ∀ i, r.body.take i≤s.data i

instance (r : Edge) (s : State) : Decidable (enabled r s) := by
  unfold enabled
  infer_instance

def first : List Edge → State → Option Edge
  | [], _ => none
  | r::rs,s => if enabled r s then some r else first rs s

theorem first_local (P : List Edge) (s : State) :
    first P s=first (outgoing s.tag P) s := by
  induction P with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.src=s.tag
    · simp only [outgoing,h,if_pos,first]
      by_cases he : enabled r s <;> simp [he,ih]
    · have hf : ¬enabled r s := fun e => h e.1
      simpa [outgoing,h,first,hf] using ih

def step (P : List Edge) (s : State) : Option State :=
  (first P s).map (fun r => ⟨r.body.dst,fun i => s.data i-r.body.take i+r.body.give i⟩)

theorem compiled_first (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (s : State) (h : s.tag∈inventory Q A) :
    first (compile Q A table) s =
      first (tagged s.tag (phaseList (max 2 A) (List.range A).reverse table s.tag)) s := by
  rw [first_local,compile_outgoing Q A table _ h]

-- Actual extent updates are last exits: the exact numeric move lemmas
-- in PNPStackFractran supply their desired boundary endpoint. Remaining
-- native proof: full five-lane run through all emitted private phases,
-- inventory completeness/digit dispatch, prime-factor interpretation
-- and the actual Agda candidate-code transport. The compiler-list
-- condition is no longer a supplied arbitrary list premise.
end PNPStackEmittedList
