import Welds.PNPReentrantSweepExact

namespace PNPCompressedWord
open PNPStackEmittedList PNPStackFractran PNPActualWordBisim

abbrev Rope := List (List Nat × Nat)

def copies (w : List Nat) : Nat → List Nat
  | 0 => []
  | k+1 => w++copies w k

def expand : Rope → List Nat
  | [] => []
  | (w,k)::rs => copies w k++expand rs

def extent : Rope → Nat
  | [] => 0
  | (w,k)::rs => w.length*k+extent rs

theorem copies_length (w : List Nat) (k : Nat) :
    (copies w k).length=w.length*k := by
  induction k with
  | zero => simp [copies]
  | succ k ih =>
    simp [copies,ih,Nat.mul_succ,Nat.add_comm]

theorem copies_nil (k : Nat) : copies [] k=[] := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [copies] using ih

theorem extent_exact (r : Rope) : (expand r).length=extent r := by
  induction r with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨w,k⟩
    simp [expand,extent,copies_length,ih]

def push (b : Nat) (r : Rope) : Rope := ([b],1)::r

theorem push_exact (b : Nat) (r : Rope) : expand (push b r)=b::expand r := rfl

-- A pop reduces one block descriptor, never expands its repetitions.
def pop : Rope → Nat × Rope
  | [] => (0,[])
  | ([],_)::rs => pop rs
  | (_::_,0)::rs => pop rs
  | (b::bs,k+1)::rs => (b,(bs,1)::(b::bs,k)::rs)

theorem pop_head (r : Rope) : (pop r).1=(expand r).headD 0 := by
  induction r with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨w,k⟩
    cases w with
    | nil => simpa [pop,expand,copies_nil] using ih
    | cons b bs =>
      cases k with
      | zero => simpa [pop,expand,copies] using ih
      | succ k => rfl

theorem pop_tail (r : Rope) : expand (pop r).2=(expand r).drop 1 := by
  induction r with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨w,k⟩
    cases w with
    | nil => simpa [pop,expand,copies_nil] using ih
    | cons b bs =>
      cases k with
      | zero => simpa [pop,expand,copies] using ih
      | succ k => simp [pop,expand,copies,List.append_assoc]

structure Compressed where
  left : Rope
  scanned : Nat
  right : Rope

def reopen (c : Compressed) : Config := ⟨expand c.left,c.scanned,expand c.right⟩

def move (c : Compressed) (b : Nat) : Move → Compressed
  | .stay => ⟨c.left,b,c.right⟩
  | .right => ⟨push b c.left,(pop c.right).1,(pop c.right).2⟩
  | .left => ⟨(pop c.left).2,(pop c.left).1,push b c.right⟩

theorem reopen_right (c : Compressed) (b : Nat) :
    reopen (move c b .right)=rightMove (reopen c) b := by
  simp [reopen,move,rightMove,push_exact,pop_head,pop_tail]

theorem reopen_left (c : Compressed) (b : Nat) :
    reopen (move c b .left)=leftMove (reopen c) b := by
  simp [reopen,move,leftMove,push_exact,pop_head,pop_tail]

theorem reopen_stay (c : Compressed) (b : Nat) :
    reopen (move c b .stay)=stay (reopen c) b := rfl

def compressedResult (B q : Nat) (table : Nat → Nat → Option Instruction)
    (c : Compressed) : State :=
  match table q c.scanned with
  | none => ⟨mainTag (.halt q),dataOf B (reopen c)⟩
  | some i => ⟨mainTag (.q i.target),dataOf B (reopen (move c i.write i.move))⟩

theorem reopen_result (B q : Nat) (table : Nat → Nat → Option Instruction)
    (c : Compressed) :
    compressedResult B q table c=sourceResult B q table (reopen c) := by
  cases h : table q c.scanned with
  | none => simp [compressedResult,sourceResult,reopen,h]
  | some i =>
    cases hm : i.move <;>
      simp [compressedResult,sourceResult,reopen_right,reopen_left,reopen_stay,h,hm]

theorem actual_prime_step (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (c : Compressed) (hA : 0<A) (hq : q<Q) (ha : c.scanned<A)
    (hl : ∀ d∈expand c.left,d<A)
    (htarget : ∀ i,table q c.scanned=some i → i.target<Q) :
    ∃ k, PNPActualPrimeRun.integerRun Q A (compile Q A table) k
      (PNPActualPrimeLayout.integerState Q A
        ⟨mainTag (.q q),dataOf (max 2 A) (reopen c)⟩) =
      some (PNPActualPrimeLayout.integerState Q A
        (compressedResult (max 2 A) q table c)) := by
  rw [reopen_result]
  exact PNPActualPrimeRun.primeMacroExact Q A q table (reopen c) hA hq ha hl htarget

-- Native list expansion is semantic only; it is not performed by the
-- descriptor pop. No assertion of a bounded whole-run descriptor size.
end PNPCompressedWord
