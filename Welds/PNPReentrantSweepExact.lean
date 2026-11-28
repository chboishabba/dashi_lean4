import Welds.PNPBlankSweepExact

namespace PNPReentrantSweep
open PNPStackEmittedList PNPStackFractran
open PNPActualWordBisim PNPActualInventoryClosure
open PNPActualInstructionLedger PNPActualPrimeRun PNPActualPrimeLayout
open PNPBlankSweep

def fromWords (l r : List Nat) : Config := ⟨l,r.headD 0,r.drop 1⟩

def before (l writes : List Nat) (a : Nat) (rs : List Nat) : Config :=
  fromWords l (List.replicate writes.length 0 ++ a::rs)

def after (l writes : List Nat) (a : Nat) (rs : List Nat) : Config :=
  ⟨writes.reverse++l,a,rs⟩

theorem before_nil (l : List Nat) (a : Nat) (rs : List Nat) :
    before l [] a rs = after l [] a rs := rfl

theorem before_right (l bs : List Nat) (b a : Nat) (rs : List Nat) :
    rightMove (before l (b::bs) a rs) b = before (b::l) bs a rs := by
  simp [before,fromWords,rightMove,List.replicate_succ]

theorem after_cons (l bs : List Nat) (b a : Nat) (rs : List Nat) :
    after (b::l) bs a rs = after l (b::bs) a rs := by
  simp [after,List.reverse_cons,List.append_assoc]

-- A finite blank PREFIX may end at a nonblank sentinel. Unlike the
-- earlier all-zero packed-right theorem this retains the original tail.
theorem sentinel_raw {Q A : Nat} {table : Nat → Nat → Option Instruction}
    (legal : LegalTable Q A table) (hA : 0<A)
    {q p : Nat} {bs : List Nat} (s : Sweep table q bs p)
    (hq : q<Q) (l : List Nat) (hl : ∀ d∈l,d<A)
    (a : Nat) (rs : List Nat) :
    p<Q ∧ (∀ d∈(after l bs a rs).left,d<A) ∧
    ∃ raw, run (compile Q A table) raw
      ⟨mainTag (.q q),dataOf (max 2 A) (before l bs a rs)⟩ =
      some ⟨mainTag (.q p),dataOf (max 2 A) (after l bs a rs)⟩ := by
  induction s generalizing l with
  | done q =>
    exact ⟨hq,by simpa [after] using hl,0,by rw [before_nil]; rfl⟩
  | @step q p bs i rule right rest ih =>
    have legalRule := legal _ 0 i hq hA rule
    have hleft : ∀ d∈i.write::l,d<A := by
      intro d hd
      rcases List.mem_cons.mp hd with e|e
      · simpa [e] using legalRule.2
      · exact hl d e
    obtain ⟨hp,hleft',n,tail⟩ := ih legalRule.1 (i.write::l) hleft
    have ha : (before l (i.write::bs) a rs).scanned=0 := by
      simp [before,fromWords,List.replicate_succ]
    obtain ⟨m,head⟩ := raw_step_bisim Q A q table
      (before l (i.write::bs) a rs) hA hq (by rw [ha]; exact hA)
      (by simpa [before,fromWords] using hl)
      (fun j hj => (legal _ _ j hq (by rw [ha]; exact hA) hj).1)
    have head' : run (compile Q A table) m
      ⟨mainTag (.q q),dataOf (max 2 A) (before l (i.write::bs) a rs)⟩ =
      some ⟨mainTag (.q i.target),dataOf (max 2 A) (before (i.write::l) bs a rs)⟩ := by
      simpa [sourceResult,ha,rule,right,before_right] using head
    refine ⟨hp,?_,m+n,?_⟩
    · simpa [after_cons] using hleft'
    · rw [run_append,head']
      simpa [after_cons] using tail

theorem sentinel_reentry {Q A : Nat} {table : Nat → Nat → Option Instruction}
    (legal : LegalTable Q A table) (hA : 0<A)
    {q p : Nat} {bs : List Nat} (s : Sweep table q bs p)
    (hq : q<Q) (l : List Nat) (hl : ∀ d∈l,d<A)
    (a : Nat) (ha : a<A) (rs : List Nat) :
    ∃ raw, integerRun Q A (compile Q A table) raw
      (integerState Q A ⟨mainTag (.q q),dataOf (max 2 A) (before l bs a rs)⟩) =
      some (integerState Q A (sourceResult (max 2 A) p table (after l bs a rs))) := by
  obtain ⟨hp,hl',m,first⟩ := sentinel_raw legal hA s hq l hl a rs
  obtain ⟨n,last⟩ := raw_step_bisim Q A p table (after l bs a rs)
    hA hp ha hl' (fun i hi => (legal p a i hp ha hi).1)
  refine ⟨m+n,?_⟩
  rw [compiled_primeRunExact,run_append,first]
  simpa [last]

-- Repeat descriptors are interpreted by the existing repeatedWrites
-- and sweep_prefix_cycle_suffix. This native theorem retains represented
-- raw length; it does not certify a compressed physical execution.
end PNPReentrantSweep
