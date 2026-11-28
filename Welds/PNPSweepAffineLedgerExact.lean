import Welds.PNPBlankSweepExact

namespace PNPSweepAffineLedger
open PNPBlankSweep PNPActualPackedMacro

-- Exact affine transformation of left value AND accumulated pre-step
-- left values. This is the represented raw FRACTRAN run cost.
structure Block where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

def identity : Block := ⟨1,0,0,0⟩
def cell (B b : Nat) : Block := ⟨B,b,1,0⟩
def compose (f g : Block) : Block :=
  ⟨g.a*f.a,g.a*f.b+g.b,f.c+g.c*f.a,f.d+g.c*f.b+g.d⟩
def endpoint (f : Block) (l : Nat) : Nat := f.a*l+f.b
def accumulated (f : Block) (l : Nat) : Nat := f.c*l+f.d

theorem endpoint_compose (f g : Block) (l : Nat) :
    endpoint (compose f g) l=endpoint g (endpoint f l) := by
  simp [compose,endpoint]; ring

theorem accumulated_compose (f g : Block) (l : Nat) :
    accumulated (compose f g) l=accumulated f l+accumulated g (endpoint f l) := by
  simp [compose,endpoint,accumulated]; ring

theorem compose_assoc (f g h : Block) :
    compose (compose f g) h=compose f (compose g h) := by
  cases f; cases g; cases h
  simp [compose] <;> congr 1 <;> ring

def summarize (B : Nat) : List Nat → Block
  | [] => identity
  | b::bs => compose (cell B b) (summarize B bs)

def sumPre (B l : Nat) : List Nat → Nat
  | [] => 0
  | b::bs => l+sumPre B (B*l+b) bs

theorem endpoint_exact (B l : Nat) (bs : List Nat) :
    endpoint (summarize B bs) l=appendWrites B l bs := by
  induction bs generalizing l with
  | nil => simp [summarize,identity,endpoint,appendWrites]
  | cons b bs ih =>
    rw [summarize,endpoint_compose]
    simpa [endpoint,cell,appendWrites] using ih (B*l+b)

theorem accumulated_exact (B l : Nat) (bs : List Nat) :
    accumulated (summarize B bs) l=sumPre B l bs := by
  induction bs generalizing l with
  | nil => simp [summarize,identity,accumulated,sumPre]
  | cons b bs ih =>
    rw [summarize,accumulated_compose]
    simp [accumulated,cell,endpoint,sumPre,ih]

theorem raw_exact (B l rr : Nat) (bs : List Nat) (hr : 0<rr) :
    rawCount B l rr bs =
      6*bs.length+2*(1+B)*sumPre B l bs+min bs.length (rr-1) := by
  induction bs generalizing l rr with
  | nil => simp [rawCount,sumPre]
  | cons b bs ih =>
    have h := ih (B*l+b) (max 1 (rr-1)) (by omega)
    have e : (if 2≤rr then 1 else 0)+min bs.length (max 1 (rr-1)-1) =
        min (bs.length+1) (rr-1) := by
      split <;> omega
    simp only [rawCount,h,sumPre,List.length_cons,commonRaw]
    by_cases k : 2≤rr <;> simp [k] at e ⊢ <;>
      nlinarith [e]

-- This gives the exact raw count for a complete finite blank sweep;
-- a compact expression or residue of that count is not a physical run.
theorem summarized_raw (B l rr : Nat) (bs : List Nat) (hr : 0<rr) :
    rawCount B l rr bs =
      6*bs.length+2*(1+B)*accumulated (summarize B bs) l+
        min bs.length (rr-1) := by
  rw [accumulated_exact,raw_exact B l rr bs hr]

end PNPSweepAffineLedger
