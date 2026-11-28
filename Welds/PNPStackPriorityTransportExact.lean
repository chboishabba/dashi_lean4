import Mathlib
import Welds.PNPStackFractranExact

namespace PNPStackPriority

-- The actual fixed compiler uses one control prime per phase. No
-- unrelated source-phase rule can be enabled by the data lanes.
def oneHot (p : Nat) (i : Nat) : Nat := if i=p then 1 else 0

theorem control_guard (p i : Nat) : 1≤oneHot p i ↔ i=p := by
  by_cases h : i=p <;> simp [oneHot,h]

theorem control_transport (p q i : Nat) :
    oneHot p i - oneHot p i + oneHot q i = oneHot q i := by
  simp

-- Two active arithmetic lanes; all other data lanes are unchanged
-- throughout the private transfer pair.
structure Micro where
  phase : Nat
  x : Nat
  u : Nat
  deriving DecidableEq

structure Edge where
  src : Nat
  dst : Nat
  takeX : Nat
  takeU : Nat
  giveX : Nat
  giveU : Nat
  deriving DecidableEq

def enabled (r : Edge) (s : Micro) : Prop :=
  r.src=s.phase ∧ r.takeX≤s.x ∧ r.takeU≤s.u

instance (r : Edge) (s : Micro) : Decidable (enabled r s) := by
  unfold enabled
  infer_instance

def first : List Edge → Micro → Option Edge
  | [], _ => none
  | r::rs, s => if enabled r s then some r else first rs s

def outgoing (P : List Edge) (p : Nat) : List Edge :=
  P.filter (fun r => r.src == p)

theorem first_local (P : List Edge) (s : Micro) :
    first P s = first (outgoing P s.phase) s := by
  induction P with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.src=s.phase
    · simp [outgoing,h,first]
      by_cases h' : enabled r s <;> simp [h',ih,outgoing]
    · have hf : ¬enabled r s := fun e => h e.1
      simpa [outgoing,h,first,hf] using ih

def applyEdge (r : Edge) (s : Micro) : Micro :=
  ⟨r.dst,s.x-r.takeX+r.giveX,s.u-r.takeU+r.giveU⟩

def step (P : List Edge) (s : Micro) : Option Micro :=
  (first P s).map (fun r => applyEdge r s)

def loopEdge (p mid a b : Nat) : Edge := ⟨p,mid,a,0,0,b⟩
def returnEdge (p mid : Nat) : Edge := ⟨mid,p,0,0,0,0⟩

-- These are precisely the phase-list conditions audited for the actual
-- sparse fixed compiler, not an arbitrary ordered fraction program.
theorem transfer_first (P : List Edge) (p mid a b x u : Nat)
    (exits : List Edge)
    (hp : outgoing P p = loopEdge p mid a b :: exits)
    (h : a≤x) :
    step P ⟨p,x,u⟩ = some ⟨mid,x-a,u+b⟩ := by
  unfold step
  rw [first_local,show (Micro.mk p x u).phase=p from rfl,hp]
  simp [first,loopEdge,enabled,h,applyEdge]

theorem transfer_return (P : List Edge) (p mid x u : Nat)
    (hm : outgoing P mid = [returnEdge p mid]) :
    step P ⟨mid,x,u⟩ = some ⟨p,x,u⟩ := by
  unfold step
  rw [first_local,show (Micro.mk mid x u).phase=mid from rfl,hm]
  simp [first,returnEdge,enabled,applyEdge]

def run (P : List Edge) : Nat → Micro → Option Micro
  | 0, s => some s
  | k+1, s => (step P s).bind (run P k)

theorem transfer_repeat (P : List Edge) (p mid a b : Nat)
    (exits : List Edge)
    (hp : outgoing P p = loopEdge p mid a b :: exits)
    (hm : outgoing P mid = [returnEdge p mid])
    (k x u : Nat) (h : a*k≤x) :
    run P (2*k) ⟨p,x,u⟩ = some ⟨p,x-a*k,u+b*k⟩ := by
  induction k generalizing x u with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.mul_succ] at h
    have ha : a≤x := by omega
    have ht : a*k≤x-a := by omega
    rw [show 2*(k+1) = 2*k+2 by omega]
    simp only [run,transfer_first P p mid a b x u exits hp ha,
      Option.bind_some,transfer_return P p mid (x-a) (u+b) hm]
    rw [ih (x-a) (u+b) ht]
    simp only [Nat.mul_succ]
    congr 2 <;> omega

theorem transfer_maximal (P : List Edge) (p mid a b x u : Nat)
    (exits : List Edge)
    (hp : outgoing P p = loopEdge p mid a b :: exits)
    (hm : outgoing P mid = [returnEdge p mid])
    (ha : 0<a) :
    run P (2*(x/a)) ⟨p,x,u⟩ = some ⟨p,x%a,u+b*(x/a)⟩ := by
  have e := Nat.div_add_mod x a
  have h : a*(x/a)≤x := by omega
  rw [transfer_repeat P p mid a b exits hp hm (x/a) x u h]
  have hr : x-a*(x/a)=x%a := by omega
  rw [hr]

theorem maximal_select_exit (P : List Edge) (p mid a b x u : Nat)
    (exits : List Edge)
    (hp : outgoing P p = loopEdge p mid a b :: exits) (ha : 0<a) :
    first P ⟨p,x%a,u⟩ = first exits ⟨p,x%a,u⟩ := by
  rw [first_local,show (Micro.mk p (x%a) u).phase=p from rfl,hp]
  have h : ¬a≤x%a := not_le_of_gt (Nat.mod_lt x ha)
  simp [first,enabled,loopEdge,h]

-- The extent invariant is a BOUNDARY invariant. Scratch/push/extent
-- intermediate phases do not in general satisfy the same bound.
def boundaryInv (B : Nat) (p : PNPStackFractran.Packed) : Prop :=
  1≤p.rlen ∧ p.L<B^p.llen ∧ p.R<B^p.rlen

theorem push_bound (B d v n : Nat) (hd : d<B) (hv : v<B^n) :
    d+B*v<B^(n+1) := by
  have h := Nat.mul_le_mul_left B (show v+1≤B^n by omega)
  rw [Nat.mul_add,Nat.mul_one] at h
  rw [pow_succ,Nat.mul_comm (B^n) B]
  omega

theorem encode_bound (B : Nat) (ds : List Nat)
    (h : ∀ d∈ds,d<B) :
    PNPStackFractran.encode B ds < B^ds.length := by
  induction ds with
  | nil => simp [PNPStackFractran.encode]
  | cons d ds ih =>
    exact push_bound B d _ _ (h d (by simp))
      (ih (fun a ha => h a (by simp [ha])))

theorem pack_boundary (B : Nat) (c : PNPStackFractran.Config)
    (hl : ∀ d∈c.left,d<B) (ha : c.scanned<B)
    (hr : ∀ d∈c.right,d<B) :
    boundaryInv B (PNPStackFractran.pack B c) := by
  rcases c with ⟨l,a,r⟩
  refine ⟨by simp [PNPStackFractran.pack],encode_bound B l hl,?_⟩
  exact encode_bound B (a::r) (by
    intro d hd
    rcases List.mem_cons.mp hd with h|h
    · simpa [h] using ha
    · exact hr d h)

-- Actual raw compiler phase audit and numerical successor campaigns
-- accompany these generic ordered-priority lemmas. Native construction
-- of the complete emitted fraction list and the standard clock are
-- distinct remaining obligations; no same-horizon claim follows.
end PNPStackPriority
