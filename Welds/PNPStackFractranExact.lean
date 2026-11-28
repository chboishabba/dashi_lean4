import Mathlib

namespace PNPStackFractran

-- Digits are indexed using the original alphabet, with blank=0.
-- This is a binary exponent representation, not materialized prime powers.
def push (B d v : Nat) : Nat := d + B*v

theorem pop_push (B d v : Nat) (hB : 0 < B) (hd : d < B) :
    push B d v % B = d ∧ push B d v / B = v := by
  constructor
  · simp [push, Nat.mod_eq_of_lt hd]
  · rw [push, Nat.add_mul_div_left d v hB, Nat.div_eq_of_lt hd, zero_add]

def encode (B : Nat) : List Nat → Nat
  | [] => 0
  | d::ds => push B d (encode B ds)

def decode (B : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, v => v % B :: decode B n (v/B)

theorem decode_encode (B : Nat) (hB : 0 < B) (ds : List Nat)
    (h : ∀ d ∈ ds, d<B) : decode B ds.length (encode B ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : d<B := h d (by simp)
    have ht : ∀ e ∈ ds, e<B := fun e he => h e (by simp [he])
    have hp := pop_push B d (encode B ds) hB hd
    simp only [List.length_cons,encode,decode,hp.1,hp.2,ih ht]

theorem encode_decode (B : Nat) (hB : 0 < B) (n v : Nat)
    (hv : v < B^n) : encode B (decode B n v) = v := by
  induction n generalizing v with
  | zero =>
    simp only [pow_zero] at hv
    have : v=0 := by omega
    simp [decode,encode,this]
  | succ n ih =>
    have hq : v/B < B^n := by
      apply (Nat.div_lt_iff_lt_mul hB).mpr
      simpa [pow_succ] using hv
    simp only [decode,encode,push,ih (v/B) hq]
    exact Nat.mod_add_div v B

-- The encoded length is essential: [0] and [] have the same exponent.
theorem blank_extent_collision (B : Nat) : encode B [0] = encode B [] := by
  simp [encode,push]

structure Config where
  left : List Nat
  scanned : Nat
  right : List Nat
  deriving DecidableEq

structure Packed where
  L : Nat
  R : Nat
  llen : Nat
  rlen : Nat
  deriving DecidableEq

def pack (B : Nat) (c : Config) : Packed :=
  ⟨encode B c.left,encode B (c.scanned::c.right),c.left.length,c.right.length+1⟩

def unpack (B : Nat) (p : Packed) : Config :=
  ⟨decode B p.llen p.L,p.R%B,decode B (p.rlen-1) (p.R/B)⟩

theorem unpack_pack (B : Nat) (hB : 0<B) (c : Config)
    (hl : ∀ d ∈ c.left, d<B) (ha : c.scanned<B)
    (hr : ∀ d ∈ c.right, d<B) :
    unpack B (pack B c) = c := by
  cases c with
  | mk l a r =>
    have hp := pop_push B a (encode B r) hB ha
    simp [pack,unpack,encode,hp.1,hp.2,decode_encode B hB l hl,
      decode_encode B hB r hr]

def rightMove (c : Config) (b : Nat) : Config :=
  ⟨b::c.left,c.right.headD 0,c.right.drop 1⟩

def leftMove (c : Config) (b : Nat) : Config :=
  ⟨c.left.drop 1,c.left.headD 0,b::c.right⟩

def stay (c : Config) (b : Nat) : Config :=
  ⟨c.left,b,c.right⟩

theorem moveRight (B : Nat) (hB : 0<B) (c : Config) (b : Nat)
    (ha : c.scanned<B) :
    pack B (rightMove c b) =
    ⟨push B b (pack B c).L,(pack B c).R/B,
      (pack B c).llen+1,max 1 ((pack B c).rlen-1)⟩ := by
  cases c with
  | mk l a r =>
    have hp := pop_push B a (encode B r) hB ha
    cases r <;> simp [pack,rightMove,encode,push,hp.2] <;> omega

theorem moveLeft (B : Nat) (hB : 0<B) (c : Config) (b : Nat)
    (ha : c.scanned<B) (hl : ∀ d ∈ c.left, d<B) :
    pack B (leftMove c b) =
    ⟨(pack B c).L/B,push B ((pack B c).L%B) (push B b ((pack B c).R/B)),
      (pack B c).llen-1,(pack B c).rlen+1⟩ := by
  cases c with
  | mk l a r =>
    have hp := pop_push B a (encode B r) hB ha
    cases l with
    | nil => simp [pack,leftMove,encode,push,hp.2]
    | cons d ds =>
      have hd : d<B := hl d (by simp)
      have hq := pop_push B d (encode B ds) hB hd
      simp [pack,leftMove,encode,hp.2,hq.1,hq.2]

theorem moveStay (B : Nat) (hB : 0<B) (c : Config) (b : Nat)
    (ha : c.scanned<B) :
    pack B (stay c b) =
    ⟨(pack B c).L,push B b ((pack B c).R/B),(pack B c).llen,(pack B c).rlen⟩ := by
  cases c with
  | mk l a r =>
    have hp := pop_push B a (encode B r) hB ha
    simp [pack,stay,encode,hp.2]

-- One transfer loop consumes a from x and produces b in scratch u.
-- At maximal k=x/a, the selected guard ceases to hold; no binary search
-- is needed. These arithmetic obligations accompany the existing
-- priority interval checker, which additionally excludes higher rules.
theorem maximal_transfer (x a b u : Nat) (ha : 0<a) :
    let k := x/a
    let rest := x%a
    a*k+rest=x ∧ rest<a ∧
      (∀ j<k, a ≤ x-a*j) ∧ u+k*b = u+(x/a)*b := by
  dsimp
  refine ⟨Nat.div_add_mod x a,Nat.mod_lt x ha,?_,rfl⟩
  intro j hj
  have h := Nat.div_add_mod x a
  have hm := Nat.mul_le_mul_left a (show j+1≤x/a by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

-- A fixed number of stack arithmetic operations on binary exponents
-- is not a fixed raw FRACTRAN step count nor ordinary integer bit time.
-- Full priority/compiler/native source attachment remains separate.
end PNPStackFractran
