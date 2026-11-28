import Mathlib

namespace PNPCookAffineSeek

def tri : Nat → ℤ
  | 0 => 0
  | n+1 => tri n + n

theorem tri_closed (n : Nat) : 2*tri n = (n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tri,Nat.cast_succ]
    linarith [show ((n:ℤ)+1)*((n:ℤ)+1-1) =
      (n:ℤ)*((n:ℤ)-1)+2*(n:ℤ) by ring]

def windowPrefix (a b c : ℤ) (t j : Nat) : ℤ :=
  (j:ℤ)*(a*t+c)+b*tri j

def timePrefix (a b c : ℤ) (J t : Nat) : ℤ :=
  (J:ℤ)*(a*tri t+c*t)+b*t*tri J

theorem window_step (a b c : ℤ) (t j : Nat) :
    windowPrefix a b c t (j+1) =
      windowPrefix a b c t j + (a*t+b*j+c) := by
  simp only [windowPrefix,tri,Nat.cast_add,Nat.cast_one]
  ring

theorem time_step (a b c : ℤ) (J t : Nat) :
    timePrefix a b c J (t+1) =
      timePrefix a b c J t + windowPrefix a b c t J := by
  simp only [timePrefix,windowPrefix,tri,Nat.cast_add,Nat.cast_one]
  ring

-- Exact row-major rectangle prefix, independent of how the local
-- rejected-row template was constructed.
def windowSum (a b c : ℤ) (t : Nat) : Nat → ℤ
  | 0 => 0
  | j+1 => windowSum a b c t j + (a*t+b*j+c)

theorem window_exact (a b c : ℤ) (t j : Nat) :
    windowSum a b c t j = windowPrefix a b c t j := by
  induction j with
  | zero => simp [windowSum,windowPrefix,tri]
  | succ j ih => rw [windowSum,ih,window_step]

def timeSum (a b c : ℤ) (J : Nat) : Nat → ℤ
  | 0 => 0
  | t+1 => timeSum a b c J t + windowSum a b c t J

theorem time_exact (a b c : ℤ) (J t : Nat) :
    timeSum a b c J t = timePrefix a b c J t := by
  induction t with
  | zero => simp [timeSum,timePrefix,tri]
  | succ t ih => rw [timeSum,ih,window_exact,time_step]

-- Original CNFCookPrefixToken grammar: OR, optional NOT, VAR,
-- unary variable index, ZERO. Clause prefix AND and final FALSE
-- are counted separately.
def literalTokens (v : Nat) (pos : Bool) : List Nat :=
  [7] ++ (if pos then [] else [5]) ++ [2] ++ List.replicate v 1 ++ [0]

theorem literal_length (v : Nat) (pos : Bool) :
    (literalTokens v pos).length = v+3+(if pos then 0 else 1) := by
  cases pos <;> simp [literalTokens] <;> omega

theorem seek_unique (p : Nat → ℤ) (hp : Monotone p) (k : ℤ)
    (i j : Nat) (hi : p i≤k ∧ k<p (i+1))
    (hj : p j≤k ∧ k<p (j+1)) : i=j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have e : p (i+1)≤p j := hp (by omega)
    linarith [hi.2,hj.1]
  · have e : p (j+1)≤p i := hp (by omega)
    linarith [hj.2,hi.1]

-- Full canonical query is charged at least its unary T section.
-- Actual Agda owner supplies this length inequality; no inference
-- that embedded target execution definitionally pays it.
theorem unary_query_no_fit (T queryLength work prefix suffix : Nat)
    (h : T+1≤queryLength) :
    ¬ prefix+queryLength+work+suffix≤T := by omega

end PNPCookAffineSeek
