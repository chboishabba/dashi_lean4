import Mathlib

namespace PNPSignedCharacterTail

structure Hist where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq

def conv (x y : Hist) : Hist :=
  ⟨x.a*y.a+x.b*y.c+x.c*y.b,
   x.a*y.b+x.b*y.a+x.c*y.c,
   x.a*y.c+x.b*y.b+x.c*y.a⟩

theorem conv_assoc (x y z : Hist) : conv (conv x y) z = conv x (conv y z) := by
  cases x; cases y; cases z
  simp only [conv]
  congr 1 <;> ring

def nn (x : Hist) := 0 ≤ x.a ∧ 0 ≤ x.b ∧ 0 ≤ x.c
def below (x y : Hist) := x.a ≤ y.a ∧ x.b ≤ y.b ∧ x.c ≤ y.c

theorem conv_mono (x y X Y : Hist) (hx : nn x) (hy : nn y)
    (hX : below x X) (hY : below y Y) : below (conv x y) (conv X Y) := by
  rcases hx with ⟨xa,xb,xc⟩
  rcases hy with ⟨ya,yb,yc⟩
  rcases hX with ⟨a,b,c⟩
  rcases hY with ⟨d,e,f⟩
  simp only [below,conv]
  exact ⟨add_le_add (add_le_add (mul_le_mul a d ya (xa.trans a))
      (mul_le_mul b f yc (xb.trans b))) (mul_le_mul c e yb (xc.trans c)),
    add_le_add (add_le_add (mul_le_mul a e yb (xa.trans a))
      (mul_le_mul b d ya (xb.trans b))) (mul_le_mul c f yc (xc.trans c)),
    add_le_add (add_le_add (mul_le_mul a f yc (xa.trans a))
      (mul_le_mul b e yb (xb.trans b))) (mul_le_mul c d ya (xc.trans c))⟩

def energy (x : Hist) := (x.a-x.c)^2-(x.a-x.c)*(x.b-x.c)+(x.b-x.c)^2

theorem energy_mul (x y : Hist) : energy (conv x y) = energy x * energy y := by
  simp only [energy,conv]
  ring

def contrast (x : Hist) (d : Fin 3) : ℚ :=
  if d = 0 then 2*x.a-x.b-x.c else if d = 1 then 2*x.b-x.a-x.c else 2*x.c-x.a-x.b

theorem contrast_sq_le (x : Hist) (d : Fin 3) : contrast x d ^ 2 ≤ 4 * energy x := by
  fin_cases d <;> norm_num [contrast,energy] <;>
    nlinarith [sq_nonneg (x.a-x.b),sq_nonneg (x.a-x.c),sq_nonneg (x.b-x.c)]

theorem zero_character (x : Hist) (h : energy x = 0) (d : Fin 3) :
    contrast x d = 0 := by
  have h' := contrast_sq_le x d
  rw [h] at h'
  nlinarith [sq_nonneg (contrast x d)]

theorem pair_swap (s x y : ℚ) : (-s)*(y-x) = s*(x-y) := by ring

-- Absolute, not relative, omitted energy on the actual finite boundary.
-- Sum of products bound via scalar Cauchy--Schwarz.
theorem tail_squared {ι : Type*} (s : Finset ι)
    (a b : ι → ℚ) :
    (∑ i ∈ s, a i * b i)^2 ≤ (∑ i ∈ s, a i^2) * (∑ i ∈ s, b i^2) := by
  exact Finset.sum_mul_sq_le_sq_mul_sq s a b

end PNPSignedCharacterTail

namespace PNPGuardedTranslation

-- A fixed selected translation block, on ONE nonnegative valuation lane.
-- Ordered dispatch is separate: higher priority rules must be disabled at
-- every prefix. This theorem does not identify saturated signed IR with Z.
abbrev Rule := ℤ × ℤ
def displacement : List Rule → ℤ
  | [] => 0
  | (_,d)::rs => d+displacement rs

def need : List Rule → ℤ
  | [] => 0
  | (g,d)::rs => max 0 (max g (need rs-d))

def legal (v : ℤ) : List Rule → Prop
  | [] => 0 ≤ v
  | (g,d)::rs => 0 ≤ v ∧ g ≤ v ∧ legal (v+d) rs

theorem entry_iff (v : ℤ) (rs : List Rule) : legal v rs ↔ need rs ≤ v := by
  induction rs generalizing v with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨g,d⟩
    simp only [legal,need,ih,max_le_iff]
    omega

def run (v : ℤ) : List Rule → ℤ
  | [] => v
  | (_,d)::rs => run (v+d) rs

theorem run_exact (v : ℤ) (rs : List Rule) : run v rs = v+displacement rs := by
  induction rs generalizing v with
  | nil => simp [run,displacement]
  | cons r rs ih =>
    rcases r with ⟨g,d⟩
    simp only [run,displacement,ih]
    ring

end PNPGuardedTranslation

namespace PNPCutStateNecessity
-- One-way sufficient cut, not an arbitrary multi-round communication cut.
theorem distinct_rows_injective {L R S : Type*} (f : L → R → Bool)
    (encode : L → S) (decode : S → R → Bool)
    (sound : ∀ l r, decode (encode l) r = f l r)
    (distinct : ∀ l l', l ≠ l' → ∃ r, f l r ≠ f l' r) :
    Function.Injective encode := by
  intro l l' h
  by_contra hn
  obtain ⟨r,hr⟩ := distinct l l' hn
  apply hr
  rw [← sound l r, ← sound l' r, h]

theorem card_bound {L R S : Type*} [Fintype L] [Fintype S]
    (f : L → R → Bool) (encode : L → S) (decode : S → R → Bool)
    (sound : ∀ l r, decode (encode l) r = f l r)
    (distinct : ∀ l l', l ≠ l' → ∃ r, f l r ≠ f l' r) :
    Fintype.card L ≤ Fintype.card S :=
  Fintype.card_le_of_injective encode (distinct_rows_injective f encode decode sound distinct)
end PNPCutStateNecessity
