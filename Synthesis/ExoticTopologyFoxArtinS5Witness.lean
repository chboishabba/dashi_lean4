import Mathlib.Tactic

/-!
# Fox--Artin 1948 Example 1.1*: the PRIMARY SOURCE S₅ certificate

R. H. Fox and E. Artin, "Some Wild Cells and Spheres in
Three-Dimensional Space", Annals of Mathematics 49 (1948), 979--990,
DOI 10.2307/1969408, page 983, equation (2_n*), Figure 6.

The user's initial image is Example 1.1*, NOT Examples 1.2 or 1.3.
Source's eliminated relator is

  aₙ aₙ₊₁² aₙ₊₂ = aₙ₊₁ aₙ₊₂ aₙ₊₁⁻¹ aₙ aₙ₊₁.

The paper exhibits the three-periodic permutation representation
  n mod 3 = 0: (1 2 3 4 5)
  n mod 3 = 1: (1 2 5 3 4)
  n mod 3 = 2: (1 2 4 5 3).

We build the ACTUAL Mathlib Equiv.Perm (Fin 5), use its real group
composition, and check all three residual relations by finite decision.
This shows that the source ABSTRACT GROUP PRESENTATION has a
nontrivial S₅-valued model. It is NOT a proof that this presentation
is the actual ambient-complement fundamental group without the
geometrical Van Kampen and directed-colimit same-object bridge.

Original attribution and qualitative contrasts:
  Example 1.1*: nontrivial complement fundamental group.
  Example 1.2: wildly embedded though complement is an open 3-cell.
  Example 1.3: simply-connected complement not an open 3-cell.
These are separate embedded arcs, not three names for one knot.
-/

namespace Synthesis.ExoticTopology

abbrev FoxPerm5 := Fin 5 ≃ Fin 5

/-- Fox--Artin original cycles, using 0-based Fin 5 coordinates. -/
def foxPerm0 : FoxPerm5 where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide
  right_inv := by decide

def foxPerm1 : FoxPerm5 where
  toFun := ![1, 4, 3, 0, 2]
  invFun := ![3, 0, 4, 2, 1]
  left_inv := by decide
  right_inv := by decide

def foxPerm2 : FoxPerm5 where
  toFun := ![1, 3, 0, 4, 2]
  invFun := ![2, 0, 4, 1, 3]
  left_inv := by decide
  right_inv := by decide

/-- Explicit conventional right-to-left permutation multiplication:
    `foxMul p q` applies `q` first, then `p`. -/
def foxMul (p q : FoxPerm5) : FoxPerm5 := q.trans p

def foxA : Fin 3 → FoxPerm5 := ![foxPerm0, foxPerm1, foxPerm2]

def foxNext : Fin 3 → Fin 3 := ![1, 2, 0]

def foxLHS (n : Fin 3) : FoxPerm5 :=
  foxMul (foxMul (foxMul (foxA n) (foxA (foxNext n)))
      (foxA (foxNext n))) (foxA (foxNext (foxNext n)))

def foxRHS (n : Fin 3) : FoxPerm5 :=
  foxMul
    (foxMul
      (foxMul
        (foxMul (foxA (foxNext n))
          (foxA (foxNext (foxNext n))))
        (foxA (foxNext n)).symm)
      (foxA n))
    (foxA (foxNext n))

/-- The EXACT eliminated equation (2_n*) holds in the supplied
    three-periodic S₅ witness, for all integer n by n mod 3.
    The chosen cycle images make it a nontrivial representation. -/
theorem foxArtinOneOneStar_represented_relator
    (n : Fin 3) : foxLHS n = foxRHS n := by
  fin_cases n <;> decide

theorem foxArtinOneOneStar_nontrivial :
    foxPerm0 ≠ Equiv.refl (Fin 5) := by
  decide

/-- The first source generator image has order exactly five. -/
theorem foxArtinOneOneStar_generator_fifthPower :
    foxMul foxPerm0
      (foxMul foxPerm0
        (foxMul foxPerm0
          (foxMul foxPerm0 foxPerm0))) =
      Equiv.refl (Fin 5) := by
  decide

end Synthesis.ExoticTopology
