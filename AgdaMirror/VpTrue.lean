import AgdaMirror.DASHIValuation

/-!
# Lean mirror of `DASHI/Arithmetic/VpTrue.agda` (genuine lemmas + honest boundary)

Faithful transcription of the "public valuation layer": the fuel-free interface
`vpTrue p n = vpDepth n p n` (choosing `n` itself as the public evaluation
bound), together with the genuine fuel-plateau transport lemmas.

**Honesty boundary.** The Agda original `postulate`s an *adequacy* law
`vp-depth-adequate : vp-depth n p n ≡ vp-depth (suc n) p n`.  Following the strict
discipline of this mirror (postulates are never transcribed as axioms), we do not
assume it — and in fact, with the genuine `vpDepth` recursion (where `0` is
divisible by every base, so `vpDepth` keeps consuming fuel on `n = 0`), the
adequacy law is **genuinely false** as a universally-quantified statement.  We
record that as a real disproof (`vpDepth_adequate_false`).  The plateau-transport
lemmas, which take the plateau hypothesis as an explicit input, *are* true and are
proved.

No `sorry`, axiom-clean.
-/

namespace AgdaMirror.VpTrue

open AgdaMirror.DASHIValuation

/-- The fuel-free public valuation: evaluate `vpDepth` at fuel `= n`. -/
def vpTrue (p n : Nat) : Nat := vpDepth n p n

/-- `vpTrue` is literally `vpDepth` evaluated at fuel `n`. -/
theorem vpTrue_self (p n : Nat) : vpDepth n p n = vpTrue p n := rfl

/-- Plateau transport: if one extra unit of fuel does not change the value at
`fuel`, then it does not change it at `fuel + extra` either. -/
theorem transport_plateau (fuel p n extra : Nat)
    (plateau : vpDepth fuel p n = vpDepth (fuel + 1) p n) :
    vpDepth (fuel + extra) p n = vpDepth (fuel + extra + 1) p n := by
  induction extra with
  | zero => simpa using plateau
  | succ e ih =>
    have h := vpDepth_stable_step (fuel + e) p n ih
    have he : fuel + (e + 1) = fuel + e + 1 := by ring
    rw [he]
    simpa using h

/-- Plateau iteration: once a plateau is reached at `fuel`, the value is constant
for all larger fuels `fuel + extra`. -/
theorem plateau_iter (fuel p n extra : Nat)
    (plateau : vpDepth fuel p n = vpDepth (fuel + 1) p n) :
    vpDepth fuel p n = vpDepth (fuel + extra) p n := by
  induction extra with
  | zero => simp
  | succ e ih =>
    have h := transport_plateau fuel p n e plateau
    have he : fuel + (e + 1) = fuel + e + 1 := by ring
    rw [he]
    exact ih.trans h

/-- **Honest boundary**: the Agda `vp-depth-adequate` postulate is genuinely false
as a universal statement, because `0` is divisible by every base, so `vpDepth`
keeps consuming fuel on `n = 0`.  Concretely `vpDepth 0 2 0 = 0` but
`vpDepth 1 2 0 = 1`. -/
theorem vpDepth_adequate_false :
    ¬ (∀ p n : Nat, vpDepth n p n = vpDepth (n + 1) p n) := by
  intro h
  have := h 2 0
  simp [vpDepth] at this

end AgdaMirror.VpTrue
