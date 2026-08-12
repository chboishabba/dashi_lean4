import Mathlib
import AgdaMirror.DASHIValuation

/-!
# Lean mirror of `DASHI/Arithmetic/DeltaGrowth.agda` (genuine number theory)

Faithful transcription of the constructive divisibility frontier of the DASHI
arithmetic growth analysis.  The honest, fully constructive core of that module
is the statement that the bounded `p`-adic valuation genuinely witnesses a power
divisor:

> `p ^ (vpDepth fuel p n) ∣ n`     (`vpDepth_power_divides`)

together with the monotone power-divisibility lemma `pow_mono_divides`.  (The
Agda module's `logNat`/`deltaGrowthBound` are *postulates*, i.e. assumptions, so
following the honesty discipline they are **not** transcribed as axioms — only
the genuinely provable divisibility core is mirrored here.)

All proofs are by structural induction on the fuel; no `sorry`, axiom-clean.
-/

namespace AgdaMirror.DeltaGrowth

open AgdaMirror.DASHIValuation (vpDepth)

/-- Monotone power divisibility (mirrors `pow-mono-divides`). -/
theorem pow_mono_divides (p m n : Nat) (h : m ≤ n) : p ^ m ∣ p ^ n :=
  pow_dvd_pow p h

/-- The bounded `p`-adic valuation genuinely witnesses a power divisor of `n`
(mirrors `vp-depth-power-divides`). -/
theorem vpDepth_power_divides (fuel p n : Nat) :
    p ^ (vpDepth fuel p n) ∣ n := by
  induction fuel generalizing p n with
  | zero => simp [vpDepth]
  | succ f ih =>
    match p with
    | 0 => simp [vpDepth]
    | 1 => simp [vpDepth]
    | q + 2 =>
      simp only [vpDepth]
      by_cases hd : (q + 2) ∣ n
      · simp only [hd, if_true]
        have ihq : (q + 2) ^ (vpDepth f (q + 2) (n / (q + 2))) ∣ n / (q + 2) :=
          ih (q + 2) (n / (q + 2))
        have hmul :
            (q + 2) * (q + 2) ^ (vpDepth f (q + 2) (n / (q + 2)))
              ∣ (q + 2) * (n / (q + 2)) :=
          mul_dvd_mul_left (q + 2) ihq
        rw [Nat.mul_div_cancel' hd] at hmul
        simpa [pow_succ'] using hmul
      · simp [hd]

end AgdaMirror.DeltaGrowth
