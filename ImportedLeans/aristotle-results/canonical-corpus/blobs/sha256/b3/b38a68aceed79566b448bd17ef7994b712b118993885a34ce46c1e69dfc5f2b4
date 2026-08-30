import Mathlib

/-!
# Lean mirror of `MoonshineEarn.agda` (genuine, fully proved)

Faithful transcription of `MoonshineEarn.agda`: the FRACTRAN-style chain in which
the "perf counter" primes `7, 11, 23` are converted into the moonshine kernel
primes `47, 59, 71` by the fractions `47/23, 59/7, 71/11`.  All claims are
concrete `Nat` arithmetic identities (truncating division, exactly as in Agda),
hence genuine and proved by computation.
-/

namespace AgdaMirror.MoonshineEarn

set_option maxRecDepth 4000

theorem perf_product : 7 * 11 * 23 = 1771 := by decide

theorem moonshine_product : 47 * 59 * 71 = 196883 := by decide

theorem step1 : 1771 / 23 * 47 = 3619 := by decide

theorem step2 : 3619 / 7 * 59 = 30503 := by decide

theorem step3 : 30503 / 11 * 71 = 196883 := by decide

theorem chain : (((7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 = 196883 := by decide

theorem observer : 47 * 59 * 71 + 1 = 196884 := by decide

theorem res47 : 196884 % 47 = 1 := by decide
theorem res59 : 196884 % 59 = 1 := by decide
theorem res71 : 196884 % 71 = 1 := by decide

theorem full_earn :
    (((4 * 27 * 7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 = 4 * 27 * 47 * 59 * 71 := by decide

end AgdaMirror.MoonshineEarn
