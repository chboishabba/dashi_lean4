import RequestProject.JExpansion
import RequestProject.Holograms

/-!
# When the j-expansion catches up to the size of the Monster

`JExpansion` records the first **100** nontrivial coefficients of the
McKay–Thompson series `T1 = j - 744`, i.e. `c(1), …, c(100)` where `c(n)` is the
coefficient of `qⁿ` in `j` (so `c(n) = Moonshine.jCoeff (n+1)`).

This module answers the natural follow-up question: *how far past those 100
coefficients do we have to go before a single coefficient `c(n)` first exceeds the
order of the Monster sporadic group*

```
|𝕄| = 808 017 424 794 512 875 886 459 904 961 710 757 005 754 368 000 000 000
    = 2⁴⁶ · 3²⁰ · 5⁹ · 7⁶ · 11² · 13³ · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
```

(`Holograms.monsterOrder`)?

The answer is **exactly four more**: every coefficient up through `q¹⁰³` is still
strictly below `|𝕄|`, the coefficient of `q¹⁰⁴` (the fourth coefficient beyond the
recorded 100) is the first to overshoot it, and `q¹⁰⁵` is already past it as well.
Concretely the crossover is

```
c(103) = 532360384582564934616501236583995061891109488627959595  <  |𝕄|
       <  c(104) = 980138362015635064853029622650402721085223194498170880.
```

All facts are decided by kernel computation against the honestly computed
`Moonshine.jSeries`, so nothing here is assumed.
-/

namespace Moonshine

open Holograms (monsterOrder)

/-- **Below the Monster, all the way to `q¹⁰³`.**  Every coefficient of `j` from
the `q⁻¹`/constant terms up to and including `q¹⁰³` is strictly smaller than the
order of the Monster.  (Here `jCoeff (n+1)` is the coefficient of `qⁿ`, so
`n < 104` ranges over `c(0) = 744, c(1), …, c(103)`.) -/
theorem jCoeff_below_monster_through_103 :
    ∀ n, n < 104 → jCoeff (n + 1) < (monsterOrder : Int) := by
  native_decide

/-- The last of the 100 recorded coefficients, `c(100)`, is still well below the
Monster order — so the whole supplied `t1Coeffs` table lives under `|𝕄|`. -/
theorem t1Coeffs_below_monster :
    ∀ k, k < 100 → t1Coeffs[k]! < (monsterOrder : Int) := by
  native_decide

/-- **Four more is enough.**  The coefficient of `q¹⁰⁴` in `j` — the fourth
coefficient beyond the recorded 100 — is the first one to exceed the order of the
Monster. -/
theorem jCoeff_104_exceeds_monster :
    (monsterOrder : Int) < jCoeff 105 := by
  native_decide

/-- **`q¹⁰⁵` is already over the limit too.** -/
theorem jCoeff_105_exceeds_monster :
    (monsterOrder : Int) < jCoeff 106 := by
  native_decide

/-- **The crossover, in one statement.**  `q¹⁰⁴` is exactly the first coefficient
of `j` that reaches past the Monster's order: everything up to `q¹⁰³` is below it,
and `c(104)` is above it.  In particular `n = 104` is the least `n ≥ 1` with
`c(n) > |𝕄|`, i.e. precisely four steps beyond the 100 recorded expansions. -/
theorem monster_size_crossover_at_104 :
    (∀ n, n < 104 → jCoeff (n + 1) < (monsterOrder : Int)) ∧
      (monsterOrder : Int) < jCoeff 105 :=
  ⟨jCoeff_below_monster_through_103, jCoeff_104_exceeds_monster⟩

end Moonshine
