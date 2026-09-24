import RequestProject.QExpansionLadder

/-!
# TwistedResolution — perturbed *semantic duplicates* are resolved by higher-resolution
sampling of the twisted McKay–Thompson series, whose q-expansion introduces new primes
grade by grade, each refining the representation.

This module answers the request:

> perturb the semantics to produce duplicate ideas that have *different* semantic
> ideas, and show they are resolved by higher-resolution sampling of the
> McKay–Thompson **twisted** series; show that new primes are introduced by that
> q-expansion in grades and each creates a more refined representation.

Where `SemanticPerturbation` produced `2^n` forms that *keep* the same semantics,
here a perturbation is allowed to *change* the idea: it produces a **duplicate**
`h' = h + δ` that is a genuinely different idea (`δ ≠ 0`) yet **collides** with the
original at *low resolution* (the coarse address cannot tell them apart).  The
twin questions are then settled:

* **Resolution.**  Sampling the twisted McKay–Thompson series to higher *grade*
  (using its coefficients `c(1), c(2), …` as successive address coordinates)
  *resolves* the duplicate: once a sampled grade's coefficient exceeds the values,
  the two ideas land in different cells (`resolve_separates`,
  `dup_resolved_at_grade2`).
* **New primes per grade.**  The q-expansion of a twisted series introduces *new
  primes* as the grade increases (`t2A_cumPrimeCount`, `t2A_newPrimesAt5`,
  `cumPrimeCount_monotone_2A`), and each new prime strictly **refines** the
  representation — it splits a pair that the coarser modulus had merged
  (`newprime_refines`) while never merging anything already separated
  (`refine_coarsen`, via the project's Chinese-Remainder `coarsen`).

## §1  The twisted McKay–Thompson series (honest eta-quotient computation)

We compute two genuine twisted series of the Monster as eta-quotients, reusing the
truncated power-series machinery of `Moonshine`:

* **2B** — the Hauptmodul of `Γ₀(2)`:  `(η(τ)/η(2τ))^24` has q-expansion
  `q⁻¹ - 24 + 276 q - 2048 q² + 11202 q³ - …`, so its nontrivial coefficients are
  `t2Bcoeff n = 276, -2048, 11202, …` (`t2B_c1 … t2B_c4`).
* **2A** — the Hauptmodul of `Γ₀(2)+`:
  `(η(τ)/η(2τ))^24 + 4096 (η(2τ)/η(τ))^24` gives
  `q⁻¹ + 4372 q + 96256 q² + 1240002 q³ + …` (`t2A_c1 … t2A_c4`), the McKay–Thompson
  series whose coefficients are head characters of the Baby Monster `2.B`.

Both reproduce the classical coefficients exactly (proved against the eta-quotient
computation), and are tabulated as `t2ATable`/`t2BTable` (`t2ATable_correct`,
`t2BTable_correct`) for fast downstream analysis.

## §2  Perturbed duplicates and their resolution
## §3  New primes per grade and refinement
## §4  Reflection front-end `#twiststratify`

The honest scope is the project's usual one: an "idea" is a structural
fingerprint (a hash), a "duplicate" is a collision of fingerprints at a chosen
resolution, and "resolving"/"refining" means a finer set of coordinates
distinguishes them.  The number theory (the coefficients, their growth, and the
appearance of new primes) is genuine and machine-checked.
-/

open Lean Meta Elab Command

namespace TwistedResolution

open Moonshine ResolutionLadder QExpansionLadder

/-! ## §1  The twisted McKay–Thompson series as eta-quotients -/

/-- `∏_{n≥1} (1 - q^{2n})^{24}` — the discriminant in the variable `q²`, truncated. -/
def etaProd2 : Array Int := Id.run do
  let mut r := psOne
  for n in [1:N] do
    if 2 * n < N then
      let mut f : Array Int := zeros
      f := f.set! 0 1
      f := f.set! (2 * n) (-1)
      for _ in [0:24] do
        r := psMul r f
  return r

/-- `F = ∏(1-q^n)^{24} / ∏(1-q^{2n})^{24}`, so `(η(τ)/η(2τ))^{24} = q⁻¹ · F`. -/
def twistF : Array Int := psMul etaProd (psInv etaProd2)

/-- `G = ∏(1-q^{2n})^{24} / ∏(1-q^n)^{24}`, so `(η(2τ)/η(τ))^{24} = q · G`. -/
def twistG : Array Int := psMul etaProd2 (psInv etaProd)

/-- The `n`-th nontrivial coefficient (coeff of `qⁿ`, `n ≥ 1`) of the **2B**
McKay–Thompson series, the Hauptmodul of `Γ₀(2)`: `c(n) = [qⁿ] (η(τ)/η(2τ))^{24}`. -/
def t2Bcoeff (n : Nat) : Int := twistF[n + 1]!

/-- The `n`-th nontrivial coefficient of the **2A** McKay–Thompson series, the
Hauptmodul of `Γ₀(2)+`: `c(n) = [qⁿ] ((η(τ)/η(2τ))^{24} + 4096 (η(2τ)/η(τ))^{24})`. -/
def t2Acoeff (n : Nat) : Int := twistF[n + 1]! + 4096 * twistG[n - 1]!

/-- The 2A series reproduces the classical head coefficients (Baby-Monster
characters): `c(1) = 4372`. -/
theorem t2A_c1 : t2Acoeff 1 = 4372 := by native_decide
theorem t2A_c2 : t2Acoeff 2 = 96256 := by native_decide
theorem t2A_c3 : t2Acoeff 3 = 1240002 := by native_decide
theorem t2A_c4 : t2Acoeff 4 = 10698752 := by native_decide

/-- The 2B series reproduces the classical `Γ₀(2)`-Hauptmodul coefficients:
`c(1) = 276, c(2) = -2048, …`. -/
theorem t2B_c1 : t2Bcoeff 1 = 276 := by native_decide
theorem t2B_c2 : t2Bcoeff 2 = -2048 := by native_decide
theorem t2B_c3 : t2Bcoeff 3 = 11202 := by native_decide
theorem t2B_c4 : t2Bcoeff 4 = -49152 := by native_decide

/-- The first 32 nontrivial coefficients of the 2A series (precomputed). -/
def t2ATable : Array Int := #[
  4372, 96256, 1240002, 10698752, 74428120, 431529984, 2206741887, 10117578752,
  42616961892, 166564106240, 611800208702, 2125795885056, 7040425608760,
  22327393665024, 68134255043715, 200740384538624, 572950514538856,
  1588198806411264, 4286153037862594, 11283613372743680, 29030493318777216,
  73105649849655296, 180454128099240060, 437155796944945152, 1040545340935546700,
  2436001535686266880, 5614282459787463036, 12748902531008430080,
  28546382905646406648, 63071424165763399680, 137594477449401738757,
  296560785840530259968]

/-- The first 32 nontrivial coefficients of the 2B series (precomputed). -/
def t2BTable : Array Int := #[
  276, -2048, 11202, -49152, 184024, -614400, 1881471, -5373952, 14478180,
  -37122048, 91231550, -216072192, 495248952, -1102430208, 2390434947,
  -5061476352, 10487167336, -21301241856, 42481784514, -83300614144, 160791890304,
  -305854488576, 573872089212, -1063005978624, 1945403602764, -3519965179904,
  6300794030460, -11164248047616, 19591528119288, -34065932304384, 58718797964805,
  -100372723007488]

/-- **The 2A table is correct.**  Its entries are exactly the eta-quotient
coefficients `t2Acoeff 1 … t2Acoeff 32`. -/
theorem t2ATable_correct :
    (Array.range 32).map (fun i => t2Acoeff (i + 1)) = t2ATable := by native_decide

/-- **The 2B table is correct.**  Its entries are exactly the eta-quotient
coefficients `t2Bcoeff 1 … t2Bcoeff 32`. -/
theorem t2BTable_correct :
    (Array.range 32).map (fun i => t2Bcoeff (i + 1)) = t2BTable := by native_decide

/-! ## §2  Perturbed duplicates and their resolution by higher-grade sampling -/

/-- The modulus contributed by sampling grade `k+1` of a twisted series: the
absolute value of the `(k+1)`-st coefficient (table index `k`). -/
def modAt (tab : Array Int) (k : Nat) : Nat := (tab[k]!).natAbs

/-- The depth-`N` **twisted address** of an idea (fingerprint) `h`: its residues
against the first `N` grades of the twisted series. -/
def addr (tab : Array Int) (h N : Nat) : List Nat :=
  (List.range N).map (fun k => h % modAt tab k)

/-- A **semantic perturbation**: nudge the idea `h` by `δ`, producing a duplicate
`h + δ`. -/
def perturb (h δ : Nat) : Nat := h + δ

/-- A nonzero perturbation produces a genuinely *different* idea. -/
theorem perturb_distinct (h : Nat) {δ : Nat} (hδ : 0 < δ) : perturb h δ ≠ h := by
  simp [perturb]; omega

/-- **Two addresses agree iff they agree grade by grade.** -/
theorem addr_eq_iff (tab : Array Int) (a b N : Nat) :
    addr tab a N = addr tab b N ↔ ∀ k, k < N → a % modAt tab k = b % modAt tab k := by
  unfold addr
  rw [List.map_inj_left]
  simp only [List.mem_range]

/-- **Low-resolution collision.**  Perturbing by exactly the grade-1 modulus makes
the duplicate share the original's grade-1 coordinate: at depth 1 the two ideas
are indistinguishable. -/
theorem perturb_collides_grade1 (tab : Array Int) (h : Nat) :
    addr tab (perturb h (modAt tab 0)) 1 = addr tab h 1 := by
  simp [addr, perturb, List.range_one, Nat.add_mod_right]

/-- **Higher-resolution sampling resolves the duplicate.**  If two distinct ideas
both lie below `B`, and some sampled grade `k < N` has modulus `≥ B`, then their
depth-`N` twisted addresses differ — the finer sampling pulls them into different
cells. -/
theorem resolve_separates (tab : Array Int) {a b N k B : Nat}
    (hk : k < N) (hne : a ≠ b) (ha : a < B) (hb : b < B) (hB : B ≤ modAt tab k) :
    addr tab a N ≠ addr tab b N := by
  intro hEq
  rw [addr_eq_iff] at hEq
  exact qcoeff_separates hne ha hb hB (hEq k hk)

/-- **Concrete duplicate.**  The ideas `5` and its perturbation `5 + 4372` (by the
grade-1 modulus of the 2A series) are distinct yet collide at depth 1. -/
theorem dup_collides_grade1 :
    addr t2ATable (perturb 5 (modAt t2ATable 0)) 1 = addr t2ATable 5 1 := by
  native_decide

theorem dup_is_distinct : perturb 5 (modAt t2ATable 0) ≠ 5 := by native_decide

/-- **…and it is resolved at grade 2.**  Sampling one more grade of the 2A series
separates the duplicate from the original: their depth-2 addresses differ. -/
theorem dup_resolved_at_grade2 :
    addr t2ATable (perturb 5 (modAt t2ATable 0)) 2 ≠ addr t2ATable 5 2 := by
  native_decide

/-! ## §3  New primes introduced grade by grade, each refining the representation -/

/-- The probe primes (all primes `≤ 300`) we watch for in the q-coefficients. -/
def probePrimes : List Nat :=
  (List.range 301).filter
    (fun p => 2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0))

theorem probePrimes_card : probePrimes.length = 62 := by native_decide

/-- The cumulative set of probe primes occurring in grades `1 … N` of a series. -/
def cumPrimes (tab : Array Int) (N : Nat) : List Nat := Id.run do
  let mut seen : List Nat := []
  for n in [1:N + 1] do
    for p in probePrimes do
      if (tab[n - 1]!).natAbs % p == 0 && !seen.contains p then
        seen := seen ++ [p]
  return seen

/-- The probe primes appearing **for the first time** at grade `n`. -/
def newPrimesAt (tab : Array Int) (n : Nat) : List Nat :=
  let prev := cumPrimes tab (n - 1)
  probePrimes.filter (fun p => (tab[n - 1]!).natAbs % p == 0 && !prev.contains p)

/-- How many distinct primes the q-expansion has introduced through grade `N`. -/
def cumPrimeCount (tab : Array Int) (N : Nat) : Nat := (cumPrimes tab N).length

/-- The cumulative **refinement radical**: the product of all primes introduced
through grade `N`.  Each new prime multiplies it, giving a strictly finer CRT
address. -/
def cumRadical (tab : Array Int) (N : Nat) : Nat := (cumPrimes tab N).foldl (· * ·) 1

/-- **New primes appear with the grades.**  The 2A series introduces, cumulatively,
`1,2,3,3,6,6,7,7,8,8,10,11,11,…,15` distinct probe primes through grades
`1 … 24` — a strictly growing supply of resolving coordinates. -/
theorem t2A_cumPrimeCount :
    (List.range 24).map (fun i => cumPrimeCount t2ATable (i + 1))
      = [1,2,3,3,6,6,7,7,8,8,10,11,11,11,11,11,12,13,14,14,14,15,15,15] := by
  native_decide

/-- Grade 5 of the 2A series introduces three brand-new primes at once,
`{5, 13, 41}` — three new coordinates appearing in a single grade. -/
theorem t2A_newPrimesAt5 : newPrimesAt t2ATable 5 = [5, 13, 41] := by native_decide

/-- The primes introduced through grade 24 of the 2A series. -/
theorem t2A_cumPrimes24 :
    cumPrimes t2ATable 24 = [2, 47, 3, 5, 13, 41, 7, 59, 23, 281, 17, 191, 103, 31, 37] := by
  native_decide

/-- The 2B series likewise introduces new primes with the grades (cumulative
counts through grades `1 … 24`). -/
theorem t2B_cumPrimeCount :
    (List.range 24).map (fun i => cumPrimeCount t2BTable (i + 1))
      = [3,3,3,3,3,4,4,5,5,7,9,11,12,12,12,12,13,13,15,15,15,15,16,16] := by
  native_decide

/-- **The prime supply never shrinks.**  Across the measured grades, the cumulative
prime count for the 2A series is monotone nondecreasing (each grade can only add
primes, never remove them). -/
theorem cumPrimeCount_monotone_2A :
    (List.range 23).all
      (fun i => decide (cumPrimeCount t2ATable (i + 1) ≤ cumPrimeCount t2ATable (i + 2)))
      = true := by native_decide

/-- **Each new prime strictly enlarges the refinement radical.**  Grade 5 (which
introduces `{5,13,41}`) multiplies the 2A radical strictly. -/
theorem cumRadical_grows_at5 : cumRadical t2ATable 4 < cumRadical t2ATable 5 := by
  native_decide

/-- **Adding a new prime creates a more refined representation.**  Modulo `M`, the
two ideas `0` and `M` are merged (same cell); adjoining a *new* prime `p`
(passing to modulus `M·p`) splits them into different cells.  So every new prime
the q-expansion supplies genuinely refines the address. -/
theorem newprime_refines {M p : Nat} (hM : 0 < M) (hp : 1 < p) :
    (0 : Nat) % M = M % M ∧ (0 : Nat) % (M * p) ≠ M % (M * p) := by
  refine ⟨by simp, ?_⟩
  have hlt : M < M * p := by nlinarith
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hlt]
  omega

/-- **Refinement only ever splits, never merges.**  A finer modulus `M·p` is a
refinement of `M`: anything it identifies was already identified by `M`.  (This is
the project's Chinese-Remainder `coarsen` specialised to a new prime factor.) -/
theorem refine_coarsen {M p a b : Nat} (h : a % (M * p) = b % (M * p)) :
    a % M = b % M :=
  ResolutionLadder.coarsen ⟨p, rfl⟩ h

/-! ## §4  Reflection front-end -/

/-- The structural fingerprint of a declaration's *statement* (its type hash) —
the same "idea" coordinate the resolution ladder uses. -/
def declFingerprint (info : ConstantInfo) : Nat := info.type.hash.toNat

/-- The first sampled grade (`< 32`) at which the original `h` and its duplicate
`h'` differ under the 2A twisted address, or `32` if none in range. -/
def firstResolvedGrade (h h' : Nat) : Nat := Id.run do
  let mut g := 32
  for k in [0:32] do
    if h % modAt t2ATable k != h' % modAt t2ATable k then
      g := k + 1
      break
  return g

/-- Build the dual-resolution report for a declaration. -/
def stratReport (decl : Name) (h : Nat) : String :=
  let m0 := modAt t2ATable 0
  let h' := perturb h m0
  let collideG1 := h % modAt t2ATable 0 == h' % modAt t2ATable 0
  let resolved := firstResolvedGrade h h'
  let primes24 := cumPrimes t2ATable 24
  let rad := cumRadical t2ATable 24
  s!"[Aristo Twisted Resolution] Stratifying: {decl}\n" ++
  s!"  ├── fingerprint (idea)      : h  = {h}\n" ++
  s!"  ├── perturbed duplicate     : h' = h + c(1) = {h'}  (distinct idea: {decide (h ≠ h')})\n" ++
  s!"  ├── collide at grade 1      : {collideG1}  (coarse 2A-address cannot separate them)\n" ++
  s!"  ├── resolved at grade       : {resolved}  (first 2A grade whose sampling separates h, h')\n" ++
  s!"  ├── primes introduced ≤ g24 : {primes24}\n" ++
  s!"  └── refinement radical g24  : {rad}  ({primes24.length} CRT coordinates)"

/-- `#twiststratify f` perturbs `f`'s statement fingerprint into a semantic
duplicate, shows it collides with the original at low resolution, and reports the
grade at which higher-resolution sampling of the 2A twisted McKay–Thompson series
resolves it — together with the new primes the q-expansion introduces grade by
grade. -/
syntax (name := twistCmd) "#twiststratify " ident : command

@[command_elab twistCmd]
def elabTwist : CommandElab := fun stx => do
  match stx with
  | `(#twiststratify $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | none => throwError "unknown declaration {name}"
    | some info =>
      logInfo (stratReport name (declFingerprint info))
  | _ => throwError "ill-formed #twiststratify command"

/-! ## §5  Test suite -/

#twiststratify Nat.add
#twiststratify List.map
#twiststratify Prod.fst

end TwistedResolution
