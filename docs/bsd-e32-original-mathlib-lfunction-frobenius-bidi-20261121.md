# BSD E32 original Mathlib LFunction ↔ point count: source-exact BIDI

21 November 2026. Original E32 y²=x³-x. This is an extension of the actual original mathematical owners on Lean main, not a new L-series. The original cmWeierstrass.LFunction, cmAllNCoefficient, cmLSeries, frobeniusCoefficient, and analytic Dedekind eta expression are ALREADY IMPLEMENTED. Do not duplicate them. Source attribution: original Mathlib localPolynomial and its author, source Frobenius owner, original E32 BSD and classical level32 eta theory.

## Exact Mathlib consumer and reverse input
Mathlib WeierstrassCurve.localPolynomial uses W.minimal R, q=Nat.card ResidueField(R), and a=q+1-Nat.card ((W.minimal R).reduction R).toAffine.Point. At good reduction its original P(T)=1-aT+qT². At additive reduction its polynomial is 1, but merely seeing discriminant divisible by p does NOT establish the additive branch. The new source-written Lean owner Synthesis/MillenniumBSDCMActualLocalEulerPointCountBidiExact.lean proves, conditional on the ORIGINAL hGood/hResidue/hReducedCount premises, that this literal Mathlib local polynomial equals the original counted polynomial with a_p=frobeniusCoefficient p. It also exposes the exact three reduction-negation inputs for the additive case and reuses the original inert-character-sum theorem for the counted polynomial. No new prime-indexed arbitrary formal L-function has been substituted. Do not conflate a natural rational prime p with the prime ideal place; this mapping is a distinct source-specific construction.

## Local exact finite acceptance
scripts/check_bsd_e32_actual_lfunction_euler_weld.py: 163 assertions PASS using SymPy 1.14.0 (30 odd primes ≤128; exact 128 original q-coefficients vs independent Euler recurrence; original a5 sign and bad p2 negative controls). This checks the integer consequence of the conditional mathematical correspondence, NOT native Mathlib reduction geometry or actual cmFormalLFunction coefficients. The conductor32 p2 additive local factor is classical data, not established by this finite script.

## Closest actual original remaining proof
1. Construct/identify rational prime p's HeightOneSpectrum (𝓞 ℚ) place, prove residue cardinality p and genuine good reduction of original cmWeierstrass for p≠2.
2. Identify the minimal reduced point group cardinality with the already-proved original ZMod-p projective count. Do not postulate a coefficient identity.
3. Prove selected p2 minimal additive reduction and polynomial 1 in Mathlib.
4. Reuse Mathlib arithmetic Euler product to identify all cmFormalLFunction coefficients, then classical level32 modularity/eta via Sturm 8, same-object Mellin/continuation, original BSD arithmetic gates. The existence of the formal complex cmLSeries does not imply convergence at s=1.
5. Run pinned Lean kernel and axiom audit in a compatible local toolchain. Existing Lean #107 is closed; no CI run and no kernel receipt. This is a DRAFT.
