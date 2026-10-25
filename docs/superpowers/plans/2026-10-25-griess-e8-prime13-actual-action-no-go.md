# Original Griess M81 → original T5-240 versus E8 Weyl: prime-13 max-cut
Date: 2026-10-25. Canonical owner: Lean #52, companion Agda #1239. Prior-art branches: Lean #43/#47; Agda #1093/#1094/#1098. Status: **local exact Python passed; new Lean/Agda proofs SOURCE-WRITTEN, not kernel verified**.

## 1. Scope and original user prompt

The original thread arose when the raw **coordinate-dependent** triality mismatch 883/8 was noted to be 5/8 below 888/8. The source-specific SO8 60-degree rotation can produce 888/8 without yielding an algebra automorphism; the positive rational related triple instead eliminates the invariant Gram-corrected product mismatch entirely (512 triality and 729 Jordan basis checks). The user separately requested cross-pollination with the genuine Chen–Lam–Shimakura three-sector Moonshine VOA. Such three-sector phases remain distinct from finite Albert, Monster 3B selected mode, and original open P3³.

The user explicitly recalled **240 and 243**. The previous 240=3^5-3 example, original diagonal-punctured T5 carrier and *different* structured E8 roots were already formalised. The original T5 240 had been shown non-invariant under the PAID existing E6 reflection s3; structured E8 roots are a separately recognised `72 + 6 + 6×27` carrier with E6×A2 and Weyl glue action. Do not reopen the arithmetic/cardinality classification.

## 2. Original source, actual old-240 mathematical action

The 1990 Griess **source** polynomial
`g(x,y)=-x0*x1*y2-x2*y0*y1+x1*x2*y0+x0*y1*y2 mod3`
on V=F3³ defines the commutative exponent-three order-81 Moufang loop
`(x,a) * (y,b)=(x+y,a+b+g(x,y))`. It satisfies `δg(x,y,z)=det(x,y,z)`.

The original 5-trit T5 is explicitly and reversibly charted as `M81 × F3` by subtracting the fifth coordinate from the first four. The selected deleted diagonal becomes `{loop identity}×F3`, leaving **240 = (M81\{1})×F3** as an EXACT carrier chart. This is neither an associative group structure nor an E8 Weyl-root identification.

The prior six original Griess source-multiplication-preserving shears, including corrections `h_s` solving `δh_s = g(Mx,My)-g(x,y)`, generate a subgroup of the 81-point permutation group of local-computed order **151632 = 2^4*3^6*13**; the image on grade coordinates is SL3(3) of order 5616, with kernel 27 character shifts. Previous exact local regression also gives source M81 orbits `3×1 + 78`; old240 orbits `6×1 + 3×78`.

## 3. NEW maximally cheap explicit adversarial witness

**A single short word** avoids relying on the large generated-group order:

1. source-corrected shear e01, then
2. source-corrected shear e12, then
3. source-corrected shear e20.

Grade matrix over F3 is `[[1,1,0],[0,1,1],[1,1,1]]`. The actual Moufang central-coordinate correction is essential: the first application to `((1,0,0),0)` is **`((1,0,1),2)`**, not `((1,0,1),0)`. Local Python checked each of the three 27×27 cochain conditions and a negative control where the naive uncorrected map fails by 2.

The resulting exact permutation is **order 13**, with cycle shapes:
- literal Griess M81: `3×(1)+6×(13)=81`;
- literal original diagonal-removed five-trit 240: `6×(1)+18×(13)=240`.

These were tested exhaustively by a standalone Python script requiring no GAP, no Sage and no repository helper imports. The full-group order is independent corroboration, not needed for the contradiction.

## 4. The Weyl E8 action NO-GO and strict boundary

The automorphism group of a FIXED E8 root system is its Weyl group with order

```
|W(E8)| = 696729600 = 2^14 * 3^5 * 5^2 * 7
696729600 mod 13 = 8
```

By Lagrange, **no element of W(E8) has order divisible by 13** and hence no permutation of the actual E8 roots arising from that Weyl group has a 13-cycle. A bijective equivariant intertwiner `f : Old240 ≃ StructuredE8Root240` for the source's explicit 13-cycle would require such a Weyl element; **impossible**.

This is stronger than the previous s3 escape obstruction. It excludes the **specific original source-action-preserving E8 root recognition**. It does NOT preclude an arbitrary set bijection of two 240-element sets, a different action, or continuous E8 algebraic-group automorphisms without preservation of the chosen root datum. It says nothing about a literal selected Monster 3B/VOA actor or physical space.

## 5. Implementations, independent tests and provenance

- **Lean #52** `Integration/Griess1990Original240E8WeylPrime13Obstruction.lean` imports the original old240 action and the PRE-EXISTING structured E8 Weyl owner, and gives exact numerical `13 ∤ 696729600`, `78 ∤ 696729600`, `151632 ∤ 696729600` proofs and a generic no-injective-group-hom implication from Mathlib `Subgroup.card_dvd_of_injective`. All new Lean source statements UNCOMPILED.
- **Lean #52** `Integration/Griess1990Moufang81Explicit13Cycle.lean` constructs the ACTUAL three source-corrected shears and exact finite proof targets: the loop order13, first-phase image, chosen witness of exact period13, actual original-240 source transport, six fixed points/234 nonfixed. UNCOMPILED.
- **Agda #1239** `DASHI/Moonshine/Griess1990Moufang81ExplicitThirteenCycleExact.agda` imports original Agda M81 and original Kernel5 chart, computes three corrected lifts, SOURCE-WRITES 81 constructor `refl` cases for `order13All`, and computes the classic Weyl residue `696729600 = 13*53594584+8`. Neither full kernel compilation nor action-root equality claimed.
- Both canonical existing source regressions `scripts/check_griess_m81_t5_243240_actual_cocycle_action.py` expanded in place on Lean #52 and Agda #1239 with the exact three-shear cycle profile and Weyl order discriminator. Their GitHub blobs were NOT byte-for-byte rerun in this environment.
- Independently locally executed standalone script `/mnt/data/check_griess1990_explicit_13_cycle_no_weyl_e8.py`: **PASS all 81 and 240 cycles**, phase-correction checks, negative-control invalid naive shear. Local source SHA and gate receipt `/mnt/data/griess1990_explicit13_E8_weyl_no_go_receipt.json`. Exact finite Python != Lean/Agda kernel proof.

**Original authorship (do not collapse):**
- **R. L. Griess Jr.** (1990), *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131:281–293, DOI `10.1016/0021-8693(90)90176-O`: original 81-loop/Albert source.
- **Élie Cartan**, Coxeter/Weyl/classical Lie/root-system literature, Bourbaki, and **Rosa Winter & Ronald van Luijk** (2021), *The Action of the Weyl Group on the E8 Root System*, Graphs and Combinatorics 37:1965–2064, DOI `10.1007/s00373-021-02315-8`: original/general root-system structure and explicit modern references, not a DASHI discovery.
- **Alsaody--Gille (2019)** and **Barry--Tignol (2023)**: separate rational octonion isotope/triality donor roots.
- **Chen--Lam--Shimakura (2018)**: independent true Monster V#≅Vnatural Z3 orbifold source; no 27D source-to-VOA same-object witness.
- **Ibrahim/A027907 sequence author/contributor source roles**: the original 1,3,6,7,6,3,1 open P3³ row and numerical 13,52,78. An E8 root-group no-go does NOT inherit mathematical authority from OEIS coincidences.

## 6. Pareto frontier after this mathematical obstruction

P0: **CLOSE NEGATIVE** original-240 as equivariant fixed-Weyl-E8 roots under source Griess M81 shear action; do not try endless arbitrary 240×240 charts. Acceptance: exact 13-cycle/no-Weyl order. Local Python PASSED; Lean/Agda kernel compilation still OPEN.

P0: **POSITIVE OPEN** Lean original Griess Q(omega) homogeneous tensor→native rational Albert, all 729 products, and Agda actual same-object transport: retain genuine source-g formula/trace/product/action proofs and compile with kernels.

P1: Compile cheap standalone Lean algebra proof `δg=det`, 13-line PG(2,3), source automorphism and explicit 13-cycle finite proof targets. A successfully typechecked abstract no-go should consume proved group orders or a proved 13-cycle, not trust a printed source-written Bool.

P2: Construct an ACTUAL selected Chen--Lam--Shimakura Moonshine VOA mode/3B sector intertwiner only from a legitimate same-VOA source, not from matching `omega`, 13, 27, 78, 81, 240, 243 or 888 numerals.

P3: Physical original path-cube/P3³, KK/AdS3/string and RH hypotheses retain separate external observational/analytic and same-operator gates.

**Attribution invariant:** original source root, local computation, source-written code, kernel proof, external action and scientific evidence must remain separate. Do not promote an analogy or numeric equality into a proof.
