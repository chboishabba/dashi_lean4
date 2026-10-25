# Griess original Moufang81 / old T5 243–240 / intrinsic E6 and structured E8
Date: 2026-10-25. Same-workflow owner: [dashi_lean4 PR #52](https://github.com/chboishabba/dashi_lean4/pull/52), [dashi_agda PR #1239](https://github.com/chboishabba/dashi_agda/pull/1239).

## User's actual research trigger and prior art

The original prompt asked WHY the *selected nonorthonormal* 512-component Albert/Spin8 triality residual was 883/8, only 5/8 shy of 888/8, WHAT would make 888 structurally forced, and WHAT original algebra governs it. The 60-degree raw-coordinate rotation produces 888/8 without retaining both raw norms; the full rational related-triple isomorphism instead eliminates the invariant product discrepancy (zero) by an explicit original-Griess to native rational Albert map. The actual source algebra and the distinct Chen--Lam--Shimakura V#=Vnatural three-sector VOA remain separate mathematical objects.

The user ALSO reminded us that the repository already owns **240 and 243**. The relevant existing PR genealogy MUST be consumed before adding generic new finite-carrier proxies:

| Prior owner | Existing authoritative declaration/result | Import and claim status |
| --- | --- | --- |
| [Lean #43](https://github.com/chboishabba/dashi_lean4/pull/43) `Integration.T5E8RelativeComplementCandidate`; [Agda #1094](https://github.com/chboishabba/dashi_agda/pull/1094) `T5E8RelativeComplementCandidateExact` | Original 5-trit `Kernel5` has 243 states and the actual constant-diagonal locus has 3; its relative complement has 240 | Original DASHI point carrier, not E8 |
| [Lean #47](https://github.com/chboishabba/dashi_lean4/pull/47) `Integration.E6F3ExteriorSquare`, `E6Mod3QuadraticBridge` | E6 mod-3 standard 5D quadratic chart 243=1+80+90+72; literal 72 E6-root/Q2 recognition and 51,840 W(E6) image | Genuine E6 *specific* root action, not the old punctured 240 |
| Lean #47 `T5RelativeE6ActionRestrictionObstruction` | E6 simple reflection `s3` sends `(2,2,1,1,1)` back to the deleted diagonal `(1,1,1,1,1)`, ruling out inherited full E6 action on that 240 | Original 240 not stable, hard no-go for this specific inherited action |
| Lean #47 `E8StructuredTernary240E6A2Action`, `E8StructuredFullWeylRecognition`, `E8StructuredExceptionalLiftFinalMaxCut`; Agda #1098 related receipts | An independently STRUCTURED E8 root carrier `72+6+6×27=240`, full intrinsic rank-eight Cartan/Coxeter + cross-branch glue source-written; independent permutation-group order 696,729,600 computed | More complete than earlier E6×A2 phase; still distinct from original 240; kernel execution not observed here |
| [Agda #1093](https://github.com/chboishabba/dashi_agda/pull/1093) | Earlier E8 order-three quotient and centralizer; original-phase algebra relations | Reuse source work without identifying the Monster or the new original-T5 chart |
| [Lean #52](https://github.com/chboishabba/dashi_lean4/pull/52); [Agda #1239](https://github.com/chboishabba/dashi_agda/pull/1239) | Original Griess 1990 (g), order-81 commutative exponent-three Moufang loop, determinant-valued associator; real PG(2,3) 13,52,78 and actual Albert product/actor | Griess original author; local source-equivalent and new same-workflow formalization separate |

**Other unrelated 240 referents:** YM/T4's 240 interval boxes (Agda #554), pressure/Casimir 720→240 normalization and QCD ~-240 residual from the TOE work have DIFFERENT types, inputs, units and operators; they are not this root/loop 240. Avoid numerical conflations.

## NEW A: actual two-sided 243 ↔ M81 × F3 carrier chart, not a count fit

In the ACTUAL original standard five-trit carrier, define
`Phi(z0,z1,z2,z3,z4)=(((z0-z4,z1-z4,z2-z4),a=z3-z4),t=z4)`.
The inverse is `(x,a,t)↦(x0+t,x1+t,x2+t,a+t,t)`. No unspecified bijection is used; both are defined and verified over all 243 states. Under this selected F3-linear chart, the original constant diagonal `(t,t,t,t,t)` is *precisely* `{identity of the Griess M81 loop} × F3`. Consequently, as sets,
`OriginalT5\Diagonal ≅ (M81\{identity})×F3`; **240=3×80**.

The four-coordinate M81 carrier is `grade∈F3³` plus `central∈F3`. Removing its identity leaves **2** other grade-zero elements and **78=26×3** nonzero-grade elements. After the untouched fifth trit, old 240 splits **6 fixed-grade-zero + 234 nonzero-grade** states. This is a genuine exact *underlying-set* and literal-action chart, not an isomorphism of the old componentwise-addition group with the nonassociative Moufang loop.

This bridge uses original `F3Five`/actual `E6` standard quadratic source on Lean #52; `Integration.Griess1990OriginalT5Moufang243240Chart`. The #47 obstruction file itself was not present on #52's branch, so the new module uses the ACTUAL #52 `E6Mod3WeylAction.reflectStandard` and reconstructs its literal `s3` return witness, not a dangling import. The Agda bridge `DASHI.Moonshine.Griess1990OriginalKernel5M81243240ChartExact` uses the original `Local.Kernel5` and original Griess-M81 source owner, defines both concrete maps and an honest uninhabited dependent two-sided receipt. The #1094 sibling relative-carrier file is not on Agda #1239's branch; do NOT fabricate imported module or claim Agda kernel payment.

## NEW B: exact E6 quadratic interaction/no-go survives chart transport

Under the OLD standard E6 quadratic `q(z)=∑z_i² mod3`, the new chart has cross terms:
`q(Phi⁻¹(w,t))=∑_{i=0..3} w_i² + 2t∑_i w_i + 2t²` in F3.

This is NOT the direct sum of an M81 quadratic with an external F3 norm, and the original 243 still has intrinsic strata (Q0=81,Q1=90,Q2=72). The deleted diagonal is Q=(0,2,2), so its relative 240 has **Q0=80,Q1=90,Q2=70**. The previous root shell 72 is *damaged by deleting 2 of its Q2 elements*. Original inherited E6 reflection s3 remains a counterexample. Thus the new chart does not bypass the previous E6/W(E8) representation obstruction.

## NEW C: actual M81 central-corrected elementary SL3(3) automorphisms

For elementary transvection `T_{ij}:x_i↦x_i+x_j`, a naïve grade permutation leaving central phase untouched fails to preserve original Griess `g`, e.g. `g(T01(001),T01(010))=2 ≠ g(001,010)=0`. A TRUE loop automorphism must take
`(x,a)↦(T_{ij}x,a+h_{ij}(x))` with
`h(x+y)-h(x)-h(y)=g(Tx,Ty)-g(x,y)`.

Exact source-derived corrections:
- `h01=x2(1-x1²)`; `h02=0`.
- `h10=x2(1-x0²)`; `h12=x0(x2²-1)`.
- `h20=0`; `h21=x0(x1²-1)`.

New Lean #52 source `Integration.Griess1990Moufang81ElementaryLift` states all **6×729=4,374 original-g source phase equations**, six 81² (=39,366) SAME-loop product intertwiner conditions, order-three lift condition, 27 actual linear character-shift automorphisms and parameter faithfulness. SOURCE-WRITTEN, Lean kernel unavailable.

Independent **exact local** SymPy Schreier--Sims on literal 81-point permutations gives a generated subgroup of order **151,632=27×5,616**. Its projection to 27 source grades is independently computed to have order **5,616**, the complete SL3(3). The kernel consists of exactly the **27 character shifts** `(x,a)↦(x,a+lambda·x)`, each verified as a member of the group. The chosen six lifts need not be a splitting section merely because the extension and its order were computed; separate group-presentation obligation.

This is consistent with earlier general commutative Moufang automorphism literature. Original attribution for general automorphism-group results: **Lucien Bénéteau and J. Lacaze**, *Groupes d'Automorphismes des Boucles de Moufang Commutatives*, European Journal of Combinatorics **1** (1980), 299–309, DOI [10.1016/S0195-6698(80)80029-1](https://doi.org/10.1016/S0195-6698(80)80029-1); Bénéteau (1981), *Ordre minimum des boucles de Moufang commutatives de classe 2 (Resp. 3)*, DOI [10.5802/afst.561](https://doi.org/10.5802/afst.561), for the earlier classification of nonassociative loops of order81. The source **particular phase (g) and Albert construction** remains Griess (1990), not reassigned.

## NEW D: transport six actual loop automorphisms to original OLD 240 states

Lean #52 `Integration.Griess1990MoufangOriginal240Action` uses the explicit old240↔punctured M81×F3 equivalence to CONJUGATE each selected Griess loop automorphism to a total map on the REAL original 240 states. This is a genuine, nontrivial action intertwiner; it does NOT transport the original E6, structured E8 Weyl, spatial P3³ edge or Monster VOA action.

Local exact group orbit analysis: on M81, the six lifts have **orbit sizes 1,1,1,78** (the 3 central points separately fixed, and one 78-element noncentral orbit). On the original relative 240, the chart leaves the fifth coordinate t untouched: **six singleton orbits + three size-78 orbits**. Therefore the earlier **234 noncollinear unordered PG(2,3) triples**, although cardinal-equal to the 234 noncentral chart states, are transitive under source SL3(3) whereas the transported M81 action has **3 separate 78-orbits**. Cardinality 234 does NOT promote an equivariant point-triplet bijection.

## Exact local receipt and test

Original independent standalone executable:
`/mnt/data/check_griess_M81_243_240_cocycle_full_maxcut.py` SHA256 in JSON receipt
`/mnt/data/griess_M81_243_240_cocycle_receipt.json`.
Actual run 2026-10-25 PASS:
- 4,374/4,374 phase cochain equations;
- 39,366/39,366 literal M81 multiplication-intertwining checks;
- 6 order-three generating lifts, generated permutation group order151632, projected grade group order5616 and all27 normal linear shifts in the group;
- exact 243-state inverse chart, 240 relative-bijection and preservation of punctured carrier under 6 transported shears;
- Q0/Q1/Q2 original 243=(81,90,72), 240=(80,90,70);
- selected actor orbital fingerprint (1,1,1,78) original M81; 240=(1×6,78×3).
GitHub `scripts/check_griess_m81_t5_243240_actual_cocycle_action.py` committed on BOTH Lean #52 and Agda #1239, with the independently built source-equivalent local checker, but **GitHub blob not replayed byte-identically here**, and Lean/Agda toolchains NOT available. Do not claim kernel or CI green.

## Pareto max-cut and attribution stop-rule

| Priority | Kernel/source acceptance | What stays separate |
| --- | --- | --- |
| P0 | Kernel-check source `Griess1990OriginalHomogeneousFormula`→original 1839 nonzero rational structure constants→729 native Albert products; actual 27D action | Monster VOA 196884D `Vnatural_2`, the Chen--Lam--Shimakura three-sector orbifold |
| P0 | Kernel-check the simple M81 `δg=det`, six cocycle lift automorphisms, chart left/right inverse and transported Old240 actions | The old E6 action obstruction stays PAID and binding |
| P1 | Supply Agda Kernel5↔actual M81×Trit TWO-SIDED witness, not only a receipt, typecheck Agda; retain historical relative owner | No duplicate Kernel5, trit, Albert, E8 or tautological integer bridge |
| P1 | Determine whether chosen M81 exact lift extension has a split section compatible with Griess’s specified normalizer and actual F4/E6 action | 151632 is computed permutation GROUP, not a Lean group-order theorem or semidirect-product proof |
| P2 | If desired, explicit comparison against structured E8 240 must use an action-preserving root correspondence or a proved obstruction. Already paid full intrinsic structured Weyl datum and diagnostic order 696729600 on Lean #47 | Never weaken prior art back to only E6×A2; no original-relative T5 = structured E8 |
| P3 | Selected *same-VOA* Monster 3B/phase action and physical/KK/369 observables | No cross-universe inference via equal 240, 243, 234, 80, 81, 52, 78 or zeta labels |

**Author/provenance boundary:** Original Griess (1990) cubic/loop/Albert; Bénéteau–Lacaze (1980) and Bénéteau (1981) loop-theory lineage; Alsaody–Gille (2019), Barry–Tignol (2023) octonion/triality donors; Chen–Lam–Shimakura (2018) independent Monster VOA; the 5-trit factorization/structured finite code and present explicit checks are **DASHI implementation**. Mathematical literature, local computation, source-written proof, and kernel-accepted theorem are distinct evidence classes. No source is credited only because later code reuses it and no co-authorship is implied by cross-pollination.


### 2026-10-25 later Agda proof upgrade — chart witness actually constructed

The Agda #1239 source `DASHI/Moonshine/Griess1990OriginalKernel5M81243240ChartExact.agda` has now advanced beyond the earlier uninhabited point-bijection receipt: it contains nine-case trit cancellation laws, source-written proofs `kernel5LeftRoundTrip` and `m81RightRoundTrip`, an explicitly inhabited `canonicalKernel5M81CarrierBidi`, and the forward and reverse identity/diagonal witnesses `diagonalKernel5Forward`/`diagonalKernel5Backward`. This directly reuses original `Local.Kernel5`, `SSPTritCarrier`, and the original Griess M81 *set*, without any postulates. **No Agda kernel execution**; these are source-written proofs only. The stronger `Kernel5M81BidiPayment` full relative-240 and E6-action receipt remains **uninhabited** and must not be represented as finished. On Lean #52 the actual `Old240 ≃ (M81\\{1})×F3` source equivalence and transported six true Moufang loop automorphisms remain independently source-written, with exhaustive local Python checks. The original punctured T5 is still not the already-recognized structured E8 240 representation.

## 2026-10-25 Ibrahim/Pareto snowball: original 240 versus E8 is an ACTUAL prime-13 no-go

The user explicitly recalled the original 240/243 T5 work (Lean #43/#47, Agda #1094/#1098). The older cardinal equality `243=3+240` and the s3 E6-reflection escape are already-owned; the later structured E8 root carrier `72+6+6×27` is separate. **NEW STRICT SAME-ACTION RESULT** on Lean #52 / Agda #1239: the original Griess Jr. (1990) M81 phase polynomial and three actual central-cocycle-corrected shears e01→e12→e20 define one order-13 automorphism of the literal M81 loop. Exact local exhaustions: 81 states = 3 fixed + 6 thirteen-cycles; via actual original T5↔M81×F3 chart, original 240 = 6 fixed + 18 thirteen-cycles. First source-checked lift sends `((1,0,0),0)` to `((1,0,1),2)`; a grade-only shear is wrong. Hence any equivariant bijection carrying this source automorphism to a true fixed-root-system E8 Weyl action is IMPOSSIBLE, because classical `|W(E8)| = 696729600 ≡ 8 (mod13)`; no E8 Weyl/root-system automorphism has a 13-cycle. Even the full locally calculated source `|G|=151632=2^4·3^6·13` is now unnecessary for the obstruction. **This does not forbid unrelated set bijections, different source actions, E8 continuous group automorphisms outside root-system stabilizers, selected Monster VOA/3B acts, or physical hypotheses**.

* Actual Lean #52 owners: `Integration/Griess1990Original240E8WeylPrime13Obstruction.lean` (Lagrange using Mathlib `Subgroup.card_dvd_of_injective`, exact arithmetic) and `Integration/Griess1990Moufang81Explicit13Cycle.lean` (true 3-shear source word and 81/240 finite proof targets). Actual Agda #1239 owner: `DASHI/Moonshine/Griess1990Moufang81ExplicitThirteenCycleExact.agda` (reuses Griess M81 and earlier real Kernel5 chart, 81 `refl` equations, explicit Weyl modulo-13 residue). Both canonical existing source-cocycle Python regressions enlarged IN PLACE; independently executed local standalone `check_griess1990_explicit_13_cycle_no_weyl_e8.py` PASS with negative control, documented by `griess1990_explicit13_E8_weyl_no_go_receipt.json`. New source files remain **source-written, NO Lean/Lake/Agda kernel checks**.
* Focused Lean #52 plan (canonical): [Griess/E8 prime-13 actual-action no-go](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-25-griess-e8-prime13-actual-action-no-go.md).
* Original authorship: Robert L. Griess Jr., J. Algebra 131 (1990), 281–293, DOI 10.1016/0021-8693(90)90176-O (M81 source); classical Cartan/Coxeter/Bourbaki E8 Weyl root theory, with independent modern reference **Rosa Winter and Ronald van Luijk**, *Graphs and Combinatorics* 37 (2021), 1965–2064, DOI 10.1007/s00373-021-02315-8; Alsaody–Gille and Barry–Tignol are unrelated original triality donors; Chen–Lam–Shimakura retain independent Vsharp Moonshine VOA source; OEIS/Ibrahim contribute only original sequence/rubric/numerical 13/52/78 origins. Don't conflate repeated source echoes.
* Pareto: CLOSE original T5-240 to structured E8 **under the specified Griess source action** negatively; next P0 positive kernel receipt for ORIGINAL Griess tau-real source formula→native Jordan 729 products and Agda actual same-object transport; P1 kernel compile cheap 13-cycle and exact prime no-go; P2 separate Monster VOA selected-eigenspace/mode proof; P3 physical same-operator gates. Full E8 structured root datum remains valid and separate.

## 2026-10-25 PAR/Pareto–Ibrahim continuation: BOTH positive actual Albert order13 AND negative original240→W(E8) actor

**Priority/source root already known (do not misattribute as new mathematics):** R. L. Griess Jr. (1990), *J. Algebra* 131:281–293, DOI 10.1016/0021-8693(90)90176-O, explicitly described A⋊SL(3,3) inside the complex Albert automorphism group (type F4) and his 81-element quotient Moufang loop. The new DASHI contribution is the **EXPLICIT SOURCE-SPECIFIC Q-RATIONAL TAU-REAL/native Cayley-Dickson automorphism matrices, exact independent finite checks, and precise 240/E8 rejection test**, not the original discovery of F4, SL3 or the existence of order13 elements.

**P0 positive, independently executed LOCAL exact computation:** Three corrected Griess shears e01→e12→e20 yield source automorphism `S:e_x↦omega^h(x)e_(Mx)` on ACTUAL original rational 27D Albert, preserving all 729 source Jordan products. Existing rational isomorphism `A` produces `N=A*S*A⁻¹` on the SAME native octonionic Jordan 27; all 729 native Jordan products, unit, trace Gram, order13 passed exact SymPy. `charpoly27=(X−1)^3 Φ13(X)^2`, trace(S^k)=1 for every k=1..12. New Lean #52 `Integration/Griess1990Moufang81ActualAlbertOrder13.lean` defines this SOURCE algebra actor by original finite grade/phase formula and 27D native matrix conjugation with finite theorem targets (**source-written, NO Lean kernel run**). New identical finite independent checker on Lean #52 and Agda #1239: `scripts/check_griess1990_order13_actual_albert_and_traceless26.py` reuses existing original Griess Q(omega) and native Q-octonion checker (**committed blobs not yet byte-executed**). Local independent original script `/mnt/data/check_griess1990_order13_actual_albert.py` and 27×27 Q-matrix certificate `/mnt/data/griess1990_actual_albert_order13_certificate.json`.

**P0 positive ACTUAL 26D consumer, not 26=2×13 numerology:** The same N preserves original native trace, so it restricts along literal 27×26 embedding `[e0-e1,e1-e2,off12(8),off20(8),off01(8)]`. Exact local chart/projection intertwinement passed. Since actual Albert unit is a fixed complementary 1D module and χ27 known, `χ26=(X−1)^2Φ13^2`, fixed dimension 2 and two 12D rational cyclotomic blocks; trace of all nonidentity powers on traceless 26 is zero. User's older Ibrahim/OEIS **26=2×13 arithmetic** has NO authority to identify two 13D irreducibles; actual module is `2+12+12`. New Lean #52 source: `Integration/Griess1990AlbertOrder13Traceless26.lean`, finite source-basis receipts only, **UNCOMPILED**. Local `/mnt/data/check_griess1990_order13_traceless26.py`, `/mnt/data/griess1990_order13_traceless26_certificate.json`.

**P0 negative CLOSED in exact finite mathematics:** Old original T5 243→240 chart `T5≃M81×F3` turns 3-shear order13 M81 action into original old240 permutation with 6 fixed+18 length13 cycles. A true fixed E8 root-system automorphism belongs to W(E8), classical order `696729600=2¹⁴3⁵5²7≡8 (mod13)`; no element/order13 cycle. Therefore NO equivariant identification under **this exact source action** with the separate structured E8 root carrier. This is a root-Weyl same-action obstruction, NOT a general ban on 240-element set bijections, unrelated 240 actions, continuous E8 elements that do not preserve the selected root datum, original-Q F4/Monster selected 3B VOA or physical interpretations. Lean no-go proof target `Integration/Griess1990Original240E8WeylPrime13Obstruction.lean` reuses Lagrange `Subgroup.card_dvd_of_injective`; actual short witness in `Griess1990Moufang81Explicit13Cycle.lean`; Agda #1239 owns 81-case `refl` original Griess shear and original Kernel5 chart source. None kernel checked. Independent local `/mnt/data/check_griess1990_explicit_13_cycle_no_weyl_e8.py` PASS including adversarial naive-shear mismatch; `/mnt/data/griess1990_explicit13_E8_weyl_no_go_receipt.json`.

**Source genealogy:** Griess 1990 owns the algebra/loop/SL3 source; Weyl/Cartan/Coxeter/Bourbaki classical theory owns order and root automorphisms, modern original independent source Rosa Winter & Ronald van Luijk (2021), *Graphs and Combinatorics* 37:1965–2064, DOI 10.1007/s00373-021-02315-8. Alsaody–Gille 2019, Barry–Tignol 2023 own related triality results, NOT same local matrix or Griess polynomial. Chen–Lam–Shimakura 2018 own true 3-sector Monster Moonshine VOA, no paid selected same-object mode. Sloane/McGarvey/Foster/Riordan attribution in existing Ibrahim A027907 owner remains numerically orthogonal; do not promote source existence, a repeated citation, analogy, cardinality or source-written code into proof.

**Canonical focused max-cut owner:** [Lean #52 order13 actual Albert26 / E8 Weyl discriminator](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-25-griess-order13-albert26-e8-weyl-discriminator.md).

**Next Pareto:** (1) actual Lean/Lake kernel compile of original Q(omega) Griess formula and source-to-native 729 Jordan map, then concrete order13 actor (source-written now); (2) typecheck Agda 81-constructor action and instantiate original-to-native Agda transport record, not repeated arithmetic; (3) original-Q F4 classification remains separate; (4) genuine selected Monster VOA 3B source eigensector and physics consumers require independently supported same-object operators. NO CI receipts invented.
