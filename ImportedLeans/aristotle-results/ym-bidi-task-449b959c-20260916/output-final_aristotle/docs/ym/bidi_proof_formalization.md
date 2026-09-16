# The BIDI Yang–Mills note, formalized

This note records the machine-checked implementation of the bidirectional
("BIDI") Yang–Mills argument, as supplied, in
`RequestProject/YangMills/BIDI/`. Every numbered equation of the supplied note
is listed below with the Lean declaration that carries it, or with the reason it
appears as a hypothesis rather than a theorem.

All modules compile against the project's Mathlib pin. There is no `sorry`, no
axiom, no postulate, no Boolean/record placeholder, and no authority receipt in
the development; `RequestProject/YangMills/BIDI/AxiomAudit.lean` prints the axiom
dependencies of all 49 public results, and they are exactly Lean's standard
`propext`, `Classical.choice`, `Quot.sound`.

## Dictionary: note ⟶ Lean

| Note | Statement | Lean declaration | Status |
|---|---|---|---|
| (3) | `SourceDirection = TestObservable`, `sourceDirectionOf = id` | `SourceDirection`, `sourceDirectionOf`, `sourceDirectionOf_eq_id` | definitional (`rfl`) |
| (4) | `D_{J_L}D_{J_R} log Z_N = Cov_N(O_L,O_R)` | `covFinite`, `covFinite_eq_mixedLogDeriv` | definitional (`rfl`) |
| (5)–(7) | R404: `Σ_γ M_{Y,γ} ≤ M_Y ⟹ |B_Y| ≤ M_Y` | `abs_sum_le_of_termwise_le` | proved |
| (8) | R405: `Σ_Y M_Y ≤ M_shell ⟹ |B| ≤ M_shell` | `abs_double_sum_le`, `abs_double_sum_le_of_termwise` | proved |
| (9) | R406 scalarization of one differentiated term | `abs_double_sum_le_of_norm_termwise` (hypothesis `hscalar`) | attachment hypothesis |
| (10)–(12) | noncommutative telescope | `norm_prod_before_sub_prod_after_le`, `teleBound_eq_sum` | proved |
| (13)–(14) | four-stage carrier, ordinary factor bounds | `Stage`, `Stage.Valid`, `fourStage`, `norm_prod_before_le` | proved (bounds are stage data) |
| (15)–(16) | second resolvent identity and norm bound | `second_resolvent_identity`, `norm_resolvent_defect_le` | proved |
| (17) | marked stage with declared budget | `Stage.ofResolventDefect`, `valid_ofResolventDefect`, `valid_marked_of_le` | proved |
| (18)–(20) | unchanged stages / zero defect / marked family | `Stage.unchanged`, `valid_unchanged`, `norm_self_sub_self_le_zero` | proved |
| (21)–(22) | R409 four-stage marked product | `teleBound_marked`, `marked_product_bound`, four marked-stage cases | proved |
| (23)–(25) | R410 same-object attachment | `Stage` before/after, `defect = 0`, `hscalar` | open hypotheses |
| (27)–(30) | CMP116 positive localization | `abs_double_sum_le_of_termwise`, `shell_sup_bound_of_localization` | proved given `hattach` |
| (31) | R402 Cauchy extraction | `norm_mixed_deriv_le`, `norm_mixed_deriv_le_cauchyConst`, `norm_polarized_mixed_le` | proved |
| (32)–(35) | spatial -> temporal decay | `exp_decay_transfer`, `mixedLog_bound_of_source_data` | proved |
| (36) | finite covariance bound | `covariance_bound_finite` | proved |
| (37)–(38) | finite-to-continuum order closure | `norm_le_of_tendsto`, `covariance_bound_continuum` | proved given convergence |
| (39)–(42) | spectral representation / Laplace transform / no `(0,m)` weight | `SpectralRepresentation`, `measure_Ioo_eq_zero_of_laplace_decay` | measure implication proved; representation input |
| (43) | subgap spectral exclusion | `hasVacuumFormGap_of_clustering`, `no_eigenvalue_below_gap`, `resolvent_solvable_below_gap`; bounded literal-spectrum theorem | proved from spectral data |
| (44) | `Δ(H) ≥ m` form gap | `mass_gap_of_clustering` | proved |
| (45) | BIDI normal form | `bidi_waist_to_gap`, `bidi_end_to_end` | proved as implication |
| (46) | residual cut | see below | open physical/source attachments |

## What is proved, precisely

* R404/R405 finite summation layers and the generic norm localization compiler.
* The arbitrary-length ordered noncommutative telescope and its one-marked collapse.
* The CMP99 second-resolvent identity and norm estimate.
* Cauchy extraction in two-source and polarized one-parameter forms.
* Spatial-to-temporal exponential transfer and finite-to-continuum norm/order closure.
* Laplace-decay exclusion of spectral weight in `(0,m)` and the resulting vacuum form gap.
* Bounded literal spectrum exclusion and unbounded vacuum-sector resolvent consequences through the existing operator lane.
* `PolymerShellBridge`: far-shell energy is controlled with rate `m = μ - ν`.
* `ContinuumBridge`: uniform cutoff clustering feeds the existing continuum gap compiler.
* Non-vacuity witnesses for source calculus, clustering carrier and end-to-end implication.

## Residuals after repository cross-pollination

The original worker note listed both generic polymer inputs `hact` and `hcard`. The live repository has since narrowed this: `LatticeAnimalEntropy` proves the literal four-dimensional lattice shell-cardinality estimate, and `Welds.YMBidiLatticeShell` consumes it. Therefore `hcard` is not a live physical hypothesis for the actual `Z^4` route.

The current live attachments are:

1. R410 same-object CMP99/CMP109/R406 identities.
2. CMP116 positive majorants attached to the same selected decomposition.
3. The literal differentiated CMP116 activity majorant `hact` for that source activity.
4. Selected physical source-domain holomorphy / uniform analytic radii and constants.
5. Physical finite-to-continuum convergence of the covariance.
6. Physical spectral/OS representation identifying the covariance with the same Hamiltonian's correlation function.
7. The actual cutoff-to-continuum Hamiltonian graph limit / self-adjoint continuum instance.
8. The finite physical measure/operator chain: physical density-to-literal-measure weld inhabitant, same-measure expectation/L2/null semantics, literal action-variation Hamiltonian, common core/self-adjoint realization, and Row-A1 lower form-gap theorem on that same Hamiltonian.

Consequently the theorem package does **not** prove the Jaffe–Witten theorem and does not claim to. It proves the analytic/compiler chain conditional on the explicitly displayed physical/source attachments.