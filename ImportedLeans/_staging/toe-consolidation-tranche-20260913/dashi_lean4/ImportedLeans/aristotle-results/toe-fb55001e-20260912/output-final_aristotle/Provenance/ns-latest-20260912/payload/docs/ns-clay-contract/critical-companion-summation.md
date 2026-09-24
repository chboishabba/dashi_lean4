# The critical companion: fibre-as-operator summation, the proved low-output gain, and the cardinality-free Riesz summation

Lean source: `RequestProject/NavierStokes/WaleffeCriticalCompanionSummation.lean`.
Whole-project build: clean, no `sorry`, no postulates, no added axioms; every
headline theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

This round attacks the first of the two remaining welds of package `A`:
*cutoff-uniform fibre/network summation preserving the low-output `|k|` gain*.

## The objects

On the integer lattice `Wave = ℤ³`, for a mode set `T`, a field `u` and a signed
modal nonlinearity `N`:

| object | Lean name | formula |
|---|---|---|
| critical production | `critProduction` | `∑_k \|k\| Re⟪u_k, N_k⟫` |
| critical dissipation | `critDissipation` | `∑_k \|k\|³ ‖u_k‖²` |
| companion | `critCompanion` | `∑_k \|k\|⁻¹ ‖N_k‖²` |
| cellwise majorant | `cellMajorant` | `M(k) = ∑_a E_a E_{k−a}` |
| cellwise companion | `cellCompanion` | `∑_k \|k\| M(k)²` |

## 1. The reduction is cardinality-free

`abs_critProduction_le`:

    |P| ≤ √(D₁₂) · √(Q).

The `k`-fibre is never expanded into cells — the whole projected nonlinearity
`N_k` is kept as one vector — so no fibre cardinality, shell count, matching
number or Wiener `ℓ¹` factor is created by this step.

`critProduction_absorption` puts it in the Round-150 absorption shape: for every
`θ > 0`,

    |P| ≤ θ·D₁₂ + (1/(4θ))·Q.

So the whole of `A` reduces, exactly, to a cutoff-uniform time-integrated budget
for the companion `Q`.

`GalerkinFlow.abs_critProd_le_wiener_absorption` states the same on the literal
Galerkin carrier: assuming only the `HH→low` output gain
`‖f_k‖ ≤ |k| ∑_a ‖u_a‖‖u_{k−a}‖` for the projected nonlinearity of the flow,

    |P_crit(t)| ≤ θ·D₁₂(t) + (1/θ)·(∑_a ‖u_a‖)²·(∑_a |a|‖u_a‖²).

## 2. What the cellwise route costs: exactly one Wiener factor

`critCompanion_le_cellCompanion` transfers the companion through the low-output
gain, and `cellCompanion_le_wiener` bounds the result:

    Q_cell ≤ 4 (∑_a E_a)² (∑_a |a| E_a²).

The proof is two Young-type convolution estimates on the lattice,
`young_l1_first` and `young_l1_second`, proved from scratch by Cauchy–Schwarz
with the convolution weight plus the translation/reflection bounds
`sum_shift_le`, `sum_reflect_le`.  There is no cardinality, shell count or
matching number anywhere; the entire cost of the cellwise route is the squared
Wiener (`ℓ¹`) mass.

The alternative way of closing the fibre — paying the cardinality instead of the
Wiener mass — is `cellCompanion_le_card`:

    Q_cell ≤ 2·#S·(∑_a E_a²)·(∑_a |a| E_a²),

which is cutoff-dependent through `#S`.  These two are the only exits after
absolute values, and the next section shows that neither factor can be dropped.

## 3. The cellwise route cannot be repaired

`cellwise_companion_not_controlled_by_energy_enstrophy`: for every constant `C`
there is a configuration with

    C · (energy × enstrophy) < Q_cell,

where energy `= ∑_a E_a²` and enstrophy `= ∑_a |a|² E_a²`.  The witnesses are
flat unit spectra on two antipodal lattice cubes `[16N,24N]³` and `−[16N,24N]³`
(the legs), with outputs the cube `[N,2N]³`.  The configuration is strictly
high-high-to-low: `outBox_legBox_hh` proves `2|k| ≤ |a|` for every output `k` and
every leg `a` (in fact `4|k| ≤ |a|`).  The two quantitative bounds are

* `cellCompanion_flat_lower`: `Q_cell ≥ N¹⁰`;
* `energy_flat_le`, `enstrophy_flat_le`: energy `≤ 1458 N³`, enstrophy
  `≤ 2519424 N⁵`, hence energy × enstrophy `≤ 4·10⁹ N⁸`.

The ratio therefore grows like `N²`.  Since energy and enstrophy are exactly the
quantities the Galerkin system supplies with a cutoff-uniform time budget, this
is a precise no-go: **after taking absolute values inside the fibre, no
cutoff-uniform companion budget exists**, even with the full low-output `|k|`
gain and even restricted to `HH→low` incidences.  The step "triangle inequality
over `p + q = k`, then sum" is not merely wasteful; it is fatal, and the signed
cancellation inside the fibre is mandatory.

## 4. The low-output gain is now proved, not assumed

Lean source: `RequestProject/NavierStokes/WaleffeOutputGainFibre.lean`.

`GalerkinFlow.nrm_force_le_output_gain`: on the literal Galerkin carrier, using
only incompressibility,

    ‖f_k‖ ≤ |k| · ∑_a ‖u_a‖ ‖u_{k−a}‖,

with the **output** frequency `|k|` and constant `1` — no leg derivative
`|k − a|`, which is what the earlier termwise majorant carried.  The mechanism is
exact and algebraic: the BAC–CAB identity `cross_triple` on `ℂ³`, the resulting
output normal form of an advective pair with transverse legs

    i(u_p·q)u_q + i(u_q·p)u_p
      = 2i(u_p·u_q)k − i(u_p×(k×u_q) + u_q×(k×u_p)),

in which the *leg* wavevectors have cancelled, and the Leray projection killing
the remaining longitudinal term.  The fibre is symmetrised by the shared-output
involution `a ↦ k − a` (the added indices are unoccupied), which halves the
factor `2`.  Consequently
`GalerkinFlow.abs_critProd_le_wiener_absorption_of_flow` is unconditional.

## 5. The fibre summed as an operator: no cardinality, no Wiener factor

Lean sources: `RequestProject/NavierStokes/LatticeShellCounting.lean` and
`RequestProject/NavierStokes/LatticeRieszConvolution.lean`.

The fibre is now summed against the Riesz weight `|a|⁻¹|k−a|⁻¹` instead of by
the triangle inequality.  The lattice geometry is built from scratch:

* `card_shell_le` — a max-norm sphere of radius `m ≥ 1` in `ℤ³` carries at most
  `26m²` points;
* `sum_shell_bound` — the resulting fibrewise summation principle;
* `sum_inv_sq_le_of_bounded` — `∑_{0<|a|≤R} |a|⁻² ≤ 26R`;
* `sum_inv_four_le_of_lower` — `∑_{|a|≥R} |a|⁻⁴ ≤ 104/R` for `R ≥ 2`;
* `card_le_of_bounded` — `#{0<|a|≤R} ≤ 26R³`.

Splitting the fibre into the four regions `|a| ≤ |k|/2`, `|k−a| ≤ |k|/2`,
`|k|/2 < |a| ≤ 2|k|` and `|a| > 2|k|` gives the master bound
`lattice_riesz_convolution`:

    ∑_a |a|⁻² |k−a|⁻² ≤ 4000/|k|      (k ≠ 0, any finite index set).

Cauchy–Schwarz on the fibre against that weight then yields
`cellCompanion_le_enstrophy_sq`:

    ∑_k |k| M(k)² ≤ 4000 (∑_a |a|² E_a²)²,

and, on the literal Galerkin carrier,
`GalerkinFlow.abs_critProd_le_enstrophy_absorption`: for every `θ > 0`,

    |P_crit(t)| ≤ θ·D₁₂(t) + θ⁻¹·1000·(enstrophy(t))².

Every constant is absolute; no fibre cardinality, shell count, matching number
or Wiener `ℓ¹` norm appears.  This is the cutoff-uniform fibre/network summation
that preserves the low-output `|k|` gain.

On the flat high-high configuration of §3 the companion is at least `N¹⁰` while
the enstrophy is at most `2519424 N⁵`, so both sides of the companion bound grow
like `N¹⁰`: for the cellwise route the enstrophy square is of the right order,
and by §3 nothing of the shape energy × enstrophy can replace it.

## 6. Inside the dynamics: the critical energy identity and the conditional barrier

Lean source: `RequestProject/NavierStokes/WaleffeCriticalEnergyBarrier.lean`.

The estimates above are instantaneous.  On the literal Galerkin ODE the critical
energy `E₁₂(t) = ∑_k |k| ‖u_k(t)‖²` satisfies the exact identity
(`critEnergy_hasDerivAt`)

    E₁₂'(t) = −2ν D₁₂(t) + 2 P_crit(t),

with `D₁₂ = ∑_k |k|³‖u_k‖²` and `P_crit = ∑_k |k| Re⟪u_k, f_k⟫` — precisely the
objects estimated above — and its integrated form is `critEnergy_balance`.
Feeding in the cardinality-free absorption with `θ = ν/2` gives the differential
barrier (`critEnergy_differential_barrier`)

    E₁₂'(t) ≤ −ν D₁₂(t) + (4000/ν)·(enstrophy(t))²,

and integrating it gives the conditional closure
(`critEnergy_barrier_of_companion_budget`): for `t₀ ≤ t₁` and `ν > 0`,

    ∫_{t₀}^{t₁} (enstrophy)² ≤ B   ⟹
      E₁₂(t₁) + ν ∫_{t₀}^{t₁} D₁₂ ≤ E₁₂(t₀) + (4000/ν)·B.

Every constant in the chain is absolute, so the conclusion is uniform in the
Galerkin cutoff once `B` is.  This is the exact interface of the remaining
obligation: **a cutoff-uniform bound for `∫₀^T (enstrophy)² dt`**.  The energy
inequality gives `∫₀^T (enstrophy) ≤ E₀/ν`, one power short, and nothing here
claims the missing bound.

## 7. The critical trilinear bound and the small-data barrier

The companion bound of §5 can be interpolated instead of being left as a
separate obligation.  Cauchy–Schwarz against the splitting `|a|² = |a|^{1/2} ·
|a|^{3/2}` gives (`enstrophy_sq_le_critEnergy_mul_critDiss`)

    (enstrophy)² ≤ E₁₂ · D₁₂,

and feeding this into `cellCompanion ≤ 4000·(enstrophy)²` together with the
fibre-operator reduction yields the critical trilinear bound
(`abs_critProd_le_sqrt_critEnergy_mul_critDiss`)

    |P_crit(t)| ≤ 64 · √(E₁₂(t)) · D₁₂(t),

with an absolute constant and no cardinality or Wiener factor.  This is the
classical critical shape: the production is bounded by the dissipation times the
square root of the critical energy itself.

Consequently, whenever `E₁₂(t) ≤ (ν/128)²` the whole production is paid outright
by half of the viscous term (`two_critProd_le_of_small`), and a continuity
bootstrap on the closed set `{s ∈ [t₀,t] : (ν/128)² ≤ E₁₂(s)}`
(`critEnergy_le_threshold`) shows the threshold is never reached.  Integrating
the balance then gives the unconditional statement
(`critEnergy_barrier_of_small_data`): for `ν > 0`, `t₀ ≤ t₁` and
`E₁₂(t₀) < (ν/128)²`,

    E₁₂(t₁) + ν ∫_{t₀}^{t₁} D₁₂ ≤ E₁₂(t₀).

All constants depend only on `ν`, so the barrier is uniform in the Galerkin
cutoff.  This is the small-critical-data regime only: the bound is quadratic in
`√E₁₂` on the wrong side for large data, and nothing here closes the
large-critical-data case, which is exactly the Clay-sized part of `A`.

Finally, the same threshold closes the companion budget of §6 in this regime
(`integral_enstrophy_sq_le_of_small_data`): from `(enstrophy)² ≤ E₁₂ · D₁₂ ≤
(ν/128)² D₁₂` and `ν ∫ D₁₂ ≤ E₁₂(t₀)`,

    ∫_{t₀}^{t₁} (enstrophy)² ≤ (ν/128)² · E₁₂(t₀)/ν,

again with no cutoff dependence.  So the “second weld” — the time-integrated
companion budget — is genuinely closed *below the threshold*, and open above it.

## What this does not close

* It does not close `A`.  The barrier of §7 is unconditional only below the
  absolute threshold `(ν/128)²`; large critical data is untouched.  The positive
  content is the reduction and its cost;
  the missing theorem — a cutoff-uniform time-integrated bound for the *signed*
  companion `Q = ∑_k |k|⁻¹‖N_k‖²`, where `N_k` is the true projected
  nonlinearity and not its cellwise majorant — is untouched.
* The remaining companion is quartic in `H¹`: the energy inequality supplies
  `∫₀^T ‖u‖²_{H¹} ≤ E₀/ν`, not `∫₀^T ‖u‖⁴_{H¹}`.  A cutoff-uniform bound for the
  time integral of the companion — the second weld — is untouched.
* Package `B` (critical Sobolev/Simon upgrade and continuation weld) is
  untouched.
* Nothing here is an Agda result: this round is Lean-side only, and no Agda
  kernel was run.
