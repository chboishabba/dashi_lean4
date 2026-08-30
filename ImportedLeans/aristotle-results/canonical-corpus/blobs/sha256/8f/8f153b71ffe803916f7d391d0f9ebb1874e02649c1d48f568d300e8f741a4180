# The ancient-solution / Liouville route: what is now formalized, and what is not

This note records the state of the Koch–Nadirashvili–Seregin–Šverák (KNSŠ)
ancient-solution route inside the Lean development
(`RequestProject/NavierStokes/`), after the pass that added
`Poincare.lean` and `AncientLiouville.lean`.

## The route

The route splits the Clay periodic regularity target into two research gates:

* **R1 (extraction).** A first finite singular time `T < ∞` of a smooth periodic
  solution produces, after parabolic rescaling and Galilean normalization, a
  bounded ancient mild solution `U` on `ℝ³ × (-∞, 0]` that is **not spatially
  constant**.
* **R2 (rigidity).** Every bounded ancient mild solution on `ℝ³ × (-∞, 0]` is a
  constant vector field.

R1 + R2 contradict each other, so no first singular time exists, and standard
continuation gives a global smooth periodic solution.

## What is proved in Lean, without `sorry` or postulates

`ClayNS.ancient_periodic_liouville` (in
`RequestProject/NavierStokes/AncientLiouville.lean`):

> Let `ν > 0` and let `(V, P)` be a smooth `ℤ³`-periodic solution of the
> incompressible Navier–Stokes system with zero force, defined for **all** times
> (in particular for all negative times), whose cell energy `energy V t` is
> bounded by a constant `M`. Then `V` is a constant vector field.

and its sup-norm form `ClayNS.ancient_periodic_liouville_of_norm_le`, which
takes the KNSŠ hypothesis `‖V‖_∞ ≤ K` directly (on the torus a sup bound gives
the energy bound `energy V t ≤ K²/2`).

The proof, entirely from material built in this development:

1. **The cell mean is a constant of the motion** (`ClayNS.meanComp_eq`). For each
   component `a`, `d/dt ∫_cell V_a = 0`: the pressure gradient and the Laplacian
   are exact spatial derivatives of periodic functions, and the advective term is
   a spatial divergence by incompressibility, so all three integrate to zero over
   the cell.
2. **Galilean-corrected energy.** With `m` the (time-independent) mean and
   `D(t) = energy V t − ½|m|²`, one has `∫_cell |V − m|² = 2 D(t)`
   (`ClayNS.devEnergy_eq`) and `D' = −2ν · enstrophy`
   (from `ClayNS.energy_balance_enstrophy`).
3. **Coercivity from Poincaré** (`ClayNS.cellInt_poincare`, proved from scratch in
   `Poincare.lean`; `ClayNS.devEnergy_le_enstrophy`). On the unit cell,
   `∫|f − ⟨f⟩|² ≤ 3 ∫|∇f|²`, hence `D ≤ 3 · enstrophy` and therefore
   `D' ≤ −(2ν/3) D`.
4. **Backward Grönwall.** `t ↦ e^{kt} D(t)` with `k = 2ν/3` is antitone, so for
   every `t` and every `s ≤ t`, `e^{kt} D(t) ≤ e^{ks} D(s) ≤ e^{ks} M'`. Letting
   `s → −∞` gives `D(t) ≤ 0`; with `D ≥ 0` this forces `D ≡ 0`, i.e.
   `V ≡ m` everywhere.

Axioms used: `propext`, `Classical.choice`, `Quot.sound` only.

## What this does **not** settle

This is the Liouville theorem **on the torus**, not R2.

R2 concerns ancient solutions on the whole space `ℝ³`, because the KNSŠ
extraction rescales parabolically about the singular point and periodicity is
destroyed in the limit (the period of the rescaled solution tends to `∞`). The
single ingredient that makes the torus argument work — the Poincaré inequality,
i.e. the spectral gap of the Laplacian on a compact cell — is exactly what fails
on `ℝ³`: there `inf spec(−Δ) = 0`, no inequality `∫|u − m|² ≤ C ∫|∇u|²` holds,
and constants are genuine `L^∞` ancient solutions with zero dissipation that are
*not* isolated in the relevant topology. So step 3 above has no whole-space
analogue, and the backward Grönwall argument gives nothing.

Consequently:

* **R2 remains open**, exactly as stated in KNSŠ (*Acta Math.* 203 (2009),
  83–105), where the 2D case and the axisymmetric-without-swirl case are settled
  and the general 3D case is stated to be beyond the methods there.
* **R1 remains open** in the strengthened, nonconstancy-carrying form required
  here. KNSŠ produce a nonzero bounded ancient mild limit; upgrading "nonzero"
  to "nonconstant" (e.g. via a derivative or oscillation normalization such as
  `|∇U(0,0)| = 1` or `osc_{B_1} U(·,0) ≥ c₀ > 0`) is not carried out in the
  literature and is not carried out here.

The first unresolved theorem on this route is therefore R1 in the strengthened
form; the first unresolved theorem that is unambiguously frontier mathematics is
R2. Nothing in this development closes either, and no part of the Clay target is
claimed to be closed by the torus theorem above.

## Related literature consulted for the route

* Koch, Nadirashvili, Seregin, Šverák, *Liouville theorems for the Navier–Stokes
  equations and applications*, Acta Math. 203 (2009), 83–105 — the founding
  paper; blow-up limits are bounded ancient mild solutions, 2D and swirl-free
  axisymmetric Liouville theorems, general 3D open.
* Seregin, *A certain necessary condition of potential blow up for Navier–Stokes
  equations*, Comm. Math. Phys. 312 (2012), 833–845 — `‖v(·,t)‖_{L³} → ∞` is
  necessary for blow-up.
* Lei, *Improved Liouville theorems for axially symmetric Navier–Stokes
  equations*, arXiv:1701.00868 — Liouville under `Γ = r v_θ ∈ L^∞_t L^p_x`, or
  `Γ → 0` as `r → ∞`.
* arXiv:1911.01571 — Liouville for bounded mild ancient axisymmetric solutions on
  `ℝ² × 𝕋¹` with bounded swirl. This is the closest existing result to a domain
  with a compact direction; note however that it uses axisymmetry and a swirl
  bound, neither of which is available in the unrestricted `𝕋³` Clay setting,
  and its compact direction is one, not three.
