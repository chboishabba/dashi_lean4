# The resolvent-weighted Gram flux route, machine-checked

Files: `RequestProject/NavierStokes/ResolventHeatFactorization.lean`,
`RequestProject/NavierStokes/ResolventGramFlux.lean`.
Both build inside the whole project, contain no `sorry`, no postulate and no
added axiom; every headline theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## What the route is

The surviving admitted route is

    viscous pair damping  →  resolvent-weighted Gram flux  →  signed integrated Gram consumer.

The two recorded no-gos are respected: nothing here uses a pointwise sign
obtained from conjugation/sign/swap orbits, and nothing identifies the quartic
Gram debt with the (quintic) nonlinear part of `dQ/dt`.  The quartic structure
comes from the *viscous* pair rate, not from the nonlinearity.

## 1. The Cauchy kernel is a positive heat integral — for the whole family

For a finite family of cells `A_α` in a real vector space carrying a symmetric
positive semidefinite pairing, and strictly positive rates `λ_α`, define the
resolvent form

    resForm A B = ∑_{α,β} ⟪A_α, B_β⟫ / (λ_α + λ_β).

`PSDForm.resForm_eq_integral` proves

    resForm A B = ∫_0^∞ ⟪A_s, B_s⟫ ds,   A_s = ∑_α e^{-sλ_α} A_α,

from `1/(a+b) = ∫_0^∞ e^{-sa}e^{-sb} ds`.  Consequences:

* `PSDForm.resForm_nonneg` — `resForm A A ≥ 0`; the resolvent form is a genuine
  positive quadratic form (`PSDForm.resPSD` packages it as one);
* `PSDForm.neg_resOff_le_resDiag` — hence `−F_off ≤ F_diag` for the
  diagonal/off-diagonal split of the resolvent endpoint.  No absolute bound
  `|F_off| ≤ C` is needed, and none is assumed;
* `PSDForm.resDiag_le` — the diagonal endpoint is paid by a uniform ceiling on
  the resolvent weights against the plain sum of cell masses
  (`∑ w_α m_α ≤ W ∑ m_α`, `PSDForm.sum_weighted_le_ceiling`): no same-output
  multiplicity and no convolution-cardinality factor appears;
* `PSDForm.sq_resForm_le`, `PSDForm.resForm_young` — Cauchy–Schwarz and Young
  for the resolvent form itself:

      4 |resForm A F| ≤ ε · resForm A A + (4/ε) · resForm F F   for every ε > 0.

  The mixed term is absorbed into the *same* positive resolvent energy that
  already appears on the endpoint side.

## 2. The flux compiler, analytically

`integral_eq_flux_add_weighted_remainder`: if `g' = −λ g + r` with `λ > 0` on a
time window, then

    ∫_{t₀}^{t₁} g = (g(t₀) − g(t₁))/λ + (1/λ) ∫_{t₀}^{t₁} r.

This is a signed identity: no positive majorant of `g` is constructed, and no
absolute value is taken before integrating.

## 3. The factorized pair remainder

`PSDForm.weighted_remainder_eq`: summing the product-rule remainders
`r_{αβ} = 2⟪F_α,A_β⟫ + 2⟪A_α,F_β⟫` against the Cauchy weights gives exactly

    ∑_{α,β} r_{αβ}/(λ_α+λ_β) = 4 · resForm A F,

i.e. `4∫_0^∞ ⟪A_s, F_s⟫ ds` after §1 — the pair remainder reorganizes into the
same heat-weighted object as the endpoint.

## 4. The assembled statement

`PSDForm.integral_gramDebt_eq` (identity) and
`PSDForm.signed_gram_integral_bound` (bound): for cells whose pairwise Gram
scalars obey the damped-forced tangent,

    ∫_{t₀}^{t₁} D_Gram(t) dt
      = 2 resForm(A(t₀)) − 2 resForm(A(t₁)) + 4 ∫ resForm(A(t),F(t)) dt
      ≤ 2 resForm(A(t₀)) + ε ∫ resForm(A(t)) dt + (4/ε) ∫ resForm(F(t)) dt

for every `ε > 0`, where `D_Gram = ∑_{α,β} 2⟪A_α,A_β⟫` is the *signed* fibre
Gram debt.  The terminal endpoint is discarded by positivity, not bounded.

## 5. On the literal carrier

`nsPSD` is the real part of the Hermitian pairing on `Fin 3 → ℂ`, the carrier of
the mixed-helicity cells; `viscousPairRate ν p q = ν(|p|² + |q|²)` is the literal
viscous pair rate, positive whenever a leg is a nonzero lattice vector.
`nsPSD_gram_hasDerivAt` derives the damped-forced *Gram* tangent from the
componentwise damped-forced *cell* tangent by the product rule — the Gram-level
ODE is not assumed.  `ns_signed_gram_integral_bound` is then §4 on that carrier,
with hypotheses only at cell level plus integrability.

## What this does not close

The bound leaves exactly one unpaid object: the spacetime remainder energy

    ∫_{t₀}^{t₁} resForm(F(t)) dt = ∫_{t₀}^{t₁} ∫_0^∞ ‖F_s(t)‖² ds dt

for the heat-weighted remainder cells.  Two explicit reductions of it are proved
(`PSDForm.resForm_le_nrm_resolvent`, `PSDForm.resForm_le_of_rate_floor`), but
both discard the signs inside the remainder family and therefore reintroduce an
ℓ¹/cardinality cost of exactly the kind the earlier rounds identified as fatal
for a critical bound; they are recorded as reductions, not as a payment.

No claim is made about Package A, about periodic Serrin/BKM continuation, or
about the Clay statement: this round supplies the flux/absorption algebra and
its literal-carrier instantiation, nothing more.  No Agda kernel was run and no
statement about the Agda rounds is made here.
