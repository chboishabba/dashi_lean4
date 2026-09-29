# Periodic NS: signed W2 orbit payment (through R815)

**Status:** conditional implication, not an unconditional Navier–Stokes regularity proof. Sources on Agda PR #1039 are source-written/static-inspected; no exact-head kernel receipt is asserted.

## Strongest exact chain currently exposed

For cutoff N and terminal T, the R735/R742 analytic cut is

- W1: signed weighted input-Laplacian work plus terminal mixed mass,
  W_N(T) + Q_{+-,N}(T) <= B(T), with B independent of N;
- W2: the integrated physical R648 strict packet surplus is <= the
  R723 combined signed residue, at retained margin delta_N>0.

The exact R734/R735 compiler yields

  X_N(T) + delta_N D_N(T) <= X_N(0) + 12 B(T)

provided W1 and W2 hold. The positive margin must be bounded below by
one delta_0>0 independent of N for uniform dissipation coercivity;
delta_N>0 individually is not sufficient.

R737–R743 show differentiation of X-12 Q_+- cancels the weighted work
when forming the local W2 statement. Thus the derivative identity is a
reduction, not a new coercivity estimate.

R760/R781 pair and partition the **same-time finite orbit residual** into
fully separated and CC-touched classes. R779–R793, with the corrected
qEnergyLeg order six, compress the separated class into a q-cycle;
R794–R797 and R798–R813 then give the exact separated scalar normal form

  D_sep(t) = 2 * (9 N_sep(t) - Q_sep(t)),

where Q_sep is the cubic dyadic q-quotient ordered-pair transfer and
N_sep is the quintic nested R573/R571 four-helicity coherent work.
This identity does NOT state W2 and does NOT control the CC-touched part.

The R814 degree check rules out interpreting

  Q_sep = 9 N_sep

as a universal nonzero amplitude-scale-free algebraic identity. If the
degree-three and degree-five scaling laws hold on the literal selected
objects and equality is imposed at amplitudes 1 and 2, then both terms
must vanish. This does not rule out a genuine integrated signed payment.

## R815 corrects the physical normalization and sign

The old (A)/(C) story below has been superseded by the exact R745 →
R749 → R760 → R781 finite-rate transport, now source-written in Agda
`NSTriadKNR650SignedOrbitPacketWeldRound815Exact.agda`.

At a fixed cutoff/time and with the same live packet:

  R_N(t) := D_sep(t) + D_CC(t)
            + 6*(2nu-delta)*d_N(t)

  R_N(t) = 6*(Combined_N(t) - PacketStrictSurplus_N(t)).

The finite nonlinear split alone is NOT the physical surplus gap.
The retained viscous term and factor six must survive. Consequently
the sign required by pointwise W2 is R_N(t) >= 0, not <= 0.

R815 also transports this exact equality through the live integration
authority, yielding

  integral R_N dt = 6 * integral (Combined_N - PacketStrictSurplus_N) dt.

The R742 integrated W2 input is therefore paid by an integrated
NONNEGATIVE orbit expression. The eventual cancellation/estimate remains
open; R815 is an identity only.

The existing R813 refinement can be substituted into this expression:

  R_N(t) = 2*(9*N_sep(t)-Q_sep(t)) + D_CC(t)
           + 6*(2nu-delta)*d_N(t).

The needed analytic input is

  integral [ 2*(9*N_sep-Q_sep) + D_CC
             + 6*(2nu-delta)*d_N ] dt >= 0.

The desired positive viscosity margin is the one already consumed by
R742/R734; it must not be spent a second time. Without further
information, neither a sign for the cubic term nor a sign for the
quintic work is known.

After this payment, R742/R734 compile the augmented W2 bound; with
cutoff-independent W1 and an independently uniform positive margin
delta_N >= delta_0 > 0, the conditional Clay-facing bound remains

  X_N(T) + delta_0 D_N(T) <= X_N(0) + 12 B(T).

The signed estimate, W1 bound, and uniform margin are open. Smooth
continuation/limit passage is an additional distinct requirement.

## Exact status

- R745 gives the rate-to-physical-packet identity with factor three.
- R749 changes only the nonlinear incidence representation.
- R760 doubles the same nonlinear fold through physical swap.
- R781 splits the paired fold into separated and CC-touched parts.
- R813 gives the separated refinement, without requiring it to vanish.
- R815 lifts the correctly normalized physical gap to a signed
  spacetime integral. **No new analytic inequality is asserted.**
- `NSBControl/SignedOrbitPacketWeld.lean` is the corrected conditional
  scalar compiler. The older `UnifiedWeightedOrbitBarrier.lean` uses a
  hypothetical, nonliteral weld and must not be instantiated as R815.

## Verified cross-pollination boundaries

The J369/SSP T4-local/T5-complement and C3/C6 orbit geometry is
*finite action/indexing data*. The NS exponent 3 vs 5 is an
*amplitude-homogeneity grading*. These are different categories.
The valid shared abstraction is orbit averaging and preservation of
a separately typed physical residual, not identification of a T5
coordinate with quadratic kinetic energy.

In particular: neither a universal Q_sep=9*N_sep equality nor the
claim that the W1/W2 analytic leaves are proved follows from the
finite Moonshine/SSP representations.

## Lean mirror

The corrected consumer is `NSBControl/SignedOrbitPacketWeld.lean`.
It explicitly requires integrated nonnegativity, the factor-six same-object
weld, W1, and any uniform margin floor. The historical
`UnifiedWeightedOrbitBarrier.lean` remains marked nonphysical for
this particular R745–R815 instantiation.

No exact-head Agda or Lean kernel receipt is claimed.
