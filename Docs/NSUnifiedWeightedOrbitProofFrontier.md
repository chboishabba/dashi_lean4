# Periodic NS: unified weighted/orbit proof surface (R735–R814)

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

## Strongest honest combined theorem

Introduce the augmented W2 defect

  Z_N(T) :=
    [X_N(T)-12 Q_+-,N(T)]-[X_N(0)-12 Q_+-,N(0)]
      + delta_N D_N(T)-12 W_N(T).

For each cutoff and terminal, suppose:

(A) **Integrated physical weld**. The actual R742 integrated defect
    is exactly an integrated/reindexed R760/R781 orbit residual,
    separated plus CC-touched, with sign and multiplicities checked.
    R781 by itself is a same-time finite fold identity and must not
    be silently substituted for a spacetime statement.

(B) **Same-object R813 transfer**. Under that weld, the separated
    component is integrated from 2*(9 N_sep - Q_sep), retaining the
    same live cutoff/trajectory/mask.

(C) **Combined signed payment**. The integrated sum of the separated
    expression and the CC-touched residual is <= 0. Cancellation
    of the fully-separated family is optional and *stronger* than needed.
    A payment via a controlled boundary/normalization defect also qualifies
    when justified on the real physical carrier.

(D) W1 is bounded by B(T) independently of cutoff N.

(E) The original mixed mass is nonnegative; if uniform dissipation
    is required, delta_N >= delta_0 > 0 independently of cutoff.

Then (A)+(B)+(C) give Z_N(T)<=0, which is W2. W1+W2 yield

  X_N(T) + delta_N D_N(T)
    <= X_N(0) + 12 B(T) - 12 Q_+-,N(0)
    <= X_N(0) + 12 B(T).

With delta_N>=delta_0 and D_N>=0,

  X_N(T) + delta_0 D_N(T) <= X_N(0) + 12 B(T).

The downstream continuation theorem additionally needs the pre-existing
uniform-in-N initial-energy bound, suitable finite-time B(T), compactness
and smoothness/continuation hypotheses. They are not established here.

## The remaining nontrivial leaves

1. Verify/source-write the **R742 spacetime ↔ R760/R781 signed-fold
   transport**, including any factor 2 from swap-pairing and all
   zero-output and time-integration conventions. This is a theorem
   obligation, not a definitional equality.
2. Prove one physical, signed **separated+CC payment**. Exploit the
   cubic/quintic mismatch to avoid an impossible all-amplitude equality
   or an amplitude-independent estimate with invalid degree.
3. Prove W1 with a cutoff-independent B(T); prove a uniform positive
   margin floor if the terminal continuation consumes one.
4. Establish the actual selected-object amplitude scaling and a
   nonzero witness before promoting R814's degree audit into a
   no-go theorem on the physical state family.

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

NSBControl/UnifiedWeightedOrbitBarrier.lean contains:

- PhysicalOrbitWeld (explicit R742-to-R781 seam);
- SignedOrbitPayment (no cancellation assumption);
- orbitPayment_implies_W2;
- weightedOrbitBarrier;
- uniformMarginBarrier and allCutoffsUniformBarrier;
- exactSeparatedCancellation_iff (optional);
- scaleFreeBalanceForcesBothZero (degree-3 vs degree-5 negative control).

The Lean mirror is conditional algebra over real scalars. It **does not**
certify the Agda physical-to-analytic weld, nor has a fresh exact-head
Lean kernel run been performed for this tranche.
