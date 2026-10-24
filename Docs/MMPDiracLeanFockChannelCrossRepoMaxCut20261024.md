# dashi_lean4 × MMP Dirac/teleportation max-cut — 2026-10-24

## Repo archaeology: what was already proven

All links below refer to **actual repository source** inspected on 2026-10-24, not a claim that independent experimental or physical 4D MMP results exist.

1. **Merged Lean #37** (`CondensedMatter/MajoranaOperatorKernelExact.lean`, `MajoranaParityQubitExact.lean`, `MajoranaLogicalBraidGateExact.lean`) contains explicit complex Pauli/Majorana gamma operators, CAR `f f†+f† f=1`, fermion number projector, the even four-Majorana occupation code `|00>,|11>`, and exact algebraic Ising braid gates. Authors of underlying Clifford/CAR/Ising-model mathematics retain attribution; DASHI formalizes specific finite computations. A Braid representation of a mathematical code **does not** identify the physical charged LLL modes with experimentally usable Majoranas.
2. **Merged Lean #61/#76** (`QuantumMereologyFiniteSubsetMarginal.lean`, `QuantumMereologyPartialTraceCoherence.lean`, `QuantumMereologyGTPSProjectionProducer.lean`) proves finite heterogeneous coordinate-selected subset marginals from the **same** density matrix, two-stage partial trace associativity, and genuine finite HS projections for g-TPS. It **does not** select the physical tensor decomposition of the charged 4D Dirac field or produce dynamical teleportation by itself. Original finite-TPS/quantum-mereology authors have separate authority (Carroll–Singh, Zanardi–Dallas–Andreadakis et al.).
3. **Open Lean #68** supplies a corrected maximally entangled finite Schmidt-cut / RT entropy equality and a flat-vacuum Jacobson/Einstein benchmark. Its RT equality is not a proof that the MMP 4D charged fermion state is a holographic quantum channel, or that the actual Einstein–Maxwell equations are solved.
4. **Open Lean #80/#84** record the QFT/GR/gauge same-object obligations and TOE physical non-promotions. They are source manifests/finite donors, **not** a finished four-dimensional Hadamard/Maxwell–Einstein renormalized fermionic saddle.
5. **Agda #1163** already separates standard quantum teleportation, QET, signal-front speed and physical wormhole traversal. **Agda draft #1248** computes current-normalized static reduced 1+1D Dirac transmission on an **effective** two-infinity metric (P3Q), not a physical same-universe field-line-return MMP scattering matrix.

## Actual new theorem: choose the right logical carrier

In Agda #1248 the selected two-channel **single-particle** qubit encodes a two-dimensional one-particle amplitude in spherical angular modes `n=1,n=2`. For independent transmission amplitudes `t_i`, with `T_i=|t_i|²`, its mean success on a maximally mixed one-particle input is `η_single=(T1+T2)/2`.

Lean #37's even-parity four-Majorana qubit is **different**: logical `|0_L>=|00>`, `|1_L>=|11>`, using two complex fermion occupation bits. Lifting the same *assumed independent-mode loss* to the two-mode fermionic Fock space means the **no-environment-loss** logical Kraus amplitude is
`K_00 = diag(1,t1*t2)`, not `diag(t1,t2)`:
`η_no-loss=(1+T1 T2)/2`.

The output EVEN-PARITY postselection also accepts **double loss** `|11>→|00>` with distinct environment record. For loss amplitudes `s_i`, `|s_i|²=1−T_i`, its separate Kraus amplitude is `K_11 = s1*s2 |0_L><1_L|`.
Thus
```
η_even-only = (1 + T1 T2 + (1−T1)(1−T2))/2
η_even-only − η_no-loss = (1−T1)(1−T2)/2 .
```

The new Lean source proves this exact algebra, the four outcome normalization
`(t1 t2)^2+(s1 s2)^2+(s1 t2)^2+(t1 s2)^2=1` for real amplitudes, and an adversarial **total-loss** witness:
`T1=T2=0`: `η_single=0`, `η_no-loss=1/2`, `η_even-only=1`. Accepting an even output parity is plainly NOT heralding successful quantum transfer. This is a source-independent Fock-space algebraic theorem, not yet a complete Lean CP-map/Choi proof or physical 4D same-object identification.

**Numerical independently executed in Agda companion Python (not a Lean kernel receipt):**
- Effective MMP stationary *model* cutoff R=240 E=.20, `T1≈0.99986528`, `T2≈3.4463×10⁻⁵`: `η_single≈0.49994987`, `η_no-loss≈0.50001723`, `η_even-only≈0.50008459`, double-loss false acceptance `≈6.736×10⁻⁵`.
- Adversarial T1=.2,T2=.7: `η_single=.45`, `η_no-loss=.57`, `η_even-only=.69`; false parity-only acceptance `.12`. Conditional entanglement fidelity is ≈.8282 if *actual no-loss* is heralded, but ≈.6842 if only even output parity is selected.
- T1=T2=0 gives parity-only acceptance 1 and no-loss herald success .5, whereas actual two-mode one-particle transfer is 0. No faster-than-light or physical wormhole signal follows.

The explicit companion Python constructs one-mode 2×2 amplitude-damping Kraus operators, tensors two fermionic occupancy modes, restricts the input to `|00>,|11>`, includes parity-even and odd erasure branches, checks 4×4 and encoded 3×2 Kraus completeness, verifies Choi positivity, and computes the source-specific fidelity. It is a **finite free-fermion channel model**; it does not prove the physical 4D fermion dynamics realize independent losses or the particular encoding.

## Acceptance and cross-repository promotion

Lean (requires installed Mathlib / Lean 4):
```sh
lake env lean QuantumChannels/MMPDiracFockParityChannel.lean
lake env lean QuantumChannels/MMPDiracFockParityChannelRegression.lean
```
The source is committed to this branch, but **Lean/Lake is unavailable in the present execution container**, so there is no honest exact-head kernel receipt. Do not count these source-written terms as checked lemmas or import an unmerged sibling file in production.

**Future physical promotions** (not completed here):
- Construct the **same global 4D spin-c Dirac Hilbert/state** on the one-universe closed magnetic return path from which physically identifiable angular in/out modes can be extracted.
- Prove actual 4D charge/parity superselection, particle/antiparticle/observer/TPS choice, fermion-environment channel and the input/output readout. In particular 4D Dirac modes are NOT Majorana zero modes merely because two complex fermion occupations give the same two-dimensional abstract code.
- Derive a covariantly renormalized common `<T>, <J>` and coupled Einstein–Maxwell backreaction before identifying a physical traversable wormhole.
- Derive actual scattering `S` or causal retarded fermion Green function, QI Choi and no-signalling under physically sourced drive, including detector constraints, spin/gauge holonomy and antiparticles.
- Physical claims for the three plasma regions need Maxwell–MHD boundary currents, global Wilson phase and a state-dependent `δ<T>`; a finite Gaussian magnetic-drive toy or horned-sphere C3 quotient is not sufficient.

**Pareto conclusion:** The Lean **finite-subsystem-state / fermionic parity** machinery genuinely tightens the quantum-channel model now, but the full four-dimensional Hadamard-Dirac/Maxwell–Einstein source remains the primary unsolved physical mathematical task. No additional generic 369/TOE carrier is needed.
