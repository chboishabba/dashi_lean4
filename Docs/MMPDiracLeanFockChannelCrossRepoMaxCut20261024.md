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


## Stronger physical cross-pollination: ordinary electromagnetic U(1) superselection

The merged Lean #37 four-Majorana even-parity carrier is an **abstract algebraic parity code**, and in a superconducting BdG system its physical implementation can exploit a condensate/charge reservoir. If it is instead attached to **two ordinary number-conserving charged complex Dirac modes in an Einstein–Maxwell state**, the logical occupations |00> and |11> differ in electromagnetic charge by two units. Fermion parity alone does not license a coherent gauge-invariant superposition.

Under selected charge rotation `theta=pi/2`, the code action is `diag(1,-1)`. `QuantumChannels/MMPDiracChargeSuperselection.lean` reuses the existing **concrete Lean complex 2×2 Clifford matrix** `CondensedMatter.CMatrix2` and proves that invariance of a two-dimensional logical density matrix under its conjugation forces the offdiagonal charge-0/charge-2 coherence to zero. By contrast a dual-rail **one-particle** `|10>,|01>` carrier has equal charge on both amplitudes: a common gauge phase cancels in their coherence. The exact theorem assumes no separately supplied phase reference/compensating charged subsystem. It is not a global superselection theorem for all configurations or a claim superconducting Majorana codes are impossible.

Original sources for reference-frame/particle-number-superselection operations:
- Stephen D. Bartlett, Terry Rudolph, Robert W. Spekkens, *Reference frames, superselection rules, and quantum information*, Rev. Mod. Phys. **79**, 555 (2007), DOI **10.1103/RevModPhys.79.555**;
- Norbert Schuch, Frank Verstraete, J. Ignacio Cirac, *Nonlocal Resources in the Presence of Superselection Rules*, PRL **92**, 087904 (2004), DOI **10.1103/PhysRevLett.92.087904**.

A locally executed independent 2×2 complex-density numerical gate confirms: twirling the `|00>+|11>` pure code state over the selected two charge phases gives `I/2` (purity falls 1→1/2), while the same-charge one-particle dual-rail state remains pure. New Agda source `scripts/check_mmp_charge_sector_coherence_20261024.py` mirrors this finite fact.

**Pareto revised physical choice:** use a **fixed-charge one-particle dual-rail angular-mode encoding** for MMP's ordinary U1 charged Dirac theory unless a physical charge reference, superconducting pairing sector, or gauge-invariant relational encoding is independently constructed from the SAME 4D quantum state. The algebraic four-Majorana parity carrier is useful as an adversarial alternative, NOT automatically the physical qubit.

Additional Lean acceptance:
```sh
lake env lean QuantumChannels/MMPDiracChargeSuperselection.lean
```
No Lean 4 compiler is installed here, so proofs in this PR remain **source-written, not kernel checked**. Original theorem authors and physical source distinctions preserved.


## October 24 SOTA follow-on — corrected channel and selected LLL rails

**New primary literature, original owners:** MMP (2018/2023) original magnetic closed-loop wormhole; Capoferri–Murro (2025, DOI 10.1002/mana.12032) global/microlocal Dirac propagator/Hadamard construction for *Cauchy-compact globally hyperbolic* 4D spacetimes; Zahn (2014, DOI 10.1142/S0129055X13300124) charged Dirac local covariant renormalized stress/current; Freivogel–Fumagalli–Tomašević (2026, arXiv:2606.12528) actual MMP massless-fermion low-energy transmission; Sadhukhan (2026, 2609.33511) first-order trace/Hall response; Negari–Salek (Aug 2026, PRL 137 080201, DOI 10.1103/65dd-448y) fermionic Gaussian channels/extendibility/antidegradability; Lu–Yang–Zheng (arXiv 2603.26051, **PRD accepted Oct 22 2026**, DOI 10.1103/7trm-rykk) GJW holographic OTOC/channel-capacity, NOT MMP physical channel.

**Original erasure theorem authority:** Bennett–DiVincenzo–Smolin PRL 78 (1997) 3217 DOI 10.1103/PhysRevLett.78.3217; Barnum–Smolin–Terhal PRA 58 (1998) 3496. No global 4D Einstein/Maxwell state or real physical qubit claimed.

New `QuantumChannels/MMPMonopoleLLLDualRailCapacity.lean`:
- **assumes** standard spherical spin-c Dirac index result of `q` magnetic LLL zero modes (for q positive), not a locally proved 4D spinor operator theorem;
- if `q≥2`, constructs two distinct `Fin q` rail labels, a better charged fixed-sector candidate than either two different massive n levels or even |00>/|11> ordinary Dirac parity code;
- proves elementary balanced-erasure coherent-information algebra `I_c(I/2)=2T−1 > 0 ↔ T>1/2`, citing the **external** quantum erasure capacity theorem separately;
- in the source-assumed ideal massless reduced static LLL channel, both modes can be exactly reflectionless, giving a one-bit *mathematical* zero-loss limit without proving actual physical capacity or source-driven state.

New full Stinespring numerical source in Agda #1248 `check_mmp_dualrail_coherent_information_20261024.py`: fixed-charge one-particle dual rail `|j>→sqrt(T_j)|j>_B|vac>_E + sqrt(1−T_j)|vac>_B|j>_E`; constructs actual receiver and environment outputs from ONE ISOMETRY; checks Kraus/Choi, coherences, entropy eigenvalues, and `I_c` for maximally mixed input. q12 E=.20 effective massive pair has `I_c≈−0.000682974` bits despite one rail transmitting nearly perfectly; E=.55 near 1 bit; balanced erasure T=.2 has negative `I_c=-.6` and full quantum capacity 0 under Bennett et al. 1997. `check_mmp_dualrail_erasure_degradability_20261024.py` explicitly constructs CPTP receiver/environment degradation maps and checks the `T=.5` threshold.

**Scope discipline:** both executed local Python tests define a restricted fixed-charge *qutrit erasure channel*. Do not automatically apply the Negari–Salek Gaussian extension SDP or Gaussian entanglement-breaking classification without proving the channel lies in its stated fermionic Gaussian operator-algebra class. The chosen `Fin q` basis labels are not prepared wavefunctions or a detector and do not solve MMP's 4D state. For general `T1≠T2`, the displayed `I_c(I/2)` is just a *single selected input* and must not be called optimized/asymptotic capacity.

Lean/source acceptance (not kernel executed):
```sh
lake env lean QuantumChannels/MMPMonopoleLLLDualRailCapacity.lean
lake env lean QuantumChannels/MMPDiracFockParityChannelRegression.lean
```


## 2026-10-25: new 2+1D magnetic-plaquette donor is NOT the spherical LLL source

The sibling draft [dashi_agda #1248](https://github.com/chboishabba/dashi_agda/pull/1248) now owns [a finite 3×3 compact-U(1) magnetic plaquette / Dirac backreaction checker](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/scripts/check_mmp_three_port_2d_compact_u1_20261025.py) plus [causal three-port tangent/dynamic gauge checks](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/scripts/check_mmp_three_port_2d_tangent_20261025.py), source-audited [here](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/Docs/physics/MMP2DMagneticPlaquetteThreePortRepoPriorArtMaxCut20261025.md). Three separately timed external link currents acquire locally magnetic and fermionic feedback while discrete Gauss, CAR and energy-work pass local numerical checks. This is a **2+1D torus in a trivial gauge bundle with zero total oriented plaquette flux**, not the physical S² spin-c operator carrying flux index q used by `MMPMonopoleLLLDualRailCapacity.lean`.

**Actual same-object bridge required:** (1) choose a true quantized 4D S² magnetic bundle with spin-c Dirac zero modes and closed same-universe field lines; (2) identify two normalizable, equal-charge physical rail functions and their asymptotic detector/scattering algebra; (3) couple the same gauge/fermion state and counterterm-renormalized 4D metric/current/stress into Maxwell/Einstein; (4) only then compute a CPTP physical channel and coherent information. Neither local 2D magnetic energy nor a (3\times3) site count pays the spherical `q≥2` source-index obligation.

**Relevant independent recent science:** S. Bharadwaj et al., `arXiv:2603.05616`, PRD accepted 10 September 2026 (DOI `10.1103/kc9m-xv9h`) on Wilson-fermion Hamiltonian **QED3** topological Chern diagnostics. Their quantum Gauss-law gauge/matter sector is not instantiated by our classical electric-link implementation; no Chern number or physical Hall/teleportation capacity has been extracted here. Lean #85 source remains unchanged at theorem level and still requires exact-head kernel certification.


## 2026-10-25: 3D Hodge Maxwell/Dirac donor does NOT select spherical LLL rails

Sibling [Agda PR #1248](https://github.com/chboishabba/dashi_agda/pull/1248) now carries a [3×3×3 finite 3D Maxwell / four-spinor Wilson–Dirac simulation](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/scripts/check_mmp_3d_maxwell_dirac_three_ports_20261025.py) and [retarded three-source CAR tangent checker](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/scripts/check_mmp_3d_maxwell_dirac_tangent_20261025.py), fully audited [here](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/Docs/physics/MMP3DMaxwellDiracThreePortNativePriorArtMaxCut20261025.md). The periodic 27-site lattice has 81 links decomposing into 26 longitudinal, 52 coexact and 3 harmonic modes. Those **three torus harmonic one-forms**, the 3×3×3 hypervoxel count and the two-dimensional source precedents are not spherical magnetic spin-c zero-mode multiplicity `|q|` or physical fermion dual rails.

The new finite source includes independent electronic current feedback, dynamically sourced electric and magnetic fields, sourced exterior charge continuity, discrete Gauss and energy-work audits. Its **classical** link fields and rank-54 free-fermion occupied projector do not construct a four-dimensional covariantly charged Hadamard state or the asymptotic Fock scattering channels assumed by Lean #85. In particular the background sector is topologically trivial and lacks an actual S² magnetic flux/harmonic spin-c index. Any reuse by `MMPMonopoleLLLDualRailCapacity.lean` must first provide an independently constructed and properly charged S² zero-mode family, a same-object spinor-bundle/path map, distinguishable prepared/received rails and a physical channel; **no theorem-level promotion or new Lean proof is claimed here**.

Source owners: Wilson and Kogut–Susskind lattice gauge theory; Kasper–Hebenstreit–Berges (2014 PRD 90 025016) original 3D fermion/gauge backreaction; MMP 2018/2023 wormhole; the separate original quantum-erasure theorem authors. Lean source-written finite algebra and its exact-head kernel gate retain their prior status.
