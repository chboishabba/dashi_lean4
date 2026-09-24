/-
# The high–high helicity-slot kernel and its anti-parallel defect (R145 carrier)

The Agda round `DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact`
carries a genuine constructive identity (a `RingSolver` proof, no postulate) for
the `p/q` normalized-curl slot difference on the exact `ℂ³` carrier:

```
  (P × a) × b − a × (Q × b) = (P·b) a + (a·Q) b − (a·b)(P + Q),
```

where `·` is the **bilinear** (unconjugated) dot product, and, under the
transversality relations `a·P = 0` and `b·Q = 0`, the further factorisation

```
  (P × a) × b − a × (Q × b) = (Σ·b) a + (a·Σ) b − (a·b) Σ,    Σ = P + Q,
```

so that *every* term of the slot kernel factors through the anti-parallel defect
`Σ`.  That module also declares two Boolean ledger flags:
`round145HighHighSlotKernelAntiParallelFactorizationClosed = true` and
`round145AntiParallelEndpointZeroNormalizationClosed = false` — the endpoint
`Σ = 0` corollary is explicitly left *unclosed* there, pending a kernel receipt
on the exact `ℂ³` carrier.

This file is the Lean carrier for that round, stated on the Navier–Stokes lane's
own `ℂ³` vector type and its own `cross` (`ClayNS.Waleffe.cross = crossProduct`):

* `slotKernel_bacCab` — the BAC–CAB identity, machine-checked over `ℂ`;
* `slotKernel_factorsThrough_antiParallelDefect` — the transverse factorisation
  through `Σ = P + Q`;
* `slotKernel_eq_zero_of_antiParallel` — **the endpoint the Agda round leaves
  open**: at exact anti-parallelism `Σ = 0` the whole slot kernel vanishes, with
  no normalization step and no side condition beyond the two transversality
  relations;
* `exists_transverse_antiParallel_nonzero` — the endpoint theorem is not
  vacuous: an explicit transverse anti-parallel quadruple with all four vectors
  as nondegenerate as the constraints allow;
* `exists_transverse_slotKernel_ne_zero` — and it is not trivial either: with
  the same transversality but `Σ ≠ 0` the kernel is nonzero, so
  `slotKernel_eq_zero_of_antiParallel` really is carried by the defect.

Scope.  This is the *pointwise algebraic* content of the R145 lane on the exact
carrier.  It is not a bound, not an aggregation over a shell, and it closes no
Clay obligation: `round145IntraShellL2AggregationClosed` and
`round145PackageAClosed` remain false in the Agda ledger and nothing here
changes that.  The intra-shell `L²` aggregation is a separate obligation and is
not addressed.
-/
import RequestProject.NavierStokes.WaleffeAmplitude

noncomputable section

namespace ClayNS.SlotKernel

open ClayNS.Waleffe

/-! ## 1.  The bilinear dot product

The lane's `herm` is conjugate-linear in the first slot; the BAC–CAB identity is
an identity of the *bilinear* form, so it gets its own name.  (On real vectors
the two agree; on `ℂ³` they do not, and the Agda round uses the bilinear one.) -/

/-- The bilinear (unconjugated) dot product on `ℂ³`, matching the Agda
`bilinearDot3`. -/
def bdot (u v : Fin 3 → ℂ) : ℂ := ∑ i, u i * v i

theorem bdot_comm (u v : Fin 3 → ℂ) : bdot u v = bdot v u :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem bdot_add_left (u v w : Fin 3 → ℂ) : bdot (u + v) w = bdot u w + bdot v w := by
  simp only [bdot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bdot_add_right (u v w : Fin 3 → ℂ) : bdot u (v + w) = bdot u v + bdot u w := by
  simp only [bdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem bdot_zero_left (v : Fin 3 → ℂ) : bdot 0 v = 0 := by
  simp [bdot]

@[simp] theorem bdot_zero_right (u : Fin 3 → ℂ) : bdot u 0 = 0 := by
  simp [bdot]

/-! ## 2.  The slot kernel and its defect -/

/-- The anti-parallel defect of a high–high pair of wave directions. -/
def antiParallelDefect (P Q : Fin 3 → ℂ) : Fin 3 → ℂ := P + Q

/-- The `p/q` normalized-curl slot difference: `(P × a) × b − a × (Q × b)`. -/
def slotKernel (P Q a b : Fin 3 → ℂ) : Fin 3 → ℂ :=
  cross (cross P a) b - cross a (cross Q b)

/-- **BAC–CAB for the slot kernel.**  The Lean counterpart of the Agda
`slotKernelBacCabIdentity`. -/
theorem slotKernel_bacCab (P Q a b : Fin 3 → ℂ) :
    slotKernel P Q a b
      = bdot P b • a + bdot a Q • b - bdot a b • antiParallelDefect P Q := by
  funext i
  fin_cases i <;>
    simp [slotKernel, antiParallelDefect, cross, crossProduct, bdot, Fin.sum_univ_three,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- The transversality relations of a high–high pair: the Agda
`TransverseHighPair`. -/
structure TransverseHighPair (P Q a b : Fin 3 → ℂ) : Prop where
  /-- The first slot vector is transverse to the first wave direction. -/
  aTransverseP : bdot a P = 0
  /-- The second slot vector is transverse to the second wave direction. -/
  bTransverseQ : bdot b Q = 0

/-- **The factorisation through the anti-parallel defect.**  Under the two
transversality relations, all three scalar factors of the slot kernel are
readings of `Σ = P + Q`.  Lean counterpart of the Agda
`slotKernelFactorsThroughAntiParallelDefect`. -/
theorem slotKernel_factorsThrough_antiParallelDefect (P Q a b : Fin 3 → ℂ)
    (h : TransverseHighPair P Q a b) :
    slotKernel P Q a b
      = bdot (antiParallelDefect P Q) b • a + bdot a (antiParallelDefect P Q) • b
          - bdot a b • antiParallelDefect P Q := by
  have h1 : bdot (antiParallelDefect P Q) b = bdot P b := by
    rw [antiParallelDefect, bdot_add_left, bdot_comm Q b, h.bTransverseQ, add_zero]
  have h2 : bdot a (antiParallelDefect P Q) = bdot a Q := by
    rw [antiParallelDefect, bdot_add_right, h.aTransverseP, zero_add]
  rw [h1, h2, slotKernel_bacCab]

/-- **The endpoint the R145 Agda ledger leaves open.**  At exact
anti-parallelism `P + Q = 0` the transverse slot kernel vanishes identically —
no zero-normalization step is needed, the factorised form gives it directly. -/
theorem slotKernel_eq_zero_of_antiParallel (P Q a b : Fin 3 → ℂ)
    (h : TransverseHighPair P Q a b) (hSigma : antiParallelDefect P Q = 0) :
    slotKernel P Q a b = 0 := by
  rw [slotKernel_factorsThrough_antiParallelDefect P Q a b h, hSigma]
  simp

/-! ## 3.  The endpoint is neither vacuous nor trivial -/

/-- An explicit transverse quadruple at exact anti-parallelism, with every
vector nonzero: `P = e₀`, `Q = −e₀`, `a = b = e₁`. -/
theorem exists_transverse_antiParallel_nonzero :
    ∃ P Q a b : Fin 3 → ℂ, TransverseHighPair P Q a b ∧ antiParallelDefect P Q = 0 ∧
      P ≠ 0 ∧ Q ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 := by
  refine ⟨![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, 1, 0],
    ⟨by simp [bdot, Fin.sum_univ_three], by simp [bdot, Fin.sum_univ_three]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> simp [antiParallelDefect]
  · intro h; have := congrFun h 0; simp at this
  · intro h; have := congrFun h 0; simp at this
  · intro h; have := congrFun h 1; simp at this
  · intro h; have := congrFun h 1; simp at this

/-- With the same transversality but a nonzero defect the slot kernel is
nonzero, so `slotKernel_eq_zero_of_antiParallel` is genuinely carried by
`Σ = 0`: `P = Q = e₀`, `a = b = e₁` gives `Σ = 2e₀` and kernel `−2e₀`. -/
theorem exists_transverse_slotKernel_ne_zero :
    ∃ P Q a b : Fin 3 → ℂ, TransverseHighPair P Q a b ∧
      antiParallelDefect P Q ≠ 0 ∧ slotKernel P Q a b ≠ 0 := by
  refine ⟨![1, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 1, 0],
    ⟨by simp [bdot, Fin.sum_univ_three], by simp [bdot, Fin.sum_univ_three]⟩, ?_, ?_⟩
  · intro h; have := congrFun h 0; simp [antiParallelDefect] at this
  · intro h
    have := congrFun h 0
    simp [slotKernel, cross, crossProduct] at this
    norm_num at this

end ClayNS.SlotKernel
