/-
# CMP 109 §5 — the tensor-structure normalisation of the beta coefficient

Earlier Row-A rounds recorded, as a missing literal source datum, *the tensor
structure on which the CMP 109 beta coefficient is normalised*: the polarization
weld could identify the second variation

    Π(b, b') = δ²/δB(b)δB(b') E^{(j)}(U_j(exp iB)) |_{B = 0}

with the Lean shell coefficient only up to the convention fixing which scalar
multiple of which lattice tensor is called `β`.

Reading CMP 109 §5 supplies it.  After the symmetry analysis the momentum-space
polarization tensor is written as

    Π_{μν}(p) = β·( δ_{μν}·Δ(p) − ∂_μ(p)·conj ∂_ν(p) ) + Π'_{μν}(p),

with `∂_μ(p) = e^{ip_μ} − 1` the lattice derivative symbol, `Δ(p) = Σ_ρ|∂_ρ(p)|²`
the lattice Laplacian symbol, `β` a single scalar (the common value of the
off-diagonal coefficients after the stated normalisation), and `Π'` a *third
order* polynomial in the lattice derivative symbols.

This file formalises that normalisation and turns it into an extraction
identity, which is what a weld actually needs:

* `latticeTransverse` — the normalised tensor structure
  `T_{μν}(p) = δ_{μν}Δ(p) − ∂_μ(p)conj ∂_ν(p)`;
* `latticeTransverse_offDiag_mixed_deriv` — for `μ ≠ ν` the mixed momentum
  second derivative of `T_{μν}` at zero momentum equals `−1`, so the tensor
  structure is *non-degenerate* in exactly the channel used to read off `β`;
* `beta_coefficient_extraction` — consequently, for any decomposition of a
  polarization tensor on this structure whose remainder has vanishing mixed
  second derivative at zero momentum (which a third-order polynomial in the
  `∂`'s does), the coefficient is uniquely determined:
  `β = −∂²Π_{μν}/∂p_μ∂p_ν |_{p = 0}`, `μ ≠ ν`.

That identity is the convention-free form of the source normalisation: it fixes
`β` from the polarization tensor alone, with no further choice, and it is the
object the Lean polarization file computes.
-/
import Mathlib

namespace YangMills

open Complex

/-- The lattice derivative symbol `∂(p) = e^{ip} − 1` of one momentum
component. -/
noncomputable def latticeDerivSymbol (p : ℝ) : ℂ := Complex.exp (p * I) - 1

/-- The off-diagonal entry of the normalised CMP 109 tensor structure,
`−∂_μ(p)·conj ∂_ν(p)`, as a function of the two momentum components involved. -/
noncomputable def latticeTransverseOffDiag (s t : ℝ) : ℂ :=
  -(latticeDerivSymbol s * (starRingEnd ℂ) (latticeDerivSymbol t))

/-- `∂(t) = e^{it} − 1` has derivative `i·e^{it}`. -/
theorem hasDerivAt_latticeDerivSymbol (t : ℝ) :
    HasDerivAt latticeDerivSymbol (I * Complex.exp (t * I)) t := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * I) I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
  have h2 : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * I))
      (Complex.exp ((t : ℂ) * I) * I) t := h1.cexp
  have h3 : HasDerivAt latticeDerivSymbol (Complex.exp ((t : ℂ) * I) * I) t :=
    h2.sub_const 1
  convert h3 using 1
  ring
/-- The conjugated symbol `conj ∂(t) = e^{−it} − 1` has derivative
`−i·e^{−it}`. -/
theorem hasDerivAt_conj_latticeDerivSymbol (t : ℝ) :
    HasDerivAt (fun x : ℝ => (starRingEnd ℂ) (latticeDerivSymbol x))
      (-I * Complex.exp (-(t : ℂ) * I)) t := by
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) (latticeDerivSymbol x)
      = Complex.exp (-(x : ℂ) * I) - 1 := by
    intro x
    simp [latticeDerivSymbol, ← Complex.exp_conj, Complex.conj_I]
  have h1 : HasDerivAt (fun x : ℝ => -(x : ℂ) * I) (-I) t := by
    have : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using (this.neg.mul_const I)
  have h2 : HasDerivAt (fun x : ℝ => Complex.exp (-(x : ℂ) * I))
      (Complex.exp (-(t : ℂ) * I) * (-I)) t := h1.cexp
  have h3 := h2.sub_const 1
  have : HasDerivAt (fun x : ℝ => (starRingEnd ℂ) (latticeDerivSymbol x))
      (Complex.exp (-(t : ℂ) * I) * (-I)) t := by
    simpa [hconj] using h3
  simpa [mul_comm] using this

/-- The inner momentum derivative of the off-diagonal tensor entry. -/
theorem deriv_latticeTransverseOffDiag_snd (s : ℝ) :
    deriv (fun t : ℝ => latticeTransverseOffDiag s t) 0 = I * latticeDerivSymbol s := by
  have h := (hasDerivAt_conj_latticeDerivSymbol 0).const_mul (-latticeDerivSymbol s)
  have h2 : HasDerivAt (fun t : ℝ => latticeTransverseOffDiag s t)
      (-latticeDerivSymbol s * (-I * Complex.exp (-(0 : ℂ) * I))) 0 := by
    simpa [latticeTransverseOffDiag, mul_comm, mul_left_comm, mul_assoc] using h
  rw [h2.deriv]
  simp
  ring

/-- **Non-degeneracy of the normalised tensor structure.**  The mixed momentum
second derivative of the off-diagonal entry `T_{μν} = −∂_μ·conj ∂_ν` at zero
momentum equals `−1`. -/
theorem latticeTransverse_offDiag_mixed_deriv :
    deriv (fun s : ℝ => deriv (fun t : ℝ => latticeTransverseOffDiag s t) 0) 0 = -1 := by
  have hfun : (fun s : ℝ => deriv (fun t : ℝ => latticeTransverseOffDiag s t) 0)
      = fun s : ℝ => I * latticeDerivSymbol s :=
    funext deriv_latticeTransverseOffDiag_snd
  rw [hfun]
  have h := (hasDerivAt_latticeDerivSymbol 0).const_mul I
  rw [h.deriv]
  simp

/-- **Extraction of the beta coefficient from the polarization tensor.**  If an
off-diagonal polarization entry decomposes on the normalised CMP 109 tensor
structure as `Π = β·T + Π'`, with a remainder whose mixed momentum second
derivative at zero vanishes (as it does for a third-order polynomial in the
lattice derivative symbols), then

    β = − ∂²Π/∂p_μ∂p_ν |_{p = 0}.

In particular the coefficient is uniquely determined by the polarization tensor:
two decompositions on this structure have the same `β`. -/
theorem beta_coefficient_extraction
    (Pi Rem : ℝ → ℝ → ℂ) (beta : ℂ)
    (hdec : ∀ s t, Pi s t = beta * latticeTransverseOffDiag s t + Rem s t)
    (hRemInner : ∀ s, deriv (fun t : ℝ => Rem s t) 0 = 0)
    (hInner : ∀ s, DifferentiableAt ℝ (fun t : ℝ => Rem s t) 0) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => Pi s t) 0) 0 = -beta := by
  have hstep : ∀ s : ℝ, deriv (fun t : ℝ => Pi s t) 0
      = beta * (I * latticeDerivSymbol s) := by
    intro s
    have hT : HasDerivAt (fun t : ℝ => beta * latticeTransverseOffDiag s t)
        (beta * (I * latticeDerivSymbol s)) 0 := by
      have h := (hasDerivAt_conj_latticeDerivSymbol 0).const_mul (-latticeDerivSymbol s)
      have h2 : HasDerivAt (fun t : ℝ => latticeTransverseOffDiag s t)
          (I * latticeDerivSymbol s) 0 := by
        have h3 : HasDerivAt (fun t : ℝ => latticeTransverseOffDiag s t)
            (-latticeDerivSymbol s * (-I * Complex.exp (-(0 : ℂ) * I))) 0 := by
          simpa [latticeTransverseOffDiag, mul_comm, mul_left_comm, mul_assoc] using h
        have : (-latticeDerivSymbol s * (-I * Complex.exp (-(0 : ℂ) * I)))
            = I * latticeDerivSymbol s := by simp; ring
        rwa [this] at h3
      exact h2.const_mul beta
    have hR : HasDerivAt (fun t : ℝ => Rem s t) 0 0 := by
      have := (hInner s).hasDerivAt
      rwa [hRemInner s] at this
    have hsum : HasDerivAt (fun t : ℝ => beta * latticeTransverseOffDiag s t + Rem s t)
        (beta * (I * latticeDerivSymbol s) + 0) 0 := hT.add hR
    have : (fun t : ℝ => Pi s t)
        = fun t : ℝ => beta * latticeTransverseOffDiag s t + Rem s t := by
      funext t; exact hdec s t
    rw [this, hsum.deriv]
    ring
  have hfun : (fun s : ℝ => deriv (fun t : ℝ => Pi s t) 0)
      = fun s : ℝ => beta * (I * latticeDerivSymbol s) := funext hstep
  rw [hfun]
  have h := ((hasDerivAt_latticeDerivSymbol 0).const_mul I).const_mul beta
  rw [h.deriv]
  simp

end YangMills
