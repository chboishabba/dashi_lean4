import DashiKakeya.NeedleTubeTransport

/-!
# Correct all-scale quotient/residual metric bridge

A finite-prefix observation cannot be globally injective on a full
continuous spatial space. A strictly positive multiplicative lower
comparison therefore fails whenever there is an address collision.

A lawful replacement is two-sided ADDITIVE distortion:
the physical distance differs from the distance of decoded prefix
representatives by at most 2ε_n, provided each original point is
within ε_n of its same-context decoded representative.

No physical approximation rate ε_n is invented or asserted here.
The source is the classical triangle inequality, not a new
Kakeya or Yang--Mills estimate.
-/

namespace DashiKakeya

universe u v w

variable {Physical : Type u} {Code : Type v}
variable [PseudoMetricSpace Physical]

/-- All-scale actual selected physical reconstruction (the supplied
context/observer is bound when the encode/decode functions are chosen). -/
structure AllScaleApproximateObservation where
  encode : ℕ → Physical → Code
  decode : ℕ → Code → Physical
  residual : ℕ → ℝ
  physicalError : ∀ n x,
    dist x (decode n (encode n x)) ≤ residual n

variable (a : AllScaleApproximateObservation (Physical := Physical) (Code := Code))

/-- Original physical distance is at most decoded distance + twice error. -/
theorem physicalDistance_le_decoded_add_twiceResidual
    (n : ℕ) (x y : Physical) :
    dist x y ≤
      dist (a.decode n (a.encode n x)) (a.decode n (a.encode n y))
        + 2 * a.residual n := by
  have h₁ := dist_triangle x (a.decode n (a.encode n x)) y
  have h₂ := dist_triangle (a.decode n (a.encode n x))
    (a.decode n (a.encode n y)) y
  have hx := a.physicalError n x
  have hy : dist (a.decode n (a.encode n y)) y ≤ a.residual n := by
    simpa [dist_comm] using a.physicalError n y
  linarith

/-- The reverse inequality is also exact, with the same two errors. -/
theorem decodedDistance_le_physical_add_twiceResidual
    (n : ℕ) (x y : Physical) :
    dist (a.decode n (a.encode n x)) (a.decode n (a.encode n y))
      ≤ dist x y + 2 * a.residual n := by
  have h₁ := dist_triangle (a.decode n (a.encode n x)) x
    (a.decode n (a.encode n y))
  have h₂ := dist_triangle x y (a.decode n (a.encode n y))
  have hx : dist (a.decode n (a.encode n x)) x ≤ a.residual n := by
    simpa [dist_comm] using a.physicalError n x
  have hy := a.physicalError n y
  linarith

/-- The explicit two-sided distortion result at every scale. -/
theorem allScaleDecodedMetricComparison (n : ℕ) (x y : Physical) :
    (dist x y ≤
      dist (a.decode n (a.encode n x)) (a.decode n (a.encode n y))
        + 2 * a.residual n) ∧
    (dist (a.decode n (a.encode n x)) (a.decode n (a.encode n y))
      ≤ dist x y + 2 * a.residual n) :=
  ⟨physicalDistance_le_decoded_add_twiceResidual a n x y,
    decodedDistance_le_physical_add_twiceResidual a n x y⟩

/-- The remaining physical problem is precisely to instantiate this
with an actual observer-state/context and prove ε_n tends to zero
(or the weaker scale-uniform distortion needed by an application).
Neither p-adic completion nor dimensional signature forces it. -/


/-- A genuine metric tube at any selected scale survives lossy
observation, with a precisely quantified 2ε_n radius inflation.
The *decoded curve* is not automatically a Euclidean straight line. -/
theorem needleTube_decode_radiusInflation
    (n : ℕ) (needle : ℝ → Physical)
    (radius : ℝ) (point : Physical)
    (h : inNeedleTube needle radius point) :
    inNeedleTube
      (fun t => a.decode n (a.encode n (needle t)))
      (radius + 2 * a.residual n)
      (a.decode n (a.encode n point)) := by
  obtain ⟨t, ht, hdist⟩ := h
  refine ⟨t, ht, ?_⟩
  have hdecoded :=
    decodedDistance_le_physical_add_twiceResidual a n point (needle t)
  exact hdecoded.trans (add_le_add_right hdist _)

/-- The correct selected family is a UNION of tubes, and the same
explicit radius inflation applies to whichever original direction
witnesses the source point. -/
theorem directionalTubeUnion_decode_radiusInflation
    {Direction : Type w} (n : ℕ)
    (needle : Direction → ℝ → Physical)
    (radius : ℝ) (point : Physical)
    (h : ∃ d : Direction, inNeedleTube (needle d) radius point) :
    ∃ d : Direction,
      inNeedleTube
        (fun t => a.decode n (a.encode n (needle d t)))
        (radius + 2 * a.residual n)
        (a.decode n (a.encode n point)) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, needleTube_decode_radiusInflation a n (needle d)
    radius point hd⟩

/-- If an independent actual geometrical source proves that the
decoded needle is the chosen target needle at all t, the same
quantitative tube inclusion holds around that target. -/
theorem selectedStraightNeedle_decode_radiusInflation
    (n : ℕ) (source target : ℝ → Physical)
    (radius : ℝ) (point : Physical)
    (sameOriginalNeedle : ∀ t,
      a.decode n (a.encode n (source t)) = target t)
    (h : inNeedleTube source radius point) :
    inNeedleTube target
      (radius + 2 * a.residual n)
      (a.decode n (a.encode n point)) := by
  obtain ⟨t, ht, hd⟩ := h
  refine ⟨t, ht, ?_⟩
  have hdecoded :=
    decodedDistance_le_physical_add_twiceResidual a n point (source t)
  rw [sameOriginalNeedle t] at hdecoded
  exact hdecoded.trans (add_le_add_right hd _)

end DashiKakeya
