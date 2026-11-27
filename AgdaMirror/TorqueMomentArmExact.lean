/-! Secondary mirror of DASHI.Interop.TorqueMomentArmExact.
Agda is authoritative. This models nonnegative perpendicular-load magnitudes,
not a general vector cross product or a verified physical runtime. -/
namespace AgdaMirror.TorqueMomentArmExact

structure PerpendicularLoad where
  momentArm : Nat
  perpendicularForce : Nat

def torqueMagnitude (load : PerpendicularLoad) : Nat :=
  load.momentArm * load.perpendicularForce

structure EqualPerpendicularLoads where
  first : PerpendicularLoad
  second : PerpendicularLoad
  sameArm : first.momentArm = second.momentArm
  sameForce : first.perpendicularForce = second.perpendicularForce

theorem equalLoadsEqualTorque (loads : EqualPerpendicularLoads) :
    torqueMagnitude loads.first = torqueMagnitude loads.second := by
  unfold torqueMagnitude
  rw [loads.sameArm, loads.sameForce]

theorem zeroArmZeroTorque (force : Nat) :
    torqueMagnitude ⟨0, force⟩ = 0 := by
  simp [torqueMagnitude]

theorem zeroForceZeroTorque (arm : Nat) :
    torqueMagnitude ⟨arm, 0⟩ = 0 := by
  simp [torqueMagnitude]


/- Citation markers identify provenance, not proof authority. -/
structure CitedCompactTorque where
  citationMarker : String
  load : PerpendicularLoad
  compactResult : Nat
  resultExact : compactResult = torqueMagnitude load

theorem citedResultSound (entry : CitedCompactTorque) :
    entry.compactResult = torqueMagnitude entry.load := entry.resultExact

def makeCitedCompactTorque (marker : String) (load : PerpendicularLoad) :
    CitedCompactTorque := ⟨marker, load, torqueMagnitude load, rfl⟩

theorem compactResultPreserved (marker : String) (load : PerpendicularLoad) :
    (makeCitedCompactTorque marker load).compactResult = torqueMagnitude load := rfl

end AgdaMirror.TorqueMomentArmExact
