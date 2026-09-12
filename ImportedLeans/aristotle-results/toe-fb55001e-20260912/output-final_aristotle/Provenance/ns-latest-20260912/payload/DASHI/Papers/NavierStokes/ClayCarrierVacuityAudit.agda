module DASHI.Papers.NavierStokes.ClayCarrierVacuityAudit where

------------------------------------------------------------------------
-- AUDIT RESULT (machine-checked)
--
-- `DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact`
-- declares
--
--   FeffermanPeriodicClayStatementB : FeffermanPeriodicClayCarrier → Set₁
--
-- and the surrounding modules describe this as "the literal Fefferman
-- periodic alternative (B)".  The type is however parametric in an
-- *uninterpreted* carrier: every mathematical notion occurring in the Clay
-- problem (smoothness, periodicity, divergence-freeness, the momentum
-- equation, the initial trace) is an abstract field of type
-- `X → Set` supplied by the carrier.
--
-- This module proves, constructively and without postulates, that the
-- family `FeffermanPeriodicClayStatementB` is inhabited: instantiating the
-- carrier with the one-point/always-true interpretation yields a total
-- inhabitant.
--
-- Consequences for the Clay lane:
--
-- * Inhabiting `FeffermanPeriodicClayStatementB carrier` for *some* carrier
--   is not evidence for periodic Navier--Stokes regularity.
-- * All mathematical force therefore sits in a carrier instance whose
--   fields are the genuine analytic predicates on real function spaces.
--   No such analytic instance exists anywhere in this repository (searched
--   for every reference to `FeffermanPeriodicClayCarrier`).
-- * Consequently the end-to-end composition
--   `inRepoPathClosesLiteralFeffermanPeriodicB` is a schematic reduction
--   between abstract records, not a proof of the Clay statement.
--
-- Nothing here weakens the Clay target.  It records precisely what the
-- in-repo target type does and does not say.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact
  as Clay

-- The degenerate ("everything holds of everything") carrier.
trivialCarrier : Clay.FeffermanPeriodicClayCarrier
trivialCarrier = record
  { Viscosity = ⊤
  ; PositiveViscosity = λ _ → ⊤
  ; SmoothPeriodicDatum = ⊤
  ; DatumSmoothOnThreeTorus = λ _ → ⊤
  ; DatumDivergenceFree = λ _ → ⊤
  ; DatumUnitPeriodicInThreeCoordinates = λ _ → ⊤
  ; GlobalVelocity = ⊤
  ; GlobalPressure = ⊤
  ; VelocitySmoothOnThreeTorusTimesNonnegativeTime = λ _ → ⊤
  ; PressureSmoothOnThreeTorusTimesNonnegativeTime = λ _ → ⊤
  ; VelocityUnitPeriodicInThreeCoordinates = λ _ → ⊤
  ; PressureUnitPeriodicInThreeCoordinates = λ _ → ⊤
  ; SolvesThreeDimensionalMomentumEquationWithZeroForce =
      λ _ _ _ _ → ⊤
  ; IncompressibleAtEveryNonnegativeTime = λ _ → ⊤
  ; AttainsInitialDatumAtTimeZero = λ _ _ → ⊤
  }

-- The in-repo "literal Clay statement" is inhabited at this carrier.
trivialCarrierSatisfiesLiteralClayStatement :
  Clay.FeffermanPeriodicClayStatementB trivialCarrier
trivialCarrierSatisfiesLiteralClayStatement _ _ _ _ _ _ = record
  { velocity = tt
  ; pressure = tt
  ; velocitySmooth = tt
  ; pressureSmooth = tt
  ; velocityPeriodic = tt
  ; pressurePeriodic = tt
  ; solvesMomentumEquation = tt
  ; incompressible = tt
  ; initialTrace = tt
  }

-- Restated as an explicit existential over carriers, for readability.
record SomeCarrierSatisfiesLiteralClayStatement : Set₂ where
  constructor someCarrier
  field
    carrier : Clay.FeffermanPeriodicClayCarrier
    witness : Clay.FeffermanPeriodicClayStatementB carrier

literalClayStatementTypeIsInhabited :
  SomeCarrierSatisfiesLiteralClayStatement
literalClayStatementTypeIsInhabited =
  someCarrier trivialCarrier trivialCarrierSatisfiesLiteralClayStatement
