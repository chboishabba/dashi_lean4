import Synthesis.ToneCore
import AgdaMirror.LogicTlurey
import AgdaMirror.TetralemmaBridge

/-!
# Synthesis layer 1: dialectic carriers over the tone primitive

The repository supplies two dialectical carriers and their tone maps:

* `AgdaMirror.LogicTlurey.Stage` — four positions, successor `next` of order 4,
  tone map `stageTone : Stage → TriTruth` (supplied, *not* equivariant);
* `AgdaMirror.DASHIAlgebra.Stage6` — six positions, successor `next6` of order 6,
  tone map `hexTone : Stage6 → HexTruth` with the supplied equivariance
  `hexTone_next`;
* `AgdaMirror.TetralemmaBridge` — the four-position alignment surface between
  `Stage`, `TriTruth` and the SensibLaw `ResidualLevel` chain.

What is proved here (all new):

* **Descent bridge.** `HexTruth → TriTruth` reduction mod 3 is rotation
  equivariant, hence the sixfold dialectic *does* carry a rotation-equivariant
  ternary tone (`stage6Tone_next`), and its period is exactly 3.
* **Impossibility.** No map whatsoever from the fourfold `Stage` to `TriTruth`
  is rotation equivariant (`no_equivariant_fourfold_tone`).  In particular the
  supplied `stageTone` is not, and no repair is possible: the obstruction is
  `gcd(4,3) = 1` together with `rotateTri` having no fixed point.  This is the
  precise reason the fourfold dialectic can only be *aligned* with, never
  *fibred over*, the ternary tone.
* **Route divergence in the tetralemma surface.** The two supplied routes
  `Stage → ResidualLevel` — via the tone and via the tetralemma position —
  genuinely disagree, and the disagreement is exactly the `contradiction` level
  that the tone route provably omits.
* The tetralemma position carrier and the residual chain are in bijection
  (`residualTetralemmaEquiv`), which is what makes the two routes comparable.

Boundary: these are statements about finite carriers and maps between them.  No
semantic, historical, or physical interpretation of "dialectic" is asserted.
-/

namespace Synthesis.DialecticTone

open AgdaMirror.Base369
open AgdaMirror.DASHIAlgebra (Stage6 next6 hexTone)
open AgdaMirror.LogicTlurey (Stage next stageTone)
open AgdaMirror.TetralemmaBridge
open Synthesis.ToneCore

/-! ## Descent: the hexadic carrier reduces to the ternary tone -/

/-- Reduction of the hexadic universe modulo 3. -/
def hexToTri : HexTruth → TriTruth
  | .h0 => .low | .h1 => .mid | .h2 => .high
  | .h3 => .low | .h4 => .mid | .h5 => .high

/-- The reduction is rotation equivariant: `ℤ/6 ↠ ℤ/3`. -/
theorem hexToTri_rotate (h : HexTruth) : hexToTri (rotateHex h) = rotateTri (hexToTri h) := by
  cases h <;> rfl

/-- The reduction is surjective and exactly two-to-one. -/
theorem hexToTri_surjective : Function.Surjective hexToTri := by
  intro t; cases t
  · exact ⟨.h0, rfl⟩
  · exact ⟨.h1, rfl⟩
  · exact ⟨.h2, rfl⟩

/-- Ternary tone of a sixfold dialectic stage. -/
def stage6Tone (s : Stage6) : TriTruth := hexToTri (hexTone s)

/-- **Sixfold descent bridge.**  The sixfold dialectic successor is carried to
the tone rotation. -/
theorem stage6Tone_next (s : Stage6) : stage6Tone (next6 s) = rotateTri (stage6Tone s) := by
  cases s <;> rfl

/-- The tone of a sixfold stage has period exactly 3 under the successor. -/
theorem stage6Tone_period_three (s : Stage6) :
    stage6Tone (next6 (next6 (next6 s))) = stage6Tone s := by
  cases s <;> rfl

/-- Three successor steps genuinely move the stage, even though they fix its
tone: the descent is a proper quotient. -/
theorem next6_cubed_ne_id : ∃ s : Stage6, next6 (next6 (next6 s)) ≠ s :=
  ⟨.affirmed, by decide⟩

instance : Fintype Stage6 := ⟨{.affirmed, .denied, .affirmedAndDenied, .inexpressible,
  .affirmedInexpressible, .deniedInexpressible}, fun x => by cases x <;> decide⟩

/-- **Classification of the sixfold equivariant tones.**  A map `Stage6 → TriTruth`
intertwines the dialectical successor with the tone rotation if and only if it is
one of the three rotations of `stage6Tone`.  So the descent bridge is not merely
available — it is essentially unique, up to the `ℤ/3` of phase choices. -/
theorem equivariant_sixfold_tone_iff (f : Stage6 → TriTruth) :
    (∀ s, f (next6 s) = rotateTri (f s)) ↔
      ∃ k : Fin 3, f = fun s => rotateTri^[(k : Nat)] (stage6Tone s) := by
  constructor
  · intro hf
    have h1 : f .denied = rotateTri (f .affirmed) := hf .affirmed
    have h2 : f .affirmedAndDenied = rotateTri (f .denied) := hf .denied
    have h3 : f .inexpressible = rotateTri (f .affirmedAndDenied) := hf .affirmedAndDenied
    have h4 : f .affirmedInexpressible = rotateTri (f .inexpressible) := hf .inexpressible
    have h5 : f .deniedInexpressible = rotateTri (f .affirmedInexpressible) :=
      hf .affirmedInexpressible
    cases ha : f .affirmed
    · exact ⟨0, by funext s; cases s <;> simp only [h1, h2, h3, h4, h5, ha] <;> rfl⟩
    · exact ⟨1, by funext s; cases s <;> simp only [h1, h2, h3, h4, h5, ha] <;> rfl⟩
    · exact ⟨2, by funext s; cases s <;> simp only [h1, h2, h3, h4, h5, ha] <;> rfl⟩
  · rintro ⟨k, rfl⟩ s
    simp only [stage6Tone_next, ← Function.iterate_succ_apply, Function.iterate_succ_apply']

/-- Counted form of the classification: exactly three equivariant tones exist. -/
theorem card_equivariant_sixfold_tones :
    (Finset.univ.filter
      (fun f : Stage6 → TriTruth => ∀ s, f (next6 s) = rotateTri (f s))).card = 3 := by
  decide

/-! ## Impossibility for the fourfold carrier -/

/-- **No fourfold tone is rotation equivariant.**  For any `f : Stage → TriTruth`
the four-step cycle forces `f seed` to be a fixed point of `rotateTri`, which has
none. -/
theorem no_equivariant_fourfold_tone :
    ¬ ∃ f : Stage → TriTruth, ∀ s, f (next s) = rotateTri (f s) := by
  rintro ⟨f, hf⟩
  have h1 : f .counter = rotateTri (f .seed) := hf .seed
  have h2 : f .resonance = rotateTri (f .counter) := hf .counter
  have h3 : f .overflow = rotateTri (f .resonance) := hf .resonance
  have h4 : f .seed = rotateTri (f .overflow) := hf .overflow
  have hchain : f .seed = rotateTri (rotateTri (rotateTri (rotateTri (f .seed)))) := by
    conv_lhs => rw [h4, h3, h2, h1]
  have hcube : rotateTri (rotateTri (rotateTri (f .seed))) = f .seed := rotateTri_cubed _
  rw [hcube] at hchain
  exact (rotateTri_no_fixpoint (f .seed)) hchain.symm

/-- In particular the supplied `stageTone` is not equivariant, witnessed at
`overflow`. -/
theorem stageTone_not_equivariant :
    ¬ ∀ s, stageTone (next s) = rotateTri (stageTone s) := by
  intro h
  exact no_equivariant_fourfold_tone ⟨stageTone, h⟩

/-- The failure is concrete: at `overflow` the stage tone stalls instead of
rotating. -/
theorem stageTone_stalls_at_overflow :
    stageTone (next .overflow) = stageTone .overflow ∧
      rotateTri (stageTone .overflow) ≠ stageTone .overflow :=
  ⟨rfl, rotateTri_no_fixpoint _⟩

/-! ## The tetralemma surface: two routes from `Stage` to `ResidualLevel` -/

instance : Fintype Stage := ⟨{.seed, .counter, .resonance, .overflow},
  fun x => by cases x <;> decide⟩
instance : Fintype ResidualLevel := ⟨{.exact, .partialMeet, .noTypedMeet, .contradiction},
  fun x => by cases x <;> decide⟩
instance : Fintype TetralemmaPosition := ⟨{.affirmation, .negation, .both, .neither},
  fun x => by cases x <;> decide⟩

/-- Tetralemma position back to a residual level (inverse of the supplied
`residualTetralemma`). -/
def tetralemmaResidual : TetralemmaPosition → ResidualLevel
  | .affirmation => .exact
  | .both => .partialMeet
  | .neither => .noTypedMeet
  | .negation => .contradiction

/-- The supplied residual → position table is a bijection. -/
def residualTetralemmaEquiv : ResidualLevel ≃ TetralemmaPosition where
  toFun := residualTetralemma
  invFun := tetralemmaResidual
  left_inv := by decide
  right_inv := by decide

/-- Route A: `Stage → ResidualLevel` through the tetralemma position. -/
def stageResidualPosition (s : Stage) : ResidualLevel :=
  tetralemmaResidual (stageTetralemma s)

/-- Route A is a bijection: the four dialectical stages exhaust the residual
chain. -/
theorem stageResidualPosition_bijective : Function.Bijective stageResidualPosition := by
  constructor
  · intro a b h; cases a <;> cases b <;> simp_all [stageResidualPosition,
      tetralemmaResidual, stageTetralemma]
  · intro r; cases r
    · exact ⟨.seed, rfl⟩
    · exact ⟨.resonance, rfl⟩
    · exact ⟨.overflow, rfl⟩
    · exact ⟨.counter, rfl⟩

/-- **Route divergence.**  The tone route (`stageResidualTone`, supplied) and the
position route disagree; concretely they disagree at `counter`, and the
disagreement is exactly the `contradiction` level. -/
theorem residual_routes_diverge :
    stageResidualTone ≠ stageResidualPosition ∧
      stageResidualPosition .counter = ResidualLevel.contradiction ∧
      stageResidualTone .counter ≠ ResidualLevel.contradiction := by
  refine ⟨fun h => ?_, rfl, stageResidualTone_excludes_contradiction _⟩
  exact absurd (congrFun h Stage.counter) (by decide)

/-- The tone route is *not* injective, so it cannot be repaired into the
position route: two stages share a residual level. -/
theorem stageResidualTone_not_injective : ¬ Function.Injective stageResidualTone := by
  intro h
  exact absurd (h (show stageResidualTone .seed = stageResidualTone .overflow from rfl))
    (by decide)

/-- The precise cause of both failures is the same stage collapse: `seed` and
`overflow` carry the same tone. -/
theorem stage_tone_collapse :
    stageTone .seed = stageTone .overflow ∧ (Stage.seed ≠ Stage.overflow) :=
  ⟨rfl, by decide⟩

end Synthesis.DialecticTone
