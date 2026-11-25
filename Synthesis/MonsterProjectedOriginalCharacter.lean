import Synthesis.MonsterActualMultiplicityCharacter
import Synthesis.MonsterCyclotomicCharacterRecognition
import Synthesis.MonsterParityProjectors

/-!
# Extract the multiplicity character from the ORIGINAL ambient action

Reuse the signed Hom entry law and trace cyclicity. The vacuum trace is an
observer of the original Conway operator, not an independent character input.
The same weighted original-word trace on a source BW model determines the
same multiplicity trace, including when the ordinary Weil trace vanishes.
Only the marked source projector expansion, original word-character match
and a nonzero selected kernel entry are inputs. Source-written; not kernel run.

Methodological donor: Hopf369 #1554 P0H, original-field spectral observers.
No mathematical identification between Hopf and Monster carriers.
Classical trace cyclicity and finite Fourier projectors retain prior authorship.
-/
namespace Synthesis.MonsterProjectedOriginalCharacter
noncomputable section
open Synthesis.MonsterWeightFrame
open Synthesis.MonsterVacuumHomEquivalence
open Synthesis.MonsterNormalizerHomAction
open Synthesis.MonsterSignedHomComposition
open Synthesis.MonsterActualMultiplicityCharacter

universe u
variable {k E S W V ι N : Type u}
variable [Field k] [Group E] [Group N] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup S] [Module k S] [FiniteDimensional k S]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (F : Frame (k := k) (S := S) (W := W) (ι := ι))
variable (A : EActionPair (k := k) (E := E) (H := Schr k ι) (W := W))
variable (L : WeylVacuumLaws F A)
variable (D : HonestInnerArrows (N := N) A)

/-- Literal inclusion and projection of the marked phase of one ambient
representation. The group algebra formula for the projector is separate. -/
structure PhaseAttachment where
  inc : W →ₗ[k] V
  res : V →ₗ[k] W
  retraction : ∀ w, res (inc w) = w
  ambient : Representation k N V
  covariant : ∀ g w, ambient g (inc w) = inc ((D.arrow g).onW w)

variable (P : PhaseAttachment (A := A) D)

def vacuumIn (i : ι) : S →ₗ[k] V :=
  P.inc.comp (F.includeWeight i)

def vacuumOut (i : ι) : V →ₗ[k] S :=
  (F.recoverWeight i).comp P.res

/-- This is the actual composite P_{i,s} on the full ambient module. -/
def vacuumProjection (i : ι) : V →ₗ[k] V :=
  (vacuumIn (A := A) (D := D) F P i).comp (vacuumOut (A := A) (D := D) F P i)

theorem vacuumRetraction (i : ι) (u : S) :
    vacuumOut (A := A) (D := D) F P i (vacuumIn (A := A) (D := D) F P i u) = u := by
  change F.recoverWeight i (P.res (P.inc (F.includeWeight i u))) = u
  rw [P.retraction, F.orthogonal, if_pos rfl]

/-- Derive the compressed actual operator, rather than postulate the
multiplicity character or identify the two carriers by their dimensions. -/
theorem compressed (g : N) (i : ι) :
    (vacuumOut (A := A) (D := D) F P i).comp
        ((P.ambient g).comp (vacuumIn (A := A) (D := D) F P i)) =
      ((D.arrow g).onH (delta i) i) • actualMultiplicity F A L D g := by
  apply LinearMap.ext
  intro u
  change F.recoverWeight i (P.res (P.ambient g (P.inc (F.includeWeight i u)))) =
    ((D.arrow g).onH (delta i) i) • vacuumArrow F F A A (D.arrow g) L L u
  rw [P.covariant, P.retraction]
  exact basis_entry F F A A (D.arrow g) L L i i u

/-- Original full-weight trace with the phase and vacuum observer inserted.
The 729-dimensional Weil trace need not be divided out. -/
theorem projectedTrace (g : N) (i : ι) :
    LinearMap.trace k V ((vacuumProjection (A := A) (D := D) F P i).comp (P.ambient g)) =
      ((D.arrow g).onH (delta i) i) * actualCharacter F A L D g := by
  calc
    _ = LinearMap.trace k V ((vacuumIn (A := A) (D := D) F P i).comp
          ((vacuumOut (A := A) (D := D) F P i).comp (P.ambient g))) := by
      rfl
    _ = LinearMap.trace k S (((vacuumOut (A := A) (D := D) F P i).comp
          (P.ambient g)).comp (vacuumIn (A := A) (D := D) F P i)) :=
      LinearMap.trace_comp_comm'
        ((vacuumOut (A := A) (D := D) F P i).comp (P.ambient g)) (vacuumIn (A := A) (D := D) F P i)
    _ = LinearMap.trace k S ((vacuumOut (A := A) (D := D) F P i).comp
          ((P.ambient g).comp (vacuumIn (A := A) (D := D) F P i))) := by
      rfl
    _ = _ := by
      simp only [compressed F A L D P, map_smul, smul_eq_mul, actualCharacter]

section OriginalWordTrace
variable {G β : Type u} [Group G] [Fintype β]
variable (rho : Representation k G V)

/-- Actual group-algebra evaluation of the projector formula. -/
def wordObserver (c : β → k) (w : β → G) : V →ₗ[k] V :=
  ∑ b, c b • rho (w b)

/-- Cyclic trace extraction on the ORIGINAL group words. -/
theorem wordObserverTrace (c : β → k) (w : β → G) (h : G) :
    LinearMap.trace k V ((wordObserver rho c w).comp (rho h)) =
      ∑ b, c b * LinearMap.trace k V (rho (w b * h)) := by
  have he : (wordObserver rho c w).comp (rho h) =
      ∑ b, c b • rho (w b * h) := by
    apply LinearMap.ext
    intro v
    simp only [wordObserver, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [map_smul, smul_eq_mul]

/-- With the original marked group words and the original phase vacuum
projector expansion, the derived actual character is fixed by the original
full ambient traces. No new multiplicity character is assumed here. -/
theorem originalCharacterWeld (c : β → k) (w : β → G)
    (h : N → G) (i : ι)
    (sameAction : ∀ g, rho (h g) = P.ambient g)
    (sameObserver : wordObserver rho c w = vacuumProjection (A := A) (D := D) F P i)
    (nonzeroEntry : ∀ g, (D.arrow g).onH (delta i) i ≠ 0)
    (a b : N → k)
    (sourceWeighted : ∀ g,
      (∑ t, c t * LinearMap.trace k V (rho (w t * h g))) =
        ((D.arrow g).onH (delta i) i) * (a g + b g)) :
    SameSourceCharacter F A L D a b := by
  intro g
  have e := wordObserverTrace rho c w (h g)
  rw [sameObserver, sameAction g, projectedTrace F A L D P] at e
  exact mul_left_cancel₀ (nonzeroEntry g) (e.trans (sourceWeighted g))

/-- The source character formula can be supplied by an independent literal
original source model with the SAME word coordinates and coefficients.
Only equality of the original word traces is required, not matrix equality
between the two ambient bases. -/
theorem weightedSourceTransfer
    {V' : Type u} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (sigma : Representation k G V') (c : β → k) (w : β → G) (h : G)
    (hmatch : ∀ t, LinearMap.trace k V (rho (w t * h)) =
      LinearMap.trace k V' (sigma (w t * h))) :
    LinearMap.trace k V ((wordObserver rho c w).comp (rho h)) =
      LinearMap.trace k V' ((wordObserver sigma c w).comp (sigma h)) := by
  rw [wordObserverTrace rho c w h, wordObserverTrace sigma c w h]
  apply Finset.sum_congr rfl
  intro t _
  rw [hmatch]

end OriginalWordTrace

/-- A phase-zero residual is constant on the marked z twists. The sum of
the nontrivial Fourier coefficients is exactly zero, so it cannot pollute
the extracted signed multiplicity character. -/
theorem zeroResidualCancellation (t r : k) (root : t^2 + t + 1 = 0) :
    r + t*r + t^2*r = 0 := by
  calc
    _ = (t^2+t+1)*r := by ring
    _ = 0 := by rw [root, zero_mul]

end
end Synthesis.MonsterProjectedOriginalCharacter
