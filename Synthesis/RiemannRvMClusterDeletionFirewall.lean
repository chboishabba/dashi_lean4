import Synthesis.RiemannRvMCenteredResidual
import Zeta23Bridge.LiteralWeilPrimeEvenCone

/-!
# Same-ordinate cluster deletion firewall for RvM centering

The literal zero sum is split exactly into

  clusterVec + offOrdVec,

where clusterVec contains every zero with ordinate exactly t and offOrdVec is
its complement.

The smooth RvM measure is exactly the signed Gamma channel.  Hence there are
two different centered objects:

  allCentered = cluster + off + Gamma,
  offCentered = off + Gamma.

They satisfy

  allCentered = cluster + offCentered,

so

  offCentered = allCentered - cluster.

Deleting the target-ordinate fibre is therefore NOT free.  Any cumulative RvM
estimate proved for the full zero measure minus mu controls allCentered; it
cannot be promoted to offCentered without paying the cluster term explicitly.

Moreover, on a short taper with vanishing prime vector and an even-cone pole
annihilator, the literal explicit formula gives

  evenCone(offCentered) = - evenCone(cluster).

Thus exact RvM centering is perfectly compatible with the explicit formula:
the off-centered channel is required to cancel the positive same-ordinate
cluster.  A future contradiction must prove a genuinely cluster-deleted
estimate strictly smaller than that cluster; an all-zero RvM discrepancy bound
alone cannot do so.
-/

noncomputable section

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilPrimeEvenCone

def rvMAllCenteredOrdinateVec
    (kFam : Fin 4 -> ℝ -> ℂ) (t : ℝ) :
    Fin 4 -> ℝ :=
  clusterVec kFam t + offOrdVec kFam t + gammaVec kFam

def rvMOffCenteredOrdinateVec
    (kFam : Fin 4 -> ℝ -> ℂ) (t : ℝ) :
    Fin 4 -> ℝ :=
  offOrdVec kFam t + gammaVec kFam

theorem rvMAllCentered_eq_cluster_add_offCentered
    (kFam : Fin 4 -> ℝ -> ℂ) (t : ℝ) :
    rvMAllCenteredOrdinateVec kFam t
      =
    clusterVec kFam t + rvMOffCenteredOrdinateVec kFam t := by
  unfold rvMAllCenteredOrdinateVec rvMOffCenteredOrdinateVec
  abel

theorem rvMOffCentered_eq_allCentered_sub_cluster
    (kFam : Fin 4 -> ℝ -> ℂ) (t : ℝ) :
    rvMOffCenteredOrdinateVec kFam t
      =
    rvMAllCenteredOrdinateVec kFam t - clusterVec kFam t := by
  unfold rvMAllCenteredOrdinateVec rvMOffCenteredOrdinateVec
  abel

theorem evenCone_allCentered_eq_cluster_add_offCentered
    (kFam : Fin 4 -> ℝ -> ℂ) (t : ℝ) :
    evenConeFunctional (rvMAllCenteredOrdinateVec kFam t)
      =
    evenConeFunctional (clusterVec kFam t)
      + evenConeFunctional (rvMOffCenteredOrdinateVec kFam t) := by
  rw [rvMAllCentered_eq_cluster_add_offCentered, map_add]

theorem evenCone_offCentered_eq_allCentered_sub_cluster
    (kFam : Fin 4 -> ℝ -> ℂ) (t : ℝ) :
    evenConeFunctional (rvMOffCenteredOrdinateVec kFam t)
      =
    evenConeFunctional (rvMAllCenteredOrdinateVec kFam t)
      - evenConeFunctional (clusterVec kFam t) := by
  rw [rvMOffCentered_eq_allCentered_sub_cluster, map_sub]

/--
The literal explicit formula makes the full centered zero-minus-mu vector equal
to the negative prime-plus-pole channels.
-/
theorem rvMAllCentered_eq_neg_prime_add_pole
    {kFam : Fin 4 -> ℝ -> ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i))
    (t : ℝ) :
    rvMAllCenteredOrdinateVec kFam t
      =
    - (primeVec kFam + poleVec kFam) := by
  have hbal := literalWeilOrdinateFibreBalance hk hkc t
  unfold rvMAllCenteredOrdinateVec
  apply funext
  intro i
  have hi := congrFun hbal i
  simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hi ⊢
  linarith

/--
If the prime vector vanishes and the selected linear consumer annihilates the
pole vector, the full centered zero-minus-mu channel vanishes under that
consumer.
-/
theorem evenCone_allCentered_zero_of_prime_zero_pole_kernel
    {kFam : Fin 4 -> ℝ -> ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i))
    (t : ℝ)
    (hprime : primeVec kFam = 0)
    (hpole : evenConeFunctional (poleVec kFam) = 0) :
    evenConeFunctional (rvMAllCenteredOrdinateVec kFam t) = 0 := by
  rw [rvMAllCentered_eq_neg_prime_add_pole hk hkc t,
      map_neg, map_add, hprime, map_zero, hpole]
  simp

/--
No-free-cluster-deletion identity.  Under the prime/pole firewall the centered
off-ordinate channel is exactly the negative same-ordinate cluster.
-/
theorem evenCone_offCentered_eq_neg_cluster
    {kFam : Fin 4 -> ℝ -> ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i))
    (t : ℝ)
    (hprime : primeVec kFam = 0)
    (hpole : evenConeFunctional (poleVec kFam) = 0) :
    evenConeFunctional (rvMOffCenteredOrdinateVec kFam t)
      =
    - evenConeFunctional (clusterVec kFam t) := by
  rw [evenCone_offCentered_eq_allCentered_sub_cluster,
      evenCone_allCentered_zero_of_prime_zero_pole_kernel
        hk hkc t hprime hpole]
  ring

/--
Consequently, for a positive cluster, any claimed strict absolute bound on the
off-centered channel below the cluster contradicts the literal formula.
This is the exact target theorem species a future cluster-deleted analytic
producer must inhabit.
-/
theorem contradiction_of_offCentered_abs_lt_cluster
    {kFam : Fin 4 -> ℝ -> ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i))
    (t : ℝ)
    (hprime : primeVec kFam = 0)
    (hpole : evenConeFunctional (poleVec kFam) = 0)
    (hcluster :
      0 < evenConeFunctional (clusterVec kFam t))
    (hoff :
      |evenConeFunctional (rvMOffCenteredOrdinateVec kFam t)|
        < evenConeFunctional (clusterVec kFam t)) :
    False := by
  have heq :=
    evenCone_offCentered_eq_neg_cluster
      hk hkc t hprime hpole
  rw [heq, abs_neg, abs_of_pos hcluster] at hoff
  exact (lt_irrefl _ hoff)

end Synthesis
