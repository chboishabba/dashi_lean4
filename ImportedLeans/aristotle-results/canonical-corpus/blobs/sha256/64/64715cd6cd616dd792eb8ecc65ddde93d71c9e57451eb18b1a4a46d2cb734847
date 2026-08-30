/-
# Blow-up compactness from equicontinuity alone

`BlowupCompactness.lean` extracts an ancient limit from the rescaled sequence,
but its hypothesis is a **uniform spacetime Lipschitz bound**, one constant `L`
valid for every member of the sequence.  Nothing upstream produces that bound
near a hypothetical singularity, so the extraction should not rest on it.

This file replaces that hypothesis by the weakest form under which the
Arzelà–Ascoli extraction is true: a **common modulus of continuity**, i.e.
uniform equicontinuity of the sequence.  No rate, no Lipschitz constant, and no
differentiability is assumed.

* `ClayNS.UniformlyEquicontinuous` — the hypothesis: for every `ε > 0` there is
  one `δ > 0` working for all members of the sequence at once.
* `ClayNS.uniformlyEquicontinuous_of_equiLipschitz` — equi-Lipschitz implies
  it, so the theorem below is strictly more general than the one it replaces.
* `ClayNS.exists_locally_uniform_limit_of_equicontinuous` — the extraction:
  pointwise convergence everywhere, uniform convergence on every bounded set,
  and a limit that is bounded and carries the *same* modulus, hence is
  uniformly continuous.
* `ClayNS.blowup_compactness_and_inheritance_of_equicontinuous` — the packaged
  statement, including inheritance of the normalized oscillation defect.
* `ClayNS.LocallyEquicontinuous`,
  `ClayNS.exists_locally_uniform_limit_of_locallyEquicontinuous` and
  `ClayNS.blowup_compactness_and_inheritance_of_locallyEquicontinuous` — the
  weakest form: the modulus need only be shared on each bounded set, which is
  the shape interior parabolic estimates produce.  Uniform equicontinuity is a
  special case (`ClayNS.locallyEquicontinuous_of_uniformlyEquicontinuous`).

What is still **not** claimed, exactly as before, is that the limit solves the
Navier–Stokes system: equation, local-energy and pressure inheritance are a
separate obligation and are not smuggled in here.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.BlowupCompactness

open Metric Set Filter Topology

noncomputable section

namespace ClayNS

/-- A sequence of spacetime fields is **uniformly equicontinuous** when a single
modulus of continuity works for every member: for each `ε > 0` there is a
`δ > 0`, independent of the index, such that nearby points differ by at most
`ε`. -/
def UniformlyEquicontinuous (u : ℕ → STime → E3) : Prop :=
  ∀ eps > 0, ∃ delta > 0, ∀ (k : ℕ) (z w : STime), dist z w < delta →
    ‖u k z - u k w‖ ≤ eps

/-- An equi-Lipschitz family is uniformly equicontinuous: the new hypothesis is
weaker than the one it replaces. -/
theorem uniformlyEquicontinuous_of_equiLipschitz (u : ℕ → STime → E3) {L : ℝ}
    (hL : 0 ≤ L) (hLip : ∀ k z w, ‖u k z - u k w‖ ≤ L * dist z w) :
    UniformlyEquicontinuous u := by
  intro eps heps
  refine ⟨eps / (L + 1), by positivity, fun k z w hzw => ?_⟩
  have h1 : L * dist z w ≤ L * (eps / (L + 1)) :=
    mul_le_mul_of_nonneg_left hzw.le hL
  have hL1 : (0 : ℝ) < L + 1 := by linarith
  have h2 : L * (eps / (L + 1)) ≤ eps := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hL1]
    nlinarith [heps.le]
  exact le_trans (hLip k z w) (le_trans h1 h2)

/-- A sequence is **locally equicontinuous** when a modulus of continuity works
for every member of the sequence on each bounded set, with the modulus allowed
to depend on the set.  This is what interior parabolic estimates produce:
constants that depend on the compact region, not on the index. -/
def LocallyEquicontinuous (u : ℕ → STime → E3) : Prop :=
  ∀ S : Set STime, Bornology.IsBounded S → ∀ eps > 0, ∃ delta > 0,
    ∀ (k : ℕ), ∀ z ∈ S, ∀ w ∈ S, dist z w < delta → ‖u k z - u k w‖ ≤ eps

/-- A uniformly equicontinuous family is locally equicontinuous. -/
theorem locallyEquicontinuous_of_uniformlyEquicontinuous {u : ℕ → STime → E3}
    (hEC : UniformlyEquicontinuous u) : LocallyEquicontinuous u := by
  intro _ _ eps heps
  obtain ⟨delta, hdpos, hdelta⟩ := hEC eps heps
  exact ⟨delta, hdpos, fun k z _ w _ hzw => hdelta k z w hzw⟩

/-- **Blow-up compactness from local equicontinuity.**  A uniformly bounded
sequence whose members share a modulus of continuity on each bounded set has a
subsequence converging pointwise everywhere and uniformly on every bounded set.
The limit is bounded by the same constant and shares those local moduli, hence
is continuous. -/
theorem exists_locally_uniform_limit_of_locallyEquicontinuous
    (u : ℕ → STime → E3) {K : ℝ}
    (hK : ∀ k z, ‖u k z‖ ≤ K) (hEC : LocallyEquicontinuous u) :
    ∃ (phi : ℕ → ℕ) (U : STime → E3), StrictMono phi ∧
      (∀ z, ‖U z‖ ≤ K) ∧
      (∀ S : Set STime, Bornology.IsBounded S → ∀ eps > 0, ∃ delta > 0,
        ∀ z ∈ S, ∀ w ∈ S, dist z w < delta → ‖U z - U w‖ ≤ eps) ∧
      (∀ z, Tendsto (fun k => u (phi k) z) atTop (nhds (U z))) ∧
      (∀ S : Set STime, Bornology.IsBounded S →
        TendstoUniformlyOn (fun k => u (phi k)) U atTop S) := by
  classical
  set d : ℕ → STime := TopologicalSpace.denseSeq STime with hd
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq STime
  set C : Set (ℕ → E3) := Set.univ.pi (fun _ : ℕ => Metric.closedBall (0 : E3) K) with hC
  have hCcomp : IsCompact C := isCompact_univ_pi (fun _ => isCompact_closedBall 0 K)
  have hmem : ∀ k, (fun n => u k (d n)) ∈ C := by
    intro k n _
    simpa [Metric.mem_closedBall, dist_eq_norm] using hK k (d n)
  obtain ⟨g, _hgC, phi, hphi, htend⟩ := hCcomp.isSeqCompact hmem
  have hpt : ∀ n, Tendsto (fun k => u (phi k) (d n)) atTop (nhds (g n)) := fun n =>
    (tendsto_pi_nhds.1 htend) n
  have hcauchy : ∀ z : STime, CauchySeq (fun k => u (phi k) z) := by
    intro z
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨delta, hdpos, hdelta⟩ :=
      hEC (Metric.closedBall z 1) (Metric.isBounded_closedBall) (eps / 5) (by linarith)
    set rad : ℝ := min delta 1 with hrad
    have hradpos : 0 < rad := lt_min hdpos one_pos
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hdense z rad hradpos
    have hz : z ∈ Metric.closedBall z 1 := by simp
    have hdn : d n ∈ Metric.closedBall z 1 := by
      have : dist z (d n) ≤ 1 := le_of_lt (lt_of_lt_of_le hn (min_le_right _ _))
      simpa [Metric.mem_closedBall, dist_comm] using this
    have hnd : dist z (d n) < delta := lt_of_lt_of_le hn (min_le_left _ _)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hpt n) (eps / 5) (by linarith)
    refine ⟨N, fun j hj k hk => ?_⟩
    have h1 : ‖u (phi j) z - u (phi j) (d n)‖ ≤ eps / 5 := hdelta _ z hz (d n) hdn hnd
    have h2 : ‖u (phi k) z - u (phi k) (d n)‖ ≤ eps / 5 := hdelta _ z hz (d n) hdn hnd
    have h3 : dist (u (phi j) (d n)) (g n) < eps / 5 := hN j hj
    have h4 : dist (u (phi k) (d n)) (g n) < eps / 5 := hN k hk
    have hsplit : dist (u (phi j) z) (u (phi k) z)
        ≤ ‖u (phi j) z - u (phi j) (d n)‖ + dist (u (phi j) (d n)) (g n)
          + dist (u (phi k) (d n)) (g n) + ‖u (phi k) z - u (phi k) (d n)‖ := by
      have e1 : dist (u (phi j) z) (u (phi k) z)
          ≤ dist (u (phi j) z) (u (phi j) (d n)) + dist (u (phi j) (d n)) (g n)
            + (dist (g n) (u (phi k) (d n)) + dist (u (phi k) (d n)) (u (phi k) z)) := by
        calc dist (u (phi j) z) (u (phi k) z)
            ≤ dist (u (phi j) z) (u (phi j) (d n)) + dist (u (phi j) (d n)) (u (phi k) z) :=
              dist_triangle _ _ _
          _ ≤ dist (u (phi j) z) (u (phi j) (d n))
              + (dist (u (phi j) (d n)) (g n) + dist (g n) (u (phi k) z)) := by
              have := dist_triangle (u (phi j) (d n)) (g n) (u (phi k) z)
              linarith
          _ ≤ dist (u (phi j) z) (u (phi j) (d n)) + dist (u (phi j) (d n)) (g n)
              + (dist (g n) (u (phi k) (d n)) + dist (u (phi k) (d n)) (u (phi k) z)) := by
              have := dist_triangle (g n) (u (phi k) (d n)) (u (phi k) z)
              linarith
      have e2 : dist (g n) (u (phi k) (d n)) = dist (u (phi k) (d n)) (g n) := dist_comm _ _
      have e3 : dist (u (phi j) z) (u (phi j) (d n)) = ‖u (phi j) z - u (phi j) (d n)‖ :=
        dist_eq_norm _ _
      have e4 : dist (u (phi k) (d n)) (u (phi k) z) = ‖u (phi k) z - u (phi k) (d n)‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [e2, e3, e4] at e1
      linarith
    linarith
  set U : STime → E3 := fun z => limUnder atTop (fun k => u (phi k) z) with hU
  have hlim : ∀ z, Tendsto (fun k => u (phi k) z) atTop (nhds (U z)) := fun z =>
    (hcauchy z).tendsto_limUnder
  have hUK : ∀ z, ‖U z‖ ≤ K := fun z =>
    le_of_tendsto ((hlim z).norm) (Eventually.of_forall fun k => hK _ z)
  have hUmod : ∀ S : Set STime, Bornology.IsBounded S → ∀ eps > 0, ∃ delta > 0,
      ∀ z ∈ S, ∀ w ∈ S, dist z w < delta → ‖U z - U w‖ ≤ eps := by
    intro S hS eps heps
    obtain ⟨delta, hdpos, hdelta⟩ := hEC S hS eps heps
    refine ⟨delta, hdpos, fun z hz w hw hzw => ?_⟩
    exact le_of_tendsto (((hlim z).sub (hlim w)).norm)
      (Eventually.of_forall fun k => hdelta (phi k) z hz w hw hzw)
  have huc : ∀ S : Set STime, Bornology.IsBounded S →
      TendstoUniformlyOn (fun k => u (phi k)) U atTop S := by
    intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : STime)
    set S' : Set STime := Metric.closedBall (0 : STime) (R + 1) with hS'
    have hS'b : Bornology.IsBounded S' := Metric.isBounded_closedBall
    have hSS' : S ⊆ S' := by
      refine hR.trans ?_
      exact Metric.closedBall_subset_closedBall (by linarith)
    obtain ⟨delta, hdpos, hdelta⟩ := hEC S' hS'b (eps / 5) (by linarith)
    obtain ⟨deltaU, hdUpos, hdeltaU⟩ := hUmod S' hS'b (eps / 5) (by linarith)
    set rad : ℝ := min (min delta deltaU) 1 with hrad
    have hradpos : 0 < rad := lt_min (lt_min hdpos hdUpos) one_pos
    have hSTB : TotallyBounded S :=
      (isCompact_closedBall (0 : STime) R).totallyBounded.subset hR
    obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.1 hSTB rad hradpos
    have hall : ∀ᶠ k in atTop, ∀ y ∈ t, dist (U y) (u (phi k) y) < eps / 5 := by
      refine (Filter.eventually_all_finite htfin).2 ?_
      intro y _
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hlim y) (eps / 5) (by linarith)
      refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
      rw [dist_comm]
      exact hN k hk
    filter_upwards [hall] with k hk
    intro z hz
    obtain ⟨y, hyt, hzy⟩ : ∃ y ∈ t, z ∈ Metric.ball y rad := by
      have := hcov hz
      simpa using this
    have hzy' : dist z y < rad := by simpa [Metric.mem_ball] using hzy
    have hyz' : dist y z < rad := by rwa [dist_comm] at hzy'
    have hzS' : z ∈ S' := hSS' hz
    have hyS' : y ∈ S' := by
      have hz0 : dist z (0 : STime) ≤ R := by
        have := hR hz
        simpa [Metric.mem_closedBall] using this
      have : dist y (0 : STime) ≤ R + 1 := by
        have h1 : dist y (0 : STime) ≤ dist y z + dist z (0 : STime) := dist_triangle _ _ _
        have h2 : dist y z ≤ 1 := le_of_lt (lt_of_lt_of_le hyz' (min_le_right _ _))
        linarith
      simpa [hS', Metric.mem_closedBall] using this
    have hrad1 : rad ≤ delta := le_trans (min_le_left _ _) (min_le_left _ _)
    have hrad2 : rad ≤ deltaU := le_trans (min_le_left _ _) (min_le_right _ _)
    have h1 : ‖U z - U y‖ ≤ eps / 5 :=
      hdeltaU z hzS' y hyS' (lt_of_lt_of_le hzy' hrad2)
    have h2 : dist (U y) (u (phi k) y) < eps / 5 := hk y hyt
    have h3 : ‖u (phi k) y - u (phi k) z‖ ≤ eps / 5 :=
      hdelta (phi k) y hyS' z hzS' (lt_of_lt_of_le hyz' hrad1)
    have e1 : dist (U z) (u (phi k) z)
        ≤ ‖U z - U y‖ + dist (U y) (u (phi k) y) + ‖u (phi k) y - u (phi k) z‖ := by
      calc dist (U z) (u (phi k) z)
          ≤ dist (U z) (U y) + dist (U y) (u (phi k) z) := dist_triangle _ _ _
        _ ≤ dist (U z) (U y) + (dist (U y) (u (phi k) y) + dist (u (phi k) y) (u (phi k) z)) := by
            have := dist_triangle (U y) (u (phi k) y) (u (phi k) z)
            linarith
        _ = ‖U z - U y‖ + dist (U y) (u (phi k) y) + ‖u (phi k) y - u (phi k) z‖ := by
            rw [show dist (U z) (U y) = ‖U z - U y‖ from dist_eq_norm _ _,
              show dist (u (phi k) y) (u (phi k) z) = ‖u (phi k) y - u (phi k) z‖ from
                dist_eq_norm _ _]
            ring
    linarith
  exact ⟨phi, U, hphi, hUK, hUmod, hlim, huc⟩

/-- **Blow-up compactness without a Lipschitz bound.**  A uniformly bounded,
uniformly equicontinuous sequence of spacetime fields has a subsequence that
converges pointwise everywhere and uniformly on every bounded set, to a limit
that is bounded by the same constant and carries the same modulus of
continuity. -/
theorem exists_locally_uniform_limit_of_equicontinuous
    (u : ℕ → STime → E3) {K : ℝ}
    (hK : ∀ k z, ‖u k z‖ ≤ K) (hEC : UniformlyEquicontinuous u) :
    ∃ (phi : ℕ → ℕ) (U : STime → E3), StrictMono phi ∧
      (∀ z, ‖U z‖ ≤ K) ∧
      (∀ eps > 0, ∃ delta > 0, ∀ z w : STime, dist z w < delta → ‖U z - U w‖ ≤ eps) ∧
      (∀ z, Tendsto (fun k => u (phi k) z) atTop (nhds (U z))) ∧
      (∀ S : Set STime, Bornology.IsBounded S →
        TendstoUniformlyOn (fun k => u (phi k)) U atTop S) := by
  classical
  set d : ℕ → STime := TopologicalSpace.denseSeq STime with hd
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq STime
  set C : Set (ℕ → E3) := Set.univ.pi (fun _ : ℕ => Metric.closedBall (0 : E3) K) with hC
  have hCcomp : IsCompact C := isCompact_univ_pi (fun _ => isCompact_closedBall 0 K)
  have hmem : ∀ k, (fun n => u k (d n)) ∈ C := by
    intro k n _
    simpa [Metric.mem_closedBall, dist_eq_norm] using hK k (d n)
  obtain ⟨g, _hgC, phi, hphi, htend⟩ := hCcomp.isSeqCompact hmem
  have hpt : ∀ n, Tendsto (fun k => u (phi k) (d n)) atTop (nhds (g n)) := fun n =>
    (tendsto_pi_nhds.1 htend) n
  -- the modulus upgrades convergence on the dense set to a Cauchy property everywhere
  have hcauchy : ∀ z : STime, CauchySeq (fun k => u (phi k) z) := by
    intro z
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨delta, hdpos, hdelta⟩ := hEC (eps / 5) (by linarith)
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hdense z delta hdpos
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hpt n) (eps / 5) (by linarith)
    refine ⟨N, fun j hj k hk => ?_⟩
    have h1 : ‖u (phi j) z - u (phi j) (d n)‖ ≤ eps / 5 := hdelta _ _ _ hn
    have h2 : ‖u (phi k) z - u (phi k) (d n)‖ ≤ eps / 5 := hdelta _ _ _ hn
    have h3 : dist (u (phi j) (d n)) (g n) < eps / 5 := hN j hj
    have h4 : dist (u (phi k) (d n)) (g n) < eps / 5 := hN k hk
    have hsplit : dist (u (phi j) z) (u (phi k) z)
        ≤ ‖u (phi j) z - u (phi j) (d n)‖ + dist (u (phi j) (d n)) (g n)
          + dist (u (phi k) (d n)) (g n) + ‖u (phi k) z - u (phi k) (d n)‖ := by
      have e1 : dist (u (phi j) z) (u (phi k) z)
          ≤ dist (u (phi j) z) (u (phi j) (d n)) + dist (u (phi j) (d n)) (g n)
            + (dist (g n) (u (phi k) (d n)) + dist (u (phi k) (d n)) (u (phi k) z)) := by
        calc dist (u (phi j) z) (u (phi k) z)
            ≤ dist (u (phi j) z) (u (phi j) (d n)) + dist (u (phi j) (d n)) (u (phi k) z) :=
              dist_triangle _ _ _
          _ ≤ dist (u (phi j) z) (u (phi j) (d n))
              + (dist (u (phi j) (d n)) (g n) + dist (g n) (u (phi k) z)) := by
              have := dist_triangle (u (phi j) (d n)) (g n) (u (phi k) z)
              linarith
          _ ≤ dist (u (phi j) z) (u (phi j) (d n)) + dist (u (phi j) (d n)) (g n)
              + (dist (g n) (u (phi k) (d n)) + dist (u (phi k) (d n)) (u (phi k) z)) := by
              have := dist_triangle (g n) (u (phi k) (d n)) (u (phi k) z)
              linarith
      have e2 : dist (g n) (u (phi k) (d n)) = dist (u (phi k) (d n)) (g n) := dist_comm _ _
      have e3 : dist (u (phi j) z) (u (phi j) (d n)) = ‖u (phi j) z - u (phi j) (d n)‖ :=
        dist_eq_norm _ _
      have e4 : dist (u (phi k) (d n)) (u (phi k) z) = ‖u (phi k) z - u (phi k) (d n)‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [e2, e3, e4] at e1
      linarith
    linarith
  set U : STime → E3 := fun z => limUnder atTop (fun k => u (phi k) z) with hU
  have hlim : ∀ z, Tendsto (fun k => u (phi k) z) atTop (nhds (U z)) := fun z =>
    (hcauchy z).tendsto_limUnder
  have hUK : ∀ z, ‖U z‖ ≤ K := fun z =>
    le_of_tendsto ((hlim z).norm) (Eventually.of_forall fun k => hK _ z)
  have hUmod : ∀ eps > 0, ∃ delta > 0, ∀ z w : STime, dist z w < delta →
      ‖U z - U w‖ ≤ eps := by
    intro eps heps
    obtain ⟨delta, hdpos, hdelta⟩ := hEC eps heps
    refine ⟨delta, hdpos, fun z w hzw => ?_⟩
    exact le_of_tendsto (((hlim z).sub (hlim w)).norm)
      (Eventually.of_forall fun k => hdelta (phi k) z w hzw)
  have huc : ∀ S : Set STime, Bornology.IsBounded S →
      TendstoUniformlyOn (fun k => u (phi k)) U atTop S := by
    intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    obtain ⟨delta, hdpos, hdelta⟩ := hEC (eps / 5) (by linarith)
    obtain ⟨deltaU, hdUpos, hdeltaU⟩ := hUmod (eps / 5) (by linarith)
    set rad : ℝ := min delta deltaU with hrad
    have hradpos : 0 < rad := lt_min hdpos hdUpos
    have hSTB : TotallyBounded S := by
      obtain ⟨r, hr⟩ := hS.subset_closedBall (0 : STime)
      exact (isCompact_closedBall (0 : STime) r).totallyBounded.subset hr
    obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.1 hSTB rad hradpos
    have hall : ∀ᶠ k in atTop, ∀ y ∈ t, dist (U y) (u (phi k) y) < eps / 5 := by
      refine (Filter.eventually_all_finite htfin).2 ?_
      intro y _
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hlim y) (eps / 5) (by linarith)
      refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
      rw [dist_comm]
      exact hN k hk
    filter_upwards [hall] with k hk
    intro z hz
    obtain ⟨y, hyt, hzy⟩ : ∃ y ∈ t, z ∈ Metric.ball y rad := by
      have := hcov hz
      simpa using this
    have hzy' : dist z y < rad := by simpa [Metric.mem_ball] using hzy
    have hyz' : dist y z < rad := by rwa [dist_comm] at hzy'
    have h1 : ‖U z - U y‖ ≤ eps / 5 :=
      hdeltaU z y (lt_of_lt_of_le hzy' (min_le_right _ _))
    have h2 : dist (U y) (u (phi k) y) < eps / 5 := hk y hyt
    have h3 : ‖u (phi k) y - u (phi k) z‖ ≤ eps / 5 :=
      hdelta (phi k) y z (lt_of_lt_of_le hyz' (min_le_left _ _))
    have e1 : dist (U z) (u (phi k) z)
        ≤ ‖U z - U y‖ + dist (U y) (u (phi k) y) + ‖u (phi k) y - u (phi k) z‖ := by
      calc dist (U z) (u (phi k) z)
          ≤ dist (U z) (U y) + dist (U y) (u (phi k) z) := dist_triangle _ _ _
        _ ≤ dist (U z) (U y) + (dist (U y) (u (phi k) y) + dist (u (phi k) y) (u (phi k) z)) := by
            have := dist_triangle (U y) (u (phi k) y) (u (phi k) z)
            linarith
        _ = ‖U z - U y‖ + dist (U y) (u (phi k) y) + ‖u (phi k) y - u (phi k) z‖ := by
            rw [show dist (U z) (U y) = ‖U z - U y‖ from dist_eq_norm _ _,
              show dist (u (phi k) y) (u (phi k) z) = ‖u (phi k) y - u (phi k) z‖ from
                dist_eq_norm _ _]
            ring
    linarith
  exact ⟨phi, U, hphi, hUK, hUmod, hlim, huc⟩

/-- **Compactness and inheritance from equicontinuity, packaged.**  Same
conclusion as `ClayNS.blowup_compactness_and_inheritance`, but the sequence is
only assumed uniformly bounded and uniformly equicontinuous.  The limit is
bounded, uniformly continuous, and inherits the normalized oscillation defect
on every bounded set on which the sequence carries it. -/
theorem blowup_compactness_and_inheritance_of_equicontinuous
    (u : ℕ → STime → E3) {K : ℝ}
    (hK : ∀ k z, ‖u k z‖ ≤ K) (hEC : UniformlyEquicontinuous u)
    (S : Set STime) (hS : Bornology.IsBounded S) {c0 : ℝ} :
    ∃ (phi : ℕ → ℕ) (U : STime → E3), StrictMono phi ∧
      (∀ z, ‖U z‖ ≤ K) ∧ UniformContinuous U ∧ Continuous U ∧
      (∀ z, Tendsto (fun k => u (phi k) z) atTop (nhds (U z))) ∧
      ((∀ k, c0 ≤ oscOn (u (phi k)) S) → c0 ≤ oscOn U S) := by
  obtain ⟨phi, U, hphi, hUK, hUmod, hlim, huc⟩ :=
    exists_locally_uniform_limit_of_equicontinuous u hK hEC
  have hUC : UniformContinuous U := by
    rw [Metric.uniformContinuous_iff]
    intro eps heps
    obtain ⟨delta, hdpos, hdelta⟩ := hUmod (eps / 2) (by linarith)
    refine ⟨delta, hdpos, fun {z w} hzw => ?_⟩
    have := hdelta z w hzw
    rw [dist_eq_norm]
    linarith
  refine ⟨phi, U, hphi, hUK, hUC, hUC.continuous, hlim, ?_⟩
  intro hdef
  have hbU : Bornology.IsBounded (U '' S) := by
    refine (Metric.isBounded_closedBall (x := (0:E3)) (r := K)).subset ?_
    rintro p ⟨z, _, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hUK z
  exact oscOn_ge_of_uniform_limit hbU
    (tendstoUniformlyOn_iff_forall_eps (huc S hS)) hdef

/-- **Compactness and inheritance from local equicontinuity, packaged.**  The
weakest hypothesis of the three: the members of the sequence need only share a
modulus of continuity on each bounded set.  The limit is bounded, continuous,
and inherits the normalized oscillation defect. -/
theorem blowup_compactness_and_inheritance_of_locallyEquicontinuous
    (u : ℕ → STime → E3) {K : ℝ}
    (hK : ∀ k z, ‖u k z‖ ≤ K) (hEC : LocallyEquicontinuous u)
    (S : Set STime) (hS : Bornology.IsBounded S) {c0 : ℝ} :
    ∃ (phi : ℕ → ℕ) (U : STime → E3), StrictMono phi ∧
      (∀ z, ‖U z‖ ≤ K) ∧ Continuous U ∧
      (∀ z, Tendsto (fun k => u (phi k) z) atTop (nhds (U z))) ∧
      ((∀ k, c0 ≤ oscOn (u (phi k)) S) → c0 ≤ oscOn U S) := by
  obtain ⟨phi, U, hphi, hUK, hUmod, hlim, huc⟩ :=
    exists_locally_uniform_limit_of_locallyEquicontinuous u hK hEC
  have hUcont : Continuous U := by
    rw [Metric.continuous_iff]
    intro z eps heps
    obtain ⟨delta, hdpos, hdelta⟩ :=
      hUmod (Metric.closedBall z 1) Metric.isBounded_closedBall (eps / 2) (by linarith)
    refine ⟨min delta 1, lt_min hdpos one_pos, fun w hw => ?_⟩
    have hwz : dist w z < delta := lt_of_lt_of_le hw (min_le_left _ _)
    have hw1 : w ∈ Metric.closedBall z 1 := by
      have : dist w z ≤ 1 := le_of_lt (lt_of_lt_of_le hw (min_le_right _ _))
      simpa [Metric.mem_closedBall] using this
    have hz1 : z ∈ Metric.closedBall z 1 := by simp
    have := hdelta w hw1 z hz1 hwz
    rw [dist_eq_norm]
    linarith
  refine ⟨phi, U, hphi, hUK, hUcont, hlim, ?_⟩
  intro hdef
  have hbU : Bornology.IsBounded (U '' S) := by
    refine (Metric.isBounded_closedBall (x := (0:E3)) (r := K)).subset ?_
    rintro p ⟨z, _, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hUK z
  exact oscOn_ge_of_uniform_limit hbU
    (tendstoUniformlyOn_iff_forall_eps (huc S hS)) hdef

end ClayNS
