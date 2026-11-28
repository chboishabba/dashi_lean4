import Synthesis.NavierStokesOriginalCellIntervalLowerExact

/-! Reverse-solve the literal five-channel interval certificate.
A supplied profile cell enclosure need not provide an independently
chosen coefficient a: compute its greatest common lower face.
The result still requires genuine profile-derived interval bounds
and a Hardy estimate. No fabricated CellSystemCondition.
-/
namespace Synthesis

def nsCellMargin (dl du zl zu cu wu ddu dzu H : ℝ) : ℝ :=
  min (min (dl-cu) (1-du)) (min (1/4-zu) (zl-ddu-cu*wu))-dzu*H

theorem nsCellMargin_ge_iff (dl du zl zu cu wu ddu dzu H μ : ℝ) :
    μ≤nsCellMargin dl du zl zu cu wu ddu dzu H ↔
      μ+dzu*H≤dl-cu ∧ μ+dzu*H≤1-du ∧
      μ+dzu*H≤1/4-zu ∧ μ+dzu*H≤zl-ddu-cu*wu := by
  unfold nsCellMargin
  rw [le_sub_iff_add_le]
  simp only [le_min_iff]
  tauto


theorem nsCellMargin_lower
    (d z c w dd dz x2 xc x1 xo x0 : ℝ)
    (dl du zl zu cu wu ddu dzu H μ : ℝ)
    (hd : dl≤d) (hd' : d≤du) (hz : zl≤z) (hz' : z≤zu)
    (hc : 0≤c) (hc' : c≤cu) (hw : 0≤w) (hw' : w≤wu)
    (hdd : dd≤ddu) (hdz : dz≤dzu) (hdu : 0≤dzu)
    (hHardy : x0^2≤H*(x2^2+xc^2+x1^2+xo^2))
    (hmargin : μ≤nsCellMargin dl du zl zu cu wu ddu dzu H) :
    μ*(x2^2+xc^2+x1^2+xo^2)≤nsBaseDensity d z c w dd dz x2 xc x1 xo x0 := by
  obtain ⟨h1,h2,h3,h4⟩ := (nsCellMargin_ge_iff dl du zl zu cu wu ddu dzu H μ).mp hmargin
  have h := nsBaseDensityIntervalLower d z c w dd dz x2 xc x1 xo x0
    dl du zl zu cu wu ddu dzu H (μ+dzu*H) hd hd' hz hz' hc hc' hw hw'
    hdd hdz hdu hHardy h1 h2 h3 h4
  simpa using h

/-- If a certificate has a global finite cell cover, a single margin
can be read from every row, not from sampled centre values. This
theorem consumes the actual cover membership and row proof. -/
theorem nsCellCover_lower {C X : Type*}
    (pick : X → C)
    (dl du zl zu cu wu ddu dzu H : C → ℝ) (μ : ℝ)
    (d z c w dd dz x2 xc x1 xo x0 : X → ℝ)
    (hrow : ∀ j,μ≤nsCellMargin (dl j) (du j) (zl j) (zu j) (cu j)
      (wu j) (ddu j) (dzu j) (H j))
    (hbox : ∀ x,dl (pick x)≤d x ∧ d x≤du (pick x) ∧
      zl (pick x)≤z x ∧ z x≤zu (pick x) ∧ 0≤c x ∧ c x≤cu (pick x) ∧
      0≤w x ∧ w x≤wu (pick x) ∧ dd x≤ddu (pick x) ∧
      dz x≤dzu (pick x) ∧ 0≤dzu (pick x))
    (hHardy : ∀ x,x0 x^2≤H (pick x)*(x2 x^2+xc x^2+x1 x^2+xo x^2)) :
    ∀ x,μ*(x2 x^2+xc x^2+x1 x^2+xo x^2)≤
      nsBaseDensity (d x) (z x) (c x) (w x) (dd x) (dz x)
        (x2 x) (xc x) (x1 x) (xo x) (x0 x) := by
  intro x
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := hbox x
  exact nsCellMargin_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (hHardy x) (hrow (pick x))

end Synthesis
