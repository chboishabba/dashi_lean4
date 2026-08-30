import Mathlib
import RequestProject.GF27
import RequestProject.KernelReflection
import RequestProject.SvgCore

/-!
# Pictures of the two themes

This file draws the objects studied in this project.  The pictures are *generated from Lean
data*, and the data is checked, by kernel computation (`decide`), against the formal
statements proved elsewhere in the project.  Running

```
lake env lean --run scripts/GenerateSvg.lean
```

writes the three images into `svg/`:

* `svg/frobenius-orbits.svg` — the 27 elements of `GF(27)`, partitioned into the orbits of the
  Frobenius endomorphism `x ↦ x³`.  The three fixed points form the prime subfield
  `𝔽₃`; every other orbit is a 3-cycle.
* `svg/frobenius-norm-retraction.svg` — the orbit product (norm) `N(x) = x · x³ · x⁹ = x¹³`,
  drawn as a map `GF(27) → 𝔽₃`: two fibres of 13 nonzero elements over `1` and `2`, and
  `0 ↦ 0`.  On `𝔽₃` it is the identity, so it is a retraction.
* `svg/center-retraction.svg` — the retraction picture `Z(G) ↪ G → Z(G)` for the group theme,
  together with the families classified in this project.

## The data that is verified

* `GF27Viz.orbits` is the list of Frobenius orbits used for the first picture.  It is proved
  to be closed under `x ↦ x³` (`GF27Viz.orbits_frobenius_closed`), to contain every element of
  `GF(27)` exactly once (`GF27Viz.orbits_cover`), to consist of 11 orbits of sizes 1 and 3
  (`GF27Viz.orbits_length`, `GF27Viz.orbit_length_eq`), and its singletons are exactly the
  prime subfield (`GF27Viz.orbit_singleton_iff`, `GF27Viz.singletons_eq_primeSubfield`).
* `GF27Viz.normFibre a` is the fibre of `x ↦ x¹³` used for the second picture; the fibres over
  `0, 1, 2` are proved to have `1, 13, 13` elements and to exhaust `GF(27)`
  (`GF27Viz.normFibre_card`, `GF27Viz.mem_normFibre_iff`), and `x ↦ x¹³` is proved to fix
  `𝔽₃` pointwise, which is exactly the retraction property.
-/

namespace GF27Viz

open GF27 SvgCore FrobeniusPrimeSubfield

/-! ### The Frobenius orbit data -/

/-- The Frobenius endomorphism of `GF(27)`, in kernel-friendly form. -/
def frob (x : GF27) : GF27 := pow' x 3

/-- The second Frobenius iterate `x ↦ x^(3²)`. -/
def frob2 (x : GF27) : GF27 := pow' x 9

theorem frob_eq (x : GF27) : frob x = x ^ 3 := pow'_eq x 3
theorem frob2_eq (x : GF27) : frob2 x = x ^ 9 := pow'_eq x 9

/-- The Frobenius orbit of `x`, listed without repetitions. -/
def orbitOf (x : GF27) : List GF27 := [x, frob x, frob2 x].dedup

/-- Position of an element in the fixed enumeration of `GF(27)`; used only to pick a
canonical representative of each orbit. -/
def idx (x : GF27) : ℕ := enum.findIdx (· == x)

/-- The representative of an orbit: the element occurring first in `enum`. -/
def isRep (x : GF27) : Bool := decide (idx x ≤ idx (frob x)) && decide (idx x ≤ idx (frob2 x))

/-- One representative per Frobenius orbit. -/
def orbitReps : List GF27 := enum.filter isRep

/-- The partition of `GF(27)` into Frobenius orbits — the data drawn in
`svg/frobenius-orbits.svg`. -/
def orbits : List (List GF27) := orbitReps.map orbitOf

/-- The picture shows 11 orbits. -/
theorem orbits_length : orbits.length = 11 := by decide +kernel

/-- Every element of `GF(27)` occurs in exactly one of the drawn orbits, exactly once. -/
theorem orbits_cover (x : GF27) : orbits.flatten.count x = 1 := by
  revert x; decide +kernel

/-- Each drawn orbit really is closed under the Frobenius `x ↦ x³`. -/
theorem orbits_frobenius_closed : ∀ o ∈ orbits, ∀ x ∈ o, x ^ 3 ∈ o := by
  have : ∀ o ∈ orbits, ∀ x ∈ o, frob x ∈ o := by decide +kernel
  intro o ho x hx
  simpa [frob_eq] using this o ho x hx

/-- Every orbit has 1 or 3 elements. -/
theorem orbit_length_eq (x : GF27) : (orbitOf x).length = 1 ∨ (orbitOf x).length = 3 := by
  revert x; decide +kernel

/-- **A drawn orbit is a single point exactly on the prime subfield.** -/
theorem orbit_singleton_iff (x : GF27) : (orbitOf x).length = 1 ↔ x ^ 3 = x := by
  constructor
  · intro hx
    have h : ∀ y : GF27, (orbitOf y).length = 1 → frob y = y := by decide +kernel
    simpa [frob_eq] using h x hx
  · intro hx
    have h : ∀ y : GF27, frob y = y → (orbitOf y).length = 1 := by decide +kernel
    exact h x (by simpa [frob_eq] using hx)

/-- The three highlighted (fixed) points of the picture are exactly the prime subfield
`𝔽₃ = {0, 1, 2}`, i.e. the image of `ZMod 3 → GF(27)`. -/
theorem singletons_eq_primeSubfield :
    {x : GF27 | (orbitOf x).length = 1} = Set.range (primeSubfieldHom GF27 3) := by
  rw [range_primeSubfieldHom]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [orbit_singleton_iff]
  exact pow_three_eq_self_iff x

/-! ### The norm (orbit product) data -/

/-- The orbit product `N(x) = x · x³ · x⁹ = x¹³`, in kernel-friendly form. -/
def norm13 (x : GF27) : GF27 := pow' x 13

theorem norm13_eq (x : GF27) : norm13 x = x ^ 13 := pow'_eq x 13

theorem norm13_eq_frobNorm (x : GF27) : norm13 x = frobNorm 3 3 x := by
  rw [norm13_eq, frobNorm_eq_pow_thirteen]

/-- The fibre of the orbit product over `a` — the fans drawn in
`svg/frobenius-norm-retraction.svg`. -/
def normFibre (a : GF27) : List GF27 := enum.filter (fun x => norm13 x == a)

theorem mem_normFibre_iff (a x : GF27) : x ∈ normFibre a ↔ x ^ 13 = a := by
  simp [normFibre, mem_enum, norm13_eq]

/-- The three fibres drawn have `1`, `13` and `13` elements. -/
theorem normFibre_card :
    (normFibre 0).length = 1 ∧ (normFibre 1).length = 13 ∧ (normFibre 2).length = 13 := by
  decide +kernel

/-- The drawn fibres exhaust `GF(27)`: the orbit product always lands in `𝔽₃`. -/
theorem normFibres_cover (x : GF27) :
    x ∈ normFibre 0 ∨ x ∈ normFibre 1 ∨ x ∈ normFibre 2 := by
  rcases norm_mem_prime x with h | h | h
  · exact Or.inl ((mem_normFibre_iff _ _).2 h)
  · exact Or.inr (Or.inl ((mem_normFibre_iff _ _).2 h))
  · exact Or.inr (Or.inr ((mem_normFibre_iff _ _).2 h))

/-- The retraction property drawn as the three gold arrows `a ↦ a`: the orbit product fixes
the prime subfield pointwise. -/
theorem norm13_fixes_prime : norm13 0 = 0 ∧ norm13 1 = 1 ∧ norm13 2 = 2 := by
  decide +kernel

/-! ### Rendering -/

/-- The three digits `c₂c₁c₀` of `x = c₀ + c₁t + c₂t²`; the compact node label. -/
def code (x : GF27) : String :=
  toString x.c2.val ++ toString x.c1.val ++ toString x.c0.val

/-- `x = c₀ + c₁t + c₂t²` written as a polynomial in `t`. -/
def label (x : GF27) : String :=
  let mono (c : ℕ) (s : String) : List String :=
    if c == 0 then [] else if s == "" then [toString c]
    else if c == 1 then [s] else [toString c ++ s]
  let parts := mono x.c2.val "t²" ++ mono x.c1.val "t" ++ mono x.c0.val ""
  if parts.isEmpty then "0" else String.intercalate " + " parts

private def pi : Float := 3.14159265358979

private def nodeR : Float := 17.0

/-- Fill colour of a node, according to the value of the orbit product on it. -/
private def fillOf (x : GF27) : String :=
  if norm13 x == 1 then "url(#fill-blue)" else if norm13 x == 2 then "url(#fill-pink)"
  else "url(#fill-slate)"

private def strokeOf (x : GF27) : String :=
  if norm13 x == 1 then "#1d4ed8" else if norm13 x == 2 then "#be185d" else "#334155"

private def arrowOf (x : GF27) : String :=
  if norm13 x == 1 then "blue" else if norm13 x == 2 then "pink" else "slate"

private def node (x : GF27) (cx cy : Float) : List String :=
  [nodeGroup
    [circle cx cy nodeR (fillOf x) (strokeOf x) 1.6 "class=\"pop\"",
     textMid cx cy (code x) 12.0 "#0f172a" "middle" "bold"]]

/-- The orbits of size 3, in the order in which they are drawn around the circle. -/
def bigOrbits : List (List GF27) := orbits.filter (fun o => o.length == 3)

/-- The fixed points, i.e. the orbits of size 1. -/
def fixedPoints : List GF27 := (orbits.filter (fun o => o.length == 1)).flatten

theorem bigOrbits_length : bigOrbits.length = 8 := by decide +kernel

theorem fixedPoints_eq : fixedPoints = [0, 1, 2] := by decide +kernel

/-- Drawing of one 3-element orbit, centred at `(ox, oy)`. -/
private def drawOrbit (o : List GF27) (ox oy : Float) : List String :=
  let vertex (j : Nat) : Float × Float :=
    let b := -pi / 2.0 + j.toFloat * (2.0 * pi / 3.0)
    (ox + 56.0 * Float.cos b, oy + 56.0 * Float.sin b)
  let col := match o.head? with
    | some x => arrowOf x
    | none => "slate"
  let strokeCol := match o.head? with
    | some x => strokeOf x
    | none => "#334155"
  let normLabel := match o.head? with
    | some x => "N = " ++ label (norm13 x)
    | none => ""
  let edges := (List.range 3).flatMap fun j =>
    let (x1, y1) := vertex j
    let (x2, y2) := vertex ((j + 1) % 3)
    let d := curveD x1 y1 x2 y2 (nodeR + 3.0) (nodeR + 7.0) 9.0
    [path d strokeCol 1.5 col, comet d strokeCol 4.0 2.4 (j.toFloat * 0.8) 90.0]
  let nodes := (o.zipIdx).flatMap fun (x, j) =>
    let (vx, vy) := vertex j
    node x vx vy
  edges ++ nodes ++ [textMid ox oy normLabel 11.0 "#64748b" "middle" "normal"]

/-- The first picture: the Frobenius orbits of `GF(27)`. -/
def orbitsSvg : String :=
  let w := 1000.0
  let h := 940.0
  let cx := 500.0
  let cy := 500.0
  let bigR := 280.0
  let title :=
    [ text (w / 2.0) 46.0 "Frobenius orbits in GF(27) = 𝔽₃[t]/(t³ − t − 1)" 26.0 "url(#ink)"
        "middle" "bold",
      text (w / 2.0) 74.0
        "each element is joined to its Frobenius image x ↦ x³; a node abc means a·t² + b·t + c"
        14.0 "#475569",
      text (w / 2.0) 96.0
        "27 = 3 fixed points (the prime subfield 𝔽₃) + 8 orbits of length 3" 14.0 "#475569" ]
  let ring := (bigOrbits.zipIdx).flatMap fun (o, i) =>
    let a := -pi / 2.0 + i.toFloat * (2.0 * pi / 8.0)
    drawOrbit o (cx + bigR * Float.cos a) (cy + bigR * Float.sin a)
  let panelW := 360.0
  let panelH := 150.0
  let panel :=
    [ card (cx - panelW / 2.0) (cy - 62.0) panelW panelH 18.0 "#fffbeb" "#b45309" 2.0,
      text cx (cy - 34.0) "𝔽₃ = { x : x³ = x }  —  the fixed points" 15.0 "#92400e"
        "middle" "bold" ] ++
    ((fixedPoints.zipIdx).flatMap fun (x, j) =>
      let nx := cx + (j.toFloat - 1.0) * 100.0
      let ny := cy + 6.0
      [ pulse nx ny (nodeR + 8.0) "#fbbf24" 2.8 (j.toFloat * 0.6),
        selfLoop nx ny nodeR "#b45309" "gold" ] ++
      [ nodeGroup
          [ circle nx ny nodeR "url(#fill-gold)" "#b45309" 1.8 "class=\"pop\"",
            textMid nx ny (code x) 12.0 "#0f172a" "middle" "bold" ],
        textMid nx (ny + 56.0) ("x = " ++ label x) 12.0 "#92400e" "middle" "normal" ])
  let legendY := h - 46.0
  let legend :=
    [ line 70.0 (legendY - 4.0) 100.0 (legendY - 4.0) "#1d4ed8" 1.6 "blue",
      text 108.0 legendY "orbit with norm N(x) = x·x³·x⁹ = 1" 13.0 "#475569" "start",
      line 400.0 (legendY - 4.0) 430.0 (legendY - 4.0) "#be185d" 1.6 "pink",
      text 438.0 legendY "orbit with norm N(x) = 2" 13.0 "#475569" "start",
      circle 700.0 (legendY - 4.0) 10.0 "url(#fill-gold)" "#b45309" 1.8,
      text 716.0 legendY "fixed point: the whole orbit is {x} ⊆ 𝔽₃" 13.0 "#475569" "start" ]
  document w h (title ++ ring ++ panel ++ legend)

/-- The second picture: the orbit product as a retraction `GF(27) → 𝔽₃`. -/
def normSvg : String :=
  let w := 980.0
  let h := 920.0
  let leftX := 300.0
  let rightX := 760.0
  let top := 180.0
  let step := 25.0
  let title :=
    [ text (w / 2.0) 46.0 "The orbit product N(x) = x · x³ · x⁹ = x¹³ : GF(27) → 𝔽₃" 25.0
        "url(#ink)" "middle" "bold",
      text (w / 2.0) 74.0
        "the product over a Frobenius orbit is Frobenius-fixed, so it lands in 𝔽₃"
        14.0 "#475569",
      text (w / 2.0) 96.0
        "and it is the identity on 𝔽₃ — hence a retraction of GF(27)ˣ onto 𝔽₃ˣ = {1, 2}"
        14.0 "#475569" ]
  let groups : List (GF27 × String × String) :=
    [(0, "#334155", "slate"), (1, "#1d4ed8", "blue"), (2, "#be185d", "pink")]
  let rows : List (GF27 × GF27) :=
    groups.flatMap fun (a, _, _) => (normFibre a).map fun x => (x, a)
  let yOf (i : Nat) : Float := top + i.toFloat * step
  let targetY (a : GF27) : Float :=
    let idxs := (rows.zipIdx).filterMap fun ((_, b), i) => if b == a then some i else none
    match idxs with
    | [] => top
    | l => (l.foldl (fun s i => s + yOf i) 0.0) / l.length.toFloat
  let edges := (rows.zipIdx).flatMap fun ((x, a), i) =>
    let col := match groups.find? (fun (b, _, _) => b == a) with
      | some (_, c, _) => c
      | none => "#334155"
    let mk := match groups.find? (fun (b, _, _) => b == a) with
      | some (_, _, m) => m
      | none => "slate"
    let fixedPt := x == a
    let d := curveD leftX (yOf i) rightX (targetY a) 10.0 26.0 (if fixedPt then 0.0 else 14.0)
    [ path d (if fixedPt then "#b45309" else col) (if fixedPt then 2.4 else 1.0)
        (if fixedPt then "gold" else mk) "none"
        (if fixedPt then "" else "opacity=\"0.55\"") ] ++
    (if fixedPt then [comet d "#fbbf24" 5.0 2.6 (i.toFloat * 0.5) 200.0] else [])
  let sources := (rows.zipIdx).flatMap fun ((x, _), i) =>
    [ circle leftX (yOf i) 7.0 (fillOf x) (strokeOf x) 1.4 "class=\"pop\"",
      textMid (leftX - 16.0) (yOf i) (label x) 12.5 "#0f172a" "end" "normal" ]
  let targets := groups.flatMap fun (a, col, _) =>
    let n := (normFibre a).length
    [ pulse rightX (targetY a) 30.0 "#fbbf24" 3.0 (n.toFloat * 0.1),
      circle rightX (targetY a) 22.0 "url(#fill-gold)" "#b45309" 2.0 "class=\"pop\"",
      textMid rightX (targetY a) (label a) 15.0 "#0f172a" "middle" "bold",
      textMid (rightX + 34.0) (targetY a)
        ("fibre of " ++ toString n ++ " element" ++ (if n == 1 then "" else "s")) 13.0 col
        "start" "normal" ]
  let panel :=
    [ rect (rightX - 60.0) (top - 50.0) 260.0 (25.0 * 27.0 + 50.0) 16.0 "#fffbeb99" "#b45309"
        1.6 "7 5",
      text (rightX - 46.0) (top - 28.0) "𝔽₃ = image of N" 14.0 "#92400e" "start" "bold" ]
  let legend :=
    [ line 70.0 (h - 54.0) 104.0 (h - 54.0) "#b45309" 2.4 "gold",
      text 112.0 (h - 50.0) "N(a) = a : the three gold arrows are the retraction fixing 𝔽₃"
        13.0 "#475569" "start",
      text 70.0 (h - 26.0)
        "all other arrows collapse a 13-element fibre onto a single element of 𝔽₃" 13.0
        "#475569" "start" ]
  document w h (title ++ panel ++ edges ++ sources ++ targets ++ legend)

end GF27Viz

namespace CenterViz

open SvgCore

/-- One row of the table of families: name, whether it retracts onto its center, and the
Lean theorem in this project that says so. -/
structure Row where
  family : String
  verdict : Bool
  note : String
  thm : String

def rows : List Row :=
  [ ⟨"G abelian", true, "r = id, Z(G) = G", "hasCenterRetraction_of_commGroup"⟩,
    ⟨"Z(G) = 1 (centerless)", true, "r = 1, trivially", "hasCenterRetraction_of_center_eq_bot"⟩,
    ⟨"Sₙ, Aₙ", true, "centerless for n ≥ 3", "hasCenterRetraction_perm_fin"⟩,
    ⟨"G × H", true, "iff both factors do", "hasCenterRetraction_prod_iff"⟩,
    ⟨"Π i, Gᵢ", true, "iff every factor does", "hasCenterRetraction_pi_iff"⟩,
    ⟨"Dₙ, 4 ∤ n", true, "parity-of-rotation retraction", "hasCenterRetraction_dihedral_iff"⟩,
    ⟨"Dₙ, 4 ∣ n", false, "central half-turn is a commutator",
      "not_hasCenterRetraction_dihedral_of_four_dvd"⟩,
    ⟨"Q₄ₙ (dicyclic), n ≥ 2", false, "central element is a square of a non-central one",
      "hasCenterRetraction_quaternion_iff"⟩,
    ⟨"nonabelian nilpotent G", false, "Z(G) meets [G,G] nontrivially",
      "not_hasCenterRetraction_of_nilpotent"⟩,
    ⟨"GL₂(R), 2 ≠ 0 in R", false, "−I is a commutator", "not_hasCenterRetraction"⟩ ]

/-- The third picture: the retraction diagram and the classification table. -/
def centerSvg : String :=
  let w := 1180.0
  let h := 800.0
  let title :=
    [ text (w / 2.0) 46.0 "Retraction onto the center: Z(G) ↪ G → Z(G)" 26.0 "url(#ink)"
        "middle" "bold",
      text (w / 2.0) 74.0
        "a group homomorphism r : G → Z(G) with r ∘ ι = id — the exact analogue of x ↦ x¹³"
        14.0 "#475569" ]
  let dy := 170.0
  let zx := 300.0
  let gx := 590.0
  let z2x := 880.0
  let diagram :=
    [ pulse zx dy 62.0 "#fbbf24" 3.2 0.0,
      circle zx dy 52.0 "url(#fill-gold)" "#b45309" 2.0 "class=\"pop\"",
      textMid zx dy "Z(G)" 18.0 "#0f172a" "middle" "bold",
      circle gx dy 62.0 "url(#fill-violet)" "#4338ca" 2.0 "class=\"pop\"",
      textMid gx dy "G" 20.0 "#0f172a" "middle" "bold",
      pulse z2x dy 62.0 "#fbbf24" 3.2 1.6,
      circle z2x dy 52.0 "url(#fill-gold)" "#b45309" 2.0 "class=\"pop\"",
      textMid z2x dy "Z(G)" 18.0 "#0f172a" "middle" "bold",
      arrow zx dy gx dy 56.0 68.0 "#334155" "slate" 2.0,
      comet (curveD zx dy gx dy 56.0 68.0 0.0) "#0ea5e9" 5.0 2.4 0.0 120.0,
      textMid ((zx + gx) / 2.0) (dy - 16.0) "ι" 17.0 "#334155" "middle" "bold",
      arrow gx dy z2x dy 66.0 58.0 "#b45309" "gold" 2.0,
      comet (curveD gx dy z2x dy 66.0 58.0 0.0) "#fbbf24" 5.0 2.4 1.2 120.0,
      textMid ((gx + z2x) / 2.0) (dy - 16.0) "r" 17.0 "#b45309" "middle" "bold",
      curve zx (dy + 52.0) z2x (dy + 52.0) 8.0 12.0 96.0 "#047857" "green" 2.0,
      textMid ((zx + z2x) / 2.0) (dy + 148.0) "r ∘ ι = id" 16.0 "#047857" "middle" "bold",
      textMid (w / 2.0) (dy + 190.0)
        "equivalently: Z(G) is a direct factor, G ≃ ker r × Z(G) with ker r centerless"
        14.0 "#475569" "middle" "normal" ]
  let tableTop := dy + 230.0
  let rowH := 34.0
  let header :=
    [ card 70.0 tableTop (w - 140.0) (rowH * (rows.length.toFloat + 1.0)) 10.0 "#ffffff"
        "#e2e8f0" 1.0,
      rect 70.0 tableTop (w - 140.0) rowH 8.0 "#eef2ff" "#94a3b8" 1.2,
      text 92.0 (tableTop + 22.0) "family" 13.5 "#0f172a" "start" "bold",
      text 330.0 (tableTop + 22.0) "retracts onto Z(G)?" 13.5 "#0f172a" "start" "bold",
      text 500.0 (tableTop + 22.0) "reason" 13.5 "#0f172a" "start" "bold",
      text 820.0 (tableTop + 22.0) "theorem in this project" 13.5 "#0f172a" "start" "bold" ]
  let body := (rows.zipIdx).flatMap fun (r, i) =>
    let y := tableTop + rowH * (i.toFloat + 1.0)
    [ rect 70.0 y (w - 140.0) rowH 0.0 (if i % 2 == 0 then "#ffffff" else "#f8fafc")
        "#e2e8f0" 1.0,
      text 92.0 (y + 22.0) r.family 13.0 "#0f172a" "start",
      text 336.0 (y + 22.0) (if r.verdict then "✓ yes" else "✗ no") 13.5
        (if r.verdict then "#047857" else "#be123c") "start" "bold",
      text 500.0 (y + 22.0) r.note 12.5 "#475569" "start",
      text 820.0 (y + 22.0) r.thm 11.5 "#1d4ed8" "start" "normal" "italic" ]
  document w h (title ++ diagram ++ header ++ body)

end CenterViz
