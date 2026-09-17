/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Engine

/-!
# Globe coordinates and geographic containment

Wikidata's *globe coordinate* datatype, used by `coordinate location` (P625),
records a latitude, a longitude, a *precision* and the `globe` the coordinate is
measured on (Earth is Q2, but the Moon, Mars … have their own items).  A
coordinate is therefore not a point but a small box: a value given to a precision
of `0.01°` denotes everything within `0.01°` of the stated latitude and longitude.

This file formalises that datatype together with the geographic containment
layer built from `located in the administrative territorial entity` (P131): a
region is given a bounding box, and the ontology is *geographically consistent*
when each containment statement shrinks the box and each coordinate lies in the
box of its own item.

* `Wikidata.GlobeCoordinate` — latitude, longitude, precision, globe, with
  well-formedness and the box `GlobeCoordinate.box` a coordinate denotes.
* `Wikidata.GeoBox` — a bounding box on a globe, its points (`GeoBox.MemPt`),
  the coordinates it contains, and the inclusion order `GeoBox.Sub`.  Proved:
  inclusion is a partial order, containment is monotone along it, and the full
  box of a globe contains every well-formed coordinate on that globe.
* `Wikidata.GlobeCoordinate.Compatible` — two measurements are compatible when
  they can denote the same point.  Proved: compatibility is reflexive and
  symmetric, is *exactly* the overlap of the two denoted boxes, and coarsening
  the precision of a measurement only ever makes it more compatible.  The
  angular distance `GlobeCoordinate.degDist` is a pseudometric vanishing exactly
  on coordinates naming the same point, and compatibility is exactly closeness in
  it: the distance is at most the sum of the two precisions.
* `Wikidata.GeoLayer` — a finite geographic layer: coordinates, bounding boxes
  and P131 statements, with the derived containment `GeoLayer.Within` (the
  reflexive–transitive closure), the certified decision procedure
  `GeoLayer.withinB` for it, and the decidable consistency check
  `GeoLayer.consistentB`, proved to decide `GeoLayer.Consistent`.  Main results:
  in a consistent layer the box of a region includes the box of every region
  contained in it, hence a coordinate of a region lies in the box of every region
  it is (transitively) inside; contrapositively, a coordinate outside a box
  refutes containment.

The worked fragment places Paris inside France inside Europe and derives that the
coordinate of Paris lies in the box of Europe, while a variant whose coordinate
falls outside the box of its region is rejected by the checker.

Boxes here do not wrap across the antimeridian; a region straddling it must be
given the full longitude range.
-/

namespace Wikidata

/-- A Wikidata globe coordinate value: a latitude and longitude in degrees, the
precision they are stated to, and the globe they are measured on. -/
structure GlobeCoordinate where
  /-- The latitude in degrees, positive to the north. -/
  lat : ℚ
  /-- The longitude in degrees, positive to the east. -/
  lon : ℚ
  /-- The precision in degrees: the value is known up to this much. -/
  prec : ℚ := 0
  /-- The globe, an item such as *Earth* (Q2). -/
  globe : Qid
deriving DecidableEq, Repr, Inhabited

/-- A bounding box on a globe: a latitude band and a longitude band. -/
structure GeoBox where
  /-- The southern edge. -/
  south : ℚ
  /-- The northern edge. -/
  north : ℚ
  /-- The western edge. -/
  west : ℚ
  /-- The eastern edge. -/
  east : ℚ
  /-- The globe the box lives on. -/
  globe : Qid
deriving DecidableEq, Repr, Inhabited

namespace GeoBox

variable (b b' b'' : GeoBox)

/-- A box is well-formed when its edges are the right way round. -/
def Wf : Prop := b.south ≤ b.north ∧ b.west ≤ b.east

/-- The points of a box, as a pair of degree values. -/
def MemPt (lat lon : ℚ) : Prop :=
  b.south ≤ lat ∧ lat ≤ b.north ∧ b.west ≤ lon ∧ lon ≤ b.east

/-- The coordinates a box contains: same globe, and the stated point inside. -/
def Contains (c : GlobeCoordinate) : Prop :=
  b.globe = c.globe ∧ b.MemPt c.lat c.lon

/-- The decision procedure for containment. -/
def containsB (c : GlobeCoordinate) : Bool :=
  decide (b.globe = c.globe) && decide (b.south ≤ c.lat) && decide (c.lat ≤ b.north) &&
    decide (b.west ≤ c.lon) && decide (c.lon ≤ b.east)

@[simp] theorem containsB_iff (c : GlobeCoordinate) : b.containsB c = true ↔ b.Contains c := by
  simp [containsB, Contains, MemPt, and_assoc]

/-- Inclusion of boxes: same globe, and both bands included. -/
def Sub : Prop :=
  b.globe = b'.globe ∧ b'.south ≤ b.south ∧ b.north ≤ b'.north ∧
    b'.west ≤ b.west ∧ b.east ≤ b'.east

/-- The decision procedure for inclusion. -/
def subB : Bool :=
  decide (b.globe = b'.globe) && decide (b'.south ≤ b.south) && decide (b.north ≤ b'.north) &&
    decide (b'.west ≤ b.west) && decide (b.east ≤ b'.east)

@[simp] theorem subB_iff : b.subB b' = true ↔ b.Sub b' := by
  simp [subB, Sub, and_assoc]

theorem sub_refl : b.Sub b := ⟨rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem sub_trans (h : b.Sub b') (h' : b'.Sub b'') : b.Sub b'' :=
  ⟨h.1.trans h'.1, h'.2.1.trans h.2.1, h.2.2.1.trans h'.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩

theorem sub_antisymm (h : b.Sub b') (h' : b'.Sub b) : b = b' := by
  cases b; cases b'
  simp only [Sub] at h h'
  obtain ⟨hg, h1, h2, h3, h4⟩ := h
  obtain ⟨-, h1', h2', h3', h4'⟩ := h'
  simp only [GeoBox.mk.injEq]
  exact ⟨le_antisymm h1' h1, le_antisymm h2 h2', le_antisymm h3' h3, le_antisymm h4 h4', hg⟩

/-- A bigger box contains everything a smaller one does. -/
theorem contains_mono {b b' : GeoBox} {c : GlobeCoordinate} (h : b.Sub b')
    (hc : b.Contains c) : b'.Contains c :=
  ⟨h.1 ▸ hc.1, le_trans h.2.1 hc.2.1, le_trans hc.2.2.1 h.2.2.1,
    le_trans h.2.2.2.1 hc.2.2.2.1, le_trans hc.2.2.2.2 h.2.2.2.2⟩

/-- The full box of a globe. -/
def full (g : Qid) : GeoBox := ⟨-90, 90, -180, 180, g⟩

@[simp] theorem full_globe (g : Qid) : (full g).globe = g := rfl

theorem wf_full (g : Qid) : (full g).Wf := by
  constructor <;> norm_num [full]

/-- Every box is included in the full box of its globe. -/
theorem sub_full (h : -90 ≤ b.south) (h' : b.north ≤ 90) (h'' : -180 ≤ b.west)
    (h''' : b.east ≤ 180) : b.Sub (full b.globe) :=
  ⟨rfl, h, h', h'', h'''⟩

end GeoBox

namespace GlobeCoordinate

variable (c c' : GlobeCoordinate)

/-- A coordinate is well-formed when it lies in the usual degree ranges and its
precision is nonnegative. -/
def Wf : Prop :=
  -90 ≤ c.lat ∧ c.lat ≤ 90 ∧ -180 ≤ c.lon ∧ c.lon ≤ 180 ∧ 0 ≤ c.prec

/-- The full box of the globe of a well-formed coordinate contains it. -/
theorem full_contains (h : c.Wf) : (GeoBox.full c.globe).Contains c :=
  ⟨rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The box a coordinate denotes: everything within its precision. -/
def box : GeoBox where
  south := c.lat - c.prec
  north := c.lat + c.prec
  west := c.lon - c.prec
  east := c.lon + c.prec
  globe := c.globe

@[simp] theorem box_globe : c.box.globe = c.globe := rfl

/-- A measurement lies in the box it denotes. -/
theorem box_contains_self (h : 0 ≤ c.prec) : c.box.Contains c := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [box] <;> linarith

/-- Coarsening a measurement enlarges the box it denotes. -/
theorem box_sub_box_of_prec_le (h : c.prec ≤ c'.prec) (hlat : c.lat = c'.lat)
    (hlon : c.lon = c'.lon) (hg : c.globe = c'.globe) : c.box.Sub c'.box := by
  refine ⟨hg, ?_, ?_, ?_, ?_⟩ <;> simp only [box, hlat, hlon] <;> linarith

/-- Two measurements are *compatible* when, given their precisions, they can
denote the same point of the same globe. -/
def Compatible : Prop :=
  c.globe = c'.globe ∧ |c.lat - c'.lat| ≤ c.prec + c'.prec ∧
    |c.lon - c'.lon| ≤ c.prec + c'.prec

theorem compatible_self (h : 0 ≤ c.prec) : c.Compatible c := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp <;> linarith

theorem compatible_comm {c c' : GlobeCoordinate} (h : c.Compatible c') : c'.Compatible c := by
  refine ⟨h.1.symm, ?_, ?_⟩
  · rw [abs_sub_comm]; linarith [h.2.1]
  · rw [abs_sub_comm]; linarith [h.2.2]

/-- Overlap of two intervals of the form `[a - p, a + p]`. -/
theorem interval_overlap_iff {a b p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∃ x : ℚ, a - p ≤ x ∧ x ≤ a + p ∧ b - q ≤ x ∧ x ≤ b + q) ↔ |a - b| ≤ p + q := by
  constructor
  · rintro ⟨x, h1, h2, h3, h4⟩
    rw [abs_le]
    constructor <;> linarith
  · intro h
    rw [abs_le] at h
    refine ⟨max (a - p) (b - q), le_max_left _ _, ?_, le_max_right _ _, ?_⟩
    · exact max_le (by linarith) (by linarith [h.1])
    · exact max_le (by linarith [h.2]) (by linarith)

/-- Compatibility of two measurements is exactly the overlap of the boxes they
denote: they are compatible precisely when some point of the globe is consistent
with both. -/
theorem compatible_iff_box_overlap (hp : 0 ≤ c.prec) (hq : 0 ≤ c'.prec) :
    c.Compatible c' ↔
      c.globe = c'.globe ∧ ∃ lat lon : ℚ, c.box.MemPt lat lon ∧ c'.box.MemPt lat lon := by
  constructor
  · rintro ⟨hg, hlat, hlon⟩
    refine ⟨hg, ?_⟩
    obtain ⟨x, hx⟩ := (interval_overlap_iff hp hq).2 hlat
    obtain ⟨y, hy⟩ := (interval_overlap_iff hp hq).2 hlon
    exact ⟨x, y, ⟨hx.1, hx.2.1, hy.1, hy.2.1⟩, ⟨hx.2.2.1, hx.2.2.2, hy.2.2.1, hy.2.2.2⟩⟩
  · rintro ⟨hg, lat, lon, ⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩
    refine ⟨hg, ?_, ?_⟩
    · exact (interval_overlap_iff hp hq).1 ⟨lat, h1, h2, h5, h6⟩
    · exact (interval_overlap_iff hp hq).1 ⟨lon, h3, h4, h7, h8⟩

/-! #### The degree distance -/

/-- The angular distance between two coordinates: the larger of the latitude and
longitude differences (the Chebyshev distance in degrees). -/
def degDist (c c' : GlobeCoordinate) : ℚ := max |c.lat - c'.lat| |c.lon - c'.lon|

theorem degDist_nonneg (c c' : GlobeCoordinate) : 0 ≤ degDist c c' :=
  le_trans (abs_nonneg _) (le_max_left _ _)

@[simp] theorem degDist_self : degDist c c = 0 := by simp [degDist]

theorem degDist_comm (c c' : GlobeCoordinate) : degDist c c' = degDist c' c := by
  simp [degDist, abs_sub_comm]

/-- The distance vanishes exactly on coordinates naming the same point. -/
theorem degDist_eq_zero_iff (c c' : GlobeCoordinate) :
    degDist c c' = 0 ↔ c.lat = c'.lat ∧ c.lon = c'.lon := by
  constructor
  · intro h
    have h1 : |c.lat - c'.lat| ≤ 0 := h ▸ le_max_left _ _
    have h2 : |c.lon - c'.lon| ≤ 0 := h ▸ le_max_right _ _
    exact ⟨sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _))),
      sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _)))⟩
  · rintro ⟨h1, h2⟩
    simp [degDist, h1, h2]

/-- The triangle inequality: the degree distance is a pseudometric. -/
theorem degDist_triangle (c c' c'' : GlobeCoordinate) :
    degDist c c'' ≤ degDist c c' + degDist c' c'' := by
  refine max_le ?_ ?_
  · refine le_trans (abs_sub_le _ c'.lat _) (add_le_add ?_ ?_)
    · exact le_max_left _ _
    · exact le_max_left _ _
  · refine le_trans (abs_sub_le _ c'.lon _) (add_le_add ?_ ?_)
    · exact le_max_right _ _
    · exact le_max_right _ _

/-- Compatibility is exactly closeness: two measurements can denote the same
point precisely when they lie on the same globe and their degree distance is at
most the sum of their precisions. -/
theorem compatible_iff_degDist_le :
    c.Compatible c' ↔ c.globe = c'.globe ∧ degDist c c' ≤ c.prec + c'.prec := by
  simp only [Compatible, degDist, max_le_iff]

/-- Coarsening a measurement can only make it more compatible with others. -/
theorem compatible_of_prec_le {c c' d : GlobeCoordinate} (hc : c.Compatible d)
    (hlat : c.lat = c'.lat) (hlon : c.lon = c'.lon) (hg : c.globe = c'.globe)
    (h : c.prec ≤ c'.prec) : c'.Compatible d := by
  obtain ⟨hg', h1, h2⟩ := hc
  refine ⟨hg ▸ hg', ?_, ?_⟩
  · rw [← hlat]; linarith
  · rw [← hlon]; linarith

end GlobeCoordinate

/-! ### The geographic layer -/

/-- A finite geographic layer over a Wikidata-style ontology: the
`coordinate location` (P625) values, the bounding box of each region, and the
`located in the administrative territorial entity` (P131) statements. -/
structure GeoLayer where
  /-- The default globe, used for items with no recorded box. -/
  globe : Qid
  /-- The `coordinate location` (P625) value of each item, if any. -/
  coords : List (Qid × GlobeCoordinate) := []
  /-- The bounding box of each region (missing regions get the full globe). -/
  boxes : List (Qid × GeoBox) := []
  /-- Direct `located in the administrative territorial entity` (P131)
  statements: the first item lies inside the second. -/
  within : List (Qid × Qid) := []
deriving DecidableEq, Repr, Inhabited

namespace GeoLayer

variable (G : GeoLayer)

/-- The bounding box of an item: the recorded one, or the whole globe. -/
def boxOf (q : Qid) : GeoBox := (G.boxes.lookup q).getD (GeoBox.full G.globe)

/-- The recorded coordinate of an item, if any. -/
def coordOf? (q : Qid) : Option GlobeCoordinate := G.coords.lookup q

/-- Derived geographic containment: the reflexive–transitive closure of the P131
statements. -/
def Within : Qid → Qid → Prop :=
  Relation.ReflTransGen (fun x y => (x, y) ∈ G.within)

theorem within_refl (q : Qid) : G.Within q q := Relation.ReflTransGen.refl

theorem within_of_mem {x y : Qid} (h : (x, y) ∈ G.within) : G.Within x y :=
  Relation.ReflTransGen.single h

theorem within_trans {x y z : Qid} (h : G.Within x y) (h' : G.Within y z) : G.Within x z :=
  h.trans h'

/-! #### Deciding containment -/

/-- All the items mentioned in the containment statements. -/
def allF : Finset Qid := (G.within.map Prod.fst ++ G.within.map Prod.snd).toFinset

/-- The items an item is directly stated to lie in. -/
def supersF (q : Qid) : Finset Qid :=
  ((G.within.filter (fun p => decide (p.1 = q))).map Prod.snd).toFinset

theorem mem_supersF {q v : Qid} : v ∈ G.supersF q ↔ (q, v) ∈ G.within := by
  simp only [supersF, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hp, h1⟩, h2⟩
    simp only at h1 h2
    subst h1; subst h2; exact hp
  · intro h
    exact ⟨(q, v), ⟨h, rfl⟩, rfl⟩

theorem supersF_subset_allF (q : Qid) : G.supersF q ⊆ G.allF := by
  intro v hv
  have h := G.mem_supersF.1 hv
  simp only [allF, List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inr ⟨(q, v), h, rfl⟩

theorem supersF_eq_empty {q : Qid} (h : q ∉ G.allF) : G.supersF q = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 (fun v hv => h ?_)
  have hw := G.mem_supersF.1 hv
  simp only [allF, List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl ⟨(q, v), hw, rfl⟩

/-- The computed set of regions an item lies in: the saturation of the P131
statements. -/
def containers (q : Qid) : Finset Qid := Reach.reach G.supersF G.allF q

/-- The decision procedure for geographic containment. -/
def withinB (x y : Qid) : Bool := decide (y ∈ G.containers x)

/-- The computation is exactly the derived containment relation: soundness and
completeness of the saturation. -/
theorem mem_containers_iff (x y : Qid) : y ∈ G.containers x ↔ G.Within x y := by
  rw [containers,
    Reach.mem_reach_iff_of_closed G.supersF G.supersF_subset_allF
      (fun _ hy => G.supersF_eq_empty hy)]
  constructor
  · exact fun h => h.mono (fun _ _ hab => G.mem_supersF.1 hab)
  · exact fun h => h.mono (fun _ _ hab => G.mem_supersF.2 hab)

@[simp] theorem withinB_iff (x y : Qid) : G.withinB x y = true ↔ G.Within x y := by
  rw [withinB, decide_eq_true_iff, mem_containers_iff]

/-- A layer is *geographically consistent* when every containment statement
shrinks the bounding box and every coordinate lies in the box of its own item. -/
def Consistent : Prop :=
  (∀ p ∈ G.within, (G.boxOf p.1).Sub (G.boxOf p.2)) ∧
    (∀ p ∈ G.coords, (G.boxOf p.1).Contains p.2)

/-- The decidable consistency check. -/
def consistentB : Bool :=
  G.within.all (fun p => (G.boxOf p.1).subB (G.boxOf p.2)) &&
    G.coords.all (fun p => (G.boxOf p.1).containsB p.2)

@[simp] theorem consistentB_iff : G.consistentB = true ↔ G.Consistent := by
  simp [consistentB, Consistent]

/-- In a consistent layer, containment includes the bounding boxes: a region lies
inside the box of every region it is (transitively) inside. -/
theorem sub_of_within (hG : G.Consistent) {x y : Qid} (h : G.Within x y) :
    (G.boxOf x).Sub (G.boxOf y) := by
  induction h with
  | refl => exact GeoBox.sub_refl _
  | tail _ hstep ih => exact GeoBox.sub_trans _ _ _ ih (hG.1 _ hstep)

/-- Hence the coordinate of a region lies in the box of every region containing
it — the inherited-location rule. -/
theorem contains_of_within (hG : G.Consistent) {x y : Qid} {c : GlobeCoordinate}
    (hc : G.coordOf? x = some c) (h : G.Within x y) : (G.boxOf y).Contains c := by
  have hmem : (x, c) ∈ G.coords := by
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hc
    rw [show G.coords = l₁ ++ (x, c) :: l₂ from hl]
    simp
  exact GeoBox.contains_mono (G.sub_of_within hG h) (hG.2 _ hmem)

/-- Contrapositive: a coordinate falling outside a box refutes containment. -/
theorem not_within_of_not_contains (hG : G.Consistent) {x y : Qid} {c : GlobeCoordinate}
    (hc : G.coordOf? x = some c) (h : ¬ (G.boxOf y).Contains c) : ¬ G.Within x y :=
  fun hw => h (G.contains_of_within hG hc hw)

/-- Two regions containing one another have the same bounding box. -/
theorem box_eq_of_within_within (hG : G.Consistent) {x y : Qid} (h : G.Within x y)
    (h' : G.Within y x) : G.boxOf x = G.boxOf y :=
  GeoBox.sub_antisymm _ _ (G.sub_of_within hG h) (G.sub_of_within hG h')

/-- All the boxes along a containment chain live on the same globe. -/
theorem globe_eq_of_within (hG : G.Consistent) {x y : Qid} (h : G.Within x y) :
    (G.boxOf x).globe = (G.boxOf y).globe := (G.sub_of_within hG h).1

end GeoLayer

/-! ### A worked fragment: Paris in France in Europe -/

namespace GeoExample

open Wikidata

/-- The globe *Earth* (Q2). -/
def earth : Qid := .wd "Q2"
/-- *Paris* (Q90). -/
def paris : Qid := .wd "Q90"
/-- *France* (Q142). -/
def france : Qid := .wd "Q142"
/-- *Europe* (Q46). -/
def europe : Qid := .wd "Q46"
/-- *the Moon* (Q405), used as a second globe. -/
def moon : Qid := .wd "Q405"

/-- The `coordinate location` (P625) of Paris, to a precision of `1/1000` degree. -/
def parisCoord : GlobeCoordinate :=
  { lat := 4885 / 100, lon := 235 / 100, prec := 1 / 1000, globe := earth }

/-- A second, coarser measurement of the same place. -/
def parisCoarse : GlobeCoordinate :=
  { lat := 489 / 10, lon := 23 / 10, prec := 1 / 10, globe := earth }

/-- A measurement of a different place. -/
def berlinCoord : GlobeCoordinate :=
  { lat := 5252 / 100, lon := 1341 / 100, prec := 1 / 1000, globe := earth }

/-- The bounding box of France. -/
def franceBox : GeoBox := ⟨41, 51, -5, 10, earth⟩
/-- The bounding box of Europe. -/
def europeBox : GeoBox := ⟨35, 71, -25, 45, earth⟩

/-- The geographic layer of the fragment. -/
def layer : GeoLayer where
  globe := earth
  coords := [(paris, parisCoord)]
  boxes := [(paris, ⟨4884 / 100, 4886 / 100, 234 / 100, 236 / 100, earth⟩),
            (france, franceBox), (europe, europeBox)]
  within := [(paris, france), (france, europe)]

/-- The fragment is geographically consistent. -/
theorem layer_consistent : layer.Consistent := by
  rw [← GeoLayer.consistentB_iff]
  native_decide

/-- Paris is derived to be inside Europe. -/
theorem paris_within_europe : layer.Within paris europe :=
  layer.within_trans (layer.within_of_mem (x := paris) (y := france) (by simp [layer]))
    (layer.within_of_mem (x := france) (y := europe) (by simp [layer]))

/-- Hence the coordinate of Paris lies in the bounding box of Europe, although no
statement says so. -/
theorem europe_contains_paris : (layer.boxOf europe).Contains parisCoord :=
  layer.contains_of_within layer_consistent (by rfl) paris_within_europe

/-- The same fact, decided by the containment engine. -/
theorem paris_within_europe_computed : layer.withinB paris europe = true := by decide

/-- Europe is not inside Paris: containment is a partial order, not a symmetry. -/
theorem europe_not_within_paris : ¬ layer.Within europe paris := by
  rw [← GeoLayer.withinB_iff]
  decide

/-- The box of Paris is included in the box of France. -/
theorem parisBox_sub_franceBox : (layer.boxOf paris).Sub (layer.boxOf france) :=
  layer.sub_of_within layer_consistent
    (layer.within_of_mem (x := paris) (y := france) (by simp [layer]))

/-- The two measurements of Paris are compatible: they can denote the same point. -/
theorem paris_compatible : parisCoord.Compatible parisCoarse := by
  refine ⟨rfl, ?_, ?_⟩ <;> rw [abs_le] <;>
    constructor <;> norm_num [parisCoord, parisCoarse]

/-- The Paris and Berlin measurements are not compatible. -/
theorem paris_not_compatible_berlin : ¬ parisCoord.Compatible berlinCoord := by
  rintro ⟨-, h, -⟩
  rw [abs_le] at h
  have h1 := h.1
  simp only [parisCoord, berlinCoord] at h1
  norm_num at h1

/-- The same numbers read on a different globe are never compatible. -/
theorem globe_matters :
    ¬ parisCoord.Compatible { parisCoord with globe := moon } := by
  rintro ⟨h, -, -⟩
  simp only [parisCoord, earth, moon] at h
  exact absurd h (by decide)

/-- A variant of the fragment whose coordinate falls outside the box of its own
region is rejected. -/
def badLayer : GeoLayer := { layer with coords := [(paris, berlinCoord)] }

theorem badLayer_inconsistent : ¬ badLayer.Consistent := by
  rw [← GeoLayer.consistentB_iff]
  native_decide

/-- A variant that puts France inside a box not containing it is rejected too. -/
def badNesting : GeoLayer :=
  { layer with boxes := [(paris, ⟨4884 / 100, 4886 / 100, 234 / 100, 236 / 100, earth⟩),
      (france, franceBox), (europe, ⟨45, 71, -25, 45, earth⟩)] }

theorem badNesting_inconsistent : ¬ badNesting.Consistent := by
  rw [← GeoLayer.consistentB_iff]
  native_decide

end GeoExample

end Wikidata
