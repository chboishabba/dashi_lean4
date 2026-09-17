# AdK Exact CV Kernel Mirror Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a minimal native Lean mirror proving exact selected-content extensionality for the AdK three-CV surface and a constructive projection collision, with source/provenance attribution kept separate from DASHI-original theorems.

**Architecture:** The theorem spine lives under `AgdaMirror/AdK`. Coordinates and adopted rounded masses use exact rationals. Canonical selected content is proof data; COM is a pure exact function of that content; the terminal theorem proves a distinct pair of atomistic configurations can share the complete source-facing three-CV input surface. Existing `AgdaMirror`, `AuthorityBoundary`, JMD Agda interop/provenance machinery, Lean 4.28, and repository CI are reused rather than duplicated.

**Tech Stack:** Lean 4.28.0, Mathlib 4.28.0, existing `AgdaMirror` library, GitHub Actions `leanprover/lean-action`.

**Spec:** `docs/superpowers/specs/2026-09-17-adk-exact-cv-kernel-mirror-design.md`

## Global Constraints

- Li-Liu-Ji 2015 DOI `10.1016/j.bpj.2015.06.059` owns source-facing AdK selection/domain roles only.
- Prohaska et al. DOI `10.1515/pac-2019-0603` owns the adopted atomic-mass convention only.
- wwPDB/PDB identifiers remain provenance/identity coordinates and do not create coordinate equality or theorem authority.
- JMD/meta-introspector owns the newly integrated Agda interoperability/provenance machinery; reuse does not reassign authorship of AdK source facts or DASHI-original theorems.
- No SHA/hash injectivity assumption.
- No PDB parser, OpenMM execution, exact `acos`, or force-field reproduction in this tranche.
- New AdK theorem files must contain no `sorry` and introduce no new `axiom` declarations.
- Do not claim kernel/elaboration GREEN until a fresh Lean build/CI succeeds.

---

### Task 1: Attribution and exact atomistic carrier

**Files:**
- Create: `AgdaMirror/AdK/Attribution.lean`
- Create: `AgdaMirror/AdK/AtomisticConfiguration.lean`

**Interfaces:**
- Produces: `AgdaMirror.AdK.Attribution.SourceCoordinate`, source constants, and attribution notes.
- Produces: `AgdaMirror.AdK.AtomisticConfiguration.Vec3Q`, `AtomId`, `Atom`, `Configuration`, exact mass helpers, and structural equality support.

- [ ] **Step 1: Write attribution constants and a compile-time carrier example**

`Attribution.lean` defines:

```lean
namespace AgdaMirror.AdK.Attribution

structure SourceCoordinate where
  owner : String
  identifier : String
  role : String
  deriving DecidableEq, Repr

def liLiuJi2015 : SourceCoordinate :=
  { owner := "Li-Liu-Ji 2015"
    identifier := "doi:10.1016/j.bpj.2015.06.059"
    role := "source-facing AdK CV residue/domain roles" }

def prohaska2021 : SourceCoordinate :=
  { owner := "Prohaska et al."
    identifier := "doi:10.1515/pac-2019-0603"
    role := "adopted abridged atomic-weight convention" }

end AgdaMirror.AdK.Attribution
```

`AtomisticConfiguration.lean` initially imports `Attribution` and contains an example expecting exact rational equality:

```lean
example : ((12345 : ℚ) / 1000) = 12.345 := by norm_num
```

- [ ] **Step 2: Run the narrow file and verify RED if required definitions/imports are missing**

Run:

```bash
lake env lean AgdaMirror/AdK/AtomisticConfiguration.lean
```

Expected before implementation: failure on missing carrier definitions if the example references them; after the minimal constants-only seed, the rational example itself may already elaborate.

- [ ] **Step 3: Implement the exact carrier**

Use:

```lean
structure Vec3Q where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

structure AtomId where
  model : Nat
  chain : String
  residue : Int
  residueName : String
  atomName : String
  altloc : String
  serial : Nat
  element : String
  deriving DecidableEq, Repr

structure Atom where
  id : AtomId
  mass : ℚ
  position : Vec3Q
  deriving DecidableEq, Repr

abbrev Configuration := List Atom
```

Also define exact adopted working masses:

```lean
def massH : ℚ := 1008 / 1000
def massC : ℚ := 12011 / 1000
def massN : ℚ := 14007 / 1000
def massO : ℚ := 15999 / 1000
def massP : ℚ := 30974 / 1000
def massS : ℚ := 32060 / 1000
def massMg : ℚ := 24305 / 1000
```

Document that exact rationals encode the chosen rounded convention, not isotope-exact or experimentally exact masses.

- [ ] **Step 4: Re-run the narrow file**

Run:

```bash
lake env lean AgdaMirror/AdK/Attribution.lean
lake env lean AgdaMirror/AdK/AtomisticConfiguration.lean
```

Expected: both exit 0.

- [ ] **Step 5: Commit**

```bash
git add AgdaMirror/AdK/Attribution.lean AgdaMirror/AdK/AtomisticConfiguration.lean
git commit -m "feat(adk): add attributed exact atomistic carrier"
```

---

### Task 2: Source selections and explicit dLN policy

**Files:**
- Create: `AgdaMirror/AdK/SourceSelections.lean`

**Interfaces:**
- Consumes: `Atom`, `Configuration`.
- Produces: `AtomPolicy`, `ResidueSpan`, `SelectionSpec`, canonical theta selections, explicit dLN policy constructor, `selectedAtoms`, and `allThreeCVSelections`.

- [ ] **Step 1: Write examples for source-paid spans and policy distinction**

Add examples that require:

```lean
example : theta1Lid.spans = [{lo := 123, hi := 155}] := rfl
example : dlnLid .backbone ≠ dlnLid .heavy := by decide
```

- [ ] **Step 2: Run and observe RED**

```bash
lake env lean AgdaMirror/AdK/SourceSelections.lean
```

Expected: unknown identifiers before implementation.

- [ ] **Step 3: Implement typed selections**

Define:

```lean
inductive AtomPolicy | backbone | heavy
  deriving DecidableEq, Repr

structure ResidueSpan where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

structure SelectionSpec where
  label : String
  spans : List ResidueSpan
  policy : AtomPolicy
  deriving DecidableEq, Repr
```

Backbone names are exactly `N`, `CA`, `C`, `O`, `OXT` as the current DASHI evaluator convention; comments must state that `OXT` inclusion is evaluator policy, not a Li-Liu-Ji quote.

Implement source selections:

```lean
def theta1Lid
ndef hinge
def core
def theta2Nmp
def dlnLid (p : AtomPolicy)
def dlnNmp (p : AtomPolicy)
```

Implement deterministic predicates and `selectedAtoms : Configuration → SelectionSpec → List Atom` using `List.filter`.

Implement:

```lean
def allThreeCVSelections (dlnPolicy : AtomPolicy) : List SelectionSpec :=
  [theta1Lid, hinge, core, theta2Nmp, dlnLid dlnPolicy, dlnNmp dlnPolicy]
```

The list contains six unique selections because hinge/core are shared between theta1/theta2; the theorem surface may reference them multiple times when forming angle inputs.

- [ ] **Step 4: Run the narrow file**

```bash
lake env lean AgdaMirror/AdK/SourceSelections.lean
```

Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add AgdaMirror/AdK/SourceSelections.lean
git commit -m "feat(adk): mirror source-facing CV selections"
```

---

### Task 3: Canonical selected content

**Files:**
- Create: `AgdaMirror/AdK/CanonicalSelectionContent.lean`

**Interfaces:**
- Consumes: `Configuration`, `SelectionSpec`, `selectedAtoms`.
- Produces: `CanonicalAtomRow`, `CanonicalSelectionContent`, `canonicalRow`, `canonicalContent`, and direct content-equality lemmas.

- [ ] **Step 1: Write failing examples for serialization/order independence**

Construct two configurations containing the same selected atoms in opposite list order and require:

```lean
example : canonicalContent q1 theta1Lid = canonicalContent q2 theta1Lid := by native_decide
```

- [ ] **Step 2: Run and observe RED**

```bash
lake env lean AgdaMirror/AdK/CanonicalSelectionContent.lean
```

Expected: missing canonical-content definitions.

- [ ] **Step 3: Implement transparent canonical rows**

Define:

```lean
structure CanonicalAtomRow where
  id : AtomId
  mass : ℚ
  position : Vec3Q
  deriving DecidableEq, Repr
```

Use the exact atom row itself as transparent proof data. Define a total deterministic ordering key over the string/numeric identity fields, then sort rows using that key. Do not hash rows.

```lean
def canonicalRow (a : Atom) : CanonicalAtomRow := ...
def canonicalContent (q : Configuration) (s : SelectionSpec) : List CanonicalAtomRow :=
  (selectedAtoms q s).map canonicalRow |>.mergeSort rowLE
```

Add theorem:

```lean
theorem canonicalContent_eq_of_selectedAtoms_perm
    (h : (selectedAtoms q₁ s).map canonicalRow ~ (selectedAtoms q₂ s).map canonicalRow) :
    canonicalContent q₁ s = canonicalContent q₂ s := ...
```

If proving the generic permutation theorem causes unnecessary complexity, retain the concrete order-independence examples and use equality of canonical lists as the theorem premise. YAGNI: no generic sorting library theorem is required for the terminal AdK result.

- [ ] **Step 4: Run the narrow file**

```bash
lake env lean AgdaMirror/AdK/CanonicalSelectionContent.lean
```

Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add AgdaMirror/AdK/CanonicalSelectionContent.lean
git commit -m "feat(adk): add transparent canonical selection content"
```

---

### Task 4: Exact rational COM and content extensionality

**Files:**
- Create: `AgdaMirror/AdK/COMGeometry.lean`

**Interfaces:**
- Consumes: `CanonicalAtomRow`, canonical selected content.
- Produces: `sumMass`, `weightedSum`, `centerOfMass?`, `COMDefined`, and exact extensionality theorems.

- [ ] **Step 1: Write a failing exact COM example**

For two carbon atoms at `(0,0,0)` and `(2,0,0)`, require COM `(1,0,0)` exactly:

```lean
example : centerOfMass? twoCarbonRows = some { x := 1, y := 0, z := 0 } := by
  norm_num [centerOfMass?, sumMass, weightedSum, twoCarbonRows, massC]
```

- [ ] **Step 2: Run and observe RED**

```bash
lake env lean AgdaMirror/AdK/COMGeometry.lean
```

Expected: missing COM definitions.

- [ ] **Step 3: Implement exact COM**

Define rational vector addition/scaling locally or through simple componentwise functions:

```lean
def Vec3Q.scale (a : ℚ) (v : Vec3Q) : Vec3Q := ...
def Vec3Q.add (u v : Vec3Q) : Vec3Q := ...
```

Define:

```lean
def sumMass : List CanonicalAtomRow → ℚ
def weightedSum : List CanonicalAtomRow → Vec3Q
def centerOfMass? (rows : List CanonicalAtomRow) : Option Vec3Q :=
  let m := sumMass rows
  if h : m = 0 then none else some ((1 / m) •q weightedSum rows)
```

Prove the theorem actually needed by later modules:

```lean
theorem centerOfMass_congr {a b : List CanonicalAtomRow} (h : a = b) :
    centerOfMass? a = centerOfMass? b := by simpa [h]
```

and lifted form:

```lean
theorem canonicalContent_centerOfMass_congr
    (h : canonicalContent q₁ s = canonicalContent q₂ s) :
    centerOfMass? (canonicalContent q₁ s) = centerOfMass? (canonicalContent q₂ s) :=
  congrArg centerOfMass? h
```

- [ ] **Step 4: Run the narrow file**

```bash
lake env lean AgdaMirror/AdK/COMGeometry.lean
```

Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add AgdaMirror/AdK/COMGeometry.lean
git commit -m "feat(adk): prove exact COM content extensionality"
```

---

### Task 5: Exact three-CV input surface

**Files:**
- Create: `AgdaMirror/AdK/CVProjection.lean`

**Interfaces:**
- Consumes: exact canonical content and COM.
- Produces: `AngleCOMTriple`, `ThreeCVInputSurface`, `threeCVInputSurface`, optional exact squared dLN, and `threeCVInput_eq_of_content_eq`.

- [ ] **Step 1: Write failing theorem signature**

Require a theorem accepting equality of the six unique selection contents for a chosen explicit `dlnPolicy` and returning equality of `ThreeCVInputSurface`.

- [ ] **Step 2: Run and observe RED**

```bash
lake env lean AgdaMirror/AdK/CVProjection.lean
```

Expected: missing surface/theorem definitions.

- [ ] **Step 3: Implement theorem-bearing CV input structure**

Define:

```lean
structure AngleCOMTriple where
  first : Option Vec3Q
  vertex : Option Vec3Q
  third : Option Vec3Q
  deriving DecidableEq, Repr

structure ThreeCVInputSurface where
  theta1 : AngleCOMTriple
  theta2 : AngleCOMTriple
  dlnFirst : Option Vec3Q
  dlnSecond : Option Vec3Q
  deriving DecidableEq, Repr
```

Define `comOf q s := centerOfMass? (canonicalContent q s)` and build theta1 `(LID, hinge, core)`, theta2 `(NMP, core, hinge)`, and dLN `(LID-domain, NMP-domain)`.

Prove:

```lean
theorem threeCVInput_eq_of_content_eq
    (hTheta1Lid : canonicalContent q₁ theta1Lid = canonicalContent q₂ theta1Lid)
    (hHinge : canonicalContent q₁ hinge = canonicalContent q₂ hinge)
    (hCore : canonicalContent q₁ core = canonicalContent q₂ core)
    (hTheta2Nmp : canonicalContent q₁ theta2Nmp = canonicalContent q₂ theta2Nmp)
    (hDlnLid : canonicalContent q₁ (dlnLid p) = canonicalContent q₂ (dlnLid p))
    (hDlnNmp : canonicalContent q₁ (dlnNmp p) = canonicalContent q₂ (dlnNmp p)) :
    threeCVInputSurface q₁ p = threeCVInputSurface q₂ p := by
  simp [threeCVInputSurface, comOf, hTheta1Lid, hHinge, hCore,
        hTheta2Nmp, hDlnLid, hDlnNmp]
```

Also define exact squared dLN on two present COM values:

```lean
def distanceSq (a b : Vec3Q) : ℚ := ...
```

No `sqrt` or `acos` is needed.

- [ ] **Step 4: Run the narrow file**

```bash
lake env lean AgdaMirror/AdK/CVProjection.lean
```

Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add AgdaMirror/AdK/CVProjection.lean
git commit -m "feat(adk): prove exact three-CV input extensionality"
```

---

### Task 6: Constructive projection collision and non-factorability

**Files:**
- Create: `AgdaMirror/AdK/NonFactorability.lean`

**Interfaces:**
- Consumes: `threeCVInputSurface` and selected-content definitions.
- Produces: concrete `q₁`, `q₂`, proof `q₁ ≠ q₂`, proof of equal projected surface, local generic `ProjectionCollision`, `FactorsThrough`, and theorem that a projection collision refutes recovery/factorisation of configuration identity.

- [ ] **Step 1: Write failing terminal theorem**

State:

```lean
structure ProjectionCollision (X Y : Type) (proj : X → Y) where
  left : X
  right : X
  distinct : left ≠ right
  sameProjection : proj left = proj right

structure FactorsThrough (X Y : Type) (proj : X → Y) where
  recover : Y → X
  leftInverse : Function.LeftInverse recover proj

theorem collision_not_factors_through
    (c : ProjectionCollision X Y proj) : ¬ FactorsThrough X Y proj := ...
```

and an AdK-specific witness:

```lean
def adkThreeCVInputCollision :
  ProjectionCollision Configuration (ThreeCVInputSurface) (fun q => threeCVInputSurface q .backbone) := ...
```

- [ ] **Step 2: Run and observe RED**

```bash
lake env lean AgdaMirror/AdK/NonFactorability.lean
```

Expected: unknown terminal definitions/witness.

- [ ] **Step 3: Implement generic collision compiler**

Prove:

```lean
theorem collision_not_factors_through
    (c : ProjectionCollision X Y proj) : ¬ FactorsThrough X Y proj := by
  intro h
  apply c.distinct
  calc
    c.left = h.recover (proj c.left) := (h.leftInverse c.left).symm
    _ = h.recover (proj c.right) := by rw [c.sameProjection]
    _ = c.right := h.leftInverse c.right
```

- [ ] **Step 4: Construct the concrete AdK collision**

Create a small configuration containing enough selected atoms for all six unique selections plus one atom at residue 1000. Define `q₂` by changing only the residue-1000 atom coordinate. Prove the configurations differ by `native_decide` or `decide`.

For each source selection, prove `canonicalContent q₁ s = canonicalContent q₂ s` by `native_decide` where possible. Then invoke `threeCVInput_eq_of_content_eq`.

Finish:

```lean
theorem adkThreeCVInput_not_factors_through :
    ¬ FactorsThrough Configuration ThreeCVInputSurface
      (fun q => threeCVInputSurface q .backbone) :=
  collision_not_factors_through adkThreeCVInputCollision
```

Comments must state that `.backbone` here is the DASHI evaluator convention used for this constructive witness; it does not resolve the Li-Liu-Ji dLN atom-subset ambiguity.

- [ ] **Step 5: Run the terminal module**

```bash
lake env lean AgdaMirror/AdK/NonFactorability.lean
```

Expected: exit 0.

- [ ] **Step 6: Audit assumptions and forbidden placeholders**

Run:

```bash
rg -n '\bsorry\b|\baxiom\b' AgdaMirror/AdK
```

Expected: no theorem code containing `sorry`; no new `axiom` declarations. Documentation may mention the words only if the grep output is manually inspected.

- [ ] **Step 7: Commit**

```bash
git add AgdaMirror/AdK/NonFactorability.lean
git commit -m "feat(adk): prove constructive CV non-factorability"
```

---

### Task 7: Aggregate integration and Lean execution receipt

**Files:**
- Modify: `AgdaMirror.lean`
- Optionally create: `AgdaMirror/AdK.lean` as a small aggregate if repo conventions prefer namespace aggregation.
- Modify: PR body only after execution evidence exists.

**Interfaces:**
- Consumes: terminal AdK theorem module.
- Produces: repository-level import path and CI receipt.

- [ ] **Step 1: Add aggregate import**

Prefer a small `AgdaMirror/AdK.lean`:

```lean
import AgdaMirror.AdK.Attribution
import AgdaMirror.AdK.AtomisticConfiguration
import AgdaMirror.AdK.SourceSelections
import AgdaMirror.AdK.CanonicalSelectionContent
import AgdaMirror.AdK.COMGeometry
import AgdaMirror.AdK.CVProjection
import AgdaMirror.AdK.NonFactorability
```

Then add:

```lean
import AgdaMirror.AdK
```

to `AgdaMirror.lean`.

- [ ] **Step 2: Build the narrow library/root**

Run:

```bash
lake env lean AgdaMirror/AdK.lean
lake env lean AgdaMirror.lean
```

Expected: exit 0 for both.

- [ ] **Step 3: Run a repository library build sufficient to exercise `AgdaMirror`**

Run:

```bash
lake build AgdaMirror
```

Expected: exit 0.

- [ ] **Step 4: Commit integration**

```bash
git add AgdaMirror.lean AgdaMirror/AdK.lean
git commit -m "feat(adk): integrate exact CV kernel mirror"
```

- [ ] **Step 5: Open draft PR and observe CI**

Open a draft PR from `agent/adk-exact-cv-kernel-mirror` to `main`. Record exact head SHA and GitHub Actions run/job state. Do not describe the theorem as kernel-GREEN until the run/job reports success.

- [ ] **Step 6: If CI fails, debug from the first concrete compiler error**

Use the repository's existing Lean workflow logs. Apply the smallest correction, rerun the narrow file locally/through available execution surface, and then rely on a fresh CI run for the completion claim.

---

## Self-review

- Spec coverage: attribution, rational carriers, explicit dLN policy, canonical content, exact COM, three-CV input equality, constructive collision, non-factorability, aggregate integration, and execution evidence are each assigned to a task.
- Placeholder scan: no `TBD`, `TODO`, or unspecified implementation steps remain.
- Type consistency: all later modules consume names introduced by earlier tasks; the six unique selection objects are reused to form the eight logical angle/distance positions.
- Scope: parser/OpenMM/transcendental numerics remain explicitly out of scope.
