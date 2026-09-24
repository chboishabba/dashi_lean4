# Base369: the finite Heisenberg group and its Schrödinger module, in Lean

A second, independent piece of this round. The Base369 lane's stated frontier
runs

```
finite Heisenberg carrier → Schrödinger module → delta orbit → irreducibility
→ Stone–von Neumann uniqueness → fixed central character → (only then) any
identification question.
```

Two new Lean modules close the first three arrows and the fourth, and record
exactly where the chain stops.

## 1. `Lean/Integration/Base369Heisenberg.lean`

Carrier: `H(n) = X × X* × 𝔽₃` with `X = 𝔽₃ⁿ` and `X*` identified with `X`
through `⟨y, x⟩ = Σᵢ yᵢ xᵢ`; the lane's case is `n = 6`.

| result | statement |
|---|---|
| `dot_add_left`, `dot_add_right`, `dot_neg_*` | the pairing is bilinear |
| `heisenbergCocycle` | the 2-cocycle identity `c(a,b) + c(ab,c) = c(b,c) + c(a,bc)` for `c(g,h) = ⟨y_g, x_h⟩` |
| `Group (H n)` instance | associativity, identity and the inverse laws **proved**, via `Group.ofLeftAxioms` |
| `card_H`, `card_H6` | `|H n| = 3^(2n+1)`; `|H 6| = 3¹³` |
| `omega_alternating`, `omega_skew`, `omega_add_left/right` | `ω(g,h) = ⟨y_g,x_h⟩ − ⟨y_h,x_g⟩` is an alternating bilinear form |
| `commutator_eq` | `[g,h] = (0,0,ω(g,h))` — the commutator *is* the symplectic form, and is central |
| `mul_comm_iff` | `gh = hg ↔ ω(g,h) = 0` |
| `omega_nondegenerate` | any nonzero `(x,y)` is detected by an explicit partner (built from a standard basis vector) |
| `mem_center_iff` | the centre is exactly the `𝔽₃` factor |
| `not_commutative` | for `n ≥ 1` the group is nonabelian |

So the finite Heisenberg group is closed at the theorem level here: no
postulate, no `sorry`, and the group instance is genuinely derived from the
cocycle.

## 2. `Lean/Integration/Base369Schrodinger.lean`

Module: `V = (𝔽₃ⁿ → ℂ)` with

```
(T g f)(u) = χ(z_g + ⟨y_g, u − x_g⟩) · f(u − x_g),      χ = ZMod.stdAddChar.
```

Working over `ℂ` rather than `ℚ(ζ₃)` is a containment, not a change of content:
`χ` takes values in the cube roots of unity.

| result | statement |
|---|---|
| `T_one`, `T_mul` | `T` is an action of the group law proved in §1 (the phase convention `⟨y, u − x⟩` is the one that matches that cocycle) |
| `T_add`, `T_smul` | each `T g` is `ℂ`-linear |
| `charSum` | `∑_{y ∈ 𝔽₃ⁿ} χ⟨y,v⟩ = 3ⁿ·[v = 0]` — coordinate Fourier orthogonality |
| `proj_eq` | the composed point projector satisfies `P_x f = (3ⁿ · f x) • δ_x`; hence `P_x f(x) = 3ⁿ f(x)` and `P_x f(u) = 0` off `x` |
| `delta_mem_of_mem` | every nonzero invariant subspace containing `f` contains `δ_x` wherever `f x ≠ 0` |
| `T_translate_delta` | translations move deltas transitively |
| `eq_sum_deltas` | deltas span `V` |
| **`schrodinger_irreducible`** | **every `T`-invariant subspace is `⊥` or `⊤`** |
| `finrank_V`, `finrank_V6` | `dim V = 3ⁿ`; `= 729` for `n = 6` |
| `dimension_is_not_identity` | the same `3ⁿ`-dimensional space carries the irreducible Schrödinger action *and* the reducible trivial action of the same group, so a dimension count identifies nothing |

## 3. Honest frontier

Not proved, and not claimed:

1. **Stone–von Neumann uniqueness.** Irreducibility is proved; that *any two*
   irreducible modules with the same central character are isomorphic is not.
2. **The central character is not extracted.** `T (0,0,z)` acts by `χ(z)`, but
   no statement classifies modules by that scalar.
3. **`ℚ(ζ₃)` is not the coefficient field.** Everything is over `ℂ`; the
   cyclotomic-field statement would need the same proofs over `ℚ(ζ₃)`, which is
   routine but not done.
4. **No Monster-related statement whatsoever.** No identification, embedding or
   comparison with any sporadic group, moonshine module or vertex algebra is
   formalised or claimed. `dimension_is_not_identity` exists precisely to block
   the inference that a matching dimension is such an identification.
5. **No Agda transport.** These are Lean theorems; no Agda module was checked.

Axiom audit: `Lean/Integration/AxiomAuditBase369.lean`; every declaration
reports only `{propext, Classical.choice, Quot.sound}`.
