# The between-block Gram debt of the partner-compressed output fibre

Lean source: `RequestProject/NavierStokes/WaleffeBetweenBlockGram.lean`
(namespace `ClayNS.Waleffe`).  Everything below compiles, contains no `sorry`,
no postulate and no added axiom; the headline theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`.

## The question

After partner compression (`WaleffeOutputGainFibre.lean`), the fibre of the
output `k` is a sum of **block cells**

```
C_p = P_k ( i(u_p·q) u_q + i(u_q·p) u_p ),   q = k − p,     ‖C_p‖ ≤ 2|k|‖u_p‖‖u_q‖ .
```

The tempting next move is a *cardinality-free* payment of the whole fibre by
summing the cellwise masses, i.e.

```
(†)   ‖∑_p C_p‖²  ≤  ∑_p ‖C_p‖² .
```

The exact identity is

```
‖∑_p C_p‖²  =  ∑_p ‖C_p‖²  +  gramDebt,        gramDebt = ∑_{p ≠ p'} Re ⟪C_p, C_{p'}⟫,
```

(`nsq_sum_herm`, `gramDebt_eq`, `gramDebt_pair`), so (†) is exactly the claim
that the **between-block Gram debt** is never positive.  The open question was
whether the *physical* cells — as opposed to abstract compressed blocks — make
that debt harmless: does the off-diagonal kernel, grouped by Bony class and
rewritten with the curl/radial identities, acquire a second symbol difference
or an orthogonality relation?

## What the off-diagonal kernel is

`blockCell_output_form`: for divergence-free legs the block cell contains **no
leg wavevector** at all,

```
C_p = i (u_p·k) P_k u_q + i (u_q·k) P_k u_p .
```

`herm_blockCell_expand`: hence every off-diagonal Gram entry is exactly

```
⟪C_p, C_{p'}⟫ = Σ (over the four leg pairings)  conj(i u_x·k) · (i u_y·k) · ⟪P_k u_x', P_k u_y'⟫ .
```

Each term is a **product** of two output symbols with a Gram entry of two
Leray-projected leg amplitudes.  No difference of symbols appears, and the
projected legs are just vectors in the plane `k^⊥ ⊆ ℂ³`, with no reason to be
orthogonal.

## The answer: no gain, and it is not an artefact

**A physical helical counterexample.**  Output `k = (0,0,2)`; two blocks

```
{ (4,8,1), (−4,−8,1) }   and   { (8,4,1), (−8,−4,1) },
```

all four legs of length exactly `9`, each carrying an *exact curl eigenvector*
with integer real and imaginary parts (`ceU_helical_*`), all divergence free
(`ceU_divFree`).  Both blocks lie in the same Bony class `HH→low` with the same
`θ = 2/9 < 1/2` (`bonyClass_ceP1`, `bonyClass_ceP2`), have the same helicity
signature `(+9, −9)` and the same leg lengths — every symbol difference between
the two blocks vanishes identically.  Exactly:

```
C₁ = (−288, 144, 0),     C₂ = (−144, 288, 0),
‖C₁‖² = ‖C₂‖² = 103680,  Re ⟪C₁,C₂⟫ = 82944,   gramDebt = 165888 > 0,
25·(Re ⟪C₁,C₂⟫)² = 16·‖C₁‖²‖C₂‖² ,
```

i.e. the between-block Gram entry sits at **4/5 of its Cauchy–Schwarz maximum**
while all available symbol differences are zero
(`between_block_gram_not_paid_by_symbols`).  So there is neither an
orthogonality relation nor a second symbol difference to be extracted.

**No constant helps either.**  A one-parameter family in the same fibre
(`famU`, `famBlocks`) has `n` distinct partner blocks with *identical* cells, so

```
‖∑_{p∈S} C_p‖² = card(S) · ∑_{p∈S} ‖C_p‖²
```

(`famBlocks_mass_eq_card_mul`), and therefore no constant `K` satisfies
`‖∑ C‖² ≤ K ∑ ‖C‖²` uniformly over divergence-free configurations
(`no_cardinality_free_constant`).  The debt of that family is
`4n² − 4n` (`gramDebt_famBlocks`).  Since the Cauchy–Schwarz bound
`‖∑ C‖² ≤ card(S)·∑‖C‖²` always holds (`nsq_sum_blockCell_le_card_mul`), the
family shows the cardinality factor of the squared route is exactly sharp
(`card_factor_sharp`).

## The counterexamples are real velocity fields

Both configurations are divergence-free amplitude configurations, which is all
the refuted propositions quantify over.  They are moreover realizable by honest
*real-valued* periodic fields: the Hermitian completion `realify u a = u a +
conj u(-a)` restores `u(-a) = conj u(a)` (`realify_hermitian`), preserves
divergence freeness (`realify_divFree`) and does not change a single cell of the
fibre of `k = (0,0,2)`, because the reflected legs sit at third coordinate `-1`
and their partners under `p ↦ k - p` are unoccupied.  Hence
`no_cardinality_free_constant_real` and
`between_block_gram_not_paid_by_symbols_real`: the obstruction survives the
reality condition verbatim.

## Consequences for the route

* `not_partnerCompressed_fibre_subadditive` — (†) is false.
* `not_partnerCompressed_fibre_subadditive_helical` — it stays false with
  helical amplitudes, equal leg lengths, equal helicity eigenvalues and a common
  Bony class.
* `no_cardinality_free_constant` — no constant version survives.

So the whole-fibre ℓ²/Gram route is closed as a source of the missing quadratic
companion: the payment cannot come from the *symbols* of the compressed blocks.
Note what is **not** touched: the ℓ¹ fibre bound
`‖f_k‖ ≤ |k| ∑_p ‖u_p‖‖u_{k−p}‖` of `WaleffeOutputGainFibre.lean` remains
valid and cardinality free — the failure is specifically of the squared,
blockwise-mass form.  Any remaining route must use information that separates
the two blocks above, which are indistinguishable by output frequency, leg
frequencies, helicity and Bony class, and differ only in their relative lattice
orientation inside the dynamics (trajectory/forcing-work information).

Nothing here proves or weakens the Clay periodic target; this tranche is a
falsification that removes a plausible but false next move.
