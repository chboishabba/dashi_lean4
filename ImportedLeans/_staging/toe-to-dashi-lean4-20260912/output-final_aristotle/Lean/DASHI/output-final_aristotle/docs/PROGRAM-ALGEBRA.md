# Programs as numbers: the algebra of ontology transformations

This note documents the modules

* [`RequestProject/RelationWords.lean`](../RequestProject/RelationWords.lean),
* [`RequestProject/ProgramAlgebra.lean`](../RequestProject/ProgramAlgebra.lean),
* [`RequestProject/SignedWords.lean`](../RequestProject/SignedWords.lean),
* [`RequestProject/CyclicAlgebra.lean`](../RequestProject/CyclicAlgebra.lean),
* [`RequestProject/CompilerPipeline.lean`](../RequestProject/CompilerPipeline.lean),

which take the idea of a *program–number correspondence* and instantiate it for
the one class of programs this development actually has: the **transformations
of the ontology layer**, i.e. the words in the relations `subclass of` (P279)
and `instance of` (P31), read as operators on items.

The point of the note is as much to say what is *not* proved as what is.

## The ladder, rung by rung

| rung | claimed? | what is actually proved |
|---|---|---|
| `ℕ` — programs are numbers | **yes** | `RelWord.encode : List Link → ℕ` is a bijection (`RelWord.decode_encode`, `RelWord.encode_decode`, packaged as `RelWord.equivNat : List Link ≃ ℕ`). It is bijective base 2: `subclass of` is the digit 1, `instance of` the digit 2. So every transformation of the ontology layer has a Gödel number and every natural number names exactly one transformation. |
| monoid — programs compose | **yes** | Concatenation of words is composition of the operators: `KB.wordStep_append`, with `KB.wordStep_nil` as unit. Words form a free monoid, so composition is associative on the nose; there is no non-associative rung here. |
| `ℤ` — the grading | **yes** | The degree `RelWord.degree` (the number of `instance of` letters) is a monoid homomorphism to `(ℤ, +)` (`RelWord.degree_append`) and is the metaclass level displacement of the operator in any ontology (`Ontology.level_add_degree`). A closed walk therefore has degree zero (`Ontology.degree_eq_zero_of_closed`), which is exactly why a mixed cycle in the data refutes every ontology model (`KB.no_ontology_of_word_return`). |
| `ℤ` with inverses | **yes** | `RequestProject/SignedWords.lean` allows each letter to be run backwards, as the `^wdt:P31` of a SPARQL property path. `SLink`, `sdegree`, `sdegree_append`, `Ontology.level_add_sdegree` and `Ontology.sdegree_eq_zero_of_closed` give an honest integer grading in which a forward and a backward `instance of` step cancel. `KB.roundTrip_isReturn` explains why the corpus searches use forward words only: with inverses every statement closes a loop, so the informative invariant is the *degree* of the loop and not its existence. |
| functoriality — compilation | **yes** | `KB.wordStep_mono` and `CompilerPipeline.wordStep_compiled_mono`: a stage that only deletes statements maps runs of a word to runs of the same word, so the repair pipeline is a morphism of transformation algebras. `CompilerPipeline.compiled_answers_subclass` / `compiled_answers_instance` say the optimisation is semantics-preserving; `compiled_size` says it is a real optimisation (2257 → 2253 → 2027 `subclass of` statements). |
| `ZMod d` — phases | **yes** | A strongly connected component of period `d` carries a `ZMod d`-valued phase certificate (`Periodicity.isPeriodDivisor_of_phase`, and the reachability-only variant `Periodicity.isPeriodDivisor_of_phaseCertB`), and then its return times are exactly the positive multiples of `d`. |
| finite periodicity | **yes** | On a finite carrier the powers of a relation are eventually periodic (`RelAlg.exists_eventually_periodic`). For the cyclic part of the downloaded corpus this is exact and computed: the eleven items on a `subclass of` cycle carry a permutation of **order exactly twelve** (`CyclicAlgebra.cyclicRel_order_twelve`), twelve being the least common multiple of the four component periods 2, 4, 3, 2 (`cyclicRel_order_eq_lcm`). Its phase group splits as `ZMod 12 ≃+* ZMod 4 × ZMod 3` (`cyclicPhaseCRT`, with `cyclicOrder_factorization : 12 = 2 ^ 2 * 3`). |
| `ℚ` | no | Nothing in the data or the semantics produces a division or a localisation of the transformation monoid. Not attempted. |
| `ℂ`, `ℍ`, `𝕆` | **no** | There is **no** complex, quaternionic or octonionic structure anywhere in this development. No non-commutative or non-associative multiplication beyond word concatenation is constructed, and none is suggested by the corpus. |
| Clifford algebras | **no** | Not constructed. There is no quadratic form on the item set in this development. |
| Bott periodicity | **no** | Not present, and not implied. The period twelve above is the least common multiple of four independent cycle lengths in one downloaded dataset; it has **no proved relation** to the 8 of real Bott periodicity, nor to the 2 of the complex one. Any resemblance is a coincidence of small numbers. |

## Reading the table

The honest summary is: the correspondence works cleanly up to and including a
**graded, finitely-periodic transformation monoid with a Gödel numbering** and a
compiler acting on it by morphisms. That is a genuine algebraic object, and
every statement about it in the table is machine-checked. The higher rungs of
the informal ladder — division algebras, Clifford algebras, Bott periodicity —
are not instantiated here, and the modules above deliberately avoid language
that would suggest otherwise.

## Where the numbers come from

The corpus is the downloaded Wikidata sample described in [`CORPUS.md`](CORPUS.md);
the cycles and the repair are the subject of [`PERIODICITY.md`](PERIODICITY.md)
and the defect report; the widened search over relations, words, phases,
feedback sets and label collisions is documented in [`SPECTRUM.md`](SPECTRUM.md).
