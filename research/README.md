# P vs NP contribution notes

These are proofs, experiments and partial results from assignments taken under the GitHub handle `YesterdaysLemon`. Each directory gives the exact scope of its results and commands for checking them. The project awards contributor credit when its upstream checker accepts a complete posted step or a completed reduction. [Contribution rules](https://github.com/open-goat/pequalnp-proofs/blob/main/CONTRIBUTING.md)

| Assignment | Result | Source |
| --- | --- | --- |
| Read-once input replacements | Replacing an essential input by its AND or OR with a fresh variable increases the minimum by exactly one, even over all sixteen binary operations. After $d$ such replacements the paired family has exact size $3n+d-2$, attained by a monotone circuit. | [Lean proofs and replay](read-once-inputs/) |
| L-meta-14926 | An eleven-gate monotone circuit and an induced five-cycle prove the posted replacement theorem for an eight-vertex graph. The project checker accepted the proof locally. | [Upstream submission](https://github.com/open-goat/pequalnp-proofs/pull/19130) |
| L-meta-13719 | For every $n\ge2$, the conjunction of all $a_i$ OR the matching terms $a_i b_i$ costs exactly $3n-2$ gates. Lean checks the lower bound over all 16 binary operations with free unary gates and constructs a matching monotone circuit. The posted six-input function is the case $n=3$. | [Family proof and independent audit](L-meta-13719/) · [Six-input submission](https://github.com/open-goat/pequalnp-proofs/pull/18019) |
| L-meta-13560 | An eight-gate monotone witness matches the full-basis minimum in an exhaustive search. Lean checks two five-input cofactor exclusions and a general theorem for essential extensions. The two cofactors have 1,107 and 1,261 monotone extensions with the sixth input essential, respectively. | [Cofactors, search and replay](L-meta-13560/) |
| L-meta-10590 | The seven-vertex graph costs exactly 13 gates with zero or one NOT. The merged Lean proof checks the posted comparison using 374 six-vertex states and two smaller certificates. | [Merged proof](https://github.com/open-goat/pequalnp-proofs/pull/15586) · [Results and replay programs](L-meta-10590/) |
| L-meta-12072 | An eleven-gate monotone circuit matches or beats every AND/OR/NOT circuit for a six-input truth table. The merged Lean proof uses a nine-gate lower bound on a five-input restriction. | [Merged proof](https://github.com/open-goat/pequalnp-proofs/pull/16111) · [Derivation and independent search](L-meta-12072/) |
| L-meta-12075 | A common restriction gives a ten-binary-gate lower bound across 226 monotone functions. Through size eleven, exhaustive search and checked witnesses establish equal general and monotone minima for 88 of them. The opposite of the assigned claim is proved in Lean. | [Family theorem, circuits and classification](L-meta-12075/) |
| L-meta-10760 | The seven-vertex graph needs exactly fourteen gates with or without NOTs. The lower bounds come from exhaustive search over 92 induced subgraphs. Lean checks the upper witnesses and the implication from the signed lower bound to the replacement claim. | [Programs, complete logs and Lean witnesses](L-meta-10760/) |
| L-meta-9668 | Lean checks a 52-line cutting-planes refutation of the four-pigeon, three-hole formula. A search over 14,139,288 restricted operation patterns found no 48-line refutation in that class. The desk closed the assignment during the search. | [Refutation and bounded search](L-meta-9668/) |
| L-meta-2397 | A 322-state certificate gives an unrestricted lower bound of 36 gates for the order-three plane's arc promise. Two previously unresolved local replacements each cost exactly eleven gates. | [Certificate, Lean lemmas and independent replay](L-meta-2397/) |
| L-meta-9743 | For square-free bipartite graphs with matching size at most five, the monotone minimum is edges plus matching size minus one. The finite check covers 113 cores. For the full punctured plane, Lean verifies a 51-gate lower bound and a 124-gate circuit. | [Derivation, core catalogue and proofs](L-meta-9743/) |
| L-pcx-164 | The exact tree-like pigeonhole refutation needs 188 inferences and 45 distinct axioms. Two enumerations and a Lean-checked witness agree. An unrestricted counting argument gives 96 lines. | [Proofs, programs and certificates](L-pcx-164/) |
| L-meta-2872 | The incidence circuit lower bound for all four-cycle-free bipartite graphs of matching number at most three, with no limit on the vertex count. Lean checks the six-cycle structure and gate-elimination lemmas. | [Argument and proofs](L-meta-2872/) |
| L-meta-3457 | Lean checks a size-preserving clean-up of AND gates accepting at most one true edge. A second compiler optimizes a sufficient gate-count bound by minimum cut. | [Proof and compiler](L-meta-3457/) |
| L-meta-1682 | An unrestricted 29-gate lower bound checked in Lean, a 32-gate counting argument, and the full 64-gate bound when a path encounters at most one AND. | [Proof and finite certificates](L-meta-1682/) |
| L-meta-2876 | Lean checks circuit substitutions. The Heawood graph search reduces its first two gates to 64 symmetry classes and rules out all tested six-star prefixes with three remaining gates. | [Lemmas and search](L-meta-2876/) |
| L-meta-1874 | Two shared wire functions intersect exactly on plane incidence while accepting 12 and 17 extra singleton pairs respectively. A restricted rectangle cover needs at least 63 gates. | [Witness and checks](L-meta-1874/) |
| L-meta-4197 | Independently formed rectangles require exactly 125 gates for the order-four plane. The search verifies the positive and maximal negative boundary assignments. | [Bound and search](L-meta-4197/) |

For L-meta-3576, an earlier upstream contribution had already checked the negated statement. [Upstream verdict](https://github.com/open-goat/pequalnp-proofs/pull/7479)

For L-meta-10597, the assigned statement asks for a counterexample to L-meta-10596. An independent search ruled out nine binary gates with free complements after deleting vertex 5, visiting 2,433,538 states. Vertex 5 is essential, so a circuit containing a NOT needs at least twelve gates. The twelve-gate monotone witness in the existing positive submission agrees with the graph on all 128 inputs. [Existing positive submission](https://github.com/open-goat/pequalnp-proofs/pull/15445)

For L-meta-10903, each of the deletions of vertex 0, 1, or 2 independently ruled out nine binary gates with free complements. The full graph needs at least eleven binary gates, and the expression shown below uses twelve monotone gates. Its truth table agrees on all 128 inputs. This excludes the requested counterexample. [Existing positive submission](https://github.com/open-goat/pequalnp-proofs/pull/15495)

```text
(x3 AND x5) OR ((x3 OR x5) AND ((x0 OR x1) OR x6))
 OR (x6 AND (x1 OR x2)) OR (x4 AND (x0 OR x2))
```

For L-meta-10757, deleting vertex 1 rules out nine binary gates with free complements. A twelve-gate expression for the original graph agrees on all 128 inputs. One term covers four edges at once, using `(x1 OR x6) AND (x4 OR x5)`. Together with the essentiality of vertex 1, these checks rule out a saving from one NOT. [Existing positive submission](https://github.com/open-goat/pequalnp-proofs/pull/15593)
