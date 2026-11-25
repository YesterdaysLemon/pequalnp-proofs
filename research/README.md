# P vs NP contribution notes

These are proofs, experiments and partial results from assignments taken under the GitHub handle `YesterdaysLemon`. Each directory gives the exact scope of its results and commands for checking them. The project awards contributor credit when its upstream checker accepts a complete posted step or a completed reduction. [Contribution rules](https://github.com/open-goat/pequalnp-proofs/blob/main/CONTRIBUTING.md)

| Assignment | Result | Source |
| --- | --- | --- |
| L-meta-10590 | The seven-vertex graph costs exactly 13 gates with zero or one NOT. The complete Lean submission checks the posted comparison using 374 six-vertex states and two smaller certificates. | [Upstream PR 15586](https://github.com/open-goat/pequalnp-proofs/pull/15586) · [Results and replay programs](L-meta-10590/) |
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
