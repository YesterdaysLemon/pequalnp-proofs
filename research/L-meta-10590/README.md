# The cost of one negation on a seven-vertex graph

The minimum is **13 gates** both for monotone circuits and for circuits with at most one NOT. Exhaustive C++ searches give both optima. The standalone Lean proof checks the posted comparison by showing that any circuit containing a NOT needs at least twelve binary gates. An explicit monotone circuit uses thirteen gates and works on all 128 inputs. [Upstream submission](https://github.com/open-goat/pequalnp-proofs/pull/15586)

| Circuit question | Exhaustive result |
| --- | --- |
| Seven vertices, AND and OR | No circuit with 12 gates. A 13-gate circuit works on all 128 inputs. |
| Seven vertices, up to one free NOT | No circuit with at most 11 binary gates. A circuit using a NOT therefore has at least 13 gates in total. |
| Delete vertex 4, allow arbitrary free complements | No circuit with at most 10 binary gates. An 11-gate monotone circuit attains the bound. |
| Delete vertex 4 and one more vertex, allow arbitrary free complements | Both isomorphism classes need eight binary gates. |

The seven-vertex graph has three adjacent twin pairs, A = {0,2}, B = {1,3}, and U = {5,6}. The cross edges join A to vertex 4 and join U to A and B. Within each twin pair compute its OR and its AND. Compute the other terms as 4 AND OR(A), and OR(U) AND (OR(A) OR OR(B)). Four OR gates combine the five terms. The circuit has 13 gates.

## Why the searches cover circuits with sharing

A shortest circuit can discard a wire after its last use. When two wires feed a gate, the search keeps either, both, or neither of them for future gates. The other live wires persist. Each binary gate can decrease the number of live wires by at most one. The output of a constant or redundant gate can be substituted directly. All input variables are essential on the full cube and on every graph searched here. The upstream proof of the backwards compression to live wires appears in L-meta-9136. [Signed live-wire search](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_9136.lean)

For monotone circuits the 13 minimal positive and eight maximal negative assignments suffice. The one-NOT search uses all 128 assignments. On a monotone suffix, an earlier wire can replace a proposed gate if it is at least as large on all positive rows and at most as large on all negative rows. A positive bank vector below a negative bank vector rules out a monotone continuation. With a NOT available, collect the positive and negative endpoints of all those order violations. A negative endpoint below a positive endpoint rules out every one-NOT continuation. Conversely, taking the upward closure of the negative endpoints gives an admissible input to the NOT, after which the positive states can be separated by another upward closure. BankInterpolation.lean checks this characterization on any preorder.

In the free-complement search every signal is represented in the polarity that is false on the all-zero input. The four possible new signals on two representatives are their AND, their OR, the first AND the complement of the second, and the second AND the complement of the first. A positive and a negative assignment with identical live bank vectors rule out every continuation. The search compares full state keys when it uses a cache. Root permutations preserve the graph. A node or memory cutoff gives an explicit UNKNOWN result.

## Independent check through a smaller graph

Fix vertex 4 to false. It is essential in the seven-vertex graph. In the live-wire computation of any circuit, its input becomes a constant. In a binary circuit with free wire complements, each future gate removes at most one live constant without an equivalent gate disappearing from the restricted circuit. More precisely, if there are k future binary gates and c currently live wires become zero, the restricted nonconstant output can be built with at most k − c gates from the nonzero projected wires. LiveRestriction.lean checks this statement for any two gate systems satisfying its collapse and preservation hypotheses. The six-vertex lower bound of 11 binary gates therefore gives 12 for the seven-vertex graph with arbitrary free complements.

The six-vertex graph is two copies of K4 sharing the edge {5,6}. Its 11-gate circuit computes the four-input OR on the private vertices, the OR and AND of the shared pair, and the AND of each private pair. One AND combines the two OR signals, and three OR gates sum the four resulting terms. The two-vertex deletions have exhaustive signed lower bound eight. The signed checker in seven_minors.cpp uses these smaller lower bounds to charge binary gates that become aliases or constants. It can repeat the six-vertex calculation with the charges disabled.

## The signed-circuit certificate

The certificate uses three graphs. Each row describes a set of signals that must still contribute to the output. For each pair of signals, the checker tries every binary operation and each choice of whether either input stays live. It rules out the resulting state by the number of remaining gates, by a positive and a negative input that the surviving signals cannot distinguish, by a cofactor lower bound, or by a previously checked state under a graph symmetry. The symmetry, the signals and the cofactor bounds are checked at every such link.

| Graph | Binary gates ruled out | Distinct states |
| --- | ---: | ---: |
| Four-vertex clique | 6 | 61 |
| One universal vertex joined to two disjoint edges | 7 | 300 |
| Two four-vertex cliques sharing an edge | 10 | 374 |

Deleting a private vertex from the six-vertex graph leaves a four-clique and one extra vertex. Setting that extra vertex to false recovers the clique and removes at least one binary gate. Deleting a shared vertex gives the five-vertex graph in the table. These two bounds supply the six single-vertex cofactors. Deleting both private vertices of either clique leaves the other clique intact. Adding these two seven-gate lower bounds reduces the six-vertex search from 1,868 states to 374. A separate 967-state enumeration checks the private-vertex deletion directly.

The following commands reproduce the three tables. Python 3 and its standard library suffice. The first two commands write their JSON files beside the scripts. The last command prints the Lean declarations for a chosen case, including every transition witness.

```sh
python3 seven_certificate.py clique universal six
python3 seven_reasons.py clique universal six
python3 certificate_tables.py six > six-tables.lean
```

The compact representation numbers signals once per graph. A row selects its live signals, records each remaining cofactor lower bound, and supplies indices for the transition witnesses. Each witness identifies either one obstruction or a lower-budget row and a variable symmetry. The checker reconstructs the possible moves from the signals themselves. A missing or inconsistent witness fails the check.

## Replay

The C++ programs require a C++20 compiler. Commands here start in this directory.

```sh
c++ -std=c++20 -O3 seven_live.cpp -o seven_live
./seven_live -1 12 0 600000000
./seven_live -1 11 1 250000000
./seven_live 4 10 2 200000000
c++ -std=c++20 -O3 seven_minors.cpp -o seven_minors
./seven_minors 0 7 0 2
./seven_minors 5 7 0 2
./seven_minors -1 10 1 2
./seven_minors -1 10 0 2
```

The first three runs respectively visited 486,971,857, 160,427,874, and 110,361,422 states including immediate pruning. In the independent six-vertex replay, using the five-variable bounds and graph symmetry reduced the number of expanded states to 1,868. Without the five-variable bounds the independent replay expanded 131,681 states.

Run the Lean files with the upstream repository's pinned toolchain. SevenBounds.lean uses L-meta-9526 for the ten-gate lower bound after deleting vertex 0 and for its gate-elimination lemma. [Upstream dependency](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_9526.lean)

```sh
lake build PEqualNP.Outside.L_meta_9526
lake env lean /path/to/SevenBounds.lean
lake env lean /path/to/BankInterpolation.lean
lake env lean /path/to/LiveRestriction.lean
```
