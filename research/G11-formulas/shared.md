# Sharing one computed value in the G11 circuit

A circuit of size at most 21 cannot compute G11 by making **one intermediate value** available to an otherwise tree-shaped AND/OR computation in either of the following cases.

- The intermediate is a disjunction of any subset of the eleven inputs.
- The intermediate is any AND/OR formula using at most four binary gates.

The intermediate can be used any number of times. Primary variables can be read any number of times in both parts. Multiple shared intermediates and larger mixed intermediates remain open. The formula bound uses a Lean formalization. The extension here uses a mathematical reduction, Python enumeration, and SAT. [Formula result](README.md)

## Adding one wire to the rectangle game

Write `t` for the number of gates used to compute the intermediate and `q` for the number of rectangles labeled by it in a partition. The downstream formula has at most `22 − t` leaves. Treat the intermediate as a new input. A leaf labeled by it can cover any rectangle in `A × B`, where `A` is the set of positive edges on which the intermediate is true and `B` is the set of negative columns on which it is false.

The SAT problem picks the smaller of `A` and `B`, enumerates each nonempty subset of that side, and chooses partners on the other side. Rectangles with the same fixed side and label can be merged. A pattern wholly eligible for an original variable can use the original variable at the same cost. The remaining patterns enter the same exact cell-cover and total-rectangle constraints as the primary variables. This representation includes every partition that could come from a formula. [Encoder](g11-shared-or.py)

If `q ≤ 1`, partition the intermediate's positive/negative game using its own formula, intersecting that partition with the auxiliary rectangle. At most `t + 1` original-variable rectangles take its place, giving a partition of size at most 22. That contradicts the checked baseline. If `B` contains at most one column, every auxiliary rectangle can first be merged into one. Among the 2,036 nontrivial OR subsets, 1,337 take this one-column argument and the other 699 give unsatisfiable SAT instances.

## Mixed gates

On the sixteen edge rows and twenty-four maximal independent columns, each input and each formula has a 40-bit truth signature. At cost `t`, intersect or unite the signatures of formulas of sizes `i` and `t − 1 − i`. Keep the first occurrence of each signature. An induction on formula trees proves completeness at each size. Two formulas with the same signature have the same auxiliary rectangles, so the minimum cost dominates all later occurrences. [Enumeration](g11-prefix.py)

| First attained at this many gates | Distinct signatures | Cases requiring a new SAT call |
| ---: | ---: | ---: |
| 1 | 109 | 0 |
| 2 | 1,110 | 0 |
| 3 | 8,824 | 332 |
| 4 | 59,214 | 1,499 |

For the remaining reductions assume `q ≥ 2`. On a single positive row, any set of auxiliary cells can be partitioned using at most two original labels, one for each edge endpoint. One label suffices if some endpoint is absent from all the columns under consideration. Sum this row-by-row bound over `A`. If it is at most `t + 2`, replacing all auxiliary pieces gives at most `22 − t − q + (t + 2) ≤ 22` rectangles.

A second reduction picks a disjunction on input set `S` costing `s = |S| − 1`. Intersect each auxiliary rectangle with the eligible rows and columns of that disjunction. Charge the exceptional cells row by row, first on rows where the disjunction is false, then on the remaining rows at columns where it is true. If the charge is at most `t − s`, the result is a valid augmented partition of at most `22 − s` rectangles for the chosen disjunction. The disjunction exclusion already rules this out. For singleton `S` this is the baseline 22-rectangle bound.

The SAT solver found all 1,831 remaining signature instances unsatisfiable. The complete disjunction and mixed-signature discovery records are included. The two commands below regenerate LRAT certificates, check them with Lean's standard LRAT checker, and compare the statuses with these records. For long lists of possible cell labels, the certificate replay uses a linear prefix counter to enforce mutual exclusion. The discovery records mark the cases run with this sequential encoding. Other discovery cases used all pairwise exclusions. The shared-wire reductions and enumeration themselves are implemented in Python. Each run uses one solver process at a time and discards a certificate after checking it. [Disjunction records](or-discovery.json) · [Mixed records](mixed-discovery.json) · [DIMACS and LRAT checker](CheckDimacs.lean)

```sh
bash research/G11-formulas/check-shared.sh or
bash research/G11-formulas/check-shared.sh mixed
```

The full replay checked 699 disjunction certificates with 14,000,501 LRAT actions and 1,831 mixed certificates with 37,207,295 LRAT actions. The manifests include the SHA-256 hash of every generated constraint system and its proof length. [Disjunction certificate manifest](or-certificates.json) · [Mixed certificate manifest](mixed-certificates.json)

Append `--quick` to either command to check one SAT exclusion. The pinned Lean toolchain, its bundled CaDiCaL solver, and Python 3 are sufficient for replay. The original discovery used the optional `python-sat` package.
