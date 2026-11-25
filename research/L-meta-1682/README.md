# Unrestricted lower bounds from cycle restrictions on the order-three plane

[L-meta-1682](https://pequalnp.com/desk/step?gap=L-meta-1682) asks for a 64-gate lower bound. A candidate must accept all 52 incident point-line pairs and reject 468 specified inputs. The following bounds apply to every fan-in-two monotone circuit satisfying those tests. They allow arbitrary depth and wire reuse.

## A Lean proof using 37 of the tests

**Every candidate has at least 29 gates.** The proof uses 26 of the 52 positive tests and 11 of the 468 negative tests. It uses the project's actual circuit evaluator, its one-gate elimination lemma and its exact lower bound for cycles. [Lean proof](GenericCycleBound.lean) · [Upstream cycle theorem](../../lean/PEqualNP/MetaComplexity/L106.lean) · [Upstream elimination lemma](../../lean/PEqualNP/MetaComplexity/Helpers/Elim.lean)

Number points 0 through 12 and lines 13 through 25. Start with the eight vertices

```text
0, 13, 1, 14, 2, 15, 5, 17
```

Their induced graph is an eight-cycle. Its ten maximal independent inputs each extend to one of the eleven selected generic negatives. Every cycle edge is a required positive. With all other vertices fixed to zero, monotonicity therefore forces the complete cycle function on these eight inputs, including inputs the original promise did not specify. That function needs eleven gates.

Order the remaining eighteen vertices so that each new vertex has an earlier neighbor. The corresponding incident pair is positive and the neighbor by itself is negative. The new vertex is therefore essential even after later vertices have been fixed to zero. Fixing it to zero saves at least one gate, and the surviving cycle keeps the residual function nonconstant. Eliminating all eighteen gives the bound of 29. The final Lean theorem takes exactly the original incidence, closure and generic-rejection hypotheses. The enumerator reconstructs the order and its witnesses. [Certificate generator](generic_cycle.py)

## Two applications of the stronger gate-elimination theorem

**Every candidate has at least 32 gates** by the following argument and finite checks. The geometry checks in this section run in Python. The combinatorial circuit results they invoke are the project's checked theorems for three-or-four-gate elimination, one-gate elimination, cycles and paths. [Three-or-four-gate theorem](../../lean/PEqualNP/MetaComplexity/L107.lean) · [Path theorem](../../lean/PEqualNP/MetaComplexity/L102.lean)

The stronger theorem applies when each input restriction stays nonconstant and no pair of essential inputs has three identical truth-table restrictions among its four settings. To check these hypotheses, take any ordered pair of distinct free vertices `p,q`. The program finds a context on other inputs for which the output equals the bit `p` for both values of `q`. It checks a required positive below the input with `p=1,q=0` and a required negative above the input with `p=0,q=1`. Monotonicity handles the other two settings. Reversing the pair gives a context reading `q`. Thus all four restrictions are different, and either value of either coordinate leaves a nonconstant function. All 650 ordered pairs of original coordinates pass this check.

The theorem now deletes some coordinate at zero for a saving of at least three gates, or at one for a saving of at least four. Singer rotations and point-line duality act transitively on the 26 coordinates. The program checks these permutations preserve both complete test sets. Take the first deleted coordinate to be point 0.

| Value assigned to point 0 | Gates saved before the second application | Cases checked after that application | Lower bound after fixing point 0 |
| --- | ---: | --- | ---: |
| Zero | 0 | All 25 choices give a bound of 27 at zero and 26 at one | 30 |
| One | 4 | At zero all 21 choices give 22. At one, 12 choices give 20 and 9 give 22 | 28 |

With point 0 true, each of its four incident lines suffices to make the output true. The input with just point 0 is negative. Each of these four lines can therefore be fixed to zero at a saving of one gate. An edge disjoint from them and point 0 keeps the function nonconstant. The ordered-pair test above then applies to all 21 remaining coordinates. It applies to all 25 coordinates after fixing point 0 false.

For the final bounds, the program locates an induced cycle or path, checks that all of its maximal independent sets extend to generic negative inputs compatible with the assigned bits, and adds remaining essential vertices in an explicit order. At each addition a forced false input becomes a forced positive exactly when the new bit is set. The smallest cases use a five-vertex path. Combining the two cases at the root gives at least `min(3 + 30, 4 + 28) = 32` gates. The 64-gate target remains open in this work. [One application with explicit cycles](generic_fanout.py) · [Two applications and case counts](generic_two_rounds.py)

## The full 64-gate bound with one AND on a path

Suppose every path from an input to the output contains at most one AND. OR gates may be shared and may have arbitrary depth. **The exact minimum in this class is 64.** Here is a direct counting proof.

1. The promise determines every singleton and every two-vertex input. Each of the 52 flags must be true. Every singleton and every other pair occurs inside a generic negative. The Lean theorem `exactOnPairs` checks this with a cover of 25 generic negatives.
2. Discard unused gates, propagate constants and bypass copies. The inputs to a remaining AND are disjunctions of raw variables. Its output reaches the circuit output through ORs. Its two sets of variables must be disjoint, since a shared variable would accept a singleton. A point cannot occur on each side, since that would accept a pair of points. The same holds for lines. Each AND therefore represents a rectangle of points times lines, every pair of which is incident.
3. Two distinct points of the plane share at most one line. Every nonempty rectangle is consequently a star of at most four flags. Choose a center for each AND, breaking the tie arbitrarily for a single edge. For a center `v`, let `t_v` count its AND gates and `d_v` count the distinct neighbors they cover. Their neighbor-side OR networks use at least `d_v − t_v` gates in the sense that their OR count plus `t_v` is at least `d_v`. Joining the `t_v` neighbor wires by another `t_v − 1` binary ORs would compute a disjunction of `d_v` distinct variables, which needs at least `d_v − 1` gates.
4. The ORs counted at different centers are disjoint. Any such OR with support of size one can be bypassed. A shared OR with at least two variables would put two neighbors in the intersection of the neighborhoods of two centers. For centers on one side of the plane that intersection has size at most one. For centers on opposite sides the neighbor variables belong to disjoint sides. Thus the lower ORs and the ANDs together cost at least the sum of the `d_v`, which is at least 52 because all flags must be covered.
5. At least 13 AND gates are needed to cover 52 flags, four per star at most. Their outputs all reach one circuit output through a binary OR network, so at least 12 further ORs are required. These upper ORs have an AND ancestor and cannot feed any of the counted lower networks. This gives `52 + 12 = 64`. Thirteen complete point stars and twelve top ORs attain it.

In particular, any 63-gate counterexample to the posted statement must contain two AND gates on a single input-to-output path. The translation and gate count in this section are a mathematical argument. The pair-test lemma is checked in Lean.

## Search for a circuit

The SAT experiment keeps all but a selected set of point stars in the standard 64-gate circuit. Inside the selected stars, it groups lines with identical selected neighbors into disjunctions and charges for those disjunctions. It asks for a smaller circuit over the resulting inputs. CaDiCaL found no four-gate replacement on the five compressed inputs for two centers, and no seven-gate replacement on the seven compressed inputs for three collinear centers. At eight gates it returned a working three-center circuit, which the program independently evaluated. The three noncollinear and four collinear cases remained unresolved at the tested conflict budgets. The SAT results apply only to these local replacements. [SAT encoding and independent witness evaluation](generic_patch.py)

## Reproduction

The finite geometry and elimination programs use Python's standard library. From this directory run

```sh
python3 generic_cycle.py
python3 generic_fanout.py
python3 generic_two_rounds.py
```

The local SAT experiment also needs `python-sat` with CaDiCaL 1.9.5. To repeat its two completed negative cases, run

```sh
python3 generic_patch.py 0 1 --conflicts 120000
python3 generic_patch.py 0 1 3 --conflicts 1200000
```

From the checkout's `lean` directory, run

```sh
lake build PEqualNP.Defs PEqualNP.MetaComplexity.L106 PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.LowMergeWires
lake env lean ../research/L-meta-1682/GenericCycleBound.lean
```
