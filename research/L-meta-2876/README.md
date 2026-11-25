# First gates and six-star circuits for the Heawood edge function

The public step [L-meta-2876](https://pequalnp.com/desk/step?gap=L-meta-2876) asks for the last two wires of a 26-gate monotone circuit. This directory gives a smaller search over its first two gates and an exhaustive result for circuits that begin by combining six complete stars. The existence of an unrestricted 26-gate circuit remains open in this work.

## Replacing a wire on the boundary

There are 21 minimal true inputs, one per edge, and 37 maximal false inputs, one per maximal independent set. Suppose an AND/OR continuation computes the target. A replacement for an earlier wire preserves its output function if the replacement is monotone and satisfies both conditions below.

- On each minimal true input, an old value of one implies a new value of one.
- On each maximal false input, a new value of one implies an old value of one.

The continuation is monotone in every incoming wire. It consequently stays true on the first set of inputs and false on the second. Every positive input contains a minimal positive input and every negative input is contained in a maximal negative input. The same argument applies to an entire vector of wires. `BoundaryReplacement.lean` proves this for the project's `Monotone2` circuit evaluator. It also proves that a nonedge pair of distinct input vertices ANDed together can be replaced by false in any monotone continuation computing a graph edge function.

## The first two gates

Take a shortest circuit after propagating constants and bypassing copies. Its gates use two distinct sources. At each step, compare the new wire to every earlier wire and to the two constants. A wire that admits a replacement by this test can be omitted. A constant introduced by replacement can be propagated along AND/OR gates. Because the target is nonconstant, this leaves a circuit with fewer gates. If the first two gates are independent, either can also be tested as a replacement for the other.

`heawood_shards.py` applies this test, then quotients by incidence-preserving permutations and interchange of two independent gates. Testing all 7! point permutations gives 168 that preserve the set of lines. Composing these with point-line duality gives the other 168 symmetries. Each resulting permutation is checked against all 21 edges.

| Prefix | Surviving ordered choices | Symmetry classes |
| --- | ---: | ---: |
| One gate | 112 of 182 | 4 |
| Two gates | 14,238 of 38,220 | 64 |

The four first gates are AND on an incidence (21), OR on two vertices on the same side (42), OR on an incidence (21), and OR on opposite, nonincident vertices (28). Of the two-gate classes, 49 have independent gates and 15 have a second gate that reads the first. The script emits all 64 representatives in the posted numbering of the inputs. Each representative still requires a search of the rest of the circuit.

## Six complete stars

Choose any six vertices. For each one, form the OR of its three neighbors and AND that value with the center. OR the six completed stars together. The prefix uses 23 gates, with two ORs and one AND per center, followed by five ORs. Let its final wire be H.

The search grants every input, both constants, H, and every disjunction of neighbors of an individual chosen center as free suffix inputs. A suffix can also read intermediate values from ORs of complete stars or individual completed stars. Replacing any such value by H only enlarges it on true inputs. The theorem `enlargeSafeWire` justifies making that replacement at every occurrence. The relaxed bank therefore contains everything needed to test a three-gate completion, for any association of the prefix.

`heawood_prefix.py` checked all 3,003 six-element center sets in 24 symmetry classes. **None admits a three-gate completion.** For a three-gate suffix, either both root inputs use at most one gate, or a chain of three gates has a free input at the root. A first gate read by both the root and the second gate is comparable to that second gate, so the root returns one of them. The program enumerates the two remaining shapes on all 58 boundary rows. A second, direct enumeration of small truth tables checks the shape-based implementation. The known seven-star circuit supplies a positive control.

Allowing a fourth suffix gate gives one successful orbit of 14 center sets. These are precisely the choices of six points or six lines. Each completes to the 27-gate circuit by forming the missing star and ORing it with H. None of the 2,989 choices mixing point and line centers works with four gates, even with the extra free side disjunctions. To enumerate four gates the program fixes the first gate, adds its value to the free bank, and runs the complete three-gate test.

## Reproduction

From this directory, run the following with Python 3.

```sh
python3 heawood_shards.py
python3 heawood_shards.py --json
python3 heawood_prefix.py
python3 heawood_prefix.py --four
```

From the repository's `lean` directory, the following commands check the semantic replacement lemmas.

```sh
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.LowMergeWires
lake env lean ../research/L-meta-2876/BoundaryReplacement.lean
```

`heawood.cpp` is a separate heuristic search. It mutates and resynthesizes gates, starting from damaged 26-gate circuits or from correct circuits with extra gates. Before writing a candidate of size at most 26 it checks the output on all 16,384 inputs. A ten-minute, single-core run with seed 2876 found no witness. Its closest 26-gate candidate missed one boundary row, and its smallest correct circuit used 27 gates.

```sh
c++ -std=c++20 -O3 heawood.cpp -o heawood
./heawood 600 2876 witness.txt
```
