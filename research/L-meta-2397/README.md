# Gate lower bounds for the order-three plane

Any monotone Boolean function that accepts the 52 flags of the order-three projective plane and rejects every independent pair of arcs needs **at least 36 fan-in-two gates**. The circuit computing that function may use NOT gates. A 322-state certificate and a separate Python checker establish the bound using published gate-elimination theorems. The posted step asks for 64 gates in the monotone circuit model. The complete 36-gate certificate has a computational replay. Its general branching and support lemmas also have Lean proofs. [Posted step](https://pequalnp.com/desk/step?gap=L-meta-2397) · [Certificate](lower-36.txt) · [Independent checker](replay_arc.py) · [Lean lemmas](ArcRules.lean)

Number the 13 points and 13 lines separately starting at zero. Point `p` belongs to line `l` if their difference modulo 13 belongs to `{0,1,3,9}`. An arc contains at most two points on each line. The dual definition applies to a set of lines. A positive row contains an incident pair. A required negative row consists of a point arc and a line arc with no incidences between them. The latter family contains 12,234 rows, including the empty input.

## Certificate

Each row gives a mask of coordinates held at one, a disjoint mask held at zero, a claimed lower bound, a rule number and its argument. Points occupy the lower 13 bits. Coordinate relabelings identify equivalent restricted problems. The checker tests every supplied permutation against all 52 graph edges. The symmetry is used on the whole promise, so a candidate function need not have any symmetry.

* **1. Essential inputs.** Each counted input has two rows differing at that input with opposite required values. A fan-in-two circuit depending on `e` inputs needs at least `e-1` gates.
* **2. Path or cycle.** The checker evaluates every assignment to the seed coordinates. Those assignments force the exact path or cycle function. It then attaches the remaining free coordinates one by one, checking a witness of essentiality and saving one gate per coordinate fixed to zero in the reverse order. [Path theorem](../../lean/PEqualNP/MetaComplexity/L102.lean) · [Cycle theorem](../../lean/PEqualNP/MetaComplexity/L106.lean)
* **3. Forced singleton positives.** The empty extension is negative and each listed singleton extension is positive. Setting all listed coordinates to zero leaves a nonconstant function. Setting them one at a time therefore saves at least one gate apiece. [One-gate elimination](../../lean/PEqualNP/MetaComplexity/Helpers/ForestElim.lean)
* **4. Three- or four-gate saving.** For every pair of free coordinates the checker verifies that no three of their four cofactors can coincide. Each triple contains two cofactors forced to disagree on a common assignment. Both restrictions at every free coordinate remain nonconstant. The upstream fanout theorem then saves three gates on some zero restriction or four on some one restriction. A minimum-size circuit ensures that the selected coordinate is essential. The checker covers every possible selection. [Fanout theorem](../../lean/PEqualNP/MetaComplexity/L107.lean)
* **5 and 6. Fixed coordinate.** An essential coordinate can be fixed to the selected value at a saving of one gate when the child remains nonconstant.
* **7. Either value.** When both restrictions on an essential coordinate remain nonconstant, at least one saves two gates. The certificate proves the required smaller bound in both children. [Two-gate elimination](../../lean/PEqualNP/MetaComplexity/Helpers/PermInputs.lean)

The full certificate uses 64 support leaves, 47 path or cycle leaves, 140 singleton steps, 31 fanout steps, 19 fixed-zero steps and 21 two-branch steps. Each recursive call fixes more coordinates. The independent checker derives each essentiality witness, cofactor disagreement, exact seed function and attachment directly from the incidence relation. It also checks the complete reachable certificate.

```sh
python3 plane_group.py plane-group.bin
python3 replay_arc.py --group plane-group.bin lower-36.txt
g++ -std=c++20 -O3 arc_game.cpp -o arc-game
P3_SYMMETRIES=plane-group.bin ./arc-game 35 36 2 regenerated-
python3 replay_arc.py --group plane-group.bin regenerated-36.txt
```

## Replacing a few stars

The standard 64-gate upper bound groups the four incident lines at each of the 13 points, ANDs the result with the center and ORs all stars together. Select two, three or four centers, keep the other stars, and group lines with the same nonempty set of selected neighbors into ORs. All gates for those groups are charged separately. The table gives the **minimum** number of additional gates for a single replacement over the resulting inputs, allowing arbitrary depth and sharing inside the replacement.

| Selected centers | Input wires after grouping | Grouping cost | Exact replacement cost | Search visits excluding a one-gate saving |
| --- | ---: | ---: | ---: | ---: |
| Two, `0 1` | 5 | 4 | 5 | 8 |
| Three collinear, `0 1 3` | 7 | 6 | 8 | 104 |
| Three noncollinear, `0 1 2` | 9 | 3 | 11 | 6,002 |
| Four collinear, `0 1 3 9` | 9 | 8 | 11 | 5,506 |

Every optimum above gives 64 total gates. Each positive witness can be checked against all 52 flags and all 12,234 independent pairs of arcs in the uncompressed plane. The last two exact minima close cases left open by the earlier SAT experiment. [Earlier experiment](https://github.com/YesterdaysLemon/pequalnp-proofs/tree/research/generic-plane3-cycle-bound/research/L-meta-1682)

The C++ search enumerates the operator and both operands of every live binary gate. It branches on which operands have further uses. A bank of `b` live wires needs at least `b-1` more gates to converge to a single output. Each sampled input variable has an essentiality witness. A bank can separate the samples only if each positive-negative pair has a wire taking values one and zero respectively. An existing wire can replace a proposed gate if it is at least as large on every positive sample and at most as large on every negative sample. Monotonicity of all following gates justifies this substitution. The search checks first-gate orbit representatives under permutations preserving both boundary sets. A resource cutoff reports `UNKNOWN`. [Row generator](patch_rows.py) · [Exact search](patch_exact.cpp) · [Full witness evaluation](check_patch.py)

```sh
g++ -std=c++20 -O3 patch_exact.cpp -o patch-exact
python3 patch_rows.py 0 1 2 > rows.txt
./patch-exact 1000000 < rows.txt
./patch-exact 1000000 1 < rows.txt > witness.txt
python3 check_patch.py witness.txt 0 1 2
```
