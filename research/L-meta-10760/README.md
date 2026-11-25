# Replacing negations in the seven-vertex graph L-meta-10760

The graph's edge function admits a fourteen-gate monotone circuit. An exhaustive search establishes that every circuit for the function needs **at least thirteen binary gates even with free complements**. A circuit containing a NOT therefore costs at least fourteen gates in the desk's gate model. Together these results give the replacement asserted by L-meta-10760, including circuits with multiple NOTs.

The signed lower bound is a computational result. Lean checks the fourteen-gate construction, all seven vertex-deletion witnesses and the implication from the binary lower bound to the replacement claim. A Lean certificate for the full signed enumeration is still needed for this result to count upstream. [Posted graph and earlier submission](https://github.com/open-goat/pequalnp-proofs/pull/16243)

## The construction

Form the five ORs for the sets `{0,2}`, `{2,5}`, `{3,5}`, `{4,6}` and `{3,4,5}`. The last reuses the OR for `{3,5}`. Take the five products below and combine them with four OR gates.

```text
x0       AND (x2 OR x5)
x1       AND (x3 OR x4 OR x5)
(x0 OR x2) AND (x4 OR x6)
x3       AND x5
(x3 OR x5) AND x6
```

The five products cover exactly the twelve edges. Lean checks these gates on all 128 inputs. Deleting any one of vertices 0 through 5 gives a six-variable function with exact signed and monotone binary size ten. Deleting vertex 6 gives size nine. The Lean witness for each deletion uses the original input order with the missing vertex omitted.

## Exhaustion

The program visits induced subgraphs in order of increasing vertex count. Isolated vertices can be omitted. There are 92 labeled nonempty induced subgraphs in which every selected vertex occurs in an edge, including the full graph. A vertex restriction pays one gate when the removed input is essential and the restricted function is nonconstant.

A live circuit can be read backwards from its output. Its bank contains those currently available wires that a later gate needs. Each binary step chooses two live operands, produces a result and retains either, both or neither operand for reuse. Every bank feeding a single output through `k` remaining binary gates contains at most `k+1` wires. Each positive assignment and each negative assignment must differ on some live wire. When all gates are monotone, they must differ in the direction in which the positive row has a one.

The signed search normalizes each wire by allowing its complement freely and picking the orientation that vanishes at the all-zero assignment. AND and OR then give four possible normalized operations on a pair of distinct wires. Constants, duplicate outputs and unary gates can be simplified. This yields a relaxation of the desk's AND/OR/NOT circuit model.

The lower bound for each proper induced subgraph supplies a further test. Set the omitted primaries to zero and charge a prefix gate only if its restricted result needs a new computation. Zero, an original input and an already available restricted wire are free. Each remaining live wire whose restriction is zero costs at least one additional eliminated gate on the way to a nonconstant output. Combining two zero wires removes at most one from this count because their normalized result is zero. A branch closes when its remaining binary budget cannot meet these obligations. The memoization key includes the bank, the remaining depth and each restriction's outstanding obligation.

At the root the signed search rejects eleven binary gates in 193 calls and twelve in 15,136,754. The run through all subgraphs used no assumed minor bounds. `verify.py` reevaluates the successful circuits on every assignment and checks the coverage of integer sizes by the recorded lower bounds and search verdicts.

The separate monotone search excludes thirteen gates in 409,800,265 calls. At size fourteen it finds a circuit with a different structure from the five-product construction. Thus the exact monotone minimum is **fourteen**, and the same is true with any number of NOT gates. The complete signed and monotone logs are included.

## Replay

```sh
g++ -std=c++20 -O3 -Wall -Wextra induced_signed.cpp -o induced
./induced 120000000 48 12 signed > signed-replay.log
python3 verify.py signed signed-replay.log
./induced 600000000 48 14 mono > monotone-replay.log
python3 verify.py mono monotone-replay.log
```

For the Lean portion, run these commands from the repository's `lean` directory with its pinned dependencies available.

```sh
lake build PEqualNP.Defs
lake env lean ../research/L-meta-10760/Graph10760.lean
```
