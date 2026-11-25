# Exact circuits for monotone functions on five inputs

An exhaustive computation finds that **free wire complements never reduce the number of AND/OR gates for a monotone Boolean function on at most five inputs**. Allowing all sixteen binary operations saves exactly one gate on 181 of the 7,581 labeled monotone functions of five inputs. Five-input majority is one of them. It needs ten AND/OR gates, even with free complements, and nine gates over the full binary basis.

The circuits allow unrestricted reuse of intermediate results. Each gate has two inputs. Constants are free in all three models. In the signed model any input, intermediate or output can also be complemented for free. A lower bound in this model applies in particular when each physical NOT is charged. The results here come from a reproducible native computation.

## Functions where the sizes differ

Permuting input labels and taking the De Morgan dual preserve all three minima. The 181 functions form three classes under these operations. Each table is written in hexadecimal with its value on assignment $r$ in bit $r$. Input zero is the low bit of the assignment.

| Representative | Labeled functions | AND/OR | AND/OR with free complements | All binary gates |
| --- | ---: | ---: | ---: | ---: |
| `eac8e880` | 120 | 9 | 9 | 8 |
| `eae8e880` | 60 | 10 | 10 | 9 |
| `fee8e880` (majority) | 1 | 10 | 10 | 9 |

For majority, write $a,b,c,d,e$ for the inputs, $u=a\oplus b$, $v=a\oplus c$, $p=c\oplus u$, $w=d\oplus e$, and $r=d\oplus p$. Four more gates give $p\oplus((u\lor v)\land(w\lor r))$. The catalogue provides the ten-gate AND/OR circuit as well. [Circuits and sizes](circuits.json)

## Coverage and lower bounds

| Number of essential inputs | Labeled functions depending on every input | Classes |
| ---: | ---: | ---: |
| 2 | 2 | 1 |
| 3 | 9 | 3 |
| 4 | 114 | 11 |
| 5 | 6,894 | 95 |

The lookup drops inessential variables and handles constants and single variables directly. The replay generates every antichain of the Boolean cube, checks that the 110 classes are disjoint and exhaustive, and evaluates every witness on every input. Every stored representative is the smallest truth table in its class.

The lower-bound search keeps only wires that a continuation still uses. A first use of two live wires may discard either, both or neither after producing the new wire. These four choices cover reuse in arbitrary circuits. A continuation of $k$ gates can connect at most $k+1$ live wires, and their joint values must separate every accepted assignment from every rejected one. Normalizing each wire to zero at the all-zero assignment leaves AND, OR, the two directed differences, and XOR as the five genuine binary choices. Removing XOR gives exactly AND/OR with free complements.

Each restriction to a smaller subcube inherits a lower bound already verified at a smaller number of inputs. The projection identifies complementary restricted wires. A gate that produces a constant, an original restricted input, or a restricted wire already present leaves the outstanding lower bound unchanged. Every other gate can pay for at most one gate in that bound. Each presently live wire that becomes constant also needs a future gate that disappears under the restriction. The underlying live-wire elimination argument has a Lean proof. [Restriction lemma](../induced-small-graphs/EssentialRestrictions.lean)

The replay checks the level below every reported full-basis size. Where the AND/OR witness matches that size, it proves all three minima. In the three other classes it also excludes a signed circuit one gate smaller than the AND/OR witness. A node limit returns an inconclusive result and fails verification if no search orientation finishes. [Replay driver](catalogue.py) · [Bounded search](bounded-circuits.cpp)

## Replay and lookup

Run from the repository root with Python 3 and a C++20 compiler. The script uses one process for each search, runs the searches in sequence, and deletes its temporary executable on exit.

```sh
bash research/five-input-circuits/check.sh
python3 research/five-input-circuits/catalogue.py research/five-input-circuits/circuits.json --lookup 5 fee8e880
```

The lookup returns gates in evaluation order. Each triple is an operation code followed by two wire indices. Codes 0 through 4 mean AND, OR, left AND NOT right, right AND NOT left, and XOR. Input wires come first. The final gate is the output.

## A six-input application

The assigned L-meta-13114 asks for an advantage from NOT on the table `feeefaeafeccf080`. Its minimum is ten gates even when XOR is available. Restricting the De Morgan dual gives 256 nontrivial subcubes whose lower bounds come from the smaller catalogue. The search rules out nine gates, and a ten-gate AND/OR circuit agrees on all 64 assignments. The replay checks both facts. The ten-gate witness comes from the independently checked positive submission by stasana666. [Six-input replay](six-application.py) · [Upstream positive proof](https://github.com/open-goat/pequalnp-proofs/pull/17601)
