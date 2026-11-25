# An eleven-gate six-input monotone function

Let `a,b,c,d` stand for inputs 0, 1, 2, 4. Write `T₂` for “at least two of those four inputs are true.” The posted table `0xfe80e800fe00e800` computes

```text
(x3 AND T₂(a,b,c,d)) OR (x5 AND a AND b AND c AND d).
```

The optimum is **eleven gates** for both monotone circuits and general fan-in-two AND/OR/NOT circuits. The complete Lean proof establishes the posted comparison. A separate exhaustive monotone search supplies the lower bound of eleven for the exact optimum. The desk originally assigned the claim that some general circuit beats every monotone circuit. The positive twin expresses the comparison proved here. [Upstream proof submission](https://github.com/open-goat/pequalnp-proofs/pull/16111)

## An eleven-gate circuit

Compute `a AND b`, `c AND d`, `a OR b`, and `c OR d`. The AND of the last two detects a true input in each pair. Taking the OR of the first two pair products and that cross-pair condition computes `T₂` in seven gates altogether. Gate eight ANDs it with `x3`. Gates nine and ten form the product of all four data bits and `x5` using the pair products. Gate eleven ORs the two terms. Direct evaluation agrees with the posted table on all 64 inputs.

## Why negations cannot help

Fix `x5 = 1`. This coordinate is essential when all four data inputs are true and `x3 = 0`. A live circuit for the original function must therefore use its input wire. Restricting it to a constant saves at least one binary gate. All remaining gates may use complemented wires without charge. The formal compilation represents each internal wire up to complement and separately handles constant and unary gates.

The five-variable restriction is `(x3 AND T₂) OR (a AND b AND c AND d)`. It needs **nine binary gates even with free complements**. For the lower bound, encode the fifth input as the complement of `x3`. When it is zero the four-variable restriction is `T₂`, which needs seven binary gates with free complements. A 253-state finite certificate propagates this bound through the five-variable search. Its four-variable subcertificate has 61 states. The upper bound uses this nine-gate expression.

```text
((a AND b) OR (x3 AND (c OR d))) AND
((c AND d) OR (x3 AND (a OR b)))
```

At `x3 = 0` it requires both full pairs. At `x3 = 1` it accepts two true inputs from either single pair or one from each.

Returning to the full function, nine binary gates after restriction imply at least ten before restriction. Any circuit that uses even one NOT therefore uses at least eleven gates. For a circuit containing only AND and OR, the circuit itself supplies the monotone witness in the comparison. The independent monotone search excludes a ten-gate circuit in 1,940,838 visits. A second search over full truth tables excludes nine signed binary gates in 4,796,210 visits.

```sh
g++ -std=c++20 -O3 block_search.cpp -o block-search
./block-search -1 10 0 10000000
./block-search -1 11 0 10000000
./block-search -1 9 2 10000000
./block-search 11 8 2 1000000
./block-search 11 9 0 1000000
```

The first argument selects a fixed input. `-1` leaves the whole table intact. Indices 0–5 fix an input to zero and 6–11 fix the corresponding input to one. Mode 0 searches monotone suffixes on the boundary rows. Mode 2 searches signed gates on every row. A node cap returns `UNKNOWN`.
