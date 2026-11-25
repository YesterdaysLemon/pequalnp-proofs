# Six-input functions with the same five-input restriction

Fix the sixth input at one. Write `a,b,c,d` for inputs 0, 1, 2, and 4, and let `T₂` mean that at least two of them are true. The common restriction is

```text
H = (x3 AND T₂(a,b,c,d)) OR (a AND b AND c AND d).
```

Every six-input function that restricts to `H` and depends essentially on its sixth input requires at least **ten binary gates**, even when complements have zero cost. A circuit containing a NOT therefore costs at least eleven gates in the project's model. If the function has a monotone circuit of size at most eleven, every general circuit has a monotone replacement of no greater size.

The Lean theorem `SharedBlock.sharedCofactor` accepts the cofactor identity, a witness that flipping input 5 changes the function, and a monotone implementation. It reuses the checked nine-binary-gate lower bound for `H`. Restricting the essential sixth input to a constant removes at least one binary gate. The proof handles zero-input and unary gates, invalid wire references with the project's default values, output wires, and multiple uses of a gate. [Five-input certificate](https://github.com/open-goat/pequalnp-proofs/pull/16111)

## The assigned table

For `0xfe80e800fe800000`, assigning rows 11 and 43 changes only input 5 and changes the target value. `Sibling12074.lean` gives an eleven-gate circuit, checks it on all 64 assignments, and proves the exact positive statement opposite L-meta-12075. The independent monotone enumeration excludes ten gates in 1,639,457 visits for this labeling. Its monotone and unrestricted minima are both eleven. Two upstream submissions already covered the positive statement. [First submission](https://github.com/open-goat/pequalnp-proofs/pull/16387) · [Second submission](https://github.com/open-goat/pequalnp-proofs/pull/16407)

## The finite family

The high 32-bit truth table for `H` is `fe80e800`. A six-input monotone extension has a monotone low word whose positive set is contained in that of `H`. Generating the 7,581 monotone five-input truth tables yields 227 possible low words. Removing the single case in which the sixth input is redundant leaves **226 labeled functions**, or **38 classes** under permutations of the four data bits.

The exhaustive search divides the 226 functions into three groups.

| Monotone minimum | Functions | What follows for unrestricted circuits |
| --- | ---: | --- |
| 10 gates | 30 | The same exact minimum follows from the shared binary lower bound. |
| 11 gates | 58 | The same exact minimum follows because every circuit containing a NOT costs at least eleven. |
| At least 12 gates | 138 | The shared binary lower bound gives ten. Deciding whether a NOT saves a gate here needs more information. |

The classification through size eleven covered every class, with a largest individual search of 56,582,935 visits. The shared comparison theorem is kernel-checked. The class counts and monotone optimality checks additionally use the C++ enumeration and independent Python witness replay.

The Python replay verifies every saved witness on all 64 rows and computes class sizes from the actual permutations. The C++ enumerator retains every possible choice of which gate operands remain available for reuse. Monotone boundary rows suffice because every assignment lies above a minimal positive row or below a maximal negative row. A size search reports `UNKNOWN` when it reaches its node cap.

## Replay

The proof dependency is present on the fork branch `research/shared-five-input-restriction`. With the repository's pinned Lean toolchain and Mathlib dependencies available, run `bash research/L-meta-12075/check.sh` from that checkout. For the independent finite enumeration, run these commands in this directory.

```sh
python3 family-search.py --results family-results.json
g++ -std=c++20 -O3 family_search.cpp -o family-search
./family-search fe800000 -1 10 0 10000000
./family-search fe800000 -1 11 0 10000000
python3 family-search.py --search ./family-search --budget 10 --node-limit 5000000 --results replay.json
python3 family-search.py --search ./family-search --budget 11 --node-limit 300000000 --results replay.json
```
