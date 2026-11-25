# Cutting planes for four pigeons and three holes

`PigeonCP.lean` gives an explicit 52-line cutting-planes refutation in the project's syntax. Lean checked every derivation step, the divisor condition on every coefficient and the final inequality `0 ≥ 1`. The posted threshold was 48. The desk closed this assignment during the search.

The construction proves the four-pigeon capacity of each hole. For that hole, summing the three pair constraints among the first three pigeons and dividing by two bounds their sum by one. Multiply this bound by two, add the three constraints pairing the last pigeon with the others, and divide by three. The resulting capacity is one. Summing the three capacities with the four pigeon obligations yields a contradiction.

The bounded search groups all 22 indispensable clause axioms into sums. A connected proof using each clause once takes 22 axiom lines and 21 additions before counting extra operations. It enumerates additional divisions, multiplications and reuse of a sum, including the option to send that sum to two other sums. For each candidate proof shape, coefficient cancellation can be checked one variable at a time. For each hole the six pair clauses are then grouped by how many go into each sum. The three holes can be combined to check the final rounded constant.

The search without Boolean bound axioms found no 48-line proof with exactly five extra operations, positive multipliers through eight and divisors through nine. It enumerated 14,139,288 canonical operation patterns. The analogous search with exactly six extra operations, multipliers through three and divisors through six found no 49-line proof in 12,987,366 patterns. These restrictions leave other proofs possible.

```sh
g++ -std=c++20 -O3 php_cp_templates.cpp -o cp-templates
./cp-templates 5 8 9
./cp-templates 6 3 6
python3 cp-witness.py --out PigeonCP.lean
```

To check the explicit refutation in the pinned repository, run `lake env lean ../research/L-meta-9668/PigeonCP.lean` from the `lean` directory after building `PEqualNP.Defs`. [Project definition of cutting planes](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/SearchCP.lean)
