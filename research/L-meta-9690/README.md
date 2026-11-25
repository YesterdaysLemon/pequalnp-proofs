# Cutting planes for five pigeons and four holes

Two explicit **109-line** cutting-planes refutations of PHP(5,4) are included. The Lean kernel checks the clause axioms, every addition, multiplication and division, and the final contradiction. The project asks for at most 100 lines in L-meta-9690 and 108 in L-meta-9695. Both thresholds remain open in this work. [First refutation](PigeonCapacity.lean) · [Alternative last hole](PigeonAlternate.lean)

For one hole, write its five Boolean variables as `x₁,…,x₅`. The ten collision clauses give all pair bounds `xᵢ + xⱼ ≤ 1`. Sum the three edges of a triangle and divide by two. This gives `S₃ ≤ 1`, where `Sₜ` sums the first `t` variables. Given `Sₜ ≤ 1`, multiply it by `t−1` and add the `t` pair bounds involving the next variable. The result is `t Sₜ₊₁ ≤ 2t−1`. Dividing by `t` gives `Sₜ₊₁ ≤ 1`. Four such capacities sum to four and the five pigeon axioms require at least five.

The construction uses each of the 45 clauses once, 44 additions, and five further operations per hole. The same generator works for every number of holes `h ≥ 2`. Writing `A = (h+1) + h·binom(h+1,2)` for the clause count, the construction lists `2A−1 + h(2h−3)` lines. The included Lean files specialize the construction to four holes. [Generator](php-five.py)

The second proof derives `S₅ ≥ 2` for the last hole from the pigeon axioms and the first three capacities. Adding that lower bound to the four incident edge bounds forces the fifth variable to zero after division by three. The same elimination forces a second variable to zero, and the remaining triangle gives the contradiction. Sharing two intermediate bounds replaces two scalar multiplications. [Search witness](last-witness.txt)

## Search for shorter proofs

The program groups premises into sums. An extra operation divides or multiplies a sum, or makes a sum available to two later groups. Coefficient divisibility is tested separately at each vertex and the constant side is rounded only for a complete assignment. Permuting the four neighbors of vertex zero removes redundant assignments. All searches below use the ten pair clauses exactly once and omit Boolean bound axioms. [C++ search](php-last-hole.cpp)

* For the last hole with the premise `S₅ ≥ 2`, no search with up to four extra operations found a contradiction using multipliers through ten and divisors through twelve. At exactly four extras the program tested 1,078,945 operation patterns. It finds the included witness with five extras.
* For a single hole, no derived inequality with all final coefficients between one and six excludes the uniform point `xᵢ = 1/4` within four extras, with multipliers through six and divisors through eight. At exactly four extras the search tested 15,886,231 completed edge allocations after arithmetic and symmetry pruning.
* The search also tests uniform coefficients through twelve for partially aggregating the last two or three holes. With the same scalar ranges, four extras per hole do not produce a bound strict enough to refute their combined load by a single final sum. The one-hole search recovers `4 S₅ ≤ 7` with four extras.

Proofs may mix individual pigeon clauses and several holes throughout. Those derivations remain outside these finite searches.

```sh
# From this directory
c++ -O3 -std=c++20 php-last-hole.cpp -o /tmp/php-last-hole
for k in 0 1 2 3 4; do /tmp/php-last-hole 5 "$k" 10 12; done
for k in 0 1 2 3 4; do /tmp/php-last-hole 5 "$k" 6 8 6; done
for s in 1 2 3; do for k in 2 3 4; do /tmp/php-last-hole 5 "$k" 6 8 12 "$s"; done; done
/tmp/php-last-hole 5 5 3 4 > /tmp/last-witness.txt
python3 php-five.py --out /tmp/PigeonCapacity.lean
python3 php-five.py --local /tmp/last-witness.txt --out /tmp/PigeonAlternate.lean
cmp PigeonCapacity.lean /tmp/PigeonCapacity.lean
cmp PigeonAlternate.lean /tmp/PigeonAlternate.lean
# From the repository's lean directory, with its dependencies built
lake env lean ../research/L-meta-9690/PigeonCapacity.lean
lake env lean ../research/L-meta-9690/PigeonAlternate.lean
```
