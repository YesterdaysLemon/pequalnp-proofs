# Six-input monotone functions through eight gates

Every monotone function on six inputs computed with at most eight AND/OR gates and arbitrary free wire complements has an AND/OR circuit with the same or fewer gates. This also settles the project’s comparison for every six-input AND/OR/NOT circuit of total size at most nine. If such a circuit uses a NOT, it has at most eight binary gates. Circuits consisting entirely of AND/OR already meet the comparison.

The computation partitions all 7,828,354 labeled monotone truth tables on six inputs. Of these, 7,785,062 depend on every input. Input permutations and De Morgan duality split the essential functions into 8,170 classes. Functions with an inessential input are covered by the complete smaller catalogue. [Five-input catalogue](../five-input-circuits/)

## Exact counts

These counts include only functions depending on all six inputs. An intermediate wire may feed any number of later gates.

| Gates | AND/OR classes | Labeled AND/OR functions | Classes with free complements | Full binary classes | Labeled full binary functions |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 5 | 33 | 5,504 | 33 | 33 | 5,504 |
| 6 | 37 | 21,360 | 37 | 37 | 21,360 |
| 7 | 166 | 90,440 | 166 | 166 | 90,440 |
| 8 | 319 | 261,928 | 319 | 322 | 266,248 |

The three additional full-basis classes have representatives `e888a080c8888080`, `e8a8c888e8a0c880`, and `eae8ea88eae80000`. Each contains 1,440 labeled functions. Each has an eight-gate circuit with XOR, and each requires at least nine AND/OR gates even with free complements. The data give explicit circuits for all 558 classes that can be computed with at most eight full-basis gates. Within each record, the sizes are in the order full binary, AND/OR with free complements, and AND/OR. A size recorded as 9 means at least 9. [Catalogue and witnesses](frontier.json)

## Verification

The replay first verifies the smaller catalogue. It constructs each six-input monotone table by choosing a lower five-input table and an upper five-input table that contains it. Adjacent input transpositions and duality generate each orbit. For each essential representative, the code evaluates the stored upper witnesses and rules out every required smaller budget. It tests absent representatives at budget eight as well. [Orbit enumeration](orbits.cpp) · [Verification program](replay.py)

For the lower bounds, fixing one or more essential inputs removes at least one binary gate per fixed input whenever the remaining function is nonconstant. The known five-input minima leave 1,000 of the 8,170 classes as candidates at size eight. The remaining comparisons use bounded live-wire search with lower bounds on smaller subcubes. This is a native exhaustive computation. The generic gate-elimination theorem used in the search has a Lean proof. [Restriction theorem](../induced-small-graphs/EssentialRestrictions.lean) · [Search implementation](../five-input-circuits/bounded-circuits.cpp)

Run the following from the repository root with a C++20 compiler and Python 3. Searches run in sequence.

```sh
bash research/six-input-frontier/check.sh
```
