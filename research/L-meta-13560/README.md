# Two five-input restrictions with a seven-gate lower bound

The six-input monotone function with truth table `0xeee8eae0eec8eac0` has exact circuit size **eight**. The witness uses AND and OR. An exhaustive search excludes seven gates over all 16 binary Boolean operations with free unary operations and unrestricted fan-out. [Desk assignment](https://pequalnp.com/desk/step?gap=L-meta-13560)

Setting input 5 to one gives `0xeee8eae0`. Setting input 4 to one gives `0xeee8eec8` after packing the remaining inputs in their original order. Lean checks a six-gate exclusion for each of these five-input tables. An essential sixth input costs at least one additional gate. The generic Lean theorem [`Six.extension_lower`](SixCofactors.lean) expresses this fact for any checked collection of positive and negative sample pairs.

| Calculation | Result |
| --- | --- |
| Independent full-basis search on `0xeee8eae0` | Budget 6 excluded after 65,158 states |
| Independent full-basis search on `0xeee8eec8` | Budget 6 excluded after 87,872 states |
| Independent full-basis search on the six-input table | Budget 7 excluded after 217,405 states |
| [Monotone circuit](monotone-witness.txt) | Eight gates, output wire 13 |

For fixed input 5, exactly 1,107 monotone six-input functions with that input essential share the first cofactor. For fixed input 4, the corresponding count for the second cofactor is 1,261. Each count comes from comparing the table with all 7,581 monotone functions on five inputs. A monotone extension has lower cofactor strictly below its upper cofactor in pointwise order.

The Lean search packs 256 positive/negative row pairs into 512 bits. A live bank of wires must separate each positive row from each negative row. Conjunction, disjunction, the two directed differences and XOR cover the genuine two-input operations up to free complement. The C++ program uses ordinary truth tables, enumerates the four possible choices of which operands remain live and checks row separation independently.

The desk closed the assignment during verification. The archived Lean results cover both finite searches, their completeness argument, projection to a cofactor and the generic extension theorem. The eight-gate result above uses the C++ replay and the witness's truth table. [Existing positive submission](https://github.com/open-goat/pequalnp-proofs/pull/17623)

From a checkout of this branch with the pinned Lean toolchain and Mathlib cache, run

```sh
bash research/L-meta-13560/check.sh
```

The script checks the archived modules from source, audits the eight-gate witness on all 64 rows, counts the monotone extensions and repeats the three full-basis searches.
