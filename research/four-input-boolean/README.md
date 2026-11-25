# Exact binary circuits for every four-input Boolean function

Every Boolean truth table on four labeled input positions can be computed with **at most seven** arbitrary two-input gates. With AND/OR and free wire complements the maximum is **ten**, attained by 320 tables. Allowing XOR and XNOR reduces the minimum for 57,318 of the 65,536 tables. Parity and its complement have the largest difference, three gates versus nine. Fan-out is unrestricted. Constants and unary operations are free in both columns. [Exact sizes and witnesses](circuits.json)

| Input positions | Truth tables | Classes using every input under permutations and complements | Largest unrestricted size | Largest signed AND/OR size |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 16 | 2 | 1 | 3 |
| 3 | 256 | 10 | 4 | 6 |
| 4 | 65,536 | 208 | 7 | 10 |

The catalogue groups functions under input permutation, individual input complementation, and output complementation. Smaller-support cases use the catalogue for their essential variables. Each witness is a list of triples giving the operation and the indices of its two arguments. Codes 0 through 4 mean AND, OR, left AND NOT right, right AND NOT left, and XOR. Normalizing the output polarity makes these operations sufficient. [Enumeration and exact search](enumerate.py) · [Bounded search kernel](../five-input-circuits/bounded-circuits.cpp)

To look up parity of four inputs, use the following command. Bit `r` of the hexadecimal integer is the function value on assignment `r`. Input zero is the low bit of each assignment. The lookup gives the representative, its input permutation and sign changes, the final output sign, and both witness circuits. [Lookup program](lookup.py)

```sh
python3 research/four-input-boolean/lookup.py 4 6996
```

To reproduce the minima, run the following from the repository root. It compiles the C++20 search and rebuilds the catalogue from scratch. It checks the stored witnesses on every row of their representatives and compares the reconstructed optima. The programs run sequentially.

```sh
bash research/four-input-boolean/check.sh
```
