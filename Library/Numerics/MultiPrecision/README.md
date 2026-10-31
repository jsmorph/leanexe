# MultiPrecision: Algorithms A, S, and M of TAOCP §4.3.1

## Request, specification, and program

[The request](request.txt) asks for addition, subtraction, and multiplication of nonnegative integers held as arrays of digits in base `b = 2^32`, least significant first, one digit to a word.  [The specification](Spec.lean) states each result through `value u`, the sum of `u[i] * b^i`, and `digits n x`, the `n` least significant digits of `x`.  The lengths of the results follow Knuth's algorithms: a sum has `k + 1` digits and a difference `k`, where `k` is the larger length of the arguments, and a product has `m + n` digits, where `m` and `n` are the lengths.  A difference `u - v` with `u < v` is `u - v + b^k`, the result of Algorithm S without its final borrow.  `Digits u` states that every word of `u` is below `b`, and the specification says nothing about other arrays.

[The program](Program.lean) follows Knuth's steps.  `add` runs Algorithm A over the `k` positions with a carry of 0 or 1 and appends the final carry.  `sub` runs Algorithm S, which adds `b` to each digit before it subtracts the digit of `v` and the borrow, so that no word wraps, and takes the new borrow as 1 when the sum stays below `b`.  `mul` runs Algorithm M: for each digit `v[j]`, an inner loop adds `u * v[j]` to the product's digits from position `j` on, and the last carry becomes digit `j + m`.  A read past the end of an argument gives 0, so the loops of `add` and `sub` run over both arguments to the larger length.  Each loop's state holds the carry or the borrow before the array that the step changes, so that the step reads the array before it writes it.  Knuth's step M2, which skips a zero digit of `v`, is a shortcut whose omission leaves the product unchanged, and the program omits it.

## The module computes the results

`verified_compile compiled := [width, add, sub, mul]` in [the verified compilation](Compiled.lean) compiles the program into a module whose exports `add`, `sub`, and `mul` are functions 3, 4, and 5.  The generated bounds of `add` and `sub` count only the growth of the result, and the bound of `mul` is one block of `m + n` words, so no function copies an array.

| Theorem | File | Statement |
|---|---|---|
| `prefixValue_digit` | [The proof](Proof.lean) | Digit `i` of the value of the first `n` digits of a digit array is its word `i`, for `i < n`. |
| `digits_eq` | [The proof](Proof.lean) | An array of `N` digits whose value is `x` modulo `b^N` is `digits N x`. |
| `add_result`, `add_eq` | [The proof](Proof.lean) | The loop of Algorithm A and its final carry give `addSpec (u, v)`, for digit arrays of fewer than `2^64` words. |
| `sub_result`, `sub_eq` | [The proof](Proof.lean) | The loop of Algorithm S gives `subSpec (u, v)`, for digit arrays of fewer than `2^64` words. |
| `mul_outer_step`, `mul_eq` | [The proof](Proof.lean) | Each pass of Algorithm M keeps the invariant of the outer loop, and `mul` gives `mulSpec (u, v)` for digit arrays whose lengths sum to less than `2^64`. |
| `add_export`, `sub_export`, `mul_export` | [The compilation](Compiled.lean) | The exports `add`, `sub`, and `mul` of `compiled.module` are functions 3, 4, and 5. |
| `add_call`, `sub_call`, `mul_call` | [The compilation](Compiled.lean) | Each function, called from a ready store with digit arrays, with the bound on the lengths for `mul`, and with room for its generated bound, returns its specification's array without a trap and leaves a ready store. |
| `multiPrecision_file`, `multiPrecision_file_decode` | [The file theorems](File.lean) | `build/verified/multiPrecision.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`prefixValue u q` is the value of the first `q` digits of `u`.  The loop of Algorithm A keeps `prefixValue w j + c * b^j = prefixValue u j + prefixValue v j`, where `w` holds the digits written so far and `c` is the carry, and the loop of Algorithm S keeps `prefixValue w j + prefixValue v j = prefixValue u j + c * b^j` with the borrow `c`.  The inner loop of Algorithm M keeps `prefixValue w' (i + j) + c * b^(i + j) = prefixValue w (i + j) + prefixValue u i * v[j] * b^j`, and the outer loop keeps `prefixValue w (j + m) = value u * prefixValue v j` with the digits from `j + m` on still 0.  Each step's equation follows from the identity of its digit, `t % b + b * (t / b) = t`, by `linear_combination` over the integers.  The limb routines of [the Uscale module](../Arithmetic/Uscale/README.md) use the same representation, which they state with `val` and `Limbs`.  The axiom reports of the three call theorems name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.MultiPrecision.Compiled
tests/verified/run.sh --cases multiPrecision
tests/native/verified.sh --module multiPrecision
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `mpInputs` in [the case inputs](../../../tests/TestSupport/Modules/MultiPrecision.lean), each pair run by all three functions: empty and zero numbers, carries and borrows through runs of digits, differences whose first argument is the smaller, products of the largest digits, every pair of lengths from 1 to 8 digits, and numbers of up to 150 digits.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each pair with the three results.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, section 4.3.1](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Verified Compiler Manual](../../../docs/verified-manual.md)
