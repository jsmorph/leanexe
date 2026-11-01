# Review of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the case inputs](../../../../tests/TestSupport/Modules/MillerRabin.lean) against [the request](request.txt), from the files alone, with Python for powers, factorizations, and models of wrong programs.  The first review found no input on which `powModSpec` or `testSpec` differs from the request.  It found two inaccurate sentences in the comment: the reason given for the branch `m = 0`, which is that Lean's `x^n % 0` is `x^n`, and a claim that the test reduces the base modulo `n`, which the definition does not do.  The comment now gives that reason and states that the result depends only on `x mod n`, since `x^e mod n = (x mod n)^e mod n`.  It found the convention `0^0 = 1` unrecorded, and the comment now records that `powModSpec (0, 0, m)` is `1 mod m`.  The docstrings omitted the failing inputs `(2047, 3)` and `(3215031751, 11)`, the modulus `2^64 - 2`, and the first arbitrary word 12345, and they now name each.  For the classes it named without inputs, the inputs now include the exponent 0 with the moduli 0 and 1, the primes 17, 97, 65537, and `27 * 2^59 + 1` with bases that pass at `j = 2`, 3, 4, 15, and 57, the strong pseudoprimes 3277, 4033, and 8321 to base 2, which pass at `j = 1`, and 65281, which passes at `j = 3`, the even numbers `2^63` and `2^64 - 2`, and the bases 0, 1, `n - 1`, and `n` for the prime `2^64 - 59`.

The first review also named a program whose loop checks `j = k` as well, and that program computes the same function.  If `x^(n - 1)` is `n - 1` modulo an odd `n`, then for each prime `p` dividing `n` the order of `x` modulo `p` divides `2(n - 1)` and not `n - 1`, so `2^(k + 1)` divides it and therefore divides `p - 1`.  Every prime factor of `n` is then 1 modulo `2^(k + 1)`, so `n` is too, which contradicts the definition of `k`.

The second review found no disagreement in value.  It found that the comment's reason for the base 1 was wrong, since `q` odd explains only why `n - 1` passes, and the comment now says that 1 passes because `1^q = 1`.  It found the phrase "`j` from 2 to 15" imprecise, since no input passes at `j` from 5 to 14, and the docstring now lists the values.  The README linked to this record before it existed.  It named three wrong programs that agreed with every sample, and the inputs now catch each:

| Wrong program | Inputs that catch it |
|---|---|
| Omits the parity test and checks `n - 1` only inside the loop, so that for even `n ≥ 4` it returns 1 when `x^(n - 1)` is 1 modulo `n` | `(4, 1)`, `(4, 5)`, `(100, 1)`, and `(2^64 - 2, 1)`, and `(4, 3)` for the form that checks `n - 1` before the loop |
| Caps the count of factors 2 of `n - 1`, at 32 or at 62 for example | `(2^63 + 1, 8881765665119413741)`, whose base is a square root of 1 other than 1 and `n - 1` modulo `n` |
| Stops squaring after `j = c` for `c` from 57 to 62 | `(27 * 2^59 + 1, 5)`, which passes at `j = 58` |

These classes remain without inputs:

| Class | Why the cases leave it out |
|---|---|
| A bound on the squarings between 58 and 62 | No prime below `2^64` has `k ≥ 60`, since `27 * 2^59 + 1` is the only prime of the form `m * 2^e + 1` with `e ≥ 59`, so only a composite could pass at such a `j`, and the search found none. |
| The answer 1 among the arbitrary inputs | Of the 30 arbitrary odd words, only 2541360246100681853 is prime, so the arbitrary inputs test the answer 1 once.  The fixed inputs test it for primes and strong pseudoprimes. |
| Wrong versions of `powMod` | The second review modeled six wrong versions, and each disagrees with some sample.  That result does not exclude others. |

`powMod_eq` and `test_eq` state that the program equals the specification on every input, so these classes concern only the comparison of the compiled module with `powModRef` and `testRef` in the cases.
