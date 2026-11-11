# Reference semantics N

N is a reference semantics for the Clight forms that the C translator emits, written once in a neutral language in [the specification](N.nsx) and rendered mechanically into Rocq and Lean.  Rocq proves each statement of N from CompCert 3.18's definitions, Lean proves the same statement from the Lean copy of Clight, and [the check](check.sh) confirms from what each prover elaborated that the two renderings say what the specification says.  The step between the provers then rests on a mechanical comparison in place of the review of a hand transcription.  N covers the integer leaf forms: the operators at the type pairs that the translator emits, the casts, the truth values of conditions, and the integer constants.  [The translator design](../docs/native-translator.md#trust-argument-and-validation) describes what these forms carry and what remains under review and tests.

## Files

| File | Content |
|---|---|
| [`N.nsx`](N.nsx) | The symbol table, macros, leaf relations, per-form statements, and laws of the base symbols |
| [`nsx.py`](nsx.py) | The renderer, the generator of the Rocq reader, the check, and the planted errors |
| [`check.sh`](check.sh) | The driver that compiles, reads back, compares, and plants errors |
| [`read.lean`](read.lean) | The Lean file that runs the reader of [`Read.lean`](../LeanExe/Native/ClightN/Read.lean) on the built modules |
| [`rocq/NBase.v`](rocq/NBase.v) | The Rocq meaning of the base and interpreted symbols |
| [`rocq/NSpec.v`](rocq/NSpec.v) | The Rocq rendering, written by `nsx.py render` |
| [`rocq/NProof.v`](rocq/NProof.v) | The Rocq proofs of every statement |
| [`Base.lean`](../LeanExe/Native/ClightN/Base.lean) | The Lean meaning of the base and interpreted symbols |
| [`Spec.lean`](../LeanExe/Native/ClightN/Spec.lean) | The Lean rendering, written by `nsx.py render` |
| [`Laws.lean`](../LeanExe/Native/ClightN/Laws.lean), [`Leaf.lean`](../LeanExe/Native/ClightN/Leaf.lean) | The Lean proofs of every statement |

## The neutral language

A specification is a sequence of S-expressions.  The symbol table declares each sort, data constructor, base symbol, and interpreted symbol with its name in Rocq and its name in Lean, and the renderer writes those names while the check expects them in the elaborated terms.  A Lean name may be an application whose arguments are fixed, such as the types and instance of the addition of integers, so that the check confirms the instance that elaboration chose.  Data constructors are the syntax and values that both provers share by name: types, operators, expressions, and values such as `Vlong`.  Interpreted symbols name the definitions under test, which the twin files `NBase.v` and `Base.lean` map to CompCert's `sem_binary_operation`, `sem_cast`, `bool_val`, and `eval_expr` and to the Lean copy's at `Archi.aarch64`.

A relation is a list of constructors, each a closed formula whose conclusion applies the relation, and a statement is a closed formula.  Formulas use `forall`, `exists`, implication, conjunction, disjunction, equivalence, negation, equality, `Some`, `None`, natural numerals, and applications of symbols, relations, and bound variables.  The language has no function definitions, pattern matching, or conditional terms, so that every declaration elaborates to a formula that a small reader prints and compares.  A macro is expanded before rendering and before comparison, and an expansion that would capture a variable of its arguments is an error.

The base symbols are integer arithmetic and order, the value of a word (`u32`, `u64`) and the word of an integer (`r32`, `r64`), the signed value of a 64-bit word (`s64`), the quotient and remainder by a positive divisor (`zdiv`, `zmod`), the power of two of a number that is not negative (`pow2`), and the bitwise operations on numbers that are not negative (`land`, `lor`, `lxor`).  The laws at the end of the specification characterize every base symbol other than arithmetic and order on the arguments with which the statements use it, and both provers prove them: `u32` and `u64` map the words one to one onto the numbers below the word size and `r32` and `r64` invert them modulo that size, `s64` subtracts 2^64 from a value of at least 2^63, `zdiv` and `zmod` satisfy Euclid's division, `pow2` doubles from 1, and the bitwise operations give each bit of their result from the bits of their operands.  The meaning that the check trusts is therefore integer arithmetic and order, the identification of words by their values, and the names of the definitions under test.

## Rendering and the check

`uv run clightn/nsx.py render clightn/N.nsx clightn/rocq/NSpec.v LeanExe/Native/ClightN/Spec.lean` writes the two renderings with every argument of every constant explicit, and the check trusts none of its output.  For Rocq, `check.sh` generates `NRead.v`, which prints under `Set Printing All` each relation with its list of constructors, the type of the relation and of each constructor, the value of each statement, the type and the assumptions of each proof, and the assumptions of CompCert's `transf_c_program_correct`, each to a file of its own.  For Lean, `ClightN.Read.dump` walks the elaborated expressions of the namespace `ClightN.Spec` and of the proofs in `ClightN.Proof` and writes them as S-expressions with every argument and the full name of every constant, together with the axioms of each proof.

`nsx.py check` maps each printed constant through the symbol table, turns numerals into integers, drops the type argument of equality, `Some`, `None`, and the existential, writes a product whose variable is unused as an implication, and replaces bound names by their depths.  It then compares every relation, constructor, and statement with the specification after the expansion of macros.  A constant outside the table never equals a term of the specification, so a coercion, an instance, or a definition that elaboration inserts appears as a difference.  The check also requires each relation to be inductive with exactly the constructors of the specification, each statement `S` to be proved by a theorem `NProof.S` in Rocq and `ClightN.Proof.S` in Lean whose type is the rendered statement itself, and each proof to assume only what CompCert's `transf_c_program_correct` assumes in Rocq and `propext`, `Classical.choice`, and `Quot.sound` in Lean.

`clightn/check.sh --mutations` then plants errors in copies of the renderings and the proofs and requires the check to report exactly those errors.  The errors are an operator, a numeral, a numeral of another type, the order of arguments, a coercion through `Nat`, and a data constructor in the Lean rendering; an operator, a coinductive relation, and an extra constructor in the Rocq rendering; and in each prover a theorem that proves a weaker statement under a statement's name and a proof that assumes its statement (`sorry` and `Admitted`).  A planted error that the comparison misses, or a difference that no planted error explains, fails the script.

## Running

The check needs `coqc`, a CompCert 3.18 tree configured for `aarch64-linux` with its proofs built, `uv`, and the Lean toolchain, and it refuses a tree configured for another target.  It works in `build/clightn`, builds the Lean modules through `tools/leanrun`, and prints the agreement of the relations and statements, followed with `--mutations` by a line for each group of planted errors.  From the repository's root, the command is:

```sh
clightn/check.sh --mutations /path/to/CompCert
```

The proofs need `Archi.ptr64 = true`: on AArch64 a cast between two `long` types passes a pointer unchanged, as the constructors of `cast_ok` say, so the Rocq proofs fail against the ARMv7-M tree.  The x86-64 path has no CompCert tree with built proofs, so AArch64 is the only target that the check covers.  [`tools/full-check`](../tools/full-check) runs the check with the planted errors after `rocq/check.sh` when its CompCert tree is configured for AArch64.

## References

- [The translator design, trust argument and validation](../docs/native-translator.md#trust-argument-and-validation)
- [Trusted base, C files and native executables](../docs/trusted-base.md#c-c-files-and-native-executables)
- [CompCert proofs in Rocq](../rocq/README.md)
- [CompCert 3.18](https://github.com/AbsInt/CompCert/tree/v3.18)
