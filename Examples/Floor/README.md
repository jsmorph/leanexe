# Floor: floor division, the floor of the mean, and a clamp on `Int64`

## Programs and specifications

[The program](Program.lean) defines `floorDiv`, `average`, and `clamp` on `Int64`.  `floorDiv a b` corrects Lean's truncating quotient `a / b` by one when the remainder is nonzero and the operands' signs differ, as Python's `//` rounds, `average a b` computes `(a &&& b) + ((a ^^^ b) >>> 1)`, the floor of the mean without overflow (Warren, Hacker's Delight, 2nd edition, section 2-5), and `clamp x lo hi` computes `max lo (min x hi)`.  [The specification](Spec.lean) states each over the integers: `expectedDiv a b` is `Int.fdiv a.toInt b.toInt`, `expectedAverage a b` is `Int.fdiv (a.toInt + b.toInt) 2`, and `expectedClamp x lo hi` is `max lo.toInt (min x.toInt hi.toInt)`.  `verified_compile compiled := [floorDiv, average, clamp]` in [the verified compilation](Compiled.lean) compiles them as [the manual](../../docs/verified-manual.md#expressions) describes `Int64`: the division and the remainder divide the magnitudes with the unsigned division, the shift is WebAssembly's `i64.shr_s`, and `<`, `min`, and `max` test `i64.lt_s` or `i64.le_s`.

## Theorems

[The proofs](Proof.lean) show that the programs meet the specifications, and [the compilation](Compiled.lean) composes them with the generated theorems.  The exclusion in `floorDiv_spec` is the one case whose floor quotient lies outside `Int64`: `minValue` by -1, whose quotient `2^63` wraps to `minValue`.  For a zero divisor, `floorDiv` gives Lean's 0, or -1 for a negative dividend, which `Int.fdiv` leaves outside the specification.

| Theorem | Statement |
|---------|-----------|
| `add_eq_xor_add_and` | `u + v = (u ^^^ v) + 2 * (u &&& v)` for natural numbers. |
| `floorDiv_spec` | For `b ≠ 0`, other than `minValue` by -1, `(floorDiv a b).toInt = expectedDiv a b`. |
| `average_spec` | `(average a b).toInt = expectedAverage a b` for every `a` and `b`. |
| `clamp_spec` | `(clamp x lo hi).toInt = expectedClamp x lo hi` for every `x`, `lo`, and `hi`, from `toInt_min` and `toInt_max`. |
| `floorDiv_call` | Function 2, the export `floorDiv`, called with the words of `a` and `b` under the premises of `floorDiv_spec` from any store, returns without a trap the word of the `Int64` whose integer is `expectedDiv a b` and leaves the store unchanged. |
| `average_call` | Function 3, the export `average`, called with the words of `a` and `b` from any store, returns without a trap the word of the `Int64` whose integer is `expectedAverage a b` and leaves the store unchanged. |
| `clamp_call` | Function 4, the export `clamp`, called with the words of `x`, `lo`, and `hi` from any store, returns without a trap the word of the `Int64` whose integer is `expectedClamp x lo hi` and leaves the store unchanged. |
| `floor_file`, `floor_file_decode` | `build/verified/floor.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

## AArch64 Images

[The AArch64 programs](../../tests/TestSupport/A64/Floor.lean) state `floorDiv_runs` and `average_runs` in the form `ProgramRuns`, from the compiler's theorems of the entries, and [the Images' theorems](../../tests/TestSupport/A64/ImageFilesFloor.lean) join them with the image's bytes and the startup.  `floordiv_image_spec` states that the Image of `floorDiv (-7) 2` writes to the UART the bytes of the word of the `Int64` whose integer is `expectedDiv (-7) 2`, which is -4, and `average_image_spec` that the Image of `average minValue (-1)` writes the word whose integer is `expectedAverage minValue (-1)`, which is `-2^62 - 1`.  `floordivmin_image` states that the Image of `floorDiv minValue (-1)` writes the word of `minValue`.  `tests/baremetal/a64-images.sh` writes the Images, has the kernel check their theorems, and runs them under QEMU.

## Cases

[The cases](Cases.lean) give the operands: the extremes of `Int64`, the values near 0, and values of both signs and parities.  [The `Int64` cases](../../Verified/Examples/SignedCases.lean) compare the exports with native Lean on every pair of them and of arbitrary words, and `clamp` with five upper bounds for each pair, through `tests/verified/run.sh --cases floor`.
