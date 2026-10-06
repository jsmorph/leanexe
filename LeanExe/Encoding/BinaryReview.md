# Binary specification review

## Scope and conclusion

Reviewed on 2026-09-27: the four binary specification modules, their use by
`encode_correct` and `encode_complete`, and their correspondence with the pinned
Talos syntax.  The reviewed grammar selects permitted encodings for its scalar
WASM domain.  The integer, opcode, control, section, and field checks below
support that conclusion.  The reference snapshot contains the discrepancies
recorded under [Reference discrepancies](#reference-discrepancies).

The comparison uses WebAssembly 3.0, dated 2026-09-21, and its [specification
source at revision 608711107b7f1edb13efd57b7d79b49477462d36][spec].  The [dated
Core 2 specification][core2], Unicode 17.0, and the official reference
interpreter resolve the stated discrepancies.  Talos is pinned to
`87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.  Lean is pinned to
`6a10ac8c22beadecabdbb0919c2b50214762f91d`.

The correspondence arguments in this document are a manual specification
review.  The checked Lean theorems establish correctness relative to
`Spec.ModuleBytes`.  The [typing review](ValidityReview.md) examines the
additional premises of the validity theorem.

## Grammar review

### Integers and containers

The [value rules](Spec/Values.lean) match the recursive LEB rules in
[binary values][values].  For unsigned integers, a terminal byte contributes
its value.  A continuation contributes `byte - 128 + 128 * tail`.  The
constructor's conclusion has width `w + 7`, with `w > 0`, which enforces the
official continuation condition that the remaining input width exceeds seven.
Induction gives a value below `2^width` and a length at most
`ceil(width / 7)`.

For signed integers, a terminal byte below 64 contributes its value.  A
terminal byte from 64 through 127 contributes `byte - 128`.  The explicit
signed bounds enforce the unused bits of the last byte.  The continuation
equation and width reduction match the signed rule.  `value.toBitVec.toInt`
selects the signed representative of the original 32-bit or 64-bit word,
preserving its bits in an integer constant.

| Rule | Checked condition |
| --- | --- |
| `Items` | Concatenates each element's bytes in list order. |
| `Vector` | Encodes the element count as `u32`, followed by those elements. |
| `Sized` | Encodes the payload byte count as `u32`.  The count excludes its own prefix. |
| `Name` | Counts UTF-8 bytes and retains their order, including embedded zero bytes. |

`Vector` agrees with the [binary list rule][lists].  The same size rule
serves code bodies and sections.  Their length premises prevent narrowing
an oversized count into a smaller integer.

For names, Lean's `String` contains a byte array and an `IsValidUTF8` proof.
At the pinned Lean revision, `String.toUTF8` returns that array, and
`String.utf8Encode_toList` equates it with the UTF-8 encoding of the character
list.  Inspection of `Char.valid` and `String.utf8EncodeChar` confirms the
Unicode scalar ranges and the one-, two-, three-, and four-byte layouts.
These agree with [Unicode's UTF-8 tables][unicode].

### Types and declarations

The [type rules](Spec/Types.lean) were compared with [binary types][types].

| Rule | Correspondence |
| --- | --- |
| `ValType` | `7f`, `7e`, `7d`, and `7c` encode `i32`, `i64`, `f32`, and `f64`. |
| `BlockType` | `40` denotes no parameters or results.  A numeric type byte denotes no parameters and one result. |
| `FuncType` | `60`, parameter vector, result vector.  Result order and multiple function results are preserved. |
| `Limits` | Flags `00` and `01` select 32-bit memory with a minimum and an optional maximum. |
| `Memory` | The record fixes `is64 = false` and empty data. |
| `Mutability` | `00` is immutable and `01` is mutable. |
| `Global` | Declared type, mutability, matching integer constant, and terminating `0b`. |

Core 3 uses `u64` for memory limits and offsets.  The grammar's `u32`
encodings are a permitted subset: any derivation of `Unsigned w bytes n`
also satisfies the unsigned rule at width `w + 32`, by induction on that
derivation.  The encoded numeric value stays equal to `n`.

In Core 3, a bare `60` function type abbreviates a final subtype with no
supertypes in a singleton recursion group.  `Shape.gcTypes` requires exactly
that Talos metadata.  Duplicate and unused type entries remain in position.

Global records preserve all five fields: the value, declared type, mutability,
constant source initializer, and empty deferred initializer.  Constant
evaluation therefore yields the recorded initial value.

### Instructions

All 71 instruction forms in the [instruction rules](Spec/Instructions.lean)
were compared with the [official instruction grammar][instructions]: 52
`Plain` rules, eight indexed rules, six memory rules, two constants, and three
structured controls.  Hexadecimal byte mappings are listed below.  Names are
WASM instruction names, with a common type prefix shown once per group.

| Instruction group | Opcode mapping |
| --- | --- |
| Control and stack | `unreachable=00`, `nop=01`, `return=0f`, `drop=1a` |
| `i32` comparisons | `eqz=45`, `eq=46`, `lt_u=49`, `gt_u=4b`, `le_u=4d`, `ge_u=4f` |
| `i64` comparisons | `eqz=50`, `eq=51`, `ne=52`, `lt_u=54`, `le_u=58`, `ge_u=5a` |
| `i32` arithmetic | `add=6a`, `and=71` |
| `i64` arithmetic | `add=7c`, `sub=7d`, `mul=7e`, `div_u=80`, `rem_u=82`, `and=83`, `or=84`, `xor=85`, `shl=86`, `shr_u=88` |
| `f32` operations | `nearest=90`, `sqrt=91`, `add=92`, `sub=93`, `mul=94`, `div=95`, and, compared on 2026-10-03, `eq=5b`, `lt=5d`, `le=5f`, `abs=8b` |
| `f64` operations | `sqrt=9f`, `add=a0`, `sub=a1`, `mul=a2`, `div=a3` |
| Integer conversion | `i32.wrap_i64=a7`, `i64.extend_i32_u=ad`, `i32.extend8_s=c0` |
| Numeric conversion | `f32.convert_i32_s=b2`, `f32.demote_f64=b6`, `f64.promote_f32=bb`, `i32.trunc_sat_f32_s=fc 00` |
| Reinterpretation | `i32.reinterpret_f32=bc`, `i64.reinterpret_f64=bd`, `f32.reinterpret_i32=be`, `f64.reinterpret_i64=bf` |
| Indexed instructions | `br=0c`, `br_if=0d`, `call=10`, `local.get=20`, `local.set=21`, `local.tee=22`, `global.get=23`, `global.set=24` |
| Loads | `i32.load=28`, `i64.load=29`, `i32.load8_u=2d` |
| Stores | `i32.store=36`, `i64.store=37`, `i32.store8=3a` |
| Memory operations | `memory.size=3f 00`, `memory.grow=40 00` |
| Constants | `i32.const=41` with signed 32-bit immediate.  `i64.const=42` with signed 64-bit immediate.  `f32.const=43` with four bytes and `f64.const=44` with eight bytes, least significant first. |
| Structured control | `block=02`, `loop=03`, `if=04`, `else=05`, `end=0b` |

The counts above date from the first review.  On 2026-10-03 the rules numbered
58 `Plain` rules, eight indexed rules, six memory rules, four constants, and
three structured controls, and then 62 `Plain` rules after the binary32
comparisons and `f32.abs`.  That day `f32.const` was added and compared, with
`f64.const`, which the encoder already had, against lines 194 and 195 of the
[instruction grammar][instructions], `0x43 p:Bf32` and `0x44 p:Bf64`, and `BfN`
in the [binary values][values], N/8 bytes through `$inv_fbytes_`.  The `Plain`
rules added after the first review have not been compared in this record.

Indexed immediates use `u32`.  In `fc 00`, the second byte encodes unsigned
subopcode zero.  The trailing zero in `memory.size` and `memory.grow` encodes
memory index zero.

For loads and stores, alignment exponents are bounded by 2, 3, or 0 for
four-byte, eight-byte, or one-byte accesses.  These bounds satisfy
`2^alignment <= accessBytes` and keep the explicit-memory flag clear.
Offsets preserve the `UInt32` value.  The encoder chooses alignment zero.
Talos records the offset and operates on memory zero.  WASM alignment is a
validation constraint and hint for these ordinary loads and stores.

Each structured rule fixes parameter count zero, an empty parameter-type
list, and result count equal to the encoded result-type list length.  The
`BlockType` premise restricts that length to zero or one.  Every nested body
receives its own `end`.  Each `if` has an explicit `else`, including an empty
else branch.  `Instrs` preserves instruction order by concatenation.

### Modules and Talos fields

The [module rules](Spec/Modules.lean) agree with the selected productions of
the [official module grammar][modules].

| Component | Checked correspondence |
| --- | --- |
| Header | Magic `00 61 73 6d`, version `01 00 00 00`. |
| Sections | IDs `1, 2, 3, 5, 6, 7, 10`, once each, in the prescribed order.  Empty vectors are permitted. |
| Type and import sections | Preserve the type table and import order.  Each imported function's selected type index resolves to its recorded signature. |
| Function and code sections | Both range over `m.funcs` in the same order.  Their counts agree.  Each type index resolves to that function's parameter and result lists. |
| Locals | Each local forms a group with count one.  Vector count therefore also bounds the expanded local count. |
| Function body | Local vector, instruction sequence, `end`, enclosed by the exact body byte length. |
| Exports | Names, kinds, and indices are retained.  The chosen order is function, global, then memory exports, preserving order within each list. |
| Section lengths | Each length counts exactly its payload. |

The eight fields represented by sections are `types`, `imports`, `funcs`,
`memory`, `globals`, `exports`, `globalExports`, and `memoryExports`.
`Shape` accounts for the other thirteen `Wasm.Module` fields: canonical
`gcTypes`; empty additional memories, tables, elements, imported non-function
entities, table exports, tag exports, and tags; absent start function; and
`dataWithoutMemory = false`.  Memory declarations also require empty data.
Every field of the pinned Talos module record is accounted for.

Declared function type indices remain unchanged.  An imported function has
names and a signature in Talos, so the binary rule permits any matching type
index.  The encoder chooses the first.  Each such choice has the same numeric
parameter and result types.  Function indices include imports before defined
functions throughout the module.

## Reference discrepancies

The [pinned Core 3 value source][values] contains three inconsistencies:

| Location | Snapshot text | Resolution used in this review |
| --- | --- | --- |
| UTF-8 continuation helper | `0x80 < b < 0xC0` | Unicode includes continuation byte `80`.  For example, U+0080 encodes as `c2 80`. |
| Four-byte UTF-8 range | Upper bound `U+11000` | Unicode's upper bound is `U+110000`.  For example, U+1F600 encodes as `f0 9f 98 80`. |
| `Bi32` and `Bi64` source aliases | Aliases of `BuN` | The same source defines general `BiN` through signed LEB.  The official decoder reads constants with `s32` and `s64`. |

The UTF-8 discrepancies also occur in the rendered Core 3 value formulas.  The
[dated Core 2 value rules][core2] give the intended signed-constant
interpretation and Unicode range.  The official [reference decoder][decoder]
confirms signed constant immediates.  For example, `41 7f` denotes the 32-bit
word `ffffffff`, which the Lean rule preserves.  The Lean definitions agree with
these resolved meanings.  A claim of literal agreement with every formula in the
Core 3 snapshot would exceed this review.

## Reviewed source identity

The SHA-256 digests of the reviewed files are:

```text
6f69b201e8e22e1febee88b6e97a093b32af26d44266ca2781222d08b7c62d76  Spec/Values.lean
42db024325fd510cbd6ceb4bb06d60c96e78c65139ee4490f7890381a11debf2  Spec/Types.lean
83fb5522de0a21f4381d4219827cba83e7dbf308ac0b33ebca2bf8940fba477c  Spec/Instructions.lean
8e7f6a904ff2c4edd8697cc5fb839c701f2f67f9959d17e065fd111eb04258db  Spec/Modules.lean
```

[spec]:
https://github.com/WebAssembly/spec/tree/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0
[values]:
https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/5.1-binary.values.spectec
[lists]: https://webassembly.github.io/spec/core/binary/conventions.html#lists
[types]:
https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/5.2-binary.types.spectec
[instructions]:
https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/5.3-binary.instructions.spectec
[modules]:
https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/5.4-binary.modules.spectec
[decoder]:
https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/interpreter/binary/decode.ml
[core2]: https://www.w3.org/TR/2025/CRD-wasm-core-2-20250616/#binary-value
[unicode]:
https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/#G7404
