import LeanExe.Dialect.Bytes

/-!
Flat descriptions of WASI Preview 1 functions.  A description lists the core WebAssembly form of
each parameter of a function in `wasi_snapshot_preview1`, after the lowering of the pinned witx
(WebAssembly/WASI commit `fae981bae14809d91f9bc2d63852d461f331d161`); the errno result that every
flat function returns is not listed.  `tools/wasi-calls.py` generates the descriptions, which
`LeanExe/Wasi/CallTable.lean` holds, from the witx.
-/

namespace LeanExe.Wasi

/-- Where a field of a subscription record takes its value: a constant, the next word argument, or
the next handle argument. -/
inductive FieldSource where
  | const (value : UInt64)
  | word
  | handle
  deriving Repr, DecidableEq

/-- A field of a subscription record: its offset and width in bytes and the source of its value.
-/
structure Field where
  offset : Nat
  width : Nat
  source : FieldSource
  deriving Repr, DecidableEq

/-- The core form of one parameter.  `word32` and `word64` are values; `enum32 count` is a 32-bit
enum of `count` values; `input` is the pointer and length of bytes that the host reads; `output` is
the pointer and capacity of a buffer that the host fills; `result32` and `result64` point to the 4
or 8 bytes of a result word; `reported scale align shown` points to a region of `scale` times a
size that the call's reporter returns, aligned to `align`, whose content the reply carries when
`shown` holds; `flags32 mask` and `flags64 mask` are 32-bit and 64-bit flags whose defined bits are
those of `mask`; `record size align fields` points to a record of `size` bytes, aligned to
`align`, that the host writes, with the offset and width in bytes of each field; `handle` is a
descriptor, which lowers, is rejected, and takes its place in a request as `word32` does.

`iovec input` is the pointer and the length 1 of an array of one element, the pointer and the
length of a buffer as two 4-byte words, which is an input of the request.  With `input` false the
buffer is a fresh output buffer of the argument's capacity, whose content the reply carries; with
`input` true it holds the argument's bytes, an input that a write reads.  `subscriptions records`
stands for the parameters `in`, `out`, and `nsubscriptions` of `poll_oneoff`: `in` points to one
record of 48 bytes for each entry of `records`, an input whose bytes are zero except for the
fields, `out` points to an event of 32 bytes for each record, aligned to 8, whose content the
reply carries, and `nsubscriptions` is the number of records. -/
inductive Param where
  | word32
  | word64
  | enum32 (count : Nat)
  | input
  | output
  | result32
  | result64
  | reported (scale align : Nat) (shown : Bool)
  | flags32 (mask : Nat)
  | flags64 (mask : Nat)
  | record (size align : Nat) (fields : List (Nat × Nat))
  | handle
  | iovec (input : Bool)
  | subscriptions (records : List (List Field))
  deriving Repr, DecidableEq

/-- A flat function: its import name, its parameters, and the name of the call whose result words
give the sizes of its `reported` regions. -/
structure Call where
  name : String
  params : List Param
  reporter : Option String := none
  deriving Repr, DecidableEq

/-- An argument of a call: a word for `word32`, `word64`, `enum32`, `flags32`, `flags64`, and
`handle`, bytes for `input` and `iovec true`, and a capacity for `output` and `iovec false`.  A
`subscriptions` parameter takes a word for each of its word and handle fields, in order.  Result,
reported, and record parameters take no argument. -/
inductive Arg where
  | word (value : UInt64)
  | bytes (value : Bytes)
  | space (capacity : UInt64)

/-- The errno of a call and the content of each region whose content it reports, in parameter
order. -/
structure Reply where
  errno : UInt64
  outputs : List Bytes

namespace Arg

def value : Arg → UInt64
  | .word value => value
  | _ => 0

def capacity : Arg → Nat
  | .space capacity => capacity.toNat
  | _ => 0

def length : Arg → Nat
  | .bytes value => value.data.size
  | _ => 0

end Arg

namespace Field

/-- Whether the field takes an argument: a word or a handle field. -/
def takesArg (field : Field) : Bool :=
  match field.source with
  | .const _ => false
  | _ => true

end Field

/-- The fields of `records` in one array from `base`: the fields of each record at its start, 48
bytes after the previous record's, plus their offsets. -/
def placedFields : Nat → List (List Field) → List Field
  | _, [] => []
  | base, fields :: records =>
    fields.map (fun field => { field with offset := base + field.offset }) ++
      placedFields (base + 48) records

/-- The fields of `records` that take arguments, in order, placed in one array. -/
def argFields (records : List (List Field)) : List Field :=
  (placedFields 0 records).filter Field.takesArg

/-- Whether the fields of a record lie apart from one another. -/
def fieldsApart : List Field → Bool
  | [] => true
  | field :: fields =>
    fields.all (fun other => decide (field.offset + field.width ≤ other.offset) ||
      decide (other.offset + other.width ≤ field.offset)) && fieldsApart fields

/-- Whether each field of each record has a width of at most 8 bytes and lies inside the record's
48 bytes, apart from the record's other fields. -/
def recordsFit (records : List (List Field)) : Bool :=
  records.all fun fields =>
    fields.all (fun field =>
      decide (field.width ≤ 8) && decide (field.offset + field.width ≤ 48)) && fieldsApart fields

namespace Param

/-- Whether the parameter takes one argument.  A `subscriptions` parameter takes one argument for
each field of `argFields`. -/
def takesArg : Param → Bool
  | .word32 | .word64 | .enum32 _ | .input | .output | .flags32 _ | .flags64 _ | .handle
  | .iovec _ => true
  | .result32 | .result64 | .reported .. | .record .. | .subscriptions _ => false

/-- The number of arguments that the parameter takes: one for a parameter that `takesArg` admits,
one for each field of `argFields` of a `subscriptions` parameter, and none otherwise. -/
def argCount : Param → Nat
  | .word32 | .word64 | .enum32 _ | .input | .output | .flags32 _ | .flags64 _ | .handle
  | .iovec _ => 1
  | .result32 | .result64 | .reported .. | .record .. => 0
  | .subscriptions records => (argFields records).length

/-- The errno that rejects an argument of the parameter before the call, or 0: 28 (`inval`) for an
`enum32` value of at least the enum's size and for a flags value with a bit outside the mask, and
61 (`overflow`) for a `word32`, `handle`, or `flags32` value, an input length, or a capacity of
`2^32` or more. -/
def reject : Param → Arg → UInt64
  | .word32, arg | .handle, arg => if arg.value.toNat < 2 ^ 32 then 0 else 61
  | .enum32 count, arg => if arg.value.toNat < count then 0 else 28
  | .input, arg | .iovec true, arg => if arg.length < 2 ^ 32 then 0 else 61
  | .output, arg | .iovec false, arg => if arg.capacity < 2 ^ 32 then 0 else 61
  | .flags32 mask, arg =>
    if arg.value.toNat < 2 ^ 32 then
      if arg.value &&& ~~~(UInt64.ofNat mask) = 0 then 0 else 28
    else 61
  | .flags64 mask, arg => if arg.value &&& ~~~(UInt64.ofNat mask) = 0 then 0 else 28
  | _, _ => 0

end Param

/-- The errno that rejects the arguments of the fields `fields`, in order, or 0: 61 (`overflow`)
for a value of `2^(8 width)` or more, where `width` is the field's width.  Wasmtime 44 answers
invalid contents of a subscription with errno 28, so a field has no other rule. -/
def rejectFields : List Field → List Arg → UInt64
  | field :: fields, arg :: args =>
    if arg.value.toNat < 2 ^ (8 * field.width) then rejectFields fields args else 61
  | _, _ => 0

/-- The errno of the first argument that its parameter rejects, or 0. -/
def rejectArgs : List Param → List Arg → UInt64
  | [], _ => 0
  | param :: params, args =>
    if param.takesArg then
      match args with
      | [] => rejectArgs params []
      | arg :: rest => if param.reject arg = 0 then rejectArgs params rest else param.reject arg
    else
      match param with
      | .subscriptions records =>
        if rejectFields (argFields records) args = 0 then
          rejectArgs params (args.drop (argFields records).length)
        else rejectFields (argFields records) args
      | _ => rejectArgs params args

/-- The size of each region whose content the reply carries, in parameter order: an `output`'s
capacity, the capacity of the buffer of `iovec false`, 4 for `result32`, 8 for `result64`, a
record's size, 32 bytes for each record of `subscriptions`, and the matching entry of `sizes` for a
shown `reported` region.  `sizes` holds one entry for each `reported` parameter. -/
def outputSizesOf : List Param → List Nat → List Arg → List Nat
  | [], _, _ => []
  | .word32 :: params, sizes, args
  | .handle :: params, sizes, args
  | .word64 :: params, sizes, args
  | .enum32 _ :: params, sizes, args
  | .flags32 _ :: params, sizes, args
  | .flags64 _ :: params, sizes, args
  | .iovec true :: params, sizes, args
  | .input :: params, sizes, args => outputSizesOf params sizes args.tail
  | .record size _ _ :: params, sizes, args => size :: outputSizesOf params sizes args
  | .output :: params, sizes, args
  | .iovec false :: params, sizes, args =>
    (args.head?.map Arg.capacity).getD 0 :: outputSizesOf params sizes args.tail
  | .result32 :: params, sizes, args => 4 :: outputSizesOf params sizes args
  | .result64 :: params, sizes, args => 8 :: outputSizesOf params sizes args
  | .reported _ _ shown :: params, sizes, args =>
    (if shown then [sizes.headD 0] else []) ++ outputSizesOf params sizes.tail args
  | .subscriptions records :: params, sizes, args =>
    32 * records.length :: outputSizesOf params sizes (args.drop (argFields records).length)

/-- Little-endian value of a byte string of at most eight bytes. -/
def littleEndian (bytes : Bytes) : UInt64 :=
  (List.range bytes.data.size).foldr (fun index value => bytes.data[index]!.toUInt64 + value * 256) 0

/-- The sizes of the `reported` regions, from the reporter's outputs in order: each region's scale
times the little-endian value of the matching output. -/
def reportedSizesOf : List Param → List Bytes → List Nat
  | [], _ => []
  | .reported scale _ _ :: params, outputs =>
    scale * (outputs.head?.map fun output => (littleEndian output).toNat).getD 0 ::
      reportedSizesOf params outputs.tail
  | _ :: params, outputs => reportedSizesOf params outputs

/-- Whether outputs have the shape that `outputSizesOf` gives for some sizes of the `reported`
regions: one output for each shown region, with the size of each `output`, `iovec false`,
`result32`, `result64`, `record`, and `subscriptions` region. -/
def replyFitsOf : List Param → List Arg → List Bytes → Bool
  | [], _, outputs => outputs.isEmpty
  | .word32 :: params, args, outputs
  | .handle :: params, args, outputs
  | .word64 :: params, args, outputs
  | .enum32 _ :: params, args, outputs
  | .flags32 _ :: params, args, outputs
  | .flags64 _ :: params, args, outputs
  | .iovec true :: params, args, outputs
  | .input :: params, args, outputs => replyFitsOf params args.tail outputs
  | .record size _ _ :: params, args, output :: outputs =>
    decide (output.data.size = size) && replyFitsOf params args outputs
  | .output :: params, args, output :: outputs
  | .iovec false :: params, args, output :: outputs =>
    decide (output.data.size = (args.head?.map Arg.capacity).getD 0) &&
      replyFitsOf params args.tail outputs
  | .result32 :: params, args, output :: outputs =>
    decide (output.data.size = 4) && replyFitsOf params args outputs
  | .result64 :: params, args, output :: outputs =>
    decide (output.data.size = 8) && replyFitsOf params args outputs
  | .reported _ _ true :: params, args, _ :: outputs => replyFitsOf params args outputs
  | .reported _ _ false :: params, args, outputs => replyFitsOf params args outputs
  | .subscriptions records :: params, args, output :: outputs =>
    decide (output.data.size = 32 * records.length) &&
      replyFitsOf params (args.drop (argFields records).length) outputs
  | _ :: _, _, [] => false

namespace Call

/-- The errno that rejects `args` before the call, or 0 when the call runs. -/
def reject (call : Call) (args : List Arg) : UInt64 := rejectArgs call.params args

def replyFits (call : Call) (args : List Arg) (outputs : List Bytes) : Bool :=
  replyFitsOf call.params args outputs

def outputSizes (call : Call) (sizes : List Nat) (args : List Arg) : List Nat :=
  outputSizesOf call.params sizes args

def sizesOf (call : Call) (outputs : List Bytes) : List Nat := reportedSizesOf call.params outputs

end Call

namespace Reply

/-- The little-endian value of output `index`, or 0. -/
def word (reply : Reply) (index : Nat) : UInt64 :=
  ((reply.outputs[index]?).map littleEndian).getD 0

/-- Output `index`, or empty bytes. -/
def bytes (reply : Reply) (index : Nat) : Bytes := (reply.outputs[index]?).getD Bytes.empty

/-- The little-endian value of the `width` bytes at `offset` of output `index`: a field of a
record. -/
def field (reply : Reply) (index offset width : Nat) : UInt64 :=
  littleEndian ⟨(reply.bytes index).data.extract offset (offset + width)⟩

/-- The first `count` bytes of output `index`, or all of them when it has fewer: the bytes that a
call read into a buffer. -/
def prefixBytes (reply : Reply) (index : Nat) (count : UInt64) : Bytes :=
  ⟨(reply.bytes index).data.extract 0 count.toNat⟩

end Reply

end LeanExe.Wasi
