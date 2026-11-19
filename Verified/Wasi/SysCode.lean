import Verified.Wasi.ReadCode
import Verified.Wasi.SysForm

/-! The code of a `sys` command, which the compiler places in the calling function.  It reads the
argument words from the locals of the argument variables, the root and the length of each input
from the two locals of its variable, and uses the i64 locals from `base` that `SysForm.width`
counts.

A flat call keeps its errno at `base` and its result words at `base + 3` and `base + 4`, which
it sets to 0 with `base + 1` and `base + 2`.  The code tests the arguments, pushes the core
arguments with the result words at scratch addresses 0 and 8, calls the import, and on errno 0
loads the result words.

A call that fills a window of a buffer takes the buffer's root and size from the two locals from
`root`.  It keeps its errno at `base`, the window's address at `base + 1`, the window's length at
`base + 2`, the count of the fill at `base + 3`, and the index of the zero fill at `base + 4`.  The
code computes the window, tests the arguments with the window's length in place of its start and
count, calls the import with the window's address and length, on errno 0 sets the count, and after
an errno, of the host or of the test, stores 0 into the window's bytes.  It pushes the errno, the
count, and the buffer's root and size.

A reported call keeps its errno at `base`, the reporter's words at `base + 1` and `base + 2`, and
its buffer's root at `base + 3` and length at `base + 4`.  The code calls the reporter with its
words at scratch addresses 0 and 8, tests the sizes, allocates one block for the shown region and
the hidden region after it at the next multiple of 4, and calls the import.

A record call keeps its errno at `base`, its block's root at `base + 1`, the record pointer at
`base + 2`, and its fields from `base + 3`.  The code tests the arguments, allocates a block of
`size + align - 1` bytes, passes its root rounded up to a multiple of `align` as the record pointer,
calls the import, on errno 0 loads each field from the record, and releases the block.

An iovec call writes its element, the window's address and length, at scratch addresses 0 and 4
with the code of the stream calls, `metadataCode`, which also sets the word at 8 to 0, passes the
element's address 0 and the count 1, and places its result word at scratch address 8.  A read is a
fill, whose count is the count that the host returns clamped to the window's length.  A write
keeps the window's address and length of its input at `base` and `base + 1`, its errno at
`base + 2`, and the count written at `base + 3`.

A `poll` call keeps its errno at `base`, its block's root at `base + 1`, the subscriptions'
pointer at `base + 2`, the number of events at `base + 3`, and the fields of the first event from
`base + 4`.  The code allocates a block of `80 n + 7` bytes for `n` subscriptions, rounds its root
up to a multiple of 8, zeroes the `48 n` bytes of the subscriptions and stores each field, places
the events after the subscriptions, calls the import, on errno 0 loads the number of events,
moves the pointer to the events, and loads the fields of the first event, and releases the block.
-/

namespace Verified.Wasi

open Wasm LeanExe.Wasi

/-- Pushes 28 when the flags word in `place` has a bit outside `mask`, and otherwise runs
`accepted`. -/
def flagsRejectCode (mask place : Nat) (accepted : Program) : Program :=
  [.localGet place, .constI64 (~~~(UInt64.ofNat mask)), .andI64, .eqzI64,
   .iff 0 1 accepted [.constI64 28] [] [.i64]]

/-- Pushes the errno that rejects the argument words in `locals`, or 0. -/
def sysRejectCode : List Param → List Nat → Program
  | [], _ => [.constI64 0]
  | .word32 :: params, place :: locals
  | .handle :: params, place :: locals
  | .output :: params, place :: locals =>
    [.localGet place, .constI64 4294967296, .geUI64,
     .iff 0 1 [.constI64 61] (sysRejectCode params locals) [] [.i64]]
  | .enum32 count :: params, place :: locals =>
    [.localGet place, .constI64 (UInt64.ofNat count), .geUI64,
     .iff 0 1 [.constI64 28] (sysRejectCode params locals) [] [.i64]]
  | .flags32 mask :: params, place :: locals =>
    [.localGet place, .constI64 4294967296, .geUI64,
     .iff 0 1 [.constI64 61] (flagsRejectCode mask place (sysRejectCode params locals)) [] [.i64]]
  | .flags64 mask :: params, place :: locals =>
    flagsRejectCode mask place (sysRejectCode params locals)
  | .word64 :: params, _ :: locals => sysRejectCode params locals
  | _ :: params, locals => sysRejectCode params locals

/-- Pushes the core arguments of a flat call: each word from its local, the window's address from
`root` and its length from its local, and the scratch address `slot` of each result word in turn.
-/
def sysLowerCode : List Param → List Nat → Nat → Nat → Program
  | [], _, _, _ => []
  | .word32 :: params, place :: locals, root, slot
  | .handle :: params, place :: locals, root, slot
  | .enum32 _ :: params, place :: locals, root, slot
  | .flags32 _ :: params, place :: locals, root, slot =>
    [.localGet place, .wrapI64] ++ sysLowerCode params locals root slot
  | .word64 :: params, place :: locals, root, slot
  | .flags64 _ :: params, place :: locals, root, slot =>
    [.localGet place] ++ sysLowerCode params locals root slot
  | .output :: params, place :: locals, root, slot =>
    [.localGet root, .wrapI64, .localGet place, .wrapI64] ++ sysLowerCode params locals root slot
  | .result32 :: params, locals, root, slot
  | .result64 :: params, locals, root, slot =>
    [.const (UInt32.ofNat slot)] ++ sysLowerCode params locals root (slot + 8)
  | _ :: params, locals, root, slot => sysLowerCode params locals root slot

/-- Loads each result word from its scratch address into the locals from `target`. -/
def sysLoadCode : List Param → Nat → Nat → Program
  | [], _, _ => []
  | .result32 :: params, slot, target =>
    [.const (UInt32.ofNat slot), .load32 0, .extendUI32, .localSet target] ++
      sysLoadCode params (slot + 8) (target + 1)
  | .result64 :: params, slot, target =>
    [.const (UInt32.ofNat slot), .load64 0, .localSet target] ++
      sysLoadCode params (slot + 8) (target + 1)
  | _ :: params, slot, target => sysLoadCode params slot target

/-- Pushes the word in local `count`, or the word in local `capacity` when the count is at least
the capacity. -/
def minCode (count capacity : Nat) : Program :=
  [.localGet count, .localGet capacity, .geUI64,
   .iff 0 1 [.localGet capacity] [.localGet count] [] [.i64]]

/-- Leaves in `target` the address of the window of a buffer and in `target + 1` its length, from
the buffer's root in local `root` and size in `root + 1` and the window's start in local `start`
and count in local `count`: the first position, the start or the size when that is smaller, in
`target`, the bytes from it to the end in `target + 1`, the length, the count or those bytes when
they are fewer, in `target + 1`, and the root plus the first position in `target`. -/
def windowCode (root start count target : Nat) : Program :=
  minCode start (root + 1) ++
    [.localSet target, .localGet (root + 1), .localGet target, .subI64, .localSet (target + 1)] ++
    minCode count (target + 1) ++
    [.localSet (target + 1), .localGet root, .localGet target, .addI64, .localSet target]

/-- Stores 0 into the bytes from the address in local `pointer` whose number is in local
`length`, with the index in local `index`. -/
def zeroCode (pointer length index : Nat) : Program :=
  [.constI64 0, .localSet index,
   .block 0 0 [.loop 0 0
     [.localGet index, .localGet length, .geUI64, .br_if 1,
      .localGet pointer, .localGet index, .addI64, .wrapI64, .const 0, .store8 0,
      .localGet index, .constI64 1, .addI64, .localSet index, .br 0] [] []] [] []]

/-- The end of a fill: after an errno, the zero fill of the window whose address and length are
in `base + 1` and `base + 2`, and then the pushes of the errno, the count, and the buffer's root
and size from the two locals from `root`. -/
def fillTailCode (root base : Nat) : Program :=
  [.localGet base, .eqzI64, .iff 0 0 [] (zeroCode (base + 1) (base + 2) (base + 4)) [] [],
   .localGet base, .localGet (base + 3), .localGet root, .localGet (root + 1)]

/-- The locals of the words of a call's arguments from the locals of a command's word variables:
the locals of each parameter in turn, with the locals of the start and the count of a window
replaced by `length` for an output or `iovec false`, and dropped for `iovec true`. -/
def lowerLocs : List Param → List Nat → Nat → List Nat
  | [], _, _ => []
  | .output :: params, locs, length | .iovec false :: params, locs, length =>
    length :: lowerLocs params (locs.drop 2) length
  | .iovec true :: params, locs, length => lowerLocs params (locs.drop 2) length
  | .word32 :: params, locs, length
  | .handle :: params, locs, length
  | .word64 :: params, locs, length
  | .enum32 _ :: params, locs, length
  | .flags32 _ :: params, locs, length
  | .flags64 _ :: params, locs, length =>
    locs.headD 0 :: lowerLocs params locs.tail length
  | .subscriptions records :: params, locs, length =>
    locs.take (argFields records).length ++
      lowerLocs params (locs.drop (argFields records).length) length
  | _ :: params, locs, length => lowerLocs params locs length

/-- The locals of the start and the count of the first window that a buffer fills. -/
def windowLocs : List Param → List Nat → Nat × Nat
  | [], _ => (0, 0)
  | .output :: _, locs | .iovec false :: _, locs => (locs.headD 0, locs.tail.headD 0)
  | param :: params, locs => windowLocs params (locs.drop param.argWords)

/-- The hidden region's address on the stack as an i32: the end of the shown region rounded up to
a multiple of 4, from the end plus 3, which the code keeps in `base + 4`. -/
def hiddenAddressCode (base : Nat) : Program :=
  [.localGet (base + 3), .localGet (base + 2), .addI64, .constI64 3, .addI64,
   .localSet (base + 4), .localGet (base + 4), .localGet (base + 4), .constI64 4, .remUI64,
   .subI64, .wrapI64]

/-- The allocation of the block of a reported call, the call, and its results. -/
def sysReportedBlockCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (base : Nat) : Program :=
  [.localGet (base + 4), .call (3 + calls.length), .localSet (base + 3)] ++
    hiddenAddressCode base ++
    [.localGet (base + 3), .wrapI64, .call (3 + calls.idxOf call), .extendUI32,
     .localSet base, .localGet base, .eqzI64,
     .iff 0 0 [.localGet (base + 2), .localSet (base + 4)]
       (discardReadCodeWith calls (base + 3) ++
         [.constI64 0, .localSet (base + 1), .constI64 0, .localSet (base + 2),
          .constI64 0, .localSet (base + 4)])
       [] []]

/-- The reporter's sizes, the size test, and the block, after the reporter returns errno 0. -/
def sysReportedSizesCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (base : Nat) : Program :=
  sysLoadCode call.reporterCall.params 0 (base + 1) ++
    [.localGet (base + 2), .localGet (base + 1), .constI64 4, .mulI64, .addI64,
     .constI64 3, .addI64, .localSet (base + 4),
     .localGet (base + 4), .constI64 4294967296, .geUI64,
     .iff 0 0
       [.constI64 61, .localSet base, .constI64 0, .localSet (base + 1),
        .constI64 0, .localSet (base + 2), .constI64 0, .localSet (base + 4)]
       (sysReportedBlockCodeWith calls call base) [] []]

def sysReportedCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (base : Nat) : Program :=
  [.constI64 0, .localSet base, .constI64 0, .localSet (base + 1),
   .constI64 0, .localSet (base + 2), .constI64 0, .localSet (base + 3),
   .constI64 0, .localSet (base + 4)] ++
    sysLowerCode call.reporterCall.params [] (base + 3) 0 ++
    [.call (3 + calls.idxOf call.reporterCall), .extendUI32, .localSet base,
     .localGet base, .eqzI64,
     .iff 0 0 (sysReportedSizesCodeWith calls call base) [] [] [],
     .localGet base, .localGet (base + 1), .localGet (base + 2), .localGet (base + 3),
     .localGet (base + 4)]

/-! ## Calls with inputs

The code of a call with inputs takes the locals of the word arguments and the locals of the input
roots as two lists.  An `input` parameter with no input local left has no code, as in the code
above, so that the code with no input locals is that code. -/

/-- Pushes the errno that rejects the arguments, or 0: the words in `words`, and the lengths of the
inputs, each in the local after its root in `inputs`. -/
def sysRejectInputsCode : List Param → List Nat → List Nat → Program
  | [], _, _ => [.constI64 0]
  | .input :: params, words, place :: inputs =>
    [.localGet (place + 1), .constI64 4294967296, .geUI64,
     .iff 0 1 [.constI64 61] (sysRejectInputsCode params words inputs) [] [.i64]]
  | .word32 :: params, place :: words, inputs
  | .handle :: params, place :: words, inputs
  | .output :: params, place :: words, inputs =>
    [.localGet place, .constI64 4294967296, .geUI64,
     .iff 0 1 [.constI64 61] (sysRejectInputsCode params words inputs) [] [.i64]]
  | .enum32 count :: params, place :: words, inputs =>
    [.localGet place, .constI64 (UInt64.ofNat count), .geUI64,
     .iff 0 1 [.constI64 28] (sysRejectInputsCode params words inputs) [] [.i64]]
  | .flags32 mask :: params, place :: words, inputs =>
    [.localGet place, .constI64 4294967296, .geUI64,
     .iff 0 1 [.constI64 61] (flagsRejectCode mask place (sysRejectInputsCode params words inputs))
       [] [.i64]]
  | .flags64 mask :: params, place :: words, inputs =>
    flagsRejectCode mask place (sysRejectInputsCode params words inputs)
  | .word64 :: params, _ :: words, inputs => sysRejectInputsCode params words inputs
  | _ :: params, words, inputs => sysRejectInputsCode params words inputs

/-- Pushes the core arguments of a flat call: each word from its local, each input's root and
length from its two locals, the window's address from `root` and its length from its local, and
the scratch address `slot` of each result word in turn. -/
def sysLowerInputsCode : List Param → List Nat → List Nat → Nat → Nat → Program
  | [], _, _, _, _ => []
  | .input :: params, words, place :: inputs, root, slot =>
    [.localGet place, .wrapI64, .localGet (place + 1), .wrapI64] ++
      sysLowerInputsCode params words inputs root slot
  | .word32 :: params, place :: words, inputs, root, slot
  | .handle :: params, place :: words, inputs, root, slot
  | .enum32 _ :: params, place :: words, inputs, root, slot
  | .flags32 _ :: params, place :: words, inputs, root, slot =>
    [.localGet place, .wrapI64] ++ sysLowerInputsCode params words inputs root slot
  | .word64 :: params, place :: words, inputs, root, slot
  | .flags64 _ :: params, place :: words, inputs, root, slot =>
    [.localGet place] ++ sysLowerInputsCode params words inputs root slot
  | .output :: params, place :: words, inputs, root, slot =>
    [.localGet root, .wrapI64, .localGet place, .wrapI64] ++
      sysLowerInputsCode params words inputs root slot
  | .result32 :: params, words, inputs, root, slot
  | .result64 :: params, words, inputs, root, slot =>
    [.const (UInt32.ofNat slot)] ++ sysLowerInputsCode params words inputs root (slot + 8)
  | _ :: params, words, inputs, root, slot => sysLowerInputsCode params words inputs root slot

/-- The code of an accepted flat request with inputs. -/
def sysFlatCallInputsCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (base : Nat) : Program :=
  sysLowerInputsCode call.params words inputs (base + 1) 0 ++
    [.call (3 + calls.idxOf call), .extendUI32, .localSet base,
     .localGet base, .eqzI64, .iff 0 0 (sysLoadCode call.params 0 (base + 3)) [] [] []]

def sysFlatInputsCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (base : Nat) : Program :=
  sysRejectInputsCode call.params words inputs ++
    [.localSet base, .constI64 0, .localSet (base + 1), .constI64 0, .localSet (base + 2),
     .constI64 0, .localSet (base + 3), .constI64 0, .localSet (base + 4),
     .localGet base, .eqzI64,
     .iff 0 0 (sysFlatCallInputsCodeWith calls call words inputs base) [] [] [],
     .localGet base] ++
    (List.range (call.params.countP Param.isResult)).map
      (fun index => .localGet (base + 3 + index))

/-- The count of a fill of a flat call: the window's length in `base + 2` for a call without a
result word, and otherwise the result word in `base + 3` clamped to that length. -/
def fillCountCode (words base : Nat) : Program :=
  if words = 0 then [.localGet (base + 2), .localSet (base + 3)]
  else minCode (base + 3) (base + 2) ++ [.localSet (base + 3)]

/-- The code of a flat call that fills the window of the buffer whose root and size lie in the two
locals from `root`, from the locals `words` of the command's word variables and `inputs` of its
inputs. -/
def sysFlatFillCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (root base : Nat) : Program :=
  windowCode root (windowLocs call.params words).1 (windowLocs call.params words).2 (base + 1) ++
    sysRejectInputsCode call.params (lowerLocs call.params words (base + 2)) inputs ++
    [.localSet base, .constI64 0, .localSet (base + 3), .localGet base, .eqzI64,
     .iff 0 0 (sysLowerInputsCode call.params (lowerLocs call.params words (base + 2)) inputs
         (base + 1) 0 ++
       [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
        .iff 0 0 (sysLoadCode call.params 0 (base + 3) ++
          fillCountCode (call.params.countP Param.isResult) base) [] [] []]) [] [] []] ++
    fillTailCode root base

/-- Pushes the field of `width` bytes at `offset` of the record whose pointer is in local
`pointer`: one byte load for a width of 1, two for a width of 2, a 32-bit load for 4, and a 64-bit
load otherwise. -/
def fieldLoadCode (pointer offset width : Nat) : Program :=
  match width with
  | 1 => [.localGet pointer, .wrapI64, .load8U (UInt32.ofNat offset), .extendUI32]
  | 2 =>
    [.localGet pointer, .wrapI64, .load8U (UInt32.ofNat offset), .extendUI32,
     .localGet pointer, .wrapI64, .load8U (UInt32.ofNat (offset + 1)), .extendUI32,
     .constI64 256, .mulI64, .addI64]
  | 4 => [.localGet pointer, .wrapI64, .load32 (UInt32.ofNat offset), .extendUI32]
  | _ => [.localGet pointer, .wrapI64, .load64 (UInt32.ofNat offset)]

/-- Loads each field of the record whose pointer is in local `pointer` into the locals from
`target`. -/
def recordLoadCode (pointer : Nat) : List (Nat × Nat) → Nat → Program
  | [], _ => []
  | field :: fields, target =>
    fieldLoadCode pointer field.1 field.2 ++
      .localSet target :: recordLoadCode pointer fields (target + 1)

/-- Sets `count` locals from `first` to 0. -/
def zeroLocalsCode (first : Nat) : Nat → Program
  | 0 => []
  | count + 1 => .constI64 0 :: .localSet first :: zeroLocalsCode (first + 1) count

/-- The record pointer: the block's root in `base + 1` rounded up to a multiple of `align`, from
the root plus `align - 1`, which the code keeps in `base + 2`. -/
def recordAddressCode (base align : Nat) : Program :=
  [.localGet (base + 1), .constI64 (UInt64.ofNat (align - 1)), .addI64, .localSet (base + 2),
   .localGet (base + 2), .localGet (base + 2), .constI64 (UInt64.ofNat align), .remUI64, .subI64,
   .localSet (base + 2)]

/-- The code of an accepted record request: the allocation of the block, the record pointer, the
call, the loads of the fields on errno 0, and the release of the block. -/
def sysRecordCallCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (base size align : Nat) (fields : List (Nat × Nat)) : Program :=
  [.constI64 (UInt64.ofNat (size + align - 1)), .call (3 + calls.length), .localSet (base + 1)] ++
    recordAddressCode base align ++
    sysLowerInputsCode call.params words inputs (base + 1) 0 ++
    [.localGet (base + 2), .wrapI64, .call (3 + calls.idxOf call), .extendUI32, .localSet base,
     .localGet base, .eqzI64, .iff 0 0 (recordLoadCode (base + 2) fields (base + 3)) [] [] []] ++
    discardReadCodeWith calls (base + 1)

def sysRecordCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (base : Nat) : Program :=
  match recordOf call.params with
  | some (size, align, fields) =>
    sysRejectInputsCode call.params words inputs ++
      .localSet base :: zeroLocalsCode (base + 3) fields.length ++
      [.localGet base, .eqzI64,
       .iff 0 0 (sysRecordCallCodeWith calls call words inputs base size align fields) [] [] [],
       .localGet base] ++
      (List.range fields.length).map (fun index => .localGet (base + 3 + index))
  | none => []

/-! ## Calls with an array of one element -/

/-- Pushes 61 when the word in local `handle` or the word in local `length` is `2^32` or more, and
otherwise 0: the test of the handle and of the capacity or input length of an iovec call. -/
def iovecRejectCode (handle length : Nat) : Program :=
  [.localGet handle, .constI64 4294967296, .geUI64,
   .iff 0 1 [.constI64 61]
     [.localGet length, .constI64 4294967296, .geUI64,
      .iff 0 1 [.constI64 61] [.constI64 0] [] [.i64]] [] [.i64]]

/-- Pushes the core arguments of an iovec call: the handle in local `handle`, the element's address
0 and the count 1, the word in local `offset` when there is one, and the result word's address 8. -/
def iovecLowerCode (handle : Nat) (offset : Option Nat) : Program :=
  [.localGet handle, .wrapI64, .const 0, .const 1] ++
    (match offset with
     | some place => [.localGet place]
     | none => []) ++ [.const 8]

/-- Loads the count that the host left at scratch address 8 into `base + 3` and clamps it to the
window's length in `base + 2`. -/
def readCountCode (base : Nat) : Program :=
  [.const 8, .load32 0, .extendUI32, .localSet (base + 3)] ++ minCode (base + 3) (base + 2) ++
    [.localSet (base + 3)]

/-- The code of an accepted read: the element of the window, the call, and on errno 0 the count.
The words of a read are the handle, the window's start and count, and the offset of `fd_pread`. -/
def sysIovecReadCallCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locs : List Nat) (base : Nat) : Program :=
  metadataCode (base + 1) (base + 2) ++ iovecLowerCode (locs.getD 0 0) locs[3]? ++
    [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
     .iff 0 0 (readCountCode base) [] [] []]

/-- The code of a read that fills the window of the buffer whose root and size lie in the two
locals from `root`. -/
def sysIovecReadCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locs : List Nat) (root base : Nat) : Program :=
  windowCode root (locs.getD 1 0) (locs.getD 2 0) (base + 1) ++
    iovecRejectCode (locs.getD 0 0) (base + 2) ++
    [.localSet base, .constI64 0, .localSet (base + 3), .localGet base, .eqzI64,
     .iff 0 0 (sysIovecReadCallCodeWith calls call locs base) [] [] []] ++
    fillTailCode root base

/-- The code of an accepted write: the element of the input, the call, and on errno 0 the count.
The words of a write are the handle and the offset of `fd_pwrite`, and its input is the bytes. -/
def sysIovecWriteCallCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locs inputs : List Nat) (base : Nat) : Program :=
  metadataCode (inputs.getD 0 0) (inputs.getD 0 0 + 1) ++
    iovecLowerCode (locs.getD 0 0) locs[1]? ++
    [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
     .iff 0 0 [.const 8, .load32 0, .extendUI32, .localSet (base + 1)] [] [] []]

def sysIovecWriteCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locs inputs : List Nat) (base : Nat) : Program :=
  iovecRejectCode (locs.getD 0 0) (inputs.getD 0 0 + 1) ++
    .localSet base :: zeroLocalsCode (base + 1) 1 ++
    [.localGet base, .eqzI64,
     .iff 0 0 (sysIovecWriteCallCodeWith calls call locs inputs base) [] [] [],
     .localGet base, .localGet (base + 1)]

/-- The code of a write of the window of the input whose root and length lie in the two locals
from `input`: the window's address and length at `base` and `base + 1`, and the write of the bytes
there, with the handle and the offset of `fd_pwrite` from `locs`. -/
def sysIovecWindowCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locs : List Nat) (input base : Nat) : Program :=
  windowCode input (locs.getD 1 0) (locs.getD 2 0) base ++
    sysIovecWriteCodeWith calls call (locs.getD 0 0 :: locs.drop 3) [base] (base + 2)

/-! ## Calls of `poll_oneoff` -/

/-- Pushes the errno that rejects the words of the fields `fields` in the locals `locs`, in order:
61 for the first value of `2^(8 width)` or more, which only a width below 8 admits, and otherwise
0. -/
def fieldsRejectCode : List Field → List Nat → Program
  | field :: fields, place :: locs =>
    if field.width < 8 then
      [.localGet place, .constI64 (UInt64.ofNat (2 ^ (8 * field.width))), .geUI64,
       .iff 0 1 [.constI64 61] (fieldsRejectCode fields locs) [] [.i64]]
    else fieldsRejectCode fields locs
  | _, _ => [.constI64 0]

/-- Stores 0 into `count` words of 8 bytes from `offset` of the block whose pointer is in local
`pointer`. -/
def zeroWordsCode (pointer offset : Nat) : Nat → Program
  | 0 => []
  | count + 1 => [.localGet pointer, .wrapI64, .constI64 0, .store64 (UInt32.ofNat offset)] ++
    zeroWordsCode pointer (offset + 8) count

/-- Stores the `width` little-endian bytes of the word that `value` pushes at `offset` of the block
whose pointer is in local `pointer`: one 64-bit store for a width of 8, one 32-bit store for 4, two
byte stores for 2, and one byte store otherwise. -/
def fieldStoreCode (pointer offset width : Nat) (value : Program) : Program :=
  match width with
  | 8 => [.localGet pointer, .wrapI64] ++ value ++ [.store64 (UInt32.ofNat offset)]
  | 4 => [.localGet pointer, .wrapI64] ++ value ++ [.wrapI64, .store32 (UInt32.ofNat offset)]
  | 2 =>
    [.localGet pointer, .wrapI64] ++ value ++ [.wrapI64, .store8 (UInt32.ofNat offset)] ++
      [.localGet pointer, .wrapI64] ++ value ++
        [.constI64 8, .shrUI64, .wrapI64, .store8 (UInt32.ofNat (offset + 1))]
  | _ => [.localGet pointer, .wrapI64] ++ value ++ [.wrapI64, .store8 (UInt32.ofNat offset)]

/-- Stores the fields `fields`, in order, into the block whose pointer is in local `pointer`: a
constant field's value, and the word of the next local of `locs` for a word or a handle field. -/
def fieldStoresCode (pointer : Nat) : List Field → List Nat → Program
  | [], _ => []
  | field :: fields, locs =>
    match field.source with
    | .const value =>
      fieldStoreCode pointer field.offset field.width [.constI64 value] ++
        fieldStoresCode pointer fields locs
    | .word | .handle =>
      fieldStoreCode pointer field.offset field.width [.localGet (locs.headD 0)] ++
        fieldStoresCode pointer fields locs.tail

/-- The code of an accepted `poll` request: the allocation of the block, the subscriptions'
pointer, the subscriptions, the call, on errno 0 the loads of the number of events and of the
fields of the first event, and the release of the block. -/
def sysPollCallCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (records : List (List Field)) (locs : List Nat) (base : Nat) : Program :=
  [.constI64 (UInt64.ofNat (80 * records.length + 7)), .call (3 + calls.length),
   .localSet (base + 1)] ++
    recordAddressCode base 8 ++ zeroWordsCode (base + 2) 0 (6 * records.length) ++
    fieldStoresCode (base + 2) (placedFields 0 records) locs ++
    [.localGet (base + 2), .wrapI64,
     .localGet (base + 2), .constI64 (UInt64.ofNat (48 * records.length)), .addI64, .wrapI64,
     .const (UInt32.ofNat records.length), .const 0,
     .call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
     .iff 0 0 ([.const 0, .load32 0, .extendUI32, .localSet (base + 3),
       .localGet (base + 2), .constI64 (UInt64.ofNat (48 * records.length)), .addI64,
       .localSet (base + 2)] ++ recordLoadCode (base + 2) eventFields (base + 4)) [] [] []] ++
    discardReadCodeWith calls (base + 1)

def sysPollCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locs : List Nat) (base : Nat) : Program :=
  match subscriptionsOf call.params with
  | some records =>
    fieldsRejectCode (argFields records) locs ++
      .localSet base :: zeroLocalsCode (base + 3) 6 ++
      [.localGet base, .eqzI64,
       .iff 0 0 (sysPollCallCodeWith calls call records locs base) [] [] [],
       .localGet base] ++
      (List.range 6).map (fun index => .localGet (base + 3 + index))
  | none => []

/-- The code of a `sys` command from the locals of its word variables, the root locals of its
input variables, and the root locals of its buffers. -/
def sysInputsCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call) (form : SysForm)
    (words inputs buffers : List Nat) (base : Nat) : Program :=
  match form with
  | .flat _ false => sysFlatInputsCodeWith calls call words inputs base
  | .flat _ true => sysFlatFillCodeWith calls call words inputs (buffers.headD 0) base
  | .reported => sysReportedCodeWith calls call base
  | .record _ => sysRecordCodeWith calls call words inputs base
  | .iovecRead => sysIovecReadCodeWith calls call words (buffers.headD 0) base
  | .iovecWrite => sysIovecWindowCodeWith calls call words (inputs.headD 0) base
  | .poll => sysPollCodeWith calls call words base

theorem sysRejectInputsCode_nil : ∀ (params : List Param) (words : List Nat),
    sysRejectInputsCode params words [] = sysRejectCode params words
  | [], _ => rfl
  | param :: params, words => by
    cases param <;> cases words <;>
      simp only [sysRejectInputsCode, sysRejectCode, sysRejectInputsCode_nil params]

theorem sysLowerInputsCode_nil : ∀ (params : List Param) (words : List Nat) (root slot : Nat),
    sysLowerInputsCode params words [] root slot = sysLowerCode params words root slot
  | [], _, _, _ => rfl
  | param :: params, words, root, slot => by
    cases param <;> cases words <;>
      simp only [sysLowerInputsCode, sysLowerCode, sysLowerInputsCode_nil params]

end Verified.Wasi
