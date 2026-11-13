import Verified.Wasi.ReadCode
import Verified.Wasi.SysForm

/-! The code of a `sys` command, which the compiler places in the calling function.  It reads the
argument words from the locals of the argument variables, the root and the length of each input
from the two locals of its variable, and uses the i64 locals from `base` that `SysForm.width`
counts.

A flat call keeps its errno at `base`, its buffer's root at `base + 1` and length at `base + 2`,
and its result words at `base + 3` and `base + 4`.  The code tests the arguments, allocates the
buffer, pushes the core arguments with the result words at scratch addresses 0 and 8, calls the
import, and on errno 0 loads the result words and keeps the buffer, or otherwise releases it.

A reported call keeps its errno at `base`, the reporter's words at `base + 1` and `base + 2`, and
its buffer's root at `base + 3` and length at `base + 4`.  The code calls the reporter with its
words at scratch addresses 0 and 8, tests the sizes, allocates one block for the shown region and
the hidden region after it at the next multiple of 4, and calls the import.

A record call keeps its errno at `base`, its block's root at `base + 1`, the record pointer at
`base + 2`, and its fields from `base + 3`.  The code tests the arguments, allocates a block of
`size + align - 1` bytes, passes its root rounded up to a multiple of `align` as the record pointer,
calls the import, on errno 0 loads each field from the record, and releases the block. -/

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

/-- Pushes the core arguments of a flat call: each word from its local, the buffer's root from
`root` and its capacity from its local, and the scratch address `slot` of each result word in
turn. -/
def sysLowerCode : List Param → List Nat → Nat → Nat → Program
  | [], _, _, _ => []
  | .word32 :: params, place :: locals, root, slot
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

/-- The local of the argument that gives the output's capacity. -/
def outputLocal : List Param → List Nat → Option Nat
  | [], _ => none
  | .output :: _, place :: _ => some place
  | param :: params, locals =>
    if param.takesArg then outputLocal params locals.tail else outputLocal params locals

/-- Allocates the output buffer of `capacity` bytes, or takes `(0, 0)` for no bytes. -/
def sysAllocateCodeWith (calls : List LeanExe.Wasi.Call) (capacity root : Nat) : Program :=
  [.localGet capacity, .eqzI64,
   .iff 0 1 [.constI64 0] [.localGet capacity, .call (3 + calls.length)] [] [.i64],
   .localSet root]

/-- The allocation of the output buffer, when the call has an output. -/
def sysAllocateBufferWith (calls : List LeanExe.Wasi.Call) (buffer : Option Nat) (base : Nat) :
    Program :=
  match buffer with
  | some capacity => sysAllocateCodeWith calls capacity (base + 1)
  | none => []

/-- The code that keeps the output buffer's capacity as its length. -/
def sysKeepCode (buffer : Option Nat) (base : Nat) : Program :=
  match buffer with
  | some capacity => [.localGet capacity, .localSet (base + 2)]
  | none => []

/-- The code that releases the output buffer after an errno. -/
def sysDiscardCodeWith (calls : List LeanExe.Wasi.Call) (buffer : Option Nat) (base : Nat) :
    Program :=
  match buffer with
  | some _ => discardReadCodeWith calls (base + 1)
  | none => []

/-- The code that pushes the output buffer's root and length. -/
def sysPushBytesCode (buffer : Option Nat) (base : Nat) : Program :=
  match buffer with
  | some _ => [.localGet (base + 1), .localGet (base + 2)]
  | none => []

/-- The code of an accepted flat request: the allocation, the call, and the results. -/
def sysFlatCallCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locals : List Nat) (base : Nat) (buffer : Option Nat) : Program :=
  sysAllocateBufferWith calls buffer base ++ sysLowerCode call.params locals (base + 1) 0 ++
    [.call (3 + calls.idxOf call), .extendUI32, .localSet base,
     .localGet base, .eqzI64,
     .iff 0 0 (sysLoadCode call.params 0 (base + 3) ++ sysKeepCode buffer base)
       (sysDiscardCodeWith calls buffer base) [] []]

def sysFlatCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (locals : List Nat) (base : Nat) : Program :=
  sysRejectCode call.params locals ++
    [.localSet base, .constI64 0, .localSet (base + 1), .constI64 0, .localSet (base + 2),
     .constI64 0, .localSet (base + 3), .constI64 0, .localSet (base + 4),
     .localGet base, .eqzI64,
     .iff 0 0 (sysFlatCallCodeWith calls call locals base (outputLocal call.params locals))
       [] [] [],
     .localGet base] ++
    (List.range (call.params.countP Param.isResult)).map
      (fun index => .localGet (base + 3 + index)) ++
    sysPushBytesCode (outputLocal call.params locals) base

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
length from its two locals, the buffer's root from `root` and its capacity from its local, and the
scratch address `slot` of each result word in turn. -/
def sysLowerInputsCode : List Param → List Nat → List Nat → Nat → Nat → Program
  | [], _, _, _, _ => []
  | .input :: params, words, place :: inputs, root, slot =>
    [.localGet place, .wrapI64, .localGet (place + 1), .wrapI64] ++
      sysLowerInputsCode params words inputs root slot
  | .word32 :: params, place :: words, inputs, root, slot
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

/-- The local of the word argument that gives the output's capacity. -/
def outputLocalInputs : List Param → List Nat → List Nat → Option Nat
  | [], _, _ => none
  | .output :: _, place :: _, _ => some place
  | .input :: params, words, _ :: inputs => outputLocalInputs params words inputs
  | param :: params, words, inputs =>
    if param.takesArg then outputLocalInputs params words.tail inputs
    else outputLocalInputs params words inputs

/-- The code of an accepted flat request with inputs. -/
def sysFlatCallInputsCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (base : Nat) (buffer : Option Nat) : Program :=
  sysAllocateBufferWith calls buffer base ++
    sysLowerInputsCode call.params words inputs (base + 1) 0 ++
    [.call (3 + calls.idxOf call), .extendUI32, .localSet base,
     .localGet base, .eqzI64,
     .iff 0 0 (sysLoadCode call.params 0 (base + 3) ++ sysKeepCode buffer base)
       (sysDiscardCodeWith calls buffer base) [] []]

def sysFlatInputsCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words inputs : List Nat) (base : Nat) : Program :=
  sysRejectInputsCode call.params words inputs ++
    [.localSet base, .constI64 0, .localSet (base + 1), .constI64 0, .localSet (base + 2),
     .constI64 0, .localSet (base + 3), .constI64 0, .localSet (base + 4),
     .localGet base, .eqzI64,
     .iff 0 0 (sysFlatCallInputsCodeWith calls call words inputs base
       (outputLocalInputs call.params words inputs)) [] [] [],
     .localGet base] ++
    (List.range (call.params.countP Param.isResult)).map
      (fun index => .localGet (base + 3 + index)) ++
    sysPushBytesCode (outputLocalInputs call.params words inputs) base

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

def sysCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call) (form : SysForm) (locals : List Nat)
    (base : Nat) : Program :=
  match form with
  | .flat .. => sysFlatCodeWith calls call locals base
  | .reported => sysReportedCodeWith calls call base
  | .record _ => sysRecordCodeWith calls call locals [] base

def sysInputsCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call) (form : SysForm)
    (words inputs : List Nat) (base : Nat) : Program :=
  match form with
  | .flat .. => sysFlatInputsCodeWith calls call words inputs base
  | .reported => sysReportedCodeWith calls call base
  | .record _ => sysRecordCodeWith calls call words inputs base

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

theorem outputLocalInputs_nil : ∀ (params : List Param) (words : List Nat),
    outputLocalInputs params words [] = outputLocal params words
  | [], _ => rfl
  | param :: params, words => by
    cases param <;> cases words <;>
      simp only [outputLocalInputs, outputLocal, outputLocalInputs_nil params]

theorem sysFlatCallInputsCodeWith_nil (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words : List Nat) (base : Nat) (buffer : Option Nat) :
    sysFlatCallInputsCodeWith calls call words [] base buffer =
      sysFlatCallCodeWith calls call words base buffer := by
  simp only [sysFlatCallInputsCodeWith, sysFlatCallCodeWith, sysLowerInputsCode_nil]

theorem sysFlatInputsCodeWith_nil (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (words : List Nat) (base : Nat) :
    sysFlatInputsCodeWith calls call words [] base = sysFlatCodeWith calls call words base := by
  simp only [sysFlatInputsCodeWith, sysFlatCodeWith, sysFlatCallInputsCodeWith_nil,
    sysRejectInputsCode_nil, outputLocalInputs_nil]

theorem sysInputsCodeWith_nil (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call)
    (form : SysForm) (words : List Nat) (base : Nat) :
    sysInputsCodeWith calls call form words [] base = sysCodeWith calls call form words base := by
  cases form with
  | flat => simp only [sysInputsCodeWith, sysCodeWith, sysFlatInputsCodeWith_nil]
  | reported => rfl
  | record => rfl

end Verified.Wasi
