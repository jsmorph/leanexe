import Verified.Wasi.ReadCode
import Verified.Wasi.SysForm

/-! The code of a `sys` command, which the compiler places in the calling function.  It reads the
argument words from the locals of the argument variables and uses six i64 locals from `base`.

A flat call keeps its errno at `base`, its buffer's root at `base + 1` and length at `base + 2`,
and its result words at `base + 3` and `base + 4`.  The code tests the arguments, allocates the
buffer, pushes the core arguments with the result words at scratch addresses 0 and 8, calls the
import, and on errno 0 loads the result words and keeps the buffer, or otherwise releases it.

A reported call keeps its errno at `base`, the reporter's words at `base + 1` and `base + 2`, and
its buffer's root at `base + 3` and length at `base + 4`.  The code calls the reporter with its
words at scratch addresses 0 and 8, tests the sizes, allocates one block for the shown region and
the hidden region after it at the next multiple of 4, and calls the import. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi

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
  | .word64 :: params, _ :: locals => sysRejectCode params locals
  | _ :: params, locals => sysRejectCode params locals

/-- Pushes the core arguments of a flat call: each word from its local, the buffer's root from
`root` and its capacity from its local, and the scratch address `slot` of each result word in
turn. -/
def sysLowerCode : List Param → List Nat → Nat → Nat → Program
  | [], _, _, _ => []
  | .word32 :: params, place :: locals, root, slot
  | .enum32 _ :: params, place :: locals, root, slot =>
    [.localGet place, .wrapI64] ++ sysLowerCode params locals root slot
  | .word64 :: params, place :: locals, root, slot =>
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

def sysCodeWith (calls : List LeanExe.Wasi.Call) (call : LeanExe.Wasi.Call) (form : SysForm) (locals : List Nat)
    (base : Nat) : Program :=
  match form with
  | .flat .. => sysFlatCodeWith calls call locals base
  | .reported => sysReportedCodeWith calls call base

end Verified.Wasi
