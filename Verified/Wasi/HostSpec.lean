import Verified.Wasi.ABI
import Verified.Wasi.Observed
import Verified.Bytes.Memory
import Interpreter.Wasm.Host.Registry
import LeanExe.Runtime.Tree

namespace Verified.Wasi

open Wasm LeanExe LeanExe.Wasi

def InRange (address : Nat) (region : Nat × Nat) : Prop :=
  region.1 ≤ address ∧ address < region.1 + region.2

structure GuestFrame (before after : Store World) (writable : List (Nat × Nat)) : Prop where
  resources : after.mapHost (fun _ => ()) =
    { before.mapHost (fun _ => ()) with mem := after.mem }
  pages : after.mem.pages = before.mem.pages
  bytes : ∀ address, (∀ region ∈ writable, ¬InRange address region) →
    after.mem.bytes address = before.mem.bytes address

theorem GuestFrame.globals {before after : Store World} {writable : List (Nat × Nat)}
    (h : GuestFrame before after writable) : after.globals = before.globals := by
  exact congrArg (fun store : Store Unit => store.globals) h.resources

theorem GuestFrame.memoryCaps {before after : Store World} {writable : List (Nat × Nat)}
    (h : GuestFrame before after writable) : after.memoryCaps = before.memoryCaps := by
  exact congrArg (fun store : Store Unit => store.memoryCaps) h.resources

structure WriteRequest (before : Store World) (args : List Value) (output : Output)
    (pointer : UInt32) (bytes : LeanExe.Bytes) : Prop where
  arguments : args = [.i32 output.fd.toUInt32, .i32 0, .i32 1, .i32 8]
  scratch : 16 ≤ before.mem.pages * 65536
  pointer_eq : before.mem.read32 0 = pointer
  length_eq : before.mem.read32 4 = UInt32.ofNat bytes.data.size
  size : bytes.data.size < 2 ^ 32
  data : Bytes.At before.mem pointer.toUInt64 bytes

structure ReadRequest (before : Store World) (args : List Value)
    (pointer capacity : UInt32) : Prop where
  arguments : args = [.i32 0, .i32 0, .i32 1, .i32 8]
  scratch : 16 ≤ before.mem.pages * 65536
  pointer_eq : before.mem.read32 0 = pointer
  length_eq : before.mem.read32 4 = capacity
  memory : pointer.toNat + capacity.toNat ≤ before.mem.pages * 65536
  address : pointer.toNat + capacity.toNat ≤ 2 ^ 32
  separate : capacity = 0 ∨ 16 ≤ pointer.toNat

def writeContract (host : Host World) : HostContract (Observed World) :=
  fun before args result => ∀ output pointer bytes,
    WriteRequest before args output pointer bytes →
    match result with
    | .Return values after => ∃ (errno committed : UInt64),
        values = [.i32 errno.toUInt32] ∧
        (observedHost host).write before.host output bytes (.returned errno committed) after.host ∧
        GuestFrame before after [ABI.scratch] ∧
        (errno = 0 → after.mem.read32 8 = committed.toUInt32)
    | .Trap after message => ∃ committed : UInt64,
        (observedHost host).write before.host output bytes (.trapped message committed) after.host ∧
        GuestFrame before after [ABI.scratch]
    | .Throw _ _ _ => False

def readContract (host : Host World) : HostContract (Observed World) :=
  fun before args result => ∀ pointer capacity,
    ReadRequest before args pointer capacity →
    match result with
    | .Return values after => ∃ (errno : UInt64) (committed : LeanExe.Bytes),
        values = [.i32 errno.toUInt32] ∧
        (observedHost host).read before.host capacity.toUInt64
          (.returned errno committed) after.host ∧
        GuestFrame before after [ABI.scratch, (pointer.toNat, capacity.toNat)] ∧
        (errno = 0 → Bytes.At after.mem pointer.toUInt64 committed ∧
          after.mem.read32 8 = UInt32.ofNat committed.data.size)
    | .Trap after message => ∃ committed : LeanExe.Bytes,
        (observedHost host).read before.host capacity.toUInt64
          (.trapped message committed) after.host ∧
        GuestFrame before after [ABI.scratch, (pointer.toNat, capacity.toNat)]
    | .Throw _ _ _ => False

def exitTrap : String := "wasi proc_exit"

def exitContract (host : Host World) : HostContract (Observed World) :=
  fun before args result => ∀ code : UInt32, args = [.i32 code] →
    match result with
    | .Trap after message => GuestFrame before after [] ∧
        ((message = exitTrap ∧ (observedHost host).exit before.host code.toUInt64 after.host) ∨
          (observedHost host).exitTrap before.host code.toUInt64 message after.host)
    | .Return _ _ | .Throw _ _ _ => False

def hostSpec (host : Host World) : HostSpec (Observed World) :=
  { contracts := [readContract host, writeContract host, exitContract host] }

theorem hostSpec_read (host : Host World) :
    (hostSpec host).contracts[0]? = some (readContract host) := rfl

theorem hostSpec_write (host : Host World) :
    (hostSpec host).contracts[1]? = some (writeContract host) := rfl

theorem hostSpec_exit (host : Host World) :
    (hostSpec host).contracts[2]? = some (exitContract host) := rfl

/-! ## Flat calls

A request of a flat call places each pointer parameter at one of `pointers`, in parameter order:
an input's bytes, an output buffer, a result word, a reported region, or a record, and for an
`iovec` the element and the buffer, and for `subscriptions` the subscriptions and the events.  The
generic frame follows from the description: the host changes only the output regions, whose sizes
are the capacities, 4 or 8 for result words, the world's reported sizes, the records' sizes, and
32 bytes for each event. -/

/-- One output region of a request: its pointer, size, alignment, and whether the reply carries
its content. -/
structure Region where
  pointer : UInt32
  size : Nat
  align : Nat
  shown : Bool

def Region.span (region : Region) : Nat × Nat := (region.pointer.toNat, region.size)

/-- Whether an argument has the kind of its parameter and fits the parameter's core type: a word
below `2^32` for `word32`, `handle`, `enum32`, and `flags32`, a word for `word64` and `flags64`,
bytes of fewer than `2^32` bytes for `input` and `iovec true`, and a capacity below `2^32` for
`output` and `iovec false`. -/
def argFits : Param → Arg → Bool
  | .word32, .word value | .handle, .word value | .enum32 _, .word value
  | .flags32 _, .word value =>
    decide (value.toNat < 2 ^ 32)
  | .word64, .word _ | .flags64 _, .word _ => true
  | .input, .bytes value | .iovec true, .bytes value => decide (value.data.size < 2 ^ 32)
  | .output, .space capacity | .iovec false, .space capacity => decide (capacity.toNat < 2 ^ 32)
  | _, _ => false

/-- Whether the arguments of the fields `fields` are words, in order, each below `2^(8 width)`. -/
def argFieldsFit : List Field → List Arg → Bool
  | [], _ => true
  | field :: fields, .word value :: args =>
    decide (value.toNat < 2 ^ (8 * field.width)) && argFieldsFit fields args
  | _ :: _, _ => false

/-- Whether `args` holds one fitting argument for each parameter that takes one, and one fitting
word for each word and handle field of a `subscriptions` parameter whose records fit, in order, and
no other.  The core arguments of such a request do not determine it alone, since the pointer and
the length of an iovec's buffer lie in the element in memory: with its input places in memory,
`OracleSys.decodeArgs` reads the request back from the core arguments (`decodeArgs_lower`). -/
def argsFit : List Param → List Arg → Bool
  | [], args => args.isEmpty
  | param :: params, args =>
    if param.takesArg then
      match args with
      | [] => false
      | arg :: rest => argFits param arg && argsFit params rest
    else
      match param with
      | .subscriptions records =>
        recordsFit records && argFieldsFit (argFields records) args &&
          argsFit params (args.drop (argFields records).length)
      | _ => argsFit params args

/-- Byte `index` of the little-endian representation of `value`. -/
def byteOf (value index : Nat) : UInt8 := UInt8.ofNat (value / 2 ^ (8 * index))

/-- The 8 bytes of an iovec element: the buffer's pointer and its length, each as 4 little-endian
bytes. -/
def elementBytes (pointer : UInt32) (length : Nat) : LeanExe.Bytes :=
  ⟨⟨(Array.range 8).map fun index =>
    if index < 4 then byteOf pointer.toNat index else byteOf (length % 2 ^ 32) (index - 4)⟩⟩

/-- The value of each field, in order: a constant's value, or the word of the next argument for a
word or a handle field. -/
def fieldValues : List Field → List Arg → List UInt64
  | [], _ => []
  | field :: fields, args =>
    match field.source with
    | .const value => value :: fieldValues fields args
    | .word | .handle => (args.head?.map Arg.value).getD 0 :: fieldValues fields args.tail

/-- Byte `index` of a block whose bytes are zero and in which each field, in order, is written as
the `width` little-endian bytes of its value at its offset. -/
def blockByte (fields : List Field) (values : List UInt64) (index : Nat) : UInt8 :=
  (fields.zip values).foldl (fun byte placed =>
    if placed.1.offset ≤ index ∧ index < placed.1.offset + placed.1.width then
      byteOf placed.2.toNat (index - placed.1.offset)
    else byte) 0

/-- The bytes of the subscription array of `records` with the arguments `args`: 48 bytes for each
record, zero except for the fields. -/
def subscriptionBytes (records : List (List Field)) (args : List Arg) : LeanExe.Bytes :=
  ⟨⟨(Array.range (48 * records.length)).map
    (blockByte (placedFields 0 records) (fieldValues (placedFields 0 records) args))⟩⟩

/-- The core arguments of a request whose pointer parameters take `pointers` in order.  An `iovec`
parameter takes two pointers, the element's and the buffer's, and a `subscriptions` parameter takes
two, the subscriptions' and the events'. -/
def lowerArgs : List Param → List Arg → List UInt32 → List Value
  | [], _, _ => []
  | .word32 :: params, args, pointers
  | .handle :: params, args, pointers
  | .enum32 _ :: params, args, pointers
  | .flags32 _ :: params, args, pointers =>
    .i32 ((args.head?.map Arg.value).getD 0).toUInt32 :: lowerArgs params args.tail pointers
  | .word64 :: params, args, pointers
  | .flags64 _ :: params, args, pointers =>
    .i64 ((args.head?.map Arg.value).getD 0) :: lowerArgs params args.tail pointers
  | .input :: params, args, pointers =>
    .i32 (pointers.headD 0) :: .i32 (UInt32.ofNat ((args.head?.map Arg.length).getD 0)) ::
      lowerArgs params args.tail pointers.tail
  | .output :: params, args, pointers =>
    .i32 (pointers.headD 0) :: .i32 (UInt32.ofNat ((args.head?.map Arg.capacity).getD 0)) ::
      lowerArgs params args.tail pointers.tail
  | .result32 :: params, args, pointers
  | .result64 :: params, args, pointers
  | .reported .. :: params, args, pointers
  | .record .. :: params, args, pointers =>
    .i32 (pointers.headD 0) :: lowerArgs params args pointers.tail
  | .iovec _ :: params, args, pointers =>
    .i32 (pointers.headD 0) :: .i32 1 :: lowerArgs params args.tail pointers.tail.tail
  | .subscriptions records :: params, args, pointers =>
    .i32 (pointers.headD 0) :: .i32 (pointers.tail.headD 0) :: .i32 (UInt32.ofNat records.length) ::
      lowerArgs params (args.drop (argFields records).length) pointers.tail.tail

/-- The input bytes of a request, each at its pointer: an input's bytes, the element of an `iovec`
and the bytes of `iovec true`, and the subscriptions of `subscriptions`. -/
def inputPlaces : List Param → List Arg → List UInt32 → List (UInt32 × LeanExe.Bytes)
  | [], _, _ => []
  | .word32 :: params, args, pointers
  | .handle :: params, args, pointers
  | .enum32 _ :: params, args, pointers
  | .flags32 _ :: params, args, pointers
  | .flags64 _ :: params, args, pointers
  | .word64 :: params, args, pointers => inputPlaces params args.tail pointers
  | .input :: params, args, pointers =>
    (pointers.headD 0, match args.head? with
      | some (.bytes value) => value
      | _ => LeanExe.Bytes.empty) :: inputPlaces params args.tail pointers.tail
  | .output :: params, args, pointers => inputPlaces params args.tail pointers.tail
  | .result32 :: params, args, pointers
  | .result64 :: params, args, pointers
  | .reported .. :: params, args, pointers
  | .record .. :: params, args, pointers => inputPlaces params args pointers.tail
  | .iovec false :: params, args, pointers =>
    (pointers.headD 0,
      elementBytes (pointers.tail.headD 0) ((args.head?.map Arg.capacity).getD 0)) ::
      inputPlaces params args.tail pointers.tail.tail
  | .iovec true :: params, args, pointers =>
    (pointers.headD 0, elementBytes (pointers.tail.headD 0) ((args.head?.map Arg.length).getD 0)) ::
      (pointers.tail.headD 0, match args.head? with
        | some (.bytes value) => value
        | _ => LeanExe.Bytes.empty) :: inputPlaces params args.tail pointers.tail.tail
  | .subscriptions records :: params, args, pointers =>
    (pointers.headD 0, subscriptionBytes records args) ::
      inputPlaces params (args.drop (argFields records).length) pointers.tail.tail

/-- The output regions of a request, in parameter order, with the sizes `sizes` of the reported
regions. -/
def outputRegions : List Param → List Nat → List Arg → List UInt32 → List Region
  | [], _, _, _ => []
  | .word32 :: params, sizes, args, pointers
  | .handle :: params, sizes, args, pointers
  | .enum32 _ :: params, sizes, args, pointers
  | .flags32 _ :: params, sizes, args, pointers
  | .flags64 _ :: params, sizes, args, pointers
  | .word64 :: params, sizes, args, pointers => outputRegions params sizes args.tail pointers
  | .input :: params, sizes, args, pointers => outputRegions params sizes args.tail pointers.tail
  | .output :: params, sizes, args, pointers =>
    ⟨pointers.headD 0, (args.head?.map Arg.capacity).getD 0, 1, true⟩ ::
      outputRegions params sizes args.tail pointers.tail
  | .result32 :: params, sizes, args, pointers =>
    ⟨pointers.headD 0, 4, 4, true⟩ :: outputRegions params sizes args pointers.tail
  | .result64 :: params, sizes, args, pointers =>
    ⟨pointers.headD 0, 8, 8, true⟩ :: outputRegions params sizes args pointers.tail
  | .reported _ align shown :: params, sizes, args, pointers =>
    ⟨pointers.headD 0, sizes.headD 0, align, shown⟩ ::
      outputRegions params sizes.tail args pointers.tail
  | .record size align _ :: params, sizes, args, pointers =>
    ⟨pointers.headD 0, size, align, true⟩ :: outputRegions params sizes args pointers.tail
  | .iovec false :: params, sizes, args, pointers =>
    ⟨pointers.tail.headD 0, (args.head?.map Arg.capacity).getD 0, 1, true⟩ ::
      outputRegions params sizes args.tail pointers.tail.tail
  | .iovec true :: params, sizes, args, pointers =>
    outputRegions params sizes args.tail pointers.tail.tail
  | .subscriptions records :: params, sizes, args, pointers =>
    ⟨pointers.tail.headD 0, 32 * records.length, 8, true⟩ ::
      outputRegions params sizes (args.drop (argFields records).length) pointers.tail.tail

/-- Each shown region holds its output, in order. -/
def ShownAt (mem : Mem) : List Region → List LeanExe.Bytes → Prop
  | [], outputs => outputs = []
  | region :: regions, outputs =>
    if region.shown then
      match outputs with
      | [] => False
      | output :: rest => Bytes.At mem region.pointer.toUInt64 output ∧ ShownAt mem regions rest
    else ShownAt mem regions outputs

/-- The premise of a flat call's contract: the core arguments lower an accepted request that fits
the call's parameters with the given pointers, the inputs lie at their pointers, and the output
regions, of the sizes the world reports for reported regions, lie in memory, end below `2^32`, and
have aligned pointers, apart from one another and from the inputs.  Inputs may overlap one
another, since the host only reads them. -/
structure SysRequest (before : Store (Observed World)) (args : List Value) (call : Call)
    (request : List Arg) (pointers : List UInt32) (sizes : List Nat) : Prop where
  fits : argsFit call.params request = true
  accepted : call.reject request = 0
  arguments : args = lowerArgs call.params request pointers
  inputs : ∀ place ∈ inputPlaces call.params request pointers,
    Bytes.At before.mem place.1.toUInt64 place.2
  bounds : ∀ region ∈ outputRegions call.params sizes request pointers,
    region.pointer.toNat + region.size ≤ before.mem.pages * 65536 ∧
      region.pointer.toNat + region.size < 2 ^ 32 ∧ region.pointer.toNat % region.align = 0
  apart : ((outputRegions call.params sizes request pointers).map Region.span).Pairwise
    LeanExe.Runtime.regionsDisjoint
  separate : ∀ region ∈ outputRegions call.params sizes request pointers,
    ∀ place ∈ inputPlaces call.params request pointers,
      LeanExe.Runtime.regionsDisjoint region.span (place.1.toNat, place.2.data.size)

/-- The contract of a flat call: for the request that the core arguments lower, the host changes
memory only in the output regions and, on return, gives the errno and leaves each shown output in
its region.  Both outcomes follow the observed host's relation. -/
def sysContract (host : Host World) (call : Call) : HostContract (Observed World) :=
  fun before args result => ∀ request pointers,
    SysRequest before args call request pointers (host.reported before.host.world call) →
    let regions := outputRegions call.params (host.reported before.host.world call) request pointers
    match result with
    | .Return values after => ∃ (errno : UInt64) (outputs : List LeanExe.Bytes),
        values = [.i32 errno.toUInt32] ∧
        (observedHost host).sys before.host call request (.returned errno outputs) after.host ∧
        GuestFrame before after (regions.map Region.span) ∧
        (errno = 0 → ShownAt after.mem regions outputs)
    | .Trap after message => ∃ outputs : List LeanExe.Bytes,
        (observedHost host).sys before.host call request (.trapped message outputs) after.host ∧
        GuestFrame before after (regions.map Region.span)
    | .Throw _ _ _ => False

/-- The host specification of a module that imports the flat calls `calls` after the three
stream imports. -/
def hostSpecWith (host : Host World) (calls : List Call) : HostSpec (Observed World) :=
  { contracts := [readContract host, writeContract host, exitContract host] ++
      calls.map (sysContract host) }

theorem hostSpecWith_nil (host : Host World) : hostSpecWith host [] = hostSpec host := rfl

theorem hostSpecWith_read (host : Host World) (calls : List Call) :
    (hostSpecWith host calls).contracts[0]? = some (readContract host) := rfl

theorem hostSpecWith_write (host : Host World) (calls : List Call) :
    (hostSpecWith host calls).contracts[1]? = some (writeContract host) := rfl

theorem hostSpecWith_exit (host : Host World) (calls : List Call) :
    (hostSpecWith host calls).contracts[2]? = some (exitContract host) := rfl

theorem hostSpecWith_sys (host : Host World) {calls : List Call} {index : Nat}
    {call : Call} (h : calls[index]? = some call) :
    (hostSpecWith host calls).contracts[3 + index]? = some (sysContract host call) := by
  simp only [hostSpecWith]
  rw [List.getElem?_append_right (by simp)]
  simp [h]

end Verified.Wasi
