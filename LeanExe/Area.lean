import Interpreter.Wasm.Syntax
import LeanExe.A64.Machine

/-!
The area that holds a module's store in a back end's memory: a header of 4,096 bytes and then
the memory's bytes.  Byte 0 of the header starts the memory's size less 8 as a 64-bit word,
global `i` lies in the word at byte `8 (i + 1)`, and the memory's byte `j` lies at byte
`4096 + j`.  The AArch64 back end places the area in its image and the Cortex-M7 back end in
DTCM, and both reach a global or a memory byte at a fixed offset from the area's address.

`areaPrefixBytes m` gives the area's first `areaPrefix m` bytes as the module starts: the size
word, the globals, and the memory up to the end of its data segments, a multiple of 8.  Every
later byte of the area is 0, as `areaByte_tail` of `LeanExe/Proof/Area.lean` states.  A word's
bytes are those that `byteOf` of the AArch64 model gives, the lowest first.
-/

namespace LeanExe

open Wasm

/-- The type of a number. -/
def valueType : Value → Option ValueType
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .f32 _ => some .f32
  | .f64 _ => some .f64
  | _ => none

/-- The types of the globals of `m`, when each is a number. -/
def globalTypesOf (m : Module) : Option (List ValueType) :=
  m.globals.mapM fun g => valueType g.init

/-- The memory of `m` fits an area of `cap` pages: it has 32-bit addresses and between 1 and
`cap` pages, and `cap` lies below 4096. -/
def areaOk (m : Module) (cap : Nat) : Bool :=
  match m.memory with
  | some d => !d.is64 && 1 ≤ d.pagesMin.toNat && d.pagesMin.toNat ≤ cap && cap < 4096
  | none => false

/-- The number of bytes of the area of a memory of `cap` pages. -/
def areaSize (cap : Nat) : Nat := 4096 + cap * 65536

/-- The word of a number in a register. -/
def wordOf : Value → UInt64
  | .i32 x => x.toUInt64
  | .i64 x => x
  | .f32 x => x.toUInt64
  | .f64 x => x
  | _ => 0

/-- Byte `j` of the area of the store `st`: the size of its memory less 8, the words of its
globals from byte 8, and from byte 4096 the bytes of its memory. -/
def areaByte (st : Store Unit) (j : Nat) : UInt8 :=
  if j < 8 then A64.byteOf (UInt64.ofNat (st.mem.pages * 65536 - 8)) j
  else if j < 4096 then
    match st.globals.globals[j / 8 - 1]? with
    | some v => A64.byteOf (wordOf v) (j % 8)
    | none => 0
  else st.mem.bytes (j - 4096)

/-- The bytes of the area of module `m` with `cap` pages, as the module starts. -/
def areaBytes (m : Module) (cap : Nat) : List UInt8 :=
  (List.range (areaSize cap)).map (areaByte m.initialStore)

/-- `n` rounded up to a multiple of `a`. -/
def roundUp (n a : Nat) : Nat := (n + a - 1) / a * a

/-- The larger of `acc` and the end of the data segment `seg`, if it has an offset. -/
def segEnd (acc : Nat) (seg : DataSegment) : Nat :=
  match seg.offset with
  | some off => max acc (off.toNat + seg.bytes.length)
  | none => acc

/-- The end of the data segments of `m`'s memory: the largest offset plus length of a segment
with an offset, or 0. -/
def dataEnd (m : Module) : Nat :=
  match m.memory with
  | some d => d.data.foldl segEnd 0
  | none => 0

/-- The number of the area's bytes that an image holds: the size word, the globals, and the
memory up to the end of its data segments, a multiple of 8.  Every later byte of the area is 0. -/
def areaPrefix (m : Module) : Nat := roundUp (4096 + dataEnd m) 8

/-- `acc` with the bytes of the data segment `seg` written from its offset, when the module's
start writes them into memory 0 of `pages` pages, as `Module.initialStore` does. -/
def segWrite (pages : Nat) (acc : List UInt8) (seg : DataSegment) : List UInt8 :=
  match seg.offset with
  | some off =>
      if seg.memIdx = 0 && seg.offsetExpr.isEmpty then
        if off.toNat + seg.bytes.length ≤ pages * 65536 then
          acc.take off.toNat ++ seg.bytes ++ acc.drop (off.toNat + seg.bytes.length)
        else acc
      else acc
  | none => acc

/-- The first `n` bytes of the initial memory of `m`, for `n` at or past `dataEnd m`, computed by
writing each data segment into a list of zeros. -/
def memPrefix (m : Module) (n : Nat) : List UInt8 :=
  match m.memory with
  | some d => d.data.foldl (segWrite d.pagesMin.toNat) (List.replicate n 0)
  | none => List.replicate n 0

/-- The area's first `areaPrefix m` bytes: the size word and the globals, then the memory. -/
def areaPrefixBytes (m : Module) : List UInt8 :=
  (List.range 4096).map (areaByte m.initialStore) ++ memPrefix m (areaPrefix m - 4096)

end LeanExe
