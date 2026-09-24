import Interpreter.Wasm.Host
import Mathlib.Data.List.Basic
import Init.Omega

namespace Project.ByteIO
open Wasm

abbrev Bytes := List UInt8

def inBounds (mem : Mem) (ptr size : Nat) : Prop :=
  ptr ≤ mem.pages * 65536 ∧ size ≤ mem.pages * 65536 - ptr

instance (mem : Mem) (ptr size : Nat) : Decidable (inBounds mem ptr size) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem inBounds_iff (mem : Mem) (ptr size : Nat) :
    inBounds mem ptr size ↔ ptr + size ≤ mem.pages * 65536 := by
  simp only [inBounds]; omega

def readBytes (mem : Mem) (ptr size : Nat) : Bytes :=
  (List.range size).map (fun i => mem.bytes (ptr + i))

def writeBytes (mem : Mem) (ptr : Nat) (bytes : Bytes) : Mem :=
  { mem with bytes := fun a =>
      if ptr ≤ a ∧ a < ptr + bytes.length then bytes[a - ptr]! else mem.bytes a }

@[simp] theorem readBytes_length (mem : Mem) (ptr size : Nat) :
    (readBytes mem ptr size).length = size := by simp [readBytes]

@[simp] theorem writeBytes_pages (mem : Mem) (ptr : Nat) (bytes : Bytes) :
    (writeBytes mem ptr bytes).pages = mem.pages := rfl

theorem writeBytes_frame (mem : Mem) (ptr : Nat) (bytes : Bytes) (a : Nat)
    (h : a < ptr ∨ ptr + bytes.length ≤ a) :
    (writeBytes mem ptr bytes).bytes a = mem.bytes a := by
  simp [writeBytes, show ¬ (ptr ≤ a ∧ a < ptr + bytes.length) by omega]

theorem writeBytes_at (mem : Mem) (ptr : Nat) (bytes : Bytes) (i : Nat)
    (h : i < bytes.length) :
    (writeBytes mem ptr bytes).bytes (ptr + i) = bytes[i]! := by
  simp [writeBytes, h]

theorem readBytes_writeBytes (mem : Mem) (ptr : Nat) (bytes : Bytes) :
    readBytes (writeBytes mem ptr bytes) ptr bytes.length = bytes := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [readBytes, List.getElem_map, List.getElem_range]
    rw [writeBytes_at mem ptr bytes i h₂]
    simp [getElem!_pos, h₂]

theorem write32_frame (mem : Mem) (ptr : UInt32) (value : UInt32) (a : Nat)
    (h : a < ptr.toNat ∨ ptr.toNat + 4 ≤ a) :
    (mem.write32 ptr value).bytes a = mem.bytes a := by
  simp [Mem.write32, show a ≠ ptr.toNat by omega,
    show a ≠ ptr.toNat + 1 by omega, show a ≠ ptr.toNat + 2 by omega,
    show a ≠ ptr.toNat + 3 by omega]

theorem write64_frame (mem : Mem) (ptr : UInt32) (value : UInt64) (a : Nat)
    (h : a < ptr.toNat ∨ ptr.toNat + 8 ≤ a) :
    (mem.write64 ptr value).bytes a = mem.bytes a := by
  simp [Mem.write64, show a ≠ ptr.toNat by omega,
    show a ≠ ptr.toNat + 1 by omega, show a ≠ ptr.toNat + 2 by omega,
    show a ≠ ptr.toNat + 3 by omega, show a ≠ ptr.toNat + 4 by omega,
    show a ≠ ptr.toNat + 5 by omega, show a ≠ ptr.toNat + 6 by omega,
    show a ≠ ptr.toNat + 7 by omega]

structure World where
  input : Bytes := []
  output : Bytes := []
  now : UInt64 := 0
  stdinNonblocking : Bool := false
  stdoutNonblocking : Bool := false
  exited : Option UInt32 := none
  deriving Repr, DecidableEq, Inhabited

/-- Read bytes are copied before the transfer count is stored, exactly as in
the native host, including overlapping caller-supplied ranges. The compiler
uses count address 8 and a heap buffer at or above 4096, so those ranges are
disjoint in generated programs. -/
def commitRead (st : Store World) (ptr countPtr : UInt32) (n : Nat) : Store World :=
  { st with
    mem := (writeBytes st.mem ptr.toNat (st.host.input.take n)).write32 countPtr
      (UInt32.ofNat n)
    host := { st.host with input := st.host.input.drop n } }

def commitWrite (st : Store World) (ptr countPtr : UInt32) (n : Nat) : Store World :=
  { st with
    mem := st.mem.write32 countPtr (UInt32.ofNat n)
    host := { st.host with output := st.host.output ++ readBytes st.mem ptr.toNat n } }

theorem commitRead_conserves (st : Store World) (ptr countPtr : UInt32) (n : Nat) :
    st.host.input.take n ++ (commitRead st ptr countPtr n).host.input = st.host.input := by
  simp [commitRead]

theorem commitRead_at (st : Store World) (ptr countPtr : UInt32) (n i : Nat)
    (hi : i < min n st.host.input.length)
    (hdisjoint : ptr.toNat + i < countPtr.toNat ∨ countPtr.toNat + 4 ≤ ptr.toNat + i) :
    (commitRead st ptr countPtr n).mem.bytes (ptr.toNat + i) = st.host.input[i]! := by
  simp only [commitRead]
  rw [write32_frame _ _ _ _ hdisjoint, writeBytes_at]
  · simp [getElem!_pos, show i < n by omega,
      show i < st.host.input.length by omega]
  · simpa using hi

theorem commitRead_frame (st : Store World) (ptr countPtr : UInt32) (n a : Nat)
    (hbuffer : a < ptr.toNat ∨ ptr.toNat + min n st.host.input.length ≤ a)
    (hcount : a < countPtr.toNat ∨ countPtr.toNat + 4 ≤ a) :
    (commitRead st ptr countPtr n).mem.bytes a = st.mem.bytes a := by
  simp only [commitRead]
  rw [write32_frame _ _ _ _ hcount]
  apply writeBytes_frame
  simpa using hbuffer

theorem commitWrite_frame (st : Store World) (ptr countPtr : UInt32) (n a : Nat)
    (hcount : a < countPtr.toNat ∨ countPtr.toNat + 4 ≤ a) :
    (commitWrite st ptr countPtr n).mem.bytes a = st.mem.bytes a :=
  write32_frame _ _ _ _ hcount

theorem commitWrite_exact (st : Store World) (ptr countPtr : UInt32) (n : Nat) :
    (commitWrite st ptr countPtr n).host.output =
      st.host.output ++ readBytes st.mem ptr.toNat n := rfl

/-- Host transfer effects preserve every other store resource, including
globals, allocation counters, other memories, tables, and runtime identities. -/
theorem commitRead_resources (st : Store World) (ptr countPtr : UInt32) (n : Nat) :
    { (commitRead st ptr countPtr n) with mem := st.mem, host := st.host } = st := rfl

theorem commitWrite_resources (st : Store World) (ptr countPtr : UInt32) (n : Nat) :
    { (commitWrite st ptr countPtr n) with mem := st.mem, host := st.host } = st := rfl

#print axioms commitRead_at
#print axioms commitRead_frame
#print axioms commitWrite_frame

end Project.ByteIO
