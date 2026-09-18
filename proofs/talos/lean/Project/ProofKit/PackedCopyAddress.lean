import Project.ProofKit.CopyAddress
import Project.ProofKit.FixedArrayCopy

namespace Project.ProofKit.PackedCopy
open Wasm

def address (pointer : UInt64) (offset index : Nat) : UInt32 :=
  (pointer + UInt64.ofNat offset + UInt64.ofNat index).toUInt32

def addressCode (pointerLocal counterLocal : Nat) (offsetLocal : Option Nat) : Wasm.Program :=
  [.localGet pointerLocal] ++
    (match offsetLocal with
      | none => []
      | some index => [.localGet index, .addI64]) ++
    [.localGet counterLocal, .addI64, .wrapI64]

theorem address_toNat (pointer : UInt64) (offset count index : Nat)
    (hFit : pointer.toNat + offset + count ≤ 4294967296) (hIndex : index < count) :
    (address pointer offset index).toNat = pointer.toNat + offset + index := by
  simp only [address, UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

theorem addressCode_spec (pointerLocal counterLocal : Nat) (offsetLocal : Option Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer : UInt64) (offset index : Nat) (tail : List Value)
    (hValues : frame.values = tail)
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hIndex : frame.get counterLocal = some (.i64 (UInt64.ofNat index)))
    (hOffset : CopyAddress.OffsetAt frame offsetLocal offset)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i32 (address pointer offset index) :: tail } env) :
    wp module_ (addressCode pointerLocal counterLocal offsetLocal ++ rest) Q store frame env := by
  cases offsetLocal with
  | none =>
    have hZero : offset = 0 := hOffset
    subst offset
    simpa only [addressCode, address, List.cons_append, List.nil_append, wp_simp,
      Frame.withValues_get, hPointer, hIndex, hValues, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero,
      Memory.toUInt32_eq_ofNat, Nat.reducePow] using hNext
  | some local_ =>
    have hRead : frame.get local_ = some (.i64 (UInt64.ofNat offset)) := hOffset
    simpa only [addressCode, address, List.cons_append, List.nil_append, wp_simp,
      Frame.withValues_get, hPointer, hIndex, hRead, hValues,
      Memory.toUInt32_eq_ofNat, Nat.reducePow] using hNext

#print axioms addressCode_spec

end Project.ProofKit.PackedCopy
