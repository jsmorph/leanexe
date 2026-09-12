import Project.ProofKit.Array
import Project.ProofKit.Frame
import Project.ProofKit.Control

namespace Project.ProofKit.CopyAddress
open Wasm

def program (pointerLocal counterLocal : Nat) (offsetLocal : Option Nat) : Wasm.Program :=
  [.localGet pointerLocal] ++
    (match offsetLocal with
      | none => [.localGet counterLocal]
      | some index => [.localGet index, .localGet counterLocal, .addI64]) ++
    [.constI64 1, .addI64, .constI64 8, .mulI64, .addI64, .wrapI64]

def OffsetAt (frame : Locals) (local_ : Option Nat) (offset : Nat) : Prop :=
  match local_ with
  | none => offset = 0
  | some index => frame.get index = some (.i64 (UInt64.ofNat offset))

theorem offset_word (offset counter : Nat) :
    (UInt64.ofNat offset + UInt64.ofNat counter + 1) * 8 =
      UInt64.ofNat (8 * (offset + counter + 1)) := by
  change (UInt64.ofNat offset + UInt64.ofNat counter + UInt64.ofNat 1) * UInt64.ofNat 8 = _
  rw [← UInt64.ofNat_add, ← UInt64.ofNat_add, ← UInt64.ofNat_mul, Nat.mul_comm]

theorem program_spec (pointerLocal counterLocal : Nat) (offsetLocal : Option Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer : UInt64) (offset counter : Nat) (tail : List Value)
    (hValues : frame.values = tail)
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hCounter : frame.get counterLocal = some (.i64 (UInt64.ofNat counter)))
    (hOffset : OffsetAt frame offsetLocal offset)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i32 (UInt64Array.wordAddress pointer (offset + counter + 1)) :: tail } env) :
    wp module_ (program pointerLocal counterLocal offsetLocal ++ rest) Q store frame env := by
  cases offsetLocal with
  | none =>
    have hZero : offset = 0 := hOffset
    subst offset
    have hWord := offset_word 0 counter
    have hZeroWord : UInt64.ofNat 0 = 0 := rfl
    simp only [hZeroWord, UInt64.zero_add, Nat.zero_add] at hWord
    simpa only [program, List.cons_append, List.nil_append, wp_simp,
      Frame.withValues_get, hPointer, hCounter, hValues, hWord, Nat.zero_add,
      UInt64Array.wordAddress, Memory.toUInt32_eq_ofNat, Nat.reducePow] using hNext
  | some index =>
    have hRead : frame.get index = some (.i64 (UInt64.ofNat offset)) := hOffset
    simpa only [program, List.cons_append, List.nil_append, wp_simp,
      Frame.withValues_get, hPointer, hCounter, hRead, hValues, offset_word,
      UInt64Array.wordAddress, Memory.toUInt32_eq_ofNat, Nat.reducePow] using hNext

#print axioms offset_word
#print axioms program_spec

end Project.ProofKit.CopyAddress
