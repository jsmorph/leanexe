import Project.ProofKit.FixedArraySearchFrame
import Project.ProofKit.Memory
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.FixedArraySearch
open Wasm Memory

def readProgram (start : Nat) : Wasm.Program :=
  [.localGet (start + 2), .constI64 32, .subI64, .wrapI64, .load64 0, .localSet (start + 3),
    .localGet (start + 2), .constI64 8, .subI64, .wrapI64, .load64 0, .localSet (start + 4)]

theorem readProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (need previous root capacity next result oldCapacity oldNext : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296)
    (hFit : root.toNat ≤ store.mem.pages * 65536)
    (hCapacityRead : store.mem.read64 (root - 32).toUInt32 = capacity)
    (hNextRead : store.mem.read64 (root - 8).toUInt32 = next)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (frame params saved tail need previous root capacity next result) env) :
    wp module_ (readProgram start ++ rest) Q store
      (frame params saved tail need previous root oldCapacity oldNext result) env := by
  have hBound (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (root - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [toUInt32_toNat, toNat_sub_of_le root offset (by omega)]
    omega
  have hCapacityBound : (root.toUInt32 - 32).toNat + 8 ≤ store.mem.pages * 65536 := by
    simpa using hBound 32 (by decide) (by decide)
  have hNextBound : (root.toUInt32 - 8).toNat + 8 ≤ store.mem.pages * 65536 := by
    simpa using hBound 8 (by decide) (by decide)
  have hCapacityRead' : store.mem.read64 (root.toUInt32 - 32) = capacity := by
    simpa using hCapacityRead
  have hNextRead' : store.mem.read64 (root.toUInt32 - 8) = next := by
    simpa using hNextRead
  subst start
  simpa [readProgram, wp_simp, frame, Nat.add_assoc, Nat.reducePow, ← toUInt32_eq_ofNat,
    hCapacityRead', hNextRead', Nat.not_lt.mpr hCapacityBound, Nat.not_lt.mpr hNextBound] using hNext

def advanceProgram (start : Nat) : Wasm.Program :=
  [.localGet (start + 2), .localSet (start + 1), .localGet (start + 4), .localSet (start + 2)]

theorem advanceProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (need previous root capacity next result : UInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (frame params saved tail need root next capacity next result) env) :
    wp module_ (advanceProgram start ++ rest) Q store
      (frame params saved tail need previous root capacity next result) env := by
  subst start
  simpa [advanceProgram, wp_simp, frame, Nat.add_assoc] using hNext

#print axioms readProgram_spec
#print axioms advanceProgram_spec

end Project.ProofKit.FixedArraySearch
