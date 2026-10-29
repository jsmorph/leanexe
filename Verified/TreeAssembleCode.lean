import Verified.TreeAssemble
import Verified.TreeFieldsStore
import Verified.LocalFrame
import Verified.TreeCopyCode
import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def sealRecordCode (width ptr : Nat) (mask : UInt64) : Program :=
  headerStore ptr 24 [.constI64 1] ++
    headerStore ptr 16 [.constI64 (UInt64.ofNat width)] ++
    headerStore ptr 8 [.constI64 mask]

theorem recordWriteValues_append (ptr : UInt64) :
    ∀ (i : Nat) (pre words : List UInt64) (store : Store Unit),
      recordWriteValues ptr i (pre ++ words) store =
        recordWriteValues ptr (i + pre.length) words (recordWriteValues ptr i pre store)
  | i, [], words, store => by simp [recordWriteValues]
  | i, word :: pre, words, store => by
    simp only [List.cons_append, recordWriteValues, List.length_cons]
    rw [recordWriteValues_append ptr (i + 1) pre words]
    congr 1
    omega

end Verified
