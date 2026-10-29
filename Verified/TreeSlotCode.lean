import Verified.TreeAdvance
import Verified.LocalFrame
import Verified.TreeCopyCode
import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem treeSlotAddress_eq (p : UInt64) (i : Nat) :
    (p + UInt64.ofNat i * 8).toUInt32 = slotAddress p i := by
  unfold slotAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

end Verified
