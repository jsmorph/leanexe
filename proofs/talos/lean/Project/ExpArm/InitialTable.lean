import Project.ExpArm.Program
import Project.ExpArm.Table
import Project.ProofKit.ArrayData

namespace Project.ExpArm
open Wasm Project.ProofKit

set_option maxRecDepth 16384

def initialBytes : List UInt8 := module.memory.get!.data[0]!.bytes

theorem initial_bytes :
    initialBytes = UInt64Array.dataBytes (256 :: table.toList) := by
  decide +kernel

theorem initial_memory : (module.initialStore (α := Unit)).mem =
    (Mem.empty 16).writeBytes 4096 (UInt64Array.dataBytes (256 :: table.toList)) := by
  have hb : initialBytes.length = 2056 := by
    rw [initial_bytes, UInt64Array.dataBytes_length]
    simp [table_size]
  have hm : module.memory = some
      { pagesMin := 16
        data := [{ offset := some 4096, bytes := initialBytes, offsetType := some .i32 }] } := rfl
  rw [UInt64Array.initialStore_data_memory module 16 4096 initialBytes hm (by
    rw [hb]; decide), initial_bytes]
  rfl

theorem initial_table : UInt64Array.At
    (module.initialStore (α := Unit)) 4096 table := by
  have hfit : 4096 + 8 * (256 :: table.toList).length ≤ UInt32.size := by
    simp [table_size, UInt32.size]
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [initial_memory]
    decide
  · rw [initial_memory]
    exact UInt64Array.dataBytes_read (Mem.empty 16) 4096 (256 :: table.toList)
      hfit 0 (by simp)
  intro i hi
  rw [initial_memory]
  have h := UInt64Array.dataBytes_read (Mem.empty 16) 4096 (256 :: table.toList)
    hfit (i + 1) (by simpa using hi)
  have hi' : i < 256 := hi
  have haddr : ((4096 : UInt64) + UInt64.ofNat (8 * (i + 1))).toUInt32 =
      UInt32.ofNat (4096 + 8 * (i + 1)) := by
    apply UInt32.toNat.inj
    simp only [Memory.toUInt32_toNat, UInt64.toNat_add,
      UInt64.toNat_ofNat]
    change ((4096 + (8 * (i + 1)) % 18446744073709551616) %
      18446744073709551616) % 4294967296 = (4096 + 8 * (i + 1)) % 4294967296
    omega
  rw [haddr]
  simpa only [List.getElem_cons_succ, Array.getElem_toList] using h

#print axioms initial_table
end Project.ExpArm
