import Verified.Wasi.ReadAllocation
import Verified.Wasi.ReadResult

namespace Verified.Wasi

open Wasm

def readOverflowCode : Program :=
  [.constI64 61, .localSet 2, .constI64 0, .localSet 1, .constI64 0, .localSet 3]

def readReturnCode : Program := [.localGet 2, .localGet 1, .localGet 3]

def readValidCode : Program := readAllocateCode ++ readCallCode 1 0 ++ readResultCode

theorem readCode_parts : readCode 0 1 2 3 =
    [.localGet 0, .constI64 4294967296, .geUI64,
      .iff 0 0 readOverflowCode readValidCode [] []] ++ readReturnCode := rfl

theorem wp_read_return {World : Type} {m : Module} {env : HostEnv World}
    {store : Store World} {Q : Assertion World} {rest : Program}
    {capacity root errno length : UInt64} {values : List Value}
    (h : wp m rest Q store
      (readLocals capacity root errno length (.i64 length :: .i64 root :: .i64 errno :: values)) env) :
    wp m (readReturnCode ++ rest) Q store (readLocals capacity root errno length values) env := by
  simpa only [readReturnCode, List.cons_append, List.nil_append, wp_localGet_cons,
    readLocals_errno, readLocals_root, readLocals_length, readLocals_values, readLocals_stack] using h

end Verified.Wasi
