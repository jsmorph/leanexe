import LeanExe.Encoding.Completeness.Writes

namespace Wasm.Encoding.TableProfileTest

def wasi : Wasm.Module :=
  { funcs := []
    tables := [Spec.emptyFunctionTable]
    tableExports := [("__indirect_function_table", 0)] }

theorem tableFree_bytes : encode ({ funcs := [] } : Wasm.Module) = .ok
    ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 1, 0, 2, 1, 0, 3, 1, 0,
      5, 1, 0, 6, 1, 0, 7, 1, 0, 10, 1, 0]⟩ := by
  rfl

theorem wasi_roundTrip :
    ∃ bytes, encode wasi = .ok bytes ∧ decode bytes = .ok wasi :=
  round_trip wasi (by simp [wasi]) (by decide +kernel)

theorem wasi_tableExports :
    ∀ entry ∈ wasi.tableExports, entry.2 < wasi.tables.length :=
  (Spec.Validity.tableProfile_valid (shape_of_isOk wasi (by decide +kernel))).2

def rejectedModules : List Wasm.Module :=
  [ { wasi with tables := [{ min := 1 }] },
    { wasi with tables := [{ min := 0, max := some 0 }] },
    { wasi with tables := [{ min := 0, elemType := .externref }] },
    { wasi with tables := [{ min := 0, elemType := .i64 }] },
    { wasi with tables := [{ min := 0, elemType := .ref false .func }] },
    { wasi with tables := [{ min := 0, is64 := true }] },
    { wasi with tables := [Spec.emptyFunctionTable, Spec.emptyFunctionTable] },
    { wasi with tables := [] },
    { wasi with tableExports := [] },
    { wasi with tableExports := [("other", 0)] },
    { wasi with tableExports := [("__indirect_function_table", 1)] },
    { wasi with tableExports := [("__indirect_function_table", 0),
        ("__indirect_function_table", 0)] } ]

theorem rejectedModules_fail :
    (rejectedModules.all fun m => !(encode m).isOk) = true := by
  decide +kernel

def exportPayload (name : String) (index : Nat) : List UInt8 :=
  [1] ++ unsigned 32 name.toUTF8.size ++ name.toUTF8.data.toList ++ [1] ++ unsigned 32 index

def binary (tablePayload exports : List UInt8) : ByteArray :=
  ⟨([0, 97, 115, 109, 1, 0, 0, 0] ++
    [4] ++ unsigned 32 tablePayload.length ++ tablePayload ++
    [7] ++ unsigned 32 exports.length ++ exports).toArray⟩

def rejectedBinaries : List ByteArray :=
  let exported := exportPayload "__indirect_function_table" 0
  [ binary [1, 0x6f, 0, 0] exported,
    binary [1, 0x7f, 0, 0] exported,
    binary [1, 0x64, 0x70, 0, 0] exported,
    binary [1, 0x70, 0, 1] exported,
    binary [1, 0x70, 1, 0, 0] exported,
    binary [1, 0x70, 4, 0] exported,
    binary [2, 0x70, 0, 0, 0x70, 0, 0] exported,
    binary [0] exported,
    binary [1, 0x70, 0, 0] [0],
    binary [1, 0x70, 0, 0] (exportPayload "other" 0),
    binary [1, 0x70, 0, 0] (exportPayload "__indirect_function_table" 1) ]

theorem rejectedBinaries_fail :
    (rejectedBinaries.all fun bytes => !(decode bytes).isOk) = true := by
  decide +kernel

theorem profileBinary_succeeds :
    (decode (binary [1, 0x70, 0, 0]
      (exportPayload "__indirect_function_table" 0))).isOk = true := by
  decide +kernel

#print axioms tableFree_bytes
#print axioms wasi_roundTrip
#print axioms wasi_tableExports
#print axioms rejectedModules_fail
#print axioms rejectedBinaries_fail
#print axioms profileBinary_succeeds

end Wasm.Encoding.TableProfileTest
