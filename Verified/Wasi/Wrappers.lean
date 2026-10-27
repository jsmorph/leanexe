import Verified.Wasi.Module
import Verified.Wasi.ReadCode

namespace Verified.Wasi.Wrappers

open Wasm

def readType : FuncType :=
  { params := [.i64], results := [.i64, .i64, .i64] }

def writeType : FuncType :=
  { params := [.i64, .i64], results := [.i64, .i64] }

def extension (source : Wasm.Module) (next : Module.Extension) : Module.Extension :=
  { types := [readType, writeType] ++ next.types
    funcs := [readFunction (Module.extraTypeIndex source 0),
      writeFunction .stdout (Module.extraTypeIndex source 1),
      writeFunction .stderr (Module.extraTypeIndex source 1)] ++ next.funcs
    exports := next.exports.map fun entry => { entry with funcIdx := 3 + entry.funcIdx } }

def readIndex (source : Wasm.Module) : Nat := Module.extraIndex source 0

def stdoutIndex (source : Wasm.Module) : Nat := Module.extraIndex source 1

def stderrIndex (source : Wasm.Module) : Nat := Module.extraIndex source 2

def effectIndex (source : Wasm.Module) (index : Nat) : Nat := Module.extraIndex source (3 + index)

theorem read_function (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length]? =
      some (readFunction (Module.extraTypeIndex source 0)) := by
  exact (Module.extra_function source (extension source next) 0).trans rfl

theorem stdout_function (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length + 1]? =
      some (writeFunction .stdout (Module.extraTypeIndex source 1)) :=
  Module.extra_function source (extension source next) 1

theorem stderr_function (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length + 2]? =
      some (writeFunction .stderr (Module.extraTypeIndex source 1)) :=
  Module.extra_function source (extension source next) 2

theorem next_function (source : Wasm.Module) (next : Module.Extension) (index : Nat) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length + (3 + index)]? =
      next.funcs[index]? := by
  rw [Module.extra_function]
  change (readFunction (Module.extraTypeIndex source 0) ::
    writeFunction .stdout (Module.extraTypeIndex source 1) ::
    writeFunction .stderr (Module.extraTypeIndex source 1) :: next.funcs)[3 + index]? = _
  rw [Nat.add_comm 3 index]
  rfl

theorem read_type (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).types[Module.extraTypeIndex source 0]? =
      some readType :=
  Module.extra_type_index source (extension source next) 0

theorem write_type (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).types[Module.extraTypeIndex source 1]? =
      some writeType :=
  Module.extra_type_index source (extension source next) 1

theorem next_export (source : Wasm.Module) {next : Module.Extension} {entry : Export}
    (h : entry ∈ next.exports) :
    { entry with funcIdx := effectIndex source entry.funcIdx } ∈
      (Module.assemble source (extension source next)).exports := by
  have hMember : { entry with funcIdx := 3 + entry.funcIdx } ∈
      (extension source next).exports := List.mem_map.mpr ⟨entry, h, rfl⟩
  exact Module.extra_export source hMember

end Verified.Wasi.Wrappers
