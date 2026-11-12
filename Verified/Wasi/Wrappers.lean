import Verified.Wasi.Module
import Verified.Wasi.ReadCode

namespace Verified.Wasi.Wrappers

open Wasm LeanExe.Wasi

def readType : FuncType :=
  { params := [.i64], results := [.i64, .i64, .i64] }

def writeType : FuncType :=
  { params := [.i64, .i64], results := [.i64, .i64] }

def extensionWith (calls : List Call) (source : Wasm.Module) (next : Module.Extension) :
    Module.Extension :=
  { types := [readType, writeType] ++ next.types
    funcs := [readFunctionWith calls (Module.extraTypeIndex source 0),
      writeFunction .stdout (Module.extraTypeIndex source 1),
      writeFunction .stderr (Module.extraTypeIndex source 1)] ++ next.funcs
    exports := next.exports.map fun entry => { entry with funcIdx := 3 + entry.funcIdx } }

def extension (source : Wasm.Module) (next : Module.Extension) : Module.Extension :=
  extensionWith [] source next

def readIndexWith (calls : List Call) (source : Wasm.Module) : Nat :=
  Module.extraIndexWith calls source 0

def readIndex (source : Wasm.Module) : Nat := readIndexWith [] source

def stdoutIndexWith (calls : List Call) (source : Wasm.Module) : Nat :=
  Module.extraIndexWith calls source 1

def stdoutIndex (source : Wasm.Module) : Nat := stdoutIndexWith [] source

def stderrIndexWith (calls : List Call) (source : Wasm.Module) : Nat :=
  Module.extraIndexWith calls source 2

def stderrIndex (source : Wasm.Module) : Nat := stderrIndexWith [] source

def effectIndexWith (calls : List Call) (source : Wasm.Module) (index : Nat) : Nat :=
  Module.extraIndexWith calls source (3 + index)

def effectIndex (source : Wasm.Module) (index : Nat) : Nat := effectIndexWith [] source index

/-- The position of an output's write wrapper among the defined functions. -/
def outputPosition (source : Wasm.Module) (output : Output) : Nat :=
  match output with
  | .stdout => source.funcs.length + 1
  | .stderr => source.funcs.length + 2

/-- The function index of an output's write wrapper in a module that imports `calls`. -/
def outputIndexWith (calls : List Call) (source : Wasm.Module) (output : Output) : Nat :=
  match output with
  | .stdout => stdoutIndexWith calls source
  | .stderr => stderrIndexWith calls source

section General

variable {calls : List Call}

theorem read_function_with (source : Wasm.Module) (next : Module.Extension) :
    (Module.assembleWith calls source (extensionWith calls source next)).funcs[source.funcs.length]? =
      some (readFunctionWith calls (Module.extraTypeIndex source 0)) := by
  exact (Module.extra_function_with source (extensionWith calls source next) 0).trans rfl

theorem stdout_function_with (source : Wasm.Module) (next : Module.Extension) :
    (Module.assembleWith calls source (extensionWith calls source next)).funcs[source.funcs.length + 1]? =
      some (writeFunction .stdout (Module.extraTypeIndex source 1)) :=
  Module.extra_function_with source (extensionWith calls source next) 1

theorem stderr_function_with (source : Wasm.Module) (next : Module.Extension) :
    (Module.assembleWith calls source (extensionWith calls source next)).funcs[source.funcs.length + 2]? =
      some (writeFunction .stderr (Module.extraTypeIndex source 1)) :=
  Module.extra_function_with source (extensionWith calls source next) 2

theorem next_function_with (source : Wasm.Module) (next : Module.Extension) (index : Nat) :
    (Module.assembleWith calls source (extensionWith calls source next)).funcs[source.funcs.length + (3 + index)]? =
      next.funcs[index]? := by
  rw [Module.extra_function_with]
  change (readFunctionWith calls (Module.extraTypeIndex source 0) ::
    writeFunction .stdout (Module.extraTypeIndex source 1) ::
    writeFunction .stderr (Module.extraTypeIndex source 1) :: next.funcs)[3 + index]? = _
  rw [Nat.add_comm 3 index]
  rfl

theorem read_type_with (source : Wasm.Module) (next : Module.Extension) :
    (Module.assembleWith calls source (extensionWith calls source next)).types[Module.extraTypeIndex source 0]? =
      some readType :=
  Module.extra_type_index_with source (extensionWith calls source next) 0
    (by simp [extensionWith])

theorem write_type_with (source : Wasm.Module) (next : Module.Extension) :
    (Module.assembleWith calls source (extensionWith calls source next)).types[Module.extraTypeIndex source 1]? =
      some writeType :=
  Module.extra_type_index_with source (extensionWith calls source next) 1
    (by simp [extensionWith])

theorem next_export_with (source : Wasm.Module) {next : Module.Extension} {entry : Export}
    (h : entry ∈ next.exports) :
    { entry with funcIdx := effectIndexWith calls source entry.funcIdx } ∈
      (Module.assembleWith calls source (extensionWith calls source next)).exports := by
  have hMember : { entry with funcIdx := 3 + entry.funcIdx } ∈
      (extensionWith calls source next).exports := List.mem_map.mpr ⟨entry, h, rfl⟩
  exact Module.extra_export_with source hMember

end General

theorem read_function (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length]? =
      some (readFunction (Module.extraTypeIndex source 0)) :=
  read_function_with source next

theorem stdout_function (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length + 1]? =
      some (writeFunction .stdout (Module.extraTypeIndex source 1)) :=
  stdout_function_with source next

theorem stderr_function (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length + 2]? =
      some (writeFunction .stderr (Module.extraTypeIndex source 1)) :=
  stderr_function_with source next

theorem next_function (source : Wasm.Module) (next : Module.Extension) (index : Nat) :
    (Module.assemble source (extension source next)).funcs[source.funcs.length + (3 + index)]? =
      next.funcs[index]? :=
  next_function_with source next index

theorem read_type (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).types[Module.extraTypeIndex source 0]? =
      some readType :=
  read_type_with source next

theorem write_type (source : Wasm.Module) (next : Module.Extension) :
    (Module.assemble source (extension source next)).types[Module.extraTypeIndex source 1]? =
      some writeType :=
  write_type_with source next

theorem next_export (source : Wasm.Module) {next : Module.Extension} {entry : Export}
    (h : entry ∈ next.exports) :
    { entry with funcIdx := effectIndex source entry.funcIdx } ∈
      (Module.assemble source (extension source next)).exports :=
  next_export_with source h

end Verified.Wasi.Wrappers
