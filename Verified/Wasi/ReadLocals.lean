import Verified.Wasi.ReadCode
import Verified.LocalFrame

namespace Verified.Wasi

open Wasm

def readLocals (capacity root errno length : UInt64) (values : List Value := []) : Locals :=
  { params := [.i64 capacity]
    locals := [.i64 root, .i64 errno, .i64 length]
    values }

@[simp] theorem readLocals_stack (capacity root errno length : UInt64) (values : List Value) :
    (readLocals capacity root errno length values).values = values := rfl

@[simp] theorem readLocals_capacity (capacity root errno length : UInt64) (values : List Value) :
    (readLocals capacity root errno length values).get 0 = some (.i64 capacity) := rfl

@[simp] theorem readLocals_root (capacity root errno length : UInt64) (values : List Value) :
    (readLocals capacity root errno length values).get 1 = some (.i64 root) := rfl

@[simp] theorem readLocals_errno (capacity root errno length : UInt64) (values : List Value) :
    (readLocals capacity root errno length values).get 2 = some (.i64 errno) := rfl

@[simp] theorem readLocals_length (capacity root errno length : UInt64) (values : List Value) :
    (readLocals capacity root errno length values).get 3 = some (.i64 length) := rfl

@[simp] theorem readLocals_values (capacity root errno length : UInt64)
    (first second : List Value) :
    { readLocals capacity root errno length first with values := second } =
      readLocals capacity root errno length second := rfl

@[simp] theorem readLocals_set_root (capacity root errno length value : UInt64)
    (values : List Value) :
    setLocal (readLocals capacity root errno length values) 1 (.i64 value) =
      readLocals capacity value errno length values := rfl

@[simp] theorem readLocals_set_errno (capacity root errno length value : UInt64)
    (values : List Value) :
    setLocal (readLocals capacity root errno length values) 2 (.i64 value) =
      readLocals capacity root value length values := rfl

@[simp] theorem readLocals_set_length (capacity root errno length value : UInt64)
    (values : List Value) :
    setLocal (readLocals capacity root errno length values) 3 (.i64 value) =
      readLocals capacity root errno value values := rfl

theorem readFunction_locals (typeIdx : Nat) (capacity : UInt64) :
    (readFunction typeIdx).toLocals [.i64 capacity] = readLocals capacity 0 0 0 := rfl

end Verified.Wasi
