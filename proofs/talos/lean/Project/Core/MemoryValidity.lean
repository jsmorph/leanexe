import Project.Core.Memory
import Project.Core.Validity

namespace Project.Core.MemoryValidity

open Wasm.Encoding.Spec.Validity
open Project.Core.Validity (numeric_nil numeric_i32 numeric_i64)

theorem read_body_typed (context : Context)
    (address : context.locals[0]? = some .i64) (memory : context.hasMemory = true) :
    Program context ByteMemory.readFunction.body [] [.i64] :=
  .cons (.localGet 0 address)
    (.cons (.unary .wrapI64)
      (.cons (.load .i32_8 0 memory)
        (.cons (.unary .extendUI32) (.nil numeric_i64))))

theorem write_body_typed (context : Context)
    (address : context.locals[0]? = some .i64)
    (value : context.locals[1]? = some .i64) (memory : context.hasMemory = true) :
    Program context ByteMemory.writeFunction.body [] [.i64] :=
  .cons (.localGet 0 address)
    (.cons (.unary .wrapI64)
      (.cons (.frame (.localGet 1 value) numeric_i32)
        (.cons (.frame (.unary .wrapI64) numeric_i32)
          (.cons (.store .i32_8 0 memory)
            (.cons (.const64 0) (.nil numeric_i64))))))

theorem grow_body_typed (context : Context)
    (delta : context.locals[0]? = some .i64) (memory : context.hasMemory = true) :
    Program context MemoryGrow.growFunction.body [] [.i64] :=
  .cons (.localGet 0 delta)
    (.cons (.unary .wrapI64)
      (.cons (.memoryGrow memory)
        (.cons (.unary .extendUI32) (.nil numeric_i64))))

theorem store_body_typed (context : Context)
    (address : context.locals[0]? = some .i64)
    (value : context.locals[1]? = some .i64) (memory : context.hasMemory = true) :
    Program context [.localGet 0, .wrapI64, .localGet 1, .wrapI64, .store8 0] [] [] :=
  .cons (.localGet 0 address)
    (.cons (.unary .wrapI64)
      (.cons (.frame (.localGet 1 value) numeric_i32)
        (.cons (.frame (.unary .wrapI64) numeric_i32)
          (.cons (.store .i32_8 0 memory) (.nil numeric_nil)))))

theorem size_body_typed (context : Context) (memory : context.hasMemory = true) :
    Program context Memory.sizeFunction.body [] [.i64] :=
  .cons (.memorySize memory)
    (.cons (.unary .extendUI32)
      (.cons (.frame (.const64 65536) numeric_i64)
        (.cons (.binary .mulI64) (.nil numeric_i64))))

theorem bounds_typed (context : Context)
    (address : context.locals[0]? = some .i64) (memory : context.hasMemory = true) :
    Program context Memory.boundsCode [] [.i32] := by
  have get := Project.Core.Validity.singleton (.localGet 0 address) numeric_i64
  have capacity := Project.Core.Validity.frame (size_body_typed context memory) [.i64] numeric_i64
  have compare := Project.Core.Validity.singleton (context := context) (.binary .ltUI64) numeric_i32
  exact Project.Core.Validity.append get (Project.Core.Validity.append capacity compare)

theorem guarded_read_body_typed (context : Context)
    (address : context.locals[0]? = some .i64) (memory : context.hasMemory = true) :
    Program context Memory.readFunction.body [] [.i64] := by
  have read := read_body_typed { context with labels := [.i64] :: context.labels } address memory
  have zero := Project.Core.Validity.word_const { context with labels := [.i64] :: context.labels } 0
  exact Project.Core.Validity.append (bounds_typed context address memory)
    (Project.Core.Validity.iff_typed (.value .i64 (by simp [Wasm.Encoding.Numeric])) numeric_i64 read zero)

theorem guarded_write_body_typed (context : Context)
    (address : context.locals[0]? = some .i64)
    (value : context.locals[1]? = some .i64) (memory : context.hasMemory = true) :
    Program context Memory.writeFunction.body [] [.i64] := by
  have store := store_body_typed { context with labels := [] :: context.labels } address value memory
  have unchanged : Program { context with labels := [] :: context.labels } [] [] [] := .nil numeric_nil
  have guarded := Project.Core.Validity.iff_typed .empty numeric_nil store unchanged
  exact Project.Core.Validity.append (bounds_typed context address memory)
    (Project.Core.Validity.append guarded (Project.Core.Validity.word_const context 0))

open Wasm.Encoding

theorem read_body_form : ProgramForm ByteMemory.readFunction.body :=
  .cons _ _ (.localGet 0 (by decide))
    (.cons _ _ .wrapI64 (.cons _ _ (.load8U 0) (.cons _ _ .extendUI32 .nil)))

theorem write_body_form : ProgramForm ByteMemory.writeFunction.body :=
  .cons _ _ (.localGet 0 (by decide))
    (.cons _ _ .wrapI64
      (.cons _ _ (.localGet 1 (by decide))
        (.cons _ _ .wrapI64 (.cons _ _ (.store8 0) (.cons _ _ (.const64 0) .nil)))))

theorem grow_body_form : ProgramForm MemoryGrow.growFunction.body :=
  .cons _ _ (.localGet 0 (by decide))
    (.cons _ _ .wrapI64 (.cons _ _ .memoryGrow (.cons _ _ .extendUI32 .nil)))

theorem form_append {first second : Wasm.Program}
    (left : ProgramForm first) (right : ProgramForm second) : ProgramForm (first ++ second) := by
  cases left with
  | nil => exact right
  | cons head tail headForm tailForm => exact .cons _ _ headForm (form_append tailForm right)
termination_by first.length

theorem size_body_form : ProgramForm Memory.sizeFunction.body :=
  .cons _ _ .memorySize
    (.cons _ _ .extendUI32 (.cons _ _ (.const64 65536) (.cons _ _ .mulI64 .nil)))

theorem bounds_form : ProgramForm Memory.boundsCode :=
  .cons _ _ (.localGet 0 (by decide))
    (.cons _ _ .memorySize
      (.cons _ _ .extendUI32
        (.cons _ _ (.const64 65536) (.cons _ _ .mulI64 (.cons _ _ .ltUI64 .nil)))))

theorem guarded_read_body_form : ProgramForm Memory.readFunction.body :=
  form_append bounds_form
    (.cons _ _ (.iff [.i64] _ _ (.value .i64 (by simp [Numeric]))
      read_body_form (.cons _ _ (.const64 0) .nil)) .nil)

theorem guarded_write_body_form : ProgramForm Memory.writeFunction.body :=
  form_append bounds_form
    (.cons _ _ (.iff [] _ _ .empty
      (.cons _ _ (.localGet 0 (by decide))
        (.cons _ _ .wrapI64
          (.cons _ _ (.localGet 1 (by decide))
            (.cons _ _ .wrapI64 (.cons _ _ (.store8 0) .nil))))) .nil)
      (.cons _ _ (.const64 0) .nil))

end Project.Core.MemoryValidity
