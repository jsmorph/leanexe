import LeanExe.Core.NativeLoop

namespace LeanExe.Core.NativeLoopLocals

open LeanExe.IR (ScalarStore)

theorem read_suffix (saved suffix : Locals) (index : Nat) :
    (saved ++ suffix)[saved.length + index]? = suffix[index]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem write_suffix (saved suffix : Locals) (index : Nat) (value : UInt64)
    (bound : index < suffix.length) :
    ScalarStore.write (saved ++ suffix) (saved.length + index) value =
      some (saved ++ suffix.set index value) := by
  simp [ScalarStore.write, List.set_append_right, bound]

/-- Captured arguments followed by the accumulator, bound, and loop counter. -/
def layout (saved : Locals) (accumulator limit : UInt64) (index : Nat)
    (scratch : Locals) : Locals :=
  saved ++ [accumulator, limit, UInt64.ofNat index] ++ scratch

@[simp] theorem layout_accumulator (saved : Locals) (accumulator limit : UInt64)
    (index : Nat) (scratch : Locals) :
    (layout saved accumulator limit index scratch)[saved.length]? = some accumulator := by
  simpa [layout, List.append_assoc] using
    read_suffix saved ([accumulator, limit, UInt64.ofNat index] ++ scratch) 0

@[simp] theorem layout_limit (saved : Locals) (accumulator limit : UInt64)
    (index : Nat) (scratch : Locals) :
    (layout saved accumulator limit index scratch)[saved.length + 1]? = some limit := by
  simpa [layout, List.append_assoc] using
    read_suffix saved ([accumulator, limit, UInt64.ofNat index] ++ scratch) 1

@[simp] theorem layout_counter (saved : Locals) (accumulator limit : UInt64)
    (index : Nat) (scratch : Locals) :
    (layout saved accumulator limit index scratch)[saved.length + 2]? =
      some (UInt64.ofNat index) := by
  simpa [layout, List.append_assoc] using
    read_suffix saved ([accumulator, limit, UInt64.ofNat index] ++ scratch) 2

@[simp] theorem layout_write_accumulator (saved : Locals) (accumulator limit value : UInt64)
    (index : Nat) (scratch : Locals) :
    ScalarStore.write (layout saved accumulator limit index scratch) saved.length value =
      some (layout saved value limit index scratch) := by
  simpa [layout, List.append_assoc] using
    write_suffix saved ([accumulator, limit, UInt64.ofNat index] ++ scratch) 0 value (by simp)

@[simp] theorem layout_write_counter (saved : Locals) (accumulator limit : UInt64)
    (index next : Nat) (scratch : Locals) :
    ScalarStore.write (layout saved accumulator limit index scratch) (saved.length + 2)
        (UInt64.ofNat next) =
      some (layout saved accumulator limit next scratch) := by
  simpa [layout, List.append_assoc] using
    write_suffix saved ([accumulator, limit, UInt64.ofNat index] ++ scratch) 2
      (UInt64.ofNat next) (by simp)

end LeanExe.Core.NativeLoopLocals
