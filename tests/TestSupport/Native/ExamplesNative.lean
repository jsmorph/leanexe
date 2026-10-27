import TestSupport.Native.Common
import Verified.Examples.Arrays
import Library.Lists.Word.Compiled
import Library.Sorting.Insertion.Compiled
import Library.Hashing.Crc.Compiled

/-!
The theorems of the translated array, list, sorting, and CRC examples (milestone M3), with
`lx_mem` of `cap` pages.  For each module, the translation exists and contains the functions
that `funcs` lists: every function but `firstAbove` of the arrays example, which returns two
results.  Each `*_native` theorem carries the verified compiler's theorem of one function to
the C function of its translation, as `NativeImpl` or `NativeTablesImpl` states.  The `*_start`
theorems relate the state that `lx_init` leaves in the program's initial memory to the module's
initial store, with its memory capped at `cap` pages, which meets the premises that the
functions' theorems put on the store and the heap; the CRC tables are borrowed arrays there.
The `*_runtime` theorems place the runtime's `alloc` and `release` in each translation, for
`alloc_native` and `release_native`.
-/

namespace TestSupport.Native.Examples

open Wasm LClight LeanExe.Native LeanExe.Pipeline TestSupport.Native

/-! ## Arrays -/

section Arrays

open Verified.Examples.Arrays

def arraysT : Translation := (translate cap compiled.module).get (by decide +kernel)

theorem arraysT_eq : translate cap compiled.module = some arraysT := (Option.some_get _).symm

attribute [irreducible] arraysT

theorem arrays_funcs : arraysT.funcs = [0, 1, 2, 3, 4, 6, 7, 8] := by decide +kernel

theorem sum_native (A : Archi) (X : ExtSem) : NativeImpl compiled.sum.implements A X cap arraysT :=
  ImplementsA.nativeImpl _ arraysT_eq (by decide +kernel)

theorem dot_native (A : Archi) (X : ExtSem) : NativeImpl compiled.dot.implements A X cap arraysT :=
  ImplementsA.nativeImpl _ arraysT_eq (by decide +kernel)

theorem count_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.count.implements A X cap arraysT :=
  ImplementsA.nativeImpl _ arraysT_eq (by decide +kernel)

theorem at3_native (A : Archi) (X : ExtSem) : NativeImpl compiled.at3.implements A X cap arraysT :=
  ImplementsA.nativeImpl _ arraysT_eq (by decide +kernel)

theorem sumBoth_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.sumBoth.implements A X cap arraysT :=
  ImplementsA.nativeImpl _ arraysT_eq (by decide +kernel)

theorem larger_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.larger.implements A X cap arraysT :=
  ImplementsA.nativeImpl _ arraysT_eq (by decide +kernel)

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem arrays_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧ 0 ∈ arraysT.funcs ∧
    1 ∈ arraysT.funcs :=
  ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

end Arrays

/-! ## Lists -/

section Lists

open Library.Lists.Word

def listsT : Translation := (translate cap compiled.module).get (by decide +kernel)

theorem listsT_eq : translate cap compiled.module = some listsT := (Option.some_get _).symm

attribute [irreducible] listsT

theorem lists_funcs : listsT.funcs = [0, 1, 2, 3, 4, 5, 6, 7] := by decide +kernel

theorem listSum_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.listSum.implements A X cap listsT :=
  ImplementsA.nativeImpl _ listsT_eq (by decide +kernel)

theorem range_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.range.implements A X cap listsT :=
  ImplementsA.nativeImpl _ listsT_eq (by decide +kernel)

theorem listsSum_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.sum.implements A X cap listsT :=
  ImplementsA.nativeImpl _ listsT_eq (by decide +kernel)

theorem reverse_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.reverse.implements A X cap listsT :=
  ImplementsA.nativeImpl _ listsT_eq (by decide +kernel)

theorem increment_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.increment.implements A X cap listsT :=
  ImplementsA.nativeImpl _ listsT_eq (by decide +kernel)

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem lists_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧ 0 ∈ listsT.funcs ∧
    1 ∈ listsT.funcs :=
  ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

end Lists

/-! ## Sorting -/

section Sorting

open Library.Sorting.Insertion

def sortT : Translation := (translate cap compiled.module).get (by decide +kernel)

theorem sortT_eq : translate cap compiled.module = some sortT := (Option.some_get _).symm

attribute [irreducible] sortT

theorem sort_funcs : sortT.funcs = [0, 1, 2] := by decide +kernel

theorem sortInsert_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.sortInsert.implements A X cap sortT :=
  ImplementsA.nativeImpl _ sortT_eq (by decide +kernel)

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem sort_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧ 0 ∈ sortT.funcs ∧
    1 ∈ sortT.funcs :=
  ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

end Sorting

/-! ## CRC -/

section Crc

open Library.Hashing.Crc

def crcT : Translation := (translate cap compiled.module).get (by decide +kernel)

theorem crcT_eq : translate cap compiled.module = some crcT := (Option.some_get _).symm

attribute [irreducible] crcT

theorem crc_funcs : crcT.funcs = [0, 1, 2, 3, 4, 5, 6, 7] := by decide +kernel

theorem updateWith_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.updateWith.implements A X cap crcT :=
  ImplementsA.nativeImpl _ crcT_eq (by decide +kernel)

theorem crcWith_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.crcWith.implements A X cap crcT :=
  ImplementsA.nativeImpl _ crcT_eq (by decide +kernel)

theorem crc32_native (A : Archi) (X : ExtSem) :
    NativeTablesImpl compiled.crc32.implements A X cap crcT :=
  ImplementsTables.nativeImpl _ crcT_eq (by decide +kernel)

theorem crc32c_native (A : Archi) (X : ExtSem) :
    NativeTablesImpl compiled.crc32c.implements A X cap crcT :=
  ImplementsTables.nativeImpl _ crcT_eq (by decide +kernel)

theorem crc32Update_native (A : Archi) (X : ExtSem) :
    NativeTablesImpl compiled.crc32Update.implements A X cap crcT :=
  ImplementsTables.nativeImpl _ crcT_eq (by decide +kernel)

theorem crc32cUpdate_native (A : Archi) (X : ExtSem) :
    NativeTablesImpl compiled.crc32cUpdate.implements A X cap crcT :=
  ImplementsTables.nativeImpl _ crcT_eq (by decide +kernel)

/-- The state that `lx_init` leaves in the CRC program's initial memory: it is related to the
module's initial store, capped at `cap` pages, in which the allocator invariant holds and both
tables are borrowed arrays at their addresses. -/
theorem crc_start (A : Archi) (X : ExtSem) :
    ∃ m1, StoreRel (envOf crcT compiled.module.globals.length cap)
        (nativeStore compiled.module cap) m1 ∧
      StatusRel (envOf crcT compiled.module.globals.length cap) m1 0 ∧
      (Verified.initialHeap compiled.tables).At (nativeStore compiled.module cap) ∧
      (nativeStore compiled.module cap).memoryCap compiled.module 0 ≤ 65535 ∧
      ∀ k (hk : k < compiled.tables.length),
        (Verified.initialHeap compiled.tables).Borrowed (nativeStore compiled.module cap)
          (Verified.tableAddr compiled.tables k) compiled.tables[k] := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, -⟩ := start crcT_eq A X
  obtain ⟨hheap, -, htables⟩ := compiled.initial
  exact ⟨m1, hst, hs, heapAt_caps hheap [cap], by rw [nativeStore_memoryCap]; decide,
    fun k hk => borrowed_caps (htables k hk) [cap]⟩

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem crc_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧ 0 ∈ crcT.funcs ∧
    1 ∈ crcT.funcs :=
  ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

end Crc

end TestSupport.Native.Examples
