import TestSupport.Native.Common
import Verified.Examples.Arrays
import Verified.Examples.Loops
import Library.Lists.Word.Compiled
import Library.Sorting.Insertion.Compiled
import Library.Hashing.Crc.Compiled

/-!
The translations of the array, loop, list, sorting, and CRC examples, with `lx_mem` of `cap`
pages, and the theorems that `verified_compile` adds for them.  The translations of the array,
list, sorting, and CRC modules contain the functions that the `*_funcs` theorems list, and every
definition has its theorem `p.f.native`, among them the arrays example's `firstAbove`, which
returns two results.
`firstAbove_native_init` calls the loop example's `firstAbove`, which also returns two results,
from the state that `lx_init` leaves, and finds them in the result globals.  `crc_start` relates
the state that `lx_init` leaves in the CRC program's initial memory to the module's initial
store, with its memory capped at `cap` pages, which meets the premises that the functions'
theorems put on the store and the heap; the CRC tables are borrowed arrays there.  The
`*_runtime` theorems place the runtime's `alloc` and `release` in each translation, for
`alloc_native` and `release_native`.
-/

namespace TestSupport.Native.Examples

open Wasm LClight LeanExe.Native LeanExe.Pipeline TestSupport.Native

/-! ## Arrays -/

section Arrays

open Verified.Examples.Arrays

theorem arrays_funcs : compiled.translation.funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8] :=
  translate_funcs_eq compiled.translation_eq compiled.translation_funcs

example (A : Archi) (X : ExtSem) : NativeImpl compiled.sum.implements A X cap compiled.translation :=
  compiled.sum.native A X

example (A : Archi) (X : ExtSem) : NativeImpl compiled.dot.implements A X cap compiled.translation :=
  compiled.dot.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.count.implements A X cap compiled.translation :=
  compiled.count.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.firstAbove.implements A X cap compiled.translation :=
  compiled.firstAbove.native A X

example (A : Archi) (X : ExtSem) : NativeImpl compiled.at3.implements A X cap compiled.translation :=
  compiled.at3.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.sumBoth.implements A X cap compiled.translation :=
  compiled.sumBoth.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.larger.implements A X cap compiled.translation :=
  compiled.larger.native A X

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem arrays_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧
    0 ∈ compiled.translation.funcs ∧ 1 ∈ compiled.translation.funcs :=
  ⟨rfl, rfl, by rw [arrays_funcs]; decide, by rw [arrays_funcs]; decide⟩

end Arrays

/-! ## Two results -/

section Loops

open Verified.Examples.Loops

/-- From the state that `lx_init` leaves, `lxf_firstAbove` on `limit` and `n` returns with
`lx_status` 0, the result global `lx_r0_l` holding the first component of `firstAbove limit n`,
and `lx_r1_l` holding the word of its second. -/
theorem firstAbove_native_init (A : Archi) (X : ExtSem) (limit n : UInt64) :
    ∃ m1 fd t m' b0 b1,
      StoreRel (envOf compiled.translation compiled.module.globals.length cap)
        (nativeStore compiled.module cap) m1 ∧
      (funId 8, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      eval_funcall A X (globalenv compiled.translation.cprogram) m1 (.Internal fd)
        [.Vlong limit, .Vlong n] t m' .Vundef ∧
      StatusRel (envOf compiled.translation compiled.module.globals.length cap) m' 0 ∧
      Genv.find_symbol (globalenv compiled.translation.cprogram) (resId 0 .i64) = some b0 ∧
      Mem.load .Mint64 m' b0 0 = some (.Vlong (firstAbove limit n).1) ∧
      Genv.find_symbol (globalenv compiled.translation.cprogram) (resId 1 .i64) = some b1 ∧
      Mem.load .Mint64 m' b1 0 = some (.Vlong (cond (firstAbove limit n).2 1 0)) := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, hE, hG, hcap, hnres, hF⟩ :=
    start compiled.translation_eq A X
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := compiled.firstAbove.native A X
  obtain ⟨rfl, rfl⟩ := sig_of hsig (ps0 := [.i64, .i64]) (rs0 := [.i64, .i64]) rfl
  obtain ⟨hheap, -, -⟩ := compiled.initial
  obtain ⟨t, m', vres, final, hcall, -, hres⟩ := hnat _ hE hG hcap hnres hF
    (nativeStore compiled.module cap) _ [.i64 limit, .i64 n] (limit, n) (heapAt_caps hheap [cap])
    trivial (by rfl) Separate.nil (by rw [nativeStore_memoryCap]; decide)
    ⟨by simp, by simp [AllHas, VT.has]⟩ m1 hst hs
  have hge : (envOf compiled.translation compiled.module.globals.length cap).ge =
      globalenv compiled.translation.cprogram := rfl
  have hargs : argVals [.i64, .i64] [Value.i64 limit, .i64 n].reverse = [.Vlong limit, .Vlong n] :=
    rfl
  rw [hge, hargs] at hcall
  have h2 : 2 ≤ compiled.translation.nres := by
    rw [translate_nres compiled.translation_eq,
      translate_funcs_eq compiled.translation_eq compiled.translation_funcs]
    decide +kernel
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨habs, -⟩
  · obtain ⟨ws, hws, -, rfl, -, hin⟩ := hr
    have hv : vs.reverse =
        [Value.i64 (firstAbove limit n).1, .i64 (cond (firstAbove limit n).2 1 0)] := hown
    have hws' : ws = [.i64 (cond (firstAbove limit n).2 1 0), .i64 (firstAbove limit n).1] := by
      have : vs = ws := by simpa using hws
      subst this
      simpa using congrArg List.reverse hv
    subst hws'
    obtain ⟨v0, hv0, -, hl0⟩ := hin 0 (by decide)
    obtain ⟨v1, hv1, -, hl1⟩ := hin 1 (by decide)
    have e0 : v0 = .i64 (firstAbove limit n).1 := by simpa using hv0.symm
    have e1 : v1 = .i64 (cond (firstAbove limit n).2 1 0) := by simpa using hv1.symm
    subst e0 e1
    refine ⟨m1, fd, t, m', _, _, hst, hfd, hcall, hs', hge ▸ hE.res 0 (by omega) .i64 rfl, hl0,
      hge ▸ hE.res 1 (by omega) .i64 rfl, hl1⟩
  · cases habs

end Loops

/-! ## Lists -/

section Lists

open Library.Lists.Word

theorem lists_funcs : compiled.translation.funcs = [0, 1, 2, 3, 4, 5, 6, 7] :=
  translate_funcs_eq compiled.translation_eq compiled.translation_funcs

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.listSum.implements A X cap compiled.translation :=
  compiled.listSum.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.range.implements A X cap compiled.translation :=
  compiled.range.native A X

example (A : Archi) (X : ExtSem) : NativeImpl compiled.sum.implements A X cap compiled.translation :=
  compiled.sum.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.reverse.implements A X cap compiled.translation :=
  compiled.reverse.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.increment.implements A X cap compiled.translation :=
  compiled.increment.native A X

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem lists_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧
    0 ∈ compiled.translation.funcs ∧ 1 ∈ compiled.translation.funcs :=
  ⟨rfl, rfl, by rw [lists_funcs]; decide, by rw [lists_funcs]; decide⟩

end Lists

/-! ## Sorting -/

section Sorting

open Library.Sorting.Insertion

theorem sort_funcs : compiled.translation.funcs = [0, 1, 2] :=
  translate_funcs_eq compiled.translation_eq compiled.translation_funcs

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.sortInsert.implements A X cap compiled.translation :=
  compiled.sortInsert.native A X

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem sort_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧
    0 ∈ compiled.translation.funcs ∧ 1 ∈ compiled.translation.funcs :=
  ⟨rfl, rfl, by rw [sort_funcs]; decide, by rw [sort_funcs]; decide⟩

end Sorting

/-! ## CRC -/

section Crc

open Library.Hashing.Crc

theorem crc_funcs : compiled.translation.funcs = [0, 1, 2, 3, 4, 5, 6, 7] :=
  translate_funcs_eq compiled.translation_eq compiled.translation_funcs

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.updateWith.implements A X cap compiled.translation :=
  compiled.updateWith.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.crcWith.implements A X cap compiled.translation :=
  compiled.crcWith.native A X

example (A : Archi) (X : ExtSem) :
    Verified.NativeTablesImpl compiled.crc32.implements A X cap compiled.translation :=
  compiled.crc32.native A X

example (A : Archi) (X : ExtSem) :
    Verified.NativeTablesImpl compiled.crc32c.implements A X cap compiled.translation :=
  compiled.crc32c.native A X

example (A : Archi) (X : ExtSem) :
    Verified.NativeTablesImpl compiled.crc32Update.implements A X cap compiled.translation :=
  compiled.crc32Update.native A X

example (A : Archi) (X : ExtSem) :
    Verified.NativeTablesImpl compiled.crc32cUpdate.implements A X cap compiled.translation :=
  compiled.crc32cUpdate.native A X

set_option maxRecDepth 100000 in
/-- The state that `lx_init` leaves in the CRC program's initial memory: it is related to the
module's initial store, capped at `cap` pages, in which the allocator invariant holds and both
tables are borrowed arrays at their addresses. -/
theorem crc_start (A : Archi) (X : ExtSem) :
    ∃ m1, StoreRel (envOf compiled.translation compiled.module.globals.length cap)
        (nativeStore compiled.module cap) m1 ∧
      StatusRel (envOf compiled.translation compiled.module.globals.length cap) m1 0 ∧
      (Verified.initialHeap compiled.tables).At (nativeStore compiled.module cap) ∧
      (nativeStore compiled.module cap).memoryCap compiled.module 0 ≤ 65535 ∧
      ∀ k (hk : k < compiled.tables.length),
        (Verified.initialHeap compiled.tables).Borrowed (nativeStore compiled.module cap)
          (Verified.tableAddr compiled.tables k) compiled.tables[k] := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, -⟩ := start compiled.translation_eq A X
  obtain ⟨hheap, -, htables⟩ := compiled.initial
  exact ⟨m1, hst, hs, heapAt_caps hheap [cap], by rw [nativeStore_memoryCap]; decide,
    fun k hk => borrowed_caps (htables k hk) [cap]⟩

/-- The runtime's `alloc` and `release` are functions 0 and 1 of the module and of its
translation, so `alloc_native` and `release_native` apply to them. -/
theorem crc_runtime : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) ∧
    compiled.module.funcs[1]? = some (LeanExe.Runtime.releaseFunction 1) ∧
    0 ∈ compiled.translation.funcs ∧ 1 ∈ compiled.translation.funcs :=
  ⟨rfl, rfl, by rw [crc_funcs]; decide, by rw [crc_funcs]; decide⟩

end Crc

end TestSupport.Native.Examples
