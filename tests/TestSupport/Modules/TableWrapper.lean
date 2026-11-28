module

public import Verified.Reflect.Command
public import Verified.Native
public import LeanExe.Dialect.ArrayLemmas

@[expose] public section

/-!
Tests of `Verified.ImplementsTables.mono` and `Verified.NativeTablesA.weaken` on wrappers over the
table `tbl` of one word.  `len` returns the number of elements of an array plus the table's word,
and `len_claims` adds the value of its result, which needs the size of the array below `2 ^ 32`, to
the postcondition of `compiled.len.trapFree`: the implication of `ImplementsTables.mono` receives
the representation, whose words bound the size.  `shift` adds the table's word to each element of
an array and may trap when the result's block does not fit, so the native theorem from
`compiled.shift.trapFree` has the precondition `Heap.Within`, which `shift_native` restates as
arithmetic on the pages of `lx_mem` through `NativeTablesA.weaken`.
-/

namespace TestSupport.Modules.TableWrapper

open LeanExe.Pipeline

/-- A table of one word. -/
def tbl : Array UInt64 := #[5]

/-- The number of elements of `xs` plus the first word of `t`. -/
def lenWith (t : Array UInt64) (xs : Array UInt64) : UInt64 :=
  xs.size.toUInt64 + t[(0 : UInt64).toNat]!

/-- `lenWith` over `tbl`. -/
def len (xs : Array UInt64) : UInt64 := lenWith tbl xs

/-- The elements of `xs`, each plus the first word of `t`. -/
def shiftWith (t : Array UInt64) (xs : Array UInt64) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]! + t[(0 : UInt64).toNat]!

/-- `shiftWith` over `tbl`. -/
def shift (xs : Array UInt64) : Array UInt64 := shiftWith tbl xs

verified_compile compiled := [lenWith, len, shiftWith, shift]

theorem len_toNat (xs : Array UInt64) (h : xs.size < 2 ^ 32) : (len xs).toNat = xs.size + 5 := by
  show (xs.size.toUInt64 + tbl[(0 : UInt64).toNat]!).toNat = _
  rw [show tbl[(0 : UInt64).toNat]! = 5 from rfl, UInt64.toNat_add, LeanExe.Dialect.size_toUInt64 xs
    (by omega)]
  simp only [UInt64.reduceToNat]
  omega

/-- The theorem of `len` without a trap, with the value of its result in the postcondition. -/
theorem len_claims :
    Verified.ImplementsTables false compiled.module 4 len [(4096, tbl)]
      (fun _ _ _ => True) (fun xs _ _ _ _ => (len xs).toNat = xs.size + 5) :=
  compiled.len.trapFree.mono (fun _ _ _ h => h) fun xs _ _ _ _ _ _ ⟨_, _, hxs⟩ _ =>
    len_toNat xs (by have := hxs.values.size_lt_memory32; omega)

/-- The C function of `shift` computes it without a trap when `top` and the bound of `shift` fit
in the pages of `lx_mem`. -/
theorem shift_native (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 5, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[5]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      Verified.NativeTablesA A X LeanExe.Native.nativeCap compiled.module compiled.translation ps
        rs fd false shift [(4096, tbl)]
        (fun xs heap _ =>
          heap.top.toNat + compiled.shift.bound xs ≤ 65536 * LeanExe.Native.nativeCap)
        (fun xs heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.shift.bound xs) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := Verified.ImplementsTables.nativeImpl (A := A) (X := X)
    compiled.shift.trapFree compiled.translation_eq
    (LeanExe.Native.translate_mem_funcs compiled.translation_eq compiled.translation_funcs
      (by decide))
  refine ⟨fd, ps, rs, hfd, hsig, Verified.NativeTablesA.weaken h ?_⟩
  intro E store heap xs m hcap hst hpre
  show heap.top.toNat + compiled.shift.bound xs ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  exact hpre

#print axioms Verified.ImplementsTables.mono
#print axioms Verified.NativeTablesA.weaken
#print axioms len_claims
#print axioms shift_native

end TestSupport.Modules.TableWrapper
