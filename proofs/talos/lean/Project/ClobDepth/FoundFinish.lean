import Project.ClobDepth.MissingFinish

/-!
# Found-price allocation finalization

This phase increments the allocation counter, records the allocated root,
writes the unchanged level count as the target array length, and initializes
the copy cursor.  The store and frame updates equal the missing-price
finalization, so the theorem reuses its definitions.
-/

namespace Project.ClobDepth.FoundFinish

open Wasm Project.Common Project.ClobDepth

set_option maxRecDepth 1048576


set_option Elab.async false in
theorem foundAllocFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (target length g2 : UInt64)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hTarget : base.locals[25]? = some (.i64 target))
    (hLength : base.locals[12]? = some (.i64 length))
    (hGlobal2 : st.globals.globals[2]? = some (.i64 g2))
    (hTargetBound : target.toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q
      (MissingFinish.finishStore st target length g2)
      (MissingFinish.finishFrame base target) env) :
    wp «module» (Entry.foundAllocFinishProg ++ rest) Q st base env := by
  have hTarget' : base.locals[25] = .i64 target := getElem_of_some hTarget
  have hLength' : base.locals[12] = .i64 length := getElem_of_some hLength
  simp only [Entry.foundAllocFinishProg, List.cons_append,
    List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hTarget', hLength']
  simp only [hGlobal2]
  rw [if_neg (Nat.not_lt.mpr hTargetBound)]
  simpa only [MissingFinish.finishStore, MissingFinish.finishFrame,
    toUInt32_eq_ofNat] using hNext

end Project.ClobDepth.FoundFinish
