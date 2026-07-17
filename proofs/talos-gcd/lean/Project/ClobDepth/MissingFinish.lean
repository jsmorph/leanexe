import Project.ClobDepth.MissingBump

/-!
# Missing-price allocation finalization

This phase increments the allocation counter, records the allocated root,
writes the target array length, and initializes the copy cursor.
-/

namespace Project.ClobDepth.MissingFinish

open Wasm Project.Common Project.ClobDepth

def finishStore (st : Store Unit) (target length g2 : UInt64) : Store Unit :=
  { st with
    globals := { globals := st.globals.globals.set 2 (.i64 (g2 + 1)) }
    mem := st.mem.write64 target.toUInt32 length }

def finishFrame (base : Locals) (target : UInt64) : Locals :=
  { base with
    locals := (base.locals.set 14 (.i64 target)).set 15 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

macro "wp_run_finish" "(" hParams:term "," hLocals:term ","
    hValues:term "," hTarget:term "," hLength:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hTarget), ($hLength)])

set_option Elab.async false in
theorem missingAllocFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (target length g2 : UInt64)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hTarget : base.locals[25]? = some (.i64 target))
    (hLength : base.locals[13]? = some (.i64 length))
    (hGlobal2 : st.globals.globals[2]? = some (.i64 g2))
    (hTargetBound : target.toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q (finishStore st target length g2)
      (finishFrame base target) env) :
    wp «module» (Entry.missingAllocFinishProg ++ rest) Q st base env := by
  have hTarget' : base.locals[25] = .i64 target := by
    apply Option.some.inj
    calc
      some base.locals[25] = base.locals[25]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 target) := hTarget
  have hLength' : base.locals[13] = .i64 length := by
    apply Option.some.inj
    calc
      some base.locals[13] = base.locals[13]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 length) := hLength
  simp only [Entry.missingAllocFinishProg, List.cons_append,
    List.nil_append]
  wp_run_finish (hParams, hLocals, hValues, hTarget', hLength')
  simp only [hGlobal2]
  rw [if_neg (Nat.not_lt.mpr hTargetBound)]
  simpa only [finishStore, finishFrame, toUInt32_eq_ofNat] using hNext

end Project.ClobDepth.MissingFinish
