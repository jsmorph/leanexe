import Verified.Correct

namespace Verified

open Wasm

theorem Prog.functions_prefix_lookup {S : List Sig} (prog : Prog S) (m : Module)
    {pool : Bytes.LiteralPool}
    (hPrefix : prog.functions (pool := pool) <+: m.funcs.drop 2) {k : Nat} (hk : k < S.length) :
    m.funcs[2 + k]? = (prog.functions (pool := pool))[k]? := by
  obtain ⟨suffix, hPrefix⟩ := hPrefix
  have h := congrArg (fun fs : List Function => fs[k]?) hPrefix
  have hLeft : (prog.functions (pool := pool) ++ suffix)[k]? =
      (prog.functions (pool := pool))[k]? :=
    List.getElem?_append_left (by simpa only [prog.functions_length pool] using hk)
  exact List.getElem?_drop.symm.trans (h.symm.trans hLeft)

theorem Prog.calls_prefix {S : List Sig} (prog : Prog S) (funs : Funs S)
    (hMeaning : prog.Meaning funs) (m : Module) (hm : Runtime m)
    {pool : Bytes.LiteralPool}
    (hPrefix : prog.functions (pool := pool) <+: m.funcs.drop 2)
    (hCovered : prog.Covered pool) :
    Calls m funs prog.flags (prog.boundsAt funs) (prog.fitsAt funs) pool :=
  prog.calls funs hMeaning m hm
    (fun _ hk => prog.functions_prefix_lookup m hPrefix hk) hCovered

theorem Prog.functions_prefix_cons {S : List Sig} (prog : Prog S) (f : Func S)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) :
    prog.functions (pool := pool) <+: (Prog.cons f prog).functions (pool := pool) :=
  ⟨[f.function (2 + S.length) pool], rfl⟩

theorem Prog.functions_prefix_consRec {S : List Sig} (prog : Prog S) (f : RecFunc S)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) :
    prog.functions (pool := pool) <+: (Prog.consRec f prog).functions (pool := pool) :=
  ⟨[f.function (2 + S.length) pool], rfl⟩

theorem Prog.functions_prefix_consTail {S : List Sig} (prog : Prog S) (f : TailFunc S)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) :
    prog.functions (pool := pool) <+: (Prog.consTail f prog).functions (pool := pool) :=
  ⟨[f.function (2 + S.length) pool], rfl⟩

theorem Prog.functions_prefix_compileWith {S : List Sig} (prog : Prog S)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper S tables.length))
    (pool : Bytes.LiteralPool := prog.literalPool (tablesEnd tables)) :
    prog.functions (pool := pool) <+: (compileWith prog tables wrappers pool).funcs.drop 2 := by
  refine ⟨prog.entries S.length ++ wrappers.mapIdx (fun j w =>
    wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex
      (2 + S.length + prog.depthFuns.length + j)), ?_⟩
  simp only [compileWith, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.append_assoc]

theorem Prog.calls_extension {S T : List Sig} (prog : Prog S) (larger : Prog T)
    (funs : Funs S) (hMeaning : prog.Meaning funs)
    {pool : Bytes.LiteralPool}
    (hPrefix : prog.functions (pool := pool) <+: larger.functions (pool := pool))
    (tables : List (Array UInt64)) (wrappers : List (Wrapper T tables.length))
    (hCovered : prog.Covered pool) :
    Calls (compileWith larger tables wrappers pool) funs prog.flags
      (prog.boundsAt funs) (prog.fitsAt funs) pool :=
  prog.calls_prefix funs hMeaning _ (compileWith_runtime larger tables wrappers pool)
    (hPrefix.trans (larger.functions_prefix_compileWith tables wrappers pool)) hCovered

#print axioms Prog.calls_prefix
#print axioms Prog.calls_extension

end Verified
