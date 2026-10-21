import Verified.Correct

namespace Verified

open Wasm

theorem Prog.functions_prefix_lookup {S : List Sig} (prog : Prog S) (m : Module)
    (hPrefix : prog.functions <+: m.funcs.drop 2) {k : Nat} (hk : k < S.length) :
    m.funcs[2 + k]? = prog.functions[k]? := by
  obtain ⟨suffix, hPrefix⟩ := hPrefix
  have h := congrArg (fun fs : List Function => fs[k]?) hPrefix
  have hLeft : (prog.functions ++ suffix)[k]? = prog.functions[k]? :=
    List.getElem?_append_left (by simpa only [prog.functions_length] using hk)
  exact List.getElem?_drop.symm.trans (h.symm.trans hLeft)

theorem Prog.calls_prefix {S : List Sig} (prog : Prog S) (funs : Funs S)
    (hMeaning : prog.Meaning funs) (m : Module) (hm : Runtime m)
    (hPrefix : prog.functions <+: m.funcs.drop 2) :
    Calls m funs prog.flags (prog.boundsAt funs) (prog.fitsAt funs) :=
  prog.calls funs hMeaning m hm fun _ hk => prog.functions_prefix_lookup m hPrefix hk

theorem Prog.functions_prefix_cons {S : List Sig} (prog : Prog S) (f : Func S) :
    prog.functions <+: (Prog.cons f prog).functions :=
  ⟨[f.function (2 + S.length)], rfl⟩

theorem Prog.functions_prefix_consRec {S : List Sig} (prog : Prog S) (f : RecFunc S) :
    prog.functions <+: (Prog.consRec f prog).functions :=
  ⟨[f.function (2 + S.length)], rfl⟩

theorem Prog.functions_prefix_consTail {S : List Sig} (prog : Prog S) (f : TailFunc S) :
    prog.functions <+: (Prog.consTail f prog).functions :=
  ⟨[f.function (2 + S.length)], rfl⟩

theorem Prog.functions_prefix_compileWith {S : List Sig} (prog : Prog S)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper S tables.length)) :
    prog.functions <+: (compileWith prog tables wrappers).funcs.drop 2 := by
  refine ⟨prog.entries S.length ++ wrappers.mapIdx (fun j w =>
    wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex
      (2 + S.length + prog.depthFuns.length + j)), ?_⟩
  simp only [compileWith, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.append_assoc]

theorem Prog.calls_extension {S T : List Sig} (prog : Prog S) (larger : Prog T)
    (funs : Funs S) (hMeaning : prog.Meaning funs)
    (hPrefix : prog.functions <+: larger.functions)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper T tables.length)) :
    Calls (compileWith larger tables wrappers) funs prog.flags
      (prog.boundsAt funs) (prog.fitsAt funs) :=
  prog.calls_prefix funs hMeaning _ (compileWith_runtime larger tables wrappers)
    (hPrefix.trans (larger.functions_prefix_compileWith tables wrappers))

#print axioms Prog.calls_prefix
#print axioms Prog.calls_extension

end Verified
