import Verified.ProgramAppend
import Verified.ModuleComposition

namespace Verified

theorem FVar.index_appendLeft {S T : List Sig} {g : Sig} (f : FVar S g) :
    (f.appendLeft T).index = f.index := by
  induction f with
  | here => rfl
  | there f ih => exact congrArg (· + 1) ih

theorem FVar.index_appendRight {S T : List Sig} {g : Sig} (f : FVar T g) :
    (f.appendRight S).index = S.length + f.index := by
  induction S with
  | nil => simp only [FVar.appendRight, List.length_nil, Nat.zero_add]
  | cons _ S ih =>
    simp only [FVar.appendRight, FVar.index, List.length_cons]
    omega

theorem FVar.callIndex_appendLeft {S T : List Sig} {g : Sig} (f : FVar S g) :
    (f.appendLeft T).callIndex = f.callIndex + T.length := by
  have bound := f.index_lt
  simp only [FVar.callIndex, FVar.index_appendLeft, List.length_append]
  omega

theorem FVar.callIndex_appendRight {S T : List Sig} {g : Sig} (f : FVar T g) :
    (f.appendRight S).callIndex = f.callIndex := by
  have bound := f.index_lt
  simp only [FVar.callIndex, FVar.index_appendRight, List.length_append]
  omega

theorem Prog.functions_cast {S T : List Sig} (h : S = T) (prog : Prog S)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) :
    (cast (congrArg Prog h) prog).functions (pool := pool) = prog.functions (pool := pool) := by
  cases h
  rfl

theorem Prog.functions_prefix_append {S T : List Sig} (source : Prog S) (target : Prog T)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) :
    target.functions (pool := pool) <+: (source.append target).functions (pool := pool) := by
  induction source with
  | nil => exact ⟨[], List.append_nil _⟩
  | cons f rest ih =>
    have hFunctions : (Prog.append (.cons f rest) target).functions (pool := pool) =
        (Prog.cons (f.renameFuns (fun v => v.appendLeft T))
          (rest.append target)).functions (pool := pool) :=
      Prog.functions_cast (pool := pool)
        (congrArg (fun g => g :: (_ ++ T)) (f.sig_renameFuns (fun v => v.appendLeft T))) _
    exact hFunctions.symm ▸ ih.trans ⟨[_], rfl⟩
  | consRec f rest ih =>
    simp only [Prog.append, Prog.functions]
    exact ih.trans ⟨[_], rfl⟩
  | consTail f rest ih =>
    have hFunctions : (Prog.append (.consTail f rest) target).functions (pool := pool) =
        (Prog.consTail (f.renameFuns (fun v => v.appendLeft T))
          (rest.append target)).functions (pool := pool) :=
      Prog.functions_cast (pool := pool)
        (congrArg (fun g => g :: (_ ++ T)) (f.sig_renameFuns (fun v => v.appendLeft T))) _
    exact hFunctions.symm ▸ ih.trans ⟨[_], rfl⟩

theorem Prog.calls_append {S T : List Sig} (source : Prog S) (target : Prog T)
    (other : Funs T) (meaning : target.Meaning other)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper (S ++ T) tables.length))
    (pool : Bytes.LiteralPool := (source.append target).literalPool (tablesEnd tables))
    (hCovered : target.Covered pool) :
    Calls (compileWith (source.append target) tables wrappers pool) other target.flags
      (target.boundsAt other) (target.fitsAt other) pool :=
  target.calls_extension (source.append target) other meaning
    (source.functions_prefix_append target pool) tables wrappers hCovered

end Verified
