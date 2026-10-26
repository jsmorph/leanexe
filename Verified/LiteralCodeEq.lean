import Verified.Compile
import Verified.LiteralCoverage

namespace Verified

theorem Expr.code_empty_pool (expr : Expr S Γ t) (address h : Nat)
    (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    expr.code (pool := ⟨address, []⟩) h slots base live =
      expr.code (pool := Bytes.LiteralPool.empty) h slots base live := by
  induction expr generalizing h slots base live <;>
    simp_all only [Expr.code, Bytes.LiteralPool.empty, Bytes.literalOffset]

theorem Expr.code_eq_of_no_literals (expr : Expr S Γ t) (first second : Bytes.LiteralPool)
    (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool)
    (hNone : expr.literals = []) :
    expr.code (pool := first) h slots base live =
      expr.code (pool := second) h slots base live := by
  revert hNone
  induction expr generalizing h slots base live <;> intro hNone
  case bytesLiteral bytes =>
    cases bytes with
    | nil => rfl
    | cons byte bytes => simp [Expr.literals] at hNone
  all_goals
    simp_all only [Expr.literals, List.append_eq_nil_iff, literals_args_eq_nil, Expr.code]

theorem bodyFunction_empty_pool {S : List Sig} {params : List Ty} {result : Ty}
    (modes : List Mode) (body : Expr S params result) (depth : Bool) (typeIdx address : Nat) :
    bodyFunction modes body depth typeIdx ⟨address, []⟩ =
      bodyFunction modes body depth typeIdx Bytes.LiteralPool.empty := by
  simp only [bodyFunction, Expr.code_empty_pool]

theorem TailBody.code_empty_pool {S : List Sig} {params Γ : List Ty} {result : Ty}
    (body : TailBody S params result Γ) (modes : List Mode)
    (h stateBase resultBase : Nat) (slots : List Slot) (base exitLabel nextLabel address : Nat) :
    body.code modes h stateBase resultBase slots base exitLabel nextLabel ⟨address, []⟩ =
      body.code modes h stateBase resultBase slots base exitLabel nextLabel
        Bytes.LiteralPool.empty := by
  simp only [TailBody.code, Expr.code_empty_pool]

theorem Prog.functions_empty_pool (prog : Prog S) (address : Nat) :
    prog.functions (pool := ⟨address, []⟩) = prog.functions (pool := Bytes.LiteralPool.empty) := by
  induction prog with
  | nil => rfl
  | cons func rest ih =>
    simp only [Prog.functions, ih, Func.function, bodyFunction_empty_pool]
  | consRec func rest ih =>
    simp only [Prog.functions, ih, RecFunc.function, bodyFunction_empty_pool]
  | consTail func rest ih =>
    simp only [Prog.functions, ih, TailFunc.function, TailBody.code_empty_pool]

theorem compileWith_eq_empty_of_no_literals (prog : Prog S) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) (hNone : prog.literals = []) :
    compileWith prog tables wrappers =
      compileWith prog tables wrappers ⟨tablesEnd tables, []⟩ := by
  have hPool : prog.literalPool (tablesEnd tables) = ⟨tablesEnd tables, []⟩ := by
    simp only [Prog.literalPool, hNone, List.eraseDups_nil]
  change compileWith prog tables wrappers (prog.literalPool (tablesEnd tables)) = _
  rw [hPool]

theorem compileWith_empty_pool (prog : Prog S) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) :
    compileWith prog tables wrappers ⟨tablesEnd tables, []⟩ =
      let n := 2 + S.length + prog.depthFuns.length
      let types := [wordToWord, wordToNone] ++ prog.types ++ prog.entryTypes ++
        wrappers.map Wrapper.type
      { funcs := [LeanExe.Runtime.allocFunction 0, LeanExe.Runtime.releaseFunction 1] ++
          prog.functions Bytes.LiteralPool.empty ++ prog.entries S.length ++
          wrappers.mapIdx fun j w => wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
            w.params w.result w.depth w.callee.callIndex (n + j)
        exports := [{ name := "alloc", funcIdx := 0 }, { name := "release", funcIdx := 1 }] ++
          prog.exports S.length ++ wrappers.mapIdx fun j w => { name := w.name, funcIdx := n + j }
        memory := some {
          pagesMin := UInt32.ofNat (max 16 ((tablesEnd tables + 65535) / 65536))
          pagesMax := some 65535
          data := tableSegments tables }
        globals := runtimeGlobals (UInt64.ofNat (tablesEnd tables))
        types
        gcTypes := types.map fun type => { comp := .func type }
        globalExports := [("allocCount", 2), ("freeCount", 3)]
        memoryExports := [("memory", 0)] } := by
  have hAligned : tablesEnd tables % 8 = 0 := by simp [tablesEnd, Nat.add_mod, Nat.mul_mod]
  simp only [compileWith, Bytes.LiteralPool.top_empty _ hAligned,
    Bytes.LiteralPool.segments_empty, List.append_nil, Prog.functions_empty_pool]

end Verified
