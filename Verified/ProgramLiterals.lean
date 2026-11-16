import Verified.ProgramAppend
import Verified.LiteralCoverage

namespace Verified

theorem TailBody.literals_renameFuns {S T : List Sig} (renameFuncs : FunRenaming S T)
    (body : TailBody S params result Γ) :
    (body.renameFuns renameFuncs).literals = body.literals := by
  induction body <;>
    simp_all only [TailBody.renameFuns, TailBody.literals_ret, TailBody.literals_next, TailBody.literals_ite, TailBody.literals_letE, TailBody.literals_letPair, TailBody.literals_treeCase,
      Expr.literals_renameFuns]

theorem Prog.literals_append {S T : List Sig} (source : Prog S) (target : Prog T) :
    (source.append target).literals = target.literals ++ source.literals := by
  induction source with
  | nil => simp only [Prog.append, Prog.literals, List.append_nil]
  | @cons S func _ _ _ rest ih =>
    let renameFuncs : FunRenaming S (S ++ T) := fun v => v.appendLeft T
    have hBody : (func.renameFuns renameFuncs).body.literals = func.body.literals :=
      func.body.literals_renameFuns renameFuncs
    change (rest.append target).literals ++ (func.renameFuns renameFuncs).body.literals = _
    rw [ih, hBody]
    exact List.append_assoc _ _ _
  | @consRec S func rest ih =>
    let renameFuncs : FunRenaming S (S ++ T) := fun v => v.appendLeft T
    have hBody : (func.renameFuns renameFuncs).body.literals = func.body.literals :=
      func.body.literals_renameFuns (renameFuncs.lift func.sig)
    change (rest.append target).literals ++ (func.renameFuns renameFuncs).body.literals = _
    rw [ih, hBody]
    exact List.append_assoc _ _ _
  | @consTail S func _ _ _ rest ih =>
    let renameFuncs : FunRenaming S (S ++ T) := fun v => v.appendLeft T
    have hBody : (func.renameFuns renameFuncs).body.literals = func.body.literals :=
      func.body.literals_renameFuns renameFuncs
    change (rest.append target).literals ++ (func.renameFuns renameFuncs).body.literals = _
    rw [ih, hBody]
    exact List.append_assoc _ _ _

theorem Prog.covered_append {S T : List Sig} (source : Prog S) (target : Prog T)
    (pool : Bytes.LiteralPool) :
    (source.append target).Covered pool ↔ source.Covered pool ∧ target.Covered pool := by
  rw [Prog.Covered, Prog.literals_append, List.append_subset]
  exact and_comm

end Verified
