import Verified.ProgramAppend
import Verified.LiteralCoverage

namespace Verified

theorem TailBody.literals_renameFuns {S T : List Sig} (renameFuncs : FunRenaming S T)
    (body : TailBody S params result Γ) :
    (body.renameFuns renameFuncs).literals = body.literals := by
  induction body <;>
    simp_all only [TailBody.renameFuns, TailBody.literals_ret, TailBody.literals_next, TailBody.literals_ite, TailBody.literals_letE, TailBody.literals_letPair, TailBody.literals_treeCase,
      Expr.literals_renameFuns]

theorem Prog.literals_cast {S T : List Sig} (types : S = T) (prog : Prog S) :
    (cast (congrArg Prog types) prog).literals = prog.literals := by
  cases types
  rfl

theorem Prog.literals_cast_eq {S T : List Sig} (types : S = T)
    (transport : Prog S = Prog T) (prog : Prog S) :
    (cast transport prog).literals = prog.literals := by
  cases types
  rfl

theorem Prog.literals_append {S T : List Sig} (source : Prog S) (target : Prog T) :
    (source.append target).literals = target.literals ++ source.literals := by
  induction source with
  | nil => simp only [Prog.append, Prog.literals, List.append_nil]
  | @cons S func rest ih =>
    let renameFuncs : FunRenaming S (S ++ T) := fun v => v.appendLeft T
    have hCast : (Prog.append (.cons func rest) target).literals =
        (Prog.cons (func.renameFuns renameFuncs) (rest.append target)).literals :=
      Prog.literals_cast_eq
        (congrArg (fun g => g :: (S ++ T)) (func.sig_renameFuns renameFuncs)) _ _
    have hBody : (func.renameFuns renameFuncs).body.literals = func.body.literals :=
      func.body.literals_renameFuns renameFuncs
    rw [hCast]
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
  | @consTail S func rest ih =>
    let renameFuncs : FunRenaming S (S ++ T) := fun v => v.appendLeft T
    have hCast : (Prog.append (.consTail func rest) target).literals =
        (Prog.consTail (func.renameFuns renameFuncs) (rest.append target)).literals :=
      Prog.literals_cast_eq
        (congrArg (fun g => g :: (S ++ T)) (func.sig_renameFuns renameFuncs)) _ _
    have hBody : (func.renameFuns renameFuncs).body.literals = func.body.literals :=
      func.body.literals_renameFuns renameFuncs
    rw [hCast]
    change (rest.append target).literals ++ (func.renameFuns renameFuncs).body.literals = _
    rw [ih, hBody]
    exact List.append_assoc _ _ _

theorem Prog.covered_append {S T : List Sig} (source : Prog S) (target : Prog T)
    (pool : Bytes.LiteralPool) :
    (source.append target).Covered pool ↔ source.Covered pool ∧ target.Covered pool := by
  rw [Prog.Covered, Prog.literals_append, List.append_subset]
  exact and_comm

end Verified
