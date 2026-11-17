import Verified.TailRelocation

namespace Verified

def Prog.append {S T : List Sig} (source : Prog S) (target : Prog T) : Prog (S ++ T) :=
  match source with
  | .nil => target
  | .cons f aborts depth h rest =>
    .cons (f.renameFuns (fun v => v.appendLeft T)) aborts depth
      ((f.sig_renameFuns (fun v => v.appendLeft T)).trans h) (rest.append target)
  | .consRec f rest =>
    .consRec (f.renameFuns (fun v => v.appendLeft T)) (rest.append target)
  | .consTail f aborts depth h rest =>
    .consTail (f.renameFuns (fun v => v.appendLeft T)) aborts depth
      ((f.sig_renameFuns (fun v => v.appendLeft T)).trans h) (rest.append target)

theorem Prog.Meaning.append {S T : List Sig} {source : Prog S} {target : Prog T}
    {funs : Funs S} {other : Funs T} (meaning : source.Meaning funs)
    (targetMeaning : target.Meaning other) :
    (source.append target).Meaning (funs.append other) := by
  induction meaning with
  | nil => exact targetMeaning
  | @cons S f aborts depth h rest funs hm ih =>
    let renamed := f.renameFuns (fun v => v.appendLeft T)
    have hBody : renamed.denote (funs.append other) = f.denote funs := by
      funext env
      exact f.denote_renameFuns _ funs _ (fun v env => Funs.get_appendLeft funs other v env) env
    have hNew := Prog.Meaning.cons (f := renamed) (aborts := aborts) (depth := depth)
      (h := (f.sig_renameFuns (fun v => v.appendLeft T)).trans h) ih
    rw [hBody] at hNew
    exact hNew
  | @consRec S f rest funs M hm fixed ih =>
    let ρ : FunRenaming S (S ++ T) := fun v => v.appendLeft T
    change (Prog.consRec (f.renameFuns (fun v => v.appendLeft T)) (rest.append target)).Meaning
      (.cons M (funs.append other))
    apply Prog.Meaning.consRec (f := f.renameFuns (fun v => v.appendLeft T)) M ih
    intro env
    change Env f.params at env
    change M env = (f.body.renameFuns (ρ.lift f.sig)).denote
      (.cons (g := f.sig) M (funs.append other)) env
    rw [fixed env]
    exact (f.body.denote_renameFuns (ρ.lift f.sig)
      (.cons (g := f.sig) M funs) (.cons (g := f.sig) M (funs.append other))
      (fun v env => by cases v with
        | here => rfl
        | there v => exact Funs.get_appendLeft funs other v env) env).symm
  | @consTail S f aborts depth h rest funs M hm decreases fixed ih =>
    let renamed := f.renameFuns (fun v => v.appendLeft T)
    have hDecrease : renamed.Decreases (funs.append other) :=
      f.decreases_renameFuns _ funs _ (fun v env => Funs.get_appendLeft funs other v env) decreases
    have hFixed : ∀ env, M env = (renamed.body.denote (funs.append other) env).elim M id := by
      intro env
      change M env = ((f.body.renameFuns _).denote (funs.append other) env).elim M id
      rw [TailBody.denote_renameFuns _ funs _ (fun v env => Funs.get_appendLeft funs other v env)]
      exact fixed env
    exact Prog.Meaning.consTail (f := renamed) (aborts := aborts) (depth := depth)
      (h := (f.sig_renameFuns (fun v => v.appendLeft T)).trans h) M ih hDecrease hFixed

end Verified
