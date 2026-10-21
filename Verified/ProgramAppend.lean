import Verified.TailRelocation

namespace Verified

def Prog.append {S T : List Sig} (source : Prog S) (target : Prog T) : Prog (S ++ T) :=
  match source with
  | .nil => target
  | .cons f rest =>
    cast (congrArg (fun g => Prog (g :: (_ ++ T)))
      (f.sig_renameFuns (fun v => v.appendLeft T)))
      (.cons (f.renameFuns (fun v => v.appendLeft T)) (rest.append target))
  | .consRec f rest =>
    .consRec (f.renameFuns (fun v => v.appendLeft T)) (rest.append target)
  | .consTail f rest =>
    cast (congrArg (fun g => Prog (g :: (_ ++ T)))
      (f.sig_renameFuns (fun v => v.appendLeft T)))
      (.consTail (f.renameFuns (fun v => v.appendLeft T)) (rest.append target))

theorem Prog.Meaning.cast {S T : List Sig} (h : S = T) (prog : Prog S) (funs : Funs S)
    (meaning : prog.Meaning funs) :
    (cast (congrArg Prog h) prog).Meaning (cast (congrArg Funs h) funs) := by
  cases h
  exact meaning

theorem Funs.cast_cons {S : List Sig} {params : List Ty} {result : Ty} {modes : List Mode}
    {a b c d : Bool} (h : Sig.mk params result a modes b = Sig.mk params result c modes d)
    (f : Env params → result.denote) (rest : Funs S) :
    cast (congrArg Funs (congrArg (fun g => g :: S) h)) (Funs.cons (g := ⟨params, result, a, modes, b⟩) f rest) =
      Funs.cons (g := ⟨params, result, c, modes, d⟩) f rest := by
  have ha : a = c := congrArg Sig.aborts h
  have hb : b = d := congrArg Sig.depth h
  cases ha
  cases hb
  rfl

theorem Prog.Meaning.append {S T : List Sig} {source : Prog S} {target : Prog T}
    {funs : Funs S} {other : Funs T} (meaning : source.Meaning funs)
    (targetMeaning : target.Meaning other) :
    (source.append target).Meaning (funs.append other) := by
  induction meaning with
  | nil => exact targetMeaning
  | @cons S f rest funs hm ih =>
    let renamed := f.renameFuns (fun v => v.appendLeft T)
    have hBody : renamed.denote (funs.append other) = f.denote funs := by
      funext env
      exact f.denote_renameFuns _ funs _ (fun v env => Funs.get_appendLeft funs other v env) env
    have hNew := Prog.Meaning.cons (f := renamed) ih
    change (Prog.cons renamed (rest.append target)).Meaning
      (.cons (renamed.denote (funs.append other)) (funs.append other)) at hNew
    rw [hBody] at hNew
    have hCast := Prog.Meaning.cast
      (congrArg (fun g => g :: (S ++ T)) (f.sig_renameFuns (fun v => v.appendLeft T))) _ _ hNew
    have hFuns := Funs.cast_cons (params := f.params) (result := f.result) (modes := f.modes)
      (a := renamed.aborts) (b := renamed.depth) (c := f.aborts) (d := f.depth)
      (f.sig_renameFuns (fun v => v.appendLeft T)) (f.denote funs) (funs.append other)
    have hCast' := Eq.mp (congrArg (fun values => (Prog.append (.cons f rest) target).Meaning values) hFuns) hCast
    exact hCast'
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
  | @consTail S f rest funs M hm decreases fixed ih =>
    let renamed := f.renameFuns (fun v => v.appendLeft T)
    have hDecrease : renamed.Decreases (funs.append other) :=
      f.decreases_renameFuns _ funs _ (fun v env => Funs.get_appendLeft funs other v env) decreases
    have hFixed : ∀ env, M env = (renamed.body.denote (funs.append other) env).elim M id := by
      intro env
      change M env = ((f.body.renameFuns _).denote (funs.append other) env).elim M id
      rw [TailBody.denote_renameFuns _ funs _ (fun v env => Funs.get_appendLeft funs other v env)]
      exact fixed env
    have hNew := Prog.Meaning.consTail (f := renamed) M ih hDecrease hFixed
    have hCast := Prog.Meaning.cast
      (congrArg (fun g => g :: (S ++ T)) (f.sig_renameFuns (fun v => v.appendLeft T))) _ _ hNew
    have hFuns := Funs.cast_cons (params := f.params) (result := f.result) (modes := f.modes)
      (a := renamed.aborts) (b := renamed.depth) (c := f.aborts) (d := f.depth)
      (f.sig_renameFuns (fun v => v.appendLeft T)) M (funs.append other)
    have hCast' := Eq.mp (congrArg (fun values => (Prog.append (.consTail f rest) target).Meaning values) hFuns) hCast
    exact hCast'

end Verified
