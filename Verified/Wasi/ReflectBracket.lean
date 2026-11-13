import Verified.Wasi.ReflectLemmas

/-! The reflection of `LeanExe.Wasi.withOpen`.  `reflect` writes `withOpen` as the canonical
expansion that its docstring shows: the open, a test of the errno, the error continuation, and the
body between the binding of the handle and the close.  The equations below relate the expansion's
meaning to `withOpen`, one for a result with a value and one for a `Unit` result, given the
relations of the two continuations in the contexts that the expansion gives them. -/

namespace Verified.Wasi.Reflect

open LeanExe.Wasi LeanExe.Pipeline

variable {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty}

theorem withOpen_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (dir dirflags : Var context .word) (path : Var context .bytes)
    (oflags rightsBase rightsInheriting fdflags : Var context .word)
    (onError' : Command pureSigs effectSigs (.elem (.prod .word .word) :: context) (.value type))
    (body' : Command pureSigs effectSigs (.word :: .elem (.prod .word .word) :: context)
      (.value type))
    (dirValue : Handle) (dirflagsValue : UInt64) (pathValue : LeanExe.Bytes)
    (oflagsValue rightsBaseValue rightsInheritingValue fdflagsValue : UInt64)
    (onError : UInt64 → Action α) (body : Handle → Action α) (flatten : α → type.denote)
    (hDir : env.get dir = dirValue.fd) (hDirflags : env.get dirflags = dirflagsValue)
    (hPath : env.get path = pathValue) (hOflags : env.get oflags = oflagsValue)
    (hRightsBase : env.get rightsBase = rightsBaseValue)
    (hRightsInheriting : env.get rightsInheriting = rightsInheritingValue)
    (hFdflags : env.get fdflags = fdflagsValue)
    (hOnError : ∀ opened : UInt64 × UInt64, Action.Rel (fun native flat => flat = flatten native)
      (onError opened.1) (onError'.denote pureFuns effectFuns (.cons opened env)))
    (hBody : ∀ (opened : UInt64 × UInt64) (handle : Handle),
      Action.Rel (fun native flat => flat = flatten native) (body handle)
        (body'.denote pureFuns effectFuns (.cons (Flat.flat handle) (.cons opened env)))) :
    Action.Rel (fun native flat => flat = flatten native)
      (withOpen dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue
        fdflagsValue onError body)
      ((Command.bind
        (Command.sys Call.pathOpen (.flat 1 false)
          [dir, dirflags, oflags, rightsBase, rightsInheriting, fdflags] [path])
        (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onError'
          (Command.bind (Command.ret (.proj .here (.snd .here)))
            (Command.bind body'
              (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
                (Command.ret (.var (.there .here)))))))).denote pureFuns effectFuns env) := by
  obtain ⟨dirValue⟩ := dirValue
  change env.get dir = dirValue at hDir
  subst hDir hDirflags hPath hOflags hRightsBase hRightsInheriting hFdflags
  refine .sys Call.pathOpen _ fun reply => ?_
  show Action.Rel _ (if reply.errno != 0 then _ else _) (bif reply.errno != 0 then _ else _)
  by_cases failed : (reply.errno != 0) = true
  · rw [ite_cond_eq_true _ _ (eq_true failed), failed]
    exact hOnError (reply.errno, reply.word 0)
  · have succeeded : (reply.errno != 0) = false := by simpa using failed
    rw [ite_cond_eq_false _ _ (eq_false failed), succeeded]
    show Action.Rel _ _ (Action.bind (body'.denote pureFuns effectFuns
      (.cons (reply.word 0) (.cons (reply.errno, reply.word 0) env))) _)
    refine .bind (hBody (reply.errno, reply.word 0) ⟨reply.word 0⟩) fun native flat same => ?_
    exact .sys Call.fdClose _ fun _ => .pure same

theorem withOpen_rel_unit (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (dir dirflags : Var context .word) (path : Var context .bytes)
    (oflags rightsBase rightsInheriting fdflags : Var context .word)
    (onError' : Command pureSigs effectSigs (.elem (.prod .word .word) :: context) .unit)
    (body' : Command pureSigs effectSigs (.word :: .elem (.prod .word .word) :: context) .unit)
    (dirValue : Handle) (dirflagsValue : UInt64) (pathValue : LeanExe.Bytes)
    (oflagsValue rightsBaseValue rightsInheritingValue fdflagsValue : UInt64)
    (onError : UInt64 → Action α) (body : Handle → Action α) (flatten : α → Unit)
    (hDir : env.get dir = dirValue.fd) (hDirflags : env.get dirflags = dirflagsValue)
    (hPath : env.get path = pathValue) (hOflags : env.get oflags = oflagsValue)
    (hRightsBase : env.get rightsBase = rightsBaseValue)
    (hRightsInheriting : env.get rightsInheriting = rightsInheritingValue)
    (hFdflags : env.get fdflags = fdflagsValue)
    (hOnError : ∀ opened : UInt64 × UInt64, Action.Rel (fun native flat => flat = flatten native)
      (onError opened.1) (onError'.denote pureFuns effectFuns (.cons opened env)))
    (hBody : ∀ (opened : UInt64 × UInt64) (handle : Handle),
      Action.Rel (fun native flat => flat = flatten native) (body handle)
        (body'.denote pureFuns effectFuns (.cons (Flat.flat handle) (.cons opened env)))) :
    Action.Rel (fun native flat => flat = flatten native)
      (withOpen dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue
        fdflagsValue onError body)
      ((Command.bind
        (Command.sys Call.pathOpen (.flat 1 false)
          [dir, dirflags, oflags, rightsBase, rightsInheriting, fdflags] [path])
        (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onError'
          (Command.bind (Command.ret (.proj .here (.snd .here)))
            (Command.bind body'
              (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.here] [])
                Command.unit))))).denote pureFuns effectFuns env) := by
  obtain ⟨dirValue⟩ := dirValue
  change env.get dir = dirValue at hDir
  subst hDir hDirflags hPath hOflags hRightsBase hRightsInheriting hFdflags
  refine .sys Call.pathOpen _ fun reply => ?_
  show Action.Rel _ (if reply.errno != 0 then _ else _) (bif reply.errno != 0 then _ else _)
  by_cases failed : (reply.errno != 0) = true
  · rw [ite_cond_eq_true _ _ (eq_true failed), failed]
    exact hOnError (reply.errno, reply.word 0)
  · have succeeded : (reply.errno != 0) = false := by simpa using failed
    rw [ite_cond_eq_false _ _ (eq_false failed), succeeded]
    show Action.Rel _ _ (Action.bind (body'.denote pureFuns effectFuns
      (.cons (reply.word 0) (.cons (reply.errno, reply.word 0) env))) _)
    refine .bind (hBody (reply.errno, reply.word 0) ⟨reply.word 0⟩) fun native flat same => ?_
    exact .sys Call.fdClose _ fun _ => .pure rfl

end Verified.Wasi.Reflect
