import Verified.Wasi.ReflectLemmas

/-! The reflection of `LeanExe.Wasi.withOpen`.  `reflect` writes `withOpen` as the canonical
expansion that its docstring shows: the open, a test of the errno, the error continuation followed
by the pair of its result and the word 0, and the body between the binding of the handle and the
close, followed by the pair of the body's result and the close's errno.  `withOpen_rel` relates
the expansion's meaning to `withOpen` for any last commands that return such pairs, given the
relations of the two continuations in the contexts that the expansion gives them.
`withOpen_rel_mk` and `withOpen_rel_pair` apply it to the last commands that `reflect` writes:
`ret` of `mk` when the continuations' result is an element, and `ret` of `pair` otherwise. -/

namespace Verified.Wasi.Reflect

open LeanExe.Wasi LeanExe.Pipeline

variable {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty}

private theorem rel_pure_of_eq {relation : α → β → Prop} {left : α} {right : Action β} {value : β}
    (same : right = .pure value) (related : relation left value) :
    Action.Rel relation (.pure left) right := by
  subst same
  exact .pure related

/-- The expansion of `withOpen` whose last commands, `errorLast` after the error continuation and
`closeLast` after the close, return `merge` of the continuation's result and 0 or the close's
errno. -/
theorem withOpen_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (dir dirflags : Var context .word) (path : Var context .bytes)
    (oflags rightsBase rightsInheriting fdflags : Var context .word)
    (onError' : Command pureSigs effectSigs (.elem (.prod .word .word) :: context) (.value type))
    (body' : Command pureSigs effectSigs (.word :: .elem (.prod .word .word) :: context)
      (.value type))
    (errorLast : Command pureSigs effectSigs (type :: .elem (.prod .word .word) :: context)
      (.value result))
    (closeLast : Command pureSigs effectSigs
      (.word :: type :: .word :: .elem (.prod .word .word) :: context) (.value result))
    (merge : type.denote → UInt64 → result.denote)
    (hErrorLast : ∀ value opened,
      errorLast.denote pureFuns effectFuns (.cons value (.cons opened env)) =
        .pure (merge value 0))
    (hCloseLast : ∀ errno value handle opened,
      closeLast.denote pureFuns effectFuns
          (.cons errno (.cons value (.cons handle (.cons opened env)))) =
        .pure (merge value errno))
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
    Action.Rel (fun native flat => flat = merge (flatten native.1) native.2)
      (withOpen dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue
        fdflagsValue onError body)
      ((Command.bind
        (Command.sys Call.pathOpen (.flat 1 false)
          [dir, dirflags, oflags, rightsBase, rightsInheriting, fdflags] [path])
        (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0))
          (Command.bind onError' errorLast)
          (Command.bind (Command.ret (.proj .here (.snd .here)))
            (Command.bind body'
              (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
                closeLast))))).denote pureFuns effectFuns env) := by
  obtain ⟨dirValue⟩ := dirValue
  change env.get dir = dirValue at hDir
  subst hDir hDirflags hPath hOflags hRightsBase hRightsInheriting hFdflags
  refine .sys Call.pathOpen _ fun reply => ?_
  show Action.Rel _ (if reply.errno != 0 then _ else _) (bif reply.errno != 0 then _ else _)
  by_cases failed : (reply.errno != 0) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true failed), failed]
    show Action.Rel _ (Action.bind (onError reply.errno) _)
      (Action.bind (onError'.denote pureFuns effectFuns (.cons (reply.errno, reply.word 0) env)) _)
    refine .bind (hOnError (reply.errno, reply.word 0)) fun native flat same => ?_
    show Action.Rel _ (.pure (native, 0))
      (errorLast.denote pureFuns effectFuns (.cons flat (.cons (reply.errno, reply.word 0) env)))
    subst same
    exact rel_pure_of_eq (hErrorLast _ _) rfl
  · have succeeded : (reply.errno != 0) = false := by simpa using failed
    rw [ite_eq_right_of_eq_false _ _ (eq_false failed), succeeded]
    show Action.Rel _ _ (Action.bind (body'.denote pureFuns effectFuns
      (.cons (reply.word 0) (.cons (reply.errno, reply.word 0) env))) _)
    refine .bind (hBody (reply.errno, reply.word 0) ⟨reply.word 0⟩) fun native flat same => ?_
    refine .sys Call.fdClose _ fun closed => ?_
    show Action.Rel _ (.pure (native, closed.errno))
      (closeLast.denote pureFuns effectFuns (.cons closed.errno
        (.cons flat (.cons (reply.word 0) (.cons (reply.errno, reply.word 0) env)))))
    subst same
    exact rel_pure_of_eq (hCloseLast _ _ _ _) rfl

/-- `withOpen_rel` for a result that is an element `element`, whose pairs are `mk`. -/
theorem withOpen_rel_mk (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (dir dirflags : Var context .word) (path : Var context .bytes)
    (oflags rightsBase rightsInheriting fdflags : Var context .word)
    (onError' : Command pureSigs effectSigs (.elem (.prod .word .word) :: context)
      (.value (.elem element)))
    (body' : Command pureSigs effectSigs (.word :: .elem (.prod .word .word) :: context)
      (.value (.elem element)))
    (dirValue : Handle) (dirflagsValue : UInt64) (pathValue : LeanExe.Bytes)
    (oflagsValue rightsBaseValue rightsInheritingValue fdflagsValue : UInt64)
    (onError : UInt64 → Action α) (body : Handle → Action α) (flatten : α → element.denote)
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
    Action.Rel (fun native flat => flat = (flatten native.1, native.2))
      (withOpen dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue
        fdflagsValue onError body)
      ((Command.bind
        (Command.sys Call.pathOpen (.flat 1 false)
          [dir, dirflags, oflags, rightsBase, rightsInheriting, fdflags] [path])
        (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0))
          (Command.bind onError' (Command.ret (.mk (.var .here) (.word 0))))
          (Command.bind (Command.ret (.proj .here (.snd .here)))
            (Command.bind body'
              (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
                (Command.ret (.mk (.var (.there .here)) (.var .here)))))))).denote
        pureFuns effectFuns env) :=
  withOpen_rel pureFuns effectFuns env dir dirflags path oflags rightsBase rightsInheriting fdflags
    onError' body' (.ret (.mk (.var .here) (.word 0)))
    (.ret (.mk (.var (.there .here)) (.var .here))) (fun value errno => (value, errno))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue fdflagsValue
    onError body flatten hDir hDirflags hPath hOflags hRightsBase hRightsInheriting hFdflags
    hOnError hBody

/-- `withOpen_rel` for a result of a type `type` that is no element, whose pairs are `pair`. -/
theorem withOpen_rel_pair (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
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
    Action.Rel (fun native flat => flat = (flatten native.1, native.2))
      (withOpen dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue
        fdflagsValue onError body)
      ((Command.bind
        (Command.sys Call.pathOpen (.flat 1 false)
          [dir, dirflags, oflags, rightsBase, rightsInheriting, fdflags] [path])
        (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0))
          (Command.bind onError' (Command.ret (.pair (.var .here) (.word 0))))
          (Command.bind (Command.ret (.proj .here (.snd .here)))
            (Command.bind body'
              (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
                (Command.ret (.pair (.var (.there .here)) (.var .here)))))))).denote
        pureFuns effectFuns env) :=
  withOpen_rel pureFuns effectFuns env dir dirflags path oflags rightsBase rightsInheriting fdflags
    onError' body' (.ret (.pair (.var .here) (.word 0)))
    (.ret (.pair (.var (.there .here)) (.var .here))) (fun value errno => (value, errno))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    dirValue dirflagsValue pathValue oflagsValue rightsBaseValue rightsInheritingValue fdflagsValue
    onError body flatten hDir hDirflags hPath hOflags hRightsBase hRightsInheriting hFdflags
    hOnError hBody

end Verified.Wasi.Reflect
