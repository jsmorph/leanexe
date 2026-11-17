import LeanExe.Wasi.CallTable
import LeanExe.Wasi.ReadAll
import LeanExe.Wasi.RelatedExec
import LeanExe.Wasi.RelatedPrefix

/-! The discipline of `withOpen` over traces.  `WellBracketed stack trace stack'` reads a trace
from left to right with a stack of descriptor numbers, the descriptors of the open brackets with
the innermost first.  A `path_open` event that returns errno 0 pushes the number it returns, an
`fd_close` event pops the top of the stack, which must be its argument, an `fd_renumber` event
breaks the discipline, and every other `sys` event takes, at each `.handle` position, 3 or a number
on the stack; read, write, and exit events leave the stack alone.  The call of every `sys` event
must be one of the descriptions of `Call.table`, which `tools/wasi-calls.py` generates from the
witx, so its `.handle` positions are the descriptor parameters of the witx: the arguments of
`handle` parameters and of the handle fields of `subscriptions` parameters.  A `path_open` event
takes its `dir` argument at a `.handle` position whether or not it succeeds.  The stack holds
numbers, so a descriptor that a closed bracket held and a later open returns again counts as open
in the later bracket.

`Action.Handles stack action post` states that every run of `action` from `stack` keeps the
discipline and that a normal return with a value leaves a stack that satisfies `post`.
`Action.Handles.exec_run` and `Action.Handles.prefix_run` derive `WellBracketed` for the `Exec` and
`Prefix` runs of such an action, and `Action.BracketRuns` states the result for a program's runs
from no open bracket.  `WellBracketed.descriptors` reads the stack as the open descriptors of the
trace for a host that never returns from `path_open` a number that is open, as Wasmtime 44 asserts
of every new descriptor, and `Action.BracketRuns.exec_descriptors` and
`Action.BracketRuns.prefix_descriptors` state the consequence for a program's runs.  "Open" is a
property of the trace: descriptors 0 to 3 are open before the first event, a `path_open` event
that returns errno 0 opens the number it returns, and an `fd_close` event closes its argument
whatever it returns.  Descriptor 3 is the preopened directory when the host is given one; without
it, 3 is open only by this definition. -/

namespace LeanExe.Wasi

/-- The words of the arguments of the handle fields among `fields`, in order: each field takes the
next argument. -/
def fieldHandles : List Field → List Arg → List UInt64
  | field :: fields, arg :: args =>
    if field.source = .handle then arg.value :: fieldHandles fields args
    else fieldHandles fields args
  | _, _ => []

/-- The words of the arguments that a parameter takes at its `.handle` positions: the argument of
a `handle` parameter, and the arguments of the handle fields of a `subscriptions` parameter. -/
def Param.handleWords : Param → List Arg → List UInt64
  | .handle, args => (args.head?.map Arg.value).toList
  | .subscriptions records, args => fieldHandles (argFields records) args
  | .word32, _ | .word64, _ | .enum32 _, _ | .input, _ | .output, _ | .result32, _
  | .result64, _ | .reported .., _ | .flags32 _, _ | .flags64 _, _ | .record .., _
  | .iovec _, _ => []

/-- The words of the arguments at the `.handle` positions of `params`, in order: each parameter
takes the next `argCount` arguments. -/
def handleArgs : List Param → List Arg → List UInt64
  | [], _ => []
  | param :: params, args =>
    param.handleWords args ++ handleArgs params (args.drop param.argCount)

/-- Whether a call event of one of the generated descriptions keeps the discipline from `stack`:
an `fd_close` closes the top of the stack, no `fd_renumber` occurs, and every other call takes 3
or a number on the stack at each `.handle` position. -/
def callDiscipline (stack : List UInt64) (call : Call) (args : List Arg) : Bool :=
  if call.name = "fd_close" then
    match stack, args with
    | top :: _, [.word fd] => fd == top
    | _, _ => false
  else if call.name = "fd_renumber" then false
  else (handleArgs call.params args).all fun fd => fd == 3 || stack.contains fd

/-- Whether a call event keeps the discipline from `stack`: its call is one of the descriptions
of `Call.table`, which `tools/wasi-calls.py` generates from the witx, so that its `.handle`
positions are the descriptor parameters of the witx, and it meets `callDiscipline`. -/
def callAllowed (stack : List UInt64) (call : Call) (args : List Arg) : Bool :=
  Call.table.contains call && callDiscipline stack call args

/-- The stack after a call event: an `fd_close` pops the top, a `path_open` that returns errno 0
pushes the number it returns, and every other call leaves the stack. -/
def callStack (stack : List UInt64) (call : Call) (reply : Transfer (List Bytes)) :
    List UInt64 :=
  if call.name = "fd_close" then stack.tail
  else if call.name = "path_open" then
    match reply with
    | .returned errno outputs =>
      if errno = 0 then (⟨0, outputs⟩ : Reply).word 0 :: stack else stack
    | .trapped _ _ => stack
  else stack

/-- The stack after one event, or `none` when the event breaks the discipline. -/
def bracketStep (stack : List UInt64) : Event → Option (List UInt64)
  | .sys call args reply =>
    if callAllowed stack call args then some (callStack stack call reply) else none
  | _ => some stack

/-- The stack after a trace, or `none` when an event breaks the discipline. -/
def bracketRun : List UInt64 → List Event → Option (List UInt64)
  | stack, [] => some stack
  | stack, event :: trace => (bracketStep stack event).bind fun next => bracketRun next trace

/-- `trace` keeps the discipline of `withOpen` from the open brackets `stack` and leaves the open
brackets `stack'`. -/
def WellBracketed (stack : List UInt64) (trace : List Event) (stack' : List UInt64) : Prop :=
  bracketRun stack trace = some stack'

theorem bracketRun_append (stack : List UInt64) (first second : List Event) :
    bracketRun stack (first ++ second) =
      (bracketRun stack first).bind fun middle => bracketRun middle second := by
  induction first generalizing stack with
  | nil => rfl
  | cons event first ih =>
    simp only [List.cons_append, bracketRun]
    cases bracketStep stack event with
    | none => rfl
    | some next => exact ih next

theorem bracketStep_sys {stack : List UInt64} {call : Call} {args : List Arg}
    {reply : Transfer (List Bytes)} (allowed : callAllowed stack call args = true) :
    bracketStep stack (.sys call args reply) = some (callStack stack call reply) := by
  simp [bracketStep, allowed]

theorem WellBracketed.nil (stack : List UInt64) : WellBracketed stack [] stack := rfl

theorem WellBracketed.append {stack middle stack' : List UInt64} {first second : List Event}
    (hFirst : WellBracketed stack first middle) (hSecond : WellBracketed middle second stack') :
    WellBracketed stack (first ++ second) stack' := by
  unfold WellBracketed at *
  rw [bracketRun_append, hFirst]
  exact hSecond

theorem WellBracketed.cons {stack next stack' : List UInt64} {event : Event} {trace : List Event}
    (hStep : bracketStep stack event = some next) (hTrace : WellBracketed next trace stack') :
    WellBracketed stack (event :: trace) stack' := by
  unfold WellBracketed bracketRun
  rw [hStep]
  exact hTrace

theorem WellBracketed.single {stack next : List UInt64} {event : Event}
    (hStep : bracketStep stack event = some next) : WellBracketed stack [event] next :=
  .cons hStep (.nil next)

/-- The outputs of a reply have the sizes that the call gives for some sizes of its reported
regions, as `Host.sys_bound` requires of every host. -/
def ReplyFits (call : Call) (args : List Arg) (outputs : List Bytes) : Prop :=
  ∃ sizes, outputs.map (·.data.size) = call.outputSizes sizes args

/-- Every run of `action` from the open brackets `stack` keeps the discipline of `withOpen`, and a
normal return with `value` leaves open brackets that satisfy `post value`.  A loop's step returns
to the stack it starts from. -/
def Action.Handles :
    {α : Type} → List UInt64 → Action α → (α → List UInt64 → Prop) → Prop
  | _, stack, .pure value, post => post value stack
  | _, stack, .read _ next, post => ∀ reply, Action.Handles stack (next reply) post
  | _, stack, .write _ _ next, post => ∀ reply, Action.Handles stack (next reply) post
  | _, _, .exit _, _ => True
  | _, stack, .loop _ _ _ step next, post =>
    (∀ index state, Action.Handles stack (step index state) fun _ after => after = stack) ∧
      ∀ state, Action.Handles stack (next state) post
  | _, stack, .sys call args next, post =>
    (call.reject args ≠ 0 → Action.Handles stack (next ⟨call.reject args, []⟩) post) ∧
      (call.reject args = 0 → callAllowed stack call args = true ∧
        ∀ errno outputs, ReplyFits call args outputs →
          Action.Handles (callStack stack call (.returned errno outputs))
            (next (sysReply errno outputs)) post)

namespace Action.Handles

theorem mono {stack : List UInt64} {action : Action α} {post other : α → List UInt64 → Prop}
    (h : Action.Handles stack action post) (weaken : ∀ value after, post value after →
      other value after) : Action.Handles stack action other := by
  induction action generalizing stack with
  | pure value => exact weaken _ _ h
  | read capacity next ih => exact fun reply => ih reply (h reply) weaken
  | write output bytes next ih => exact fun reply => ih reply (h reply) weaken
  | exit code => trivial
  | loop count state test step next _ ihNext =>
    exact ⟨h.1, fun state => ihNext state (h.2 state) weaken⟩
  | sys call args next ih =>
    refine ⟨fun hReject => ih _ (h.1 hReject) weaken, fun hFits => ⟨(h.2 hFits).1, ?_⟩⟩
    exact fun errno outputs fits => ih _ ((h.2 hFits).2 errno outputs fits) weaken

theorem bind_iff {stack : List UInt64} {action : Action α} {next : α → Action β}
    {post : β → List UInt64 → Prop} :
    Action.Handles stack (Action.bind action next) post ↔
      Action.Handles stack action fun value after => Action.Handles after (next value) post := by
  induction action generalizing stack with
  | pure value => exact Iff.rfl
  | read capacity continuation ih => exact forall_congr' fun reply => ih reply
  | write output bytes continuation ih => exact forall_congr' fun reply => ih reply
  | exit code => exact Iff.rfl
  | loop count state test step continuation _ ihNext =>
    exact and_congr Iff.rfl (forall_congr' fun state => ihNext state)
  | sys call args continuation ih =>
    refine and_congr (imp_congr_right fun _ => ih _) (imp_congr_right fun _ => ?_)
    exact and_congr Iff.rfl (forall_congr' fun errno => forall_congr' fun outputs =>
      imp_congr_right fun _ => ih _)

theorem resumeLoop {stack : List UInt64} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {post : α → List UInt64 → Prop}
    (hStep : ∀ index state, Action.Handles stack (step index state) fun _ after => after = stack)
    (hNext : ∀ state, Action.Handles stack (next state) post) (remaining : Nat) :
    ∀ index state, Action.Handles stack (LeanExe.Wasi.resumeLoop test step next remaining index
      state) post := by
  induction remaining with
  | zero => intro index state; exact hNext state
  | succ remaining ih =>
    intro index state
    simp only [LeanExe.Wasi.resumeLoop]
    split
    · refine bind_iff.mpr ((hStep _ _).mono ?_)
      intro value after same
      subst same
      exact ih _ value
    · exact hNext state

/-- A run of a loop whose steps keep the discipline and return to `stack`, and whose
continuation keeps it with `post`. -/
private theorem loopExec {World : Type} {host : Host World} {stack : List UInt64}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {post : α → List UInt64 → Prop}
    (hStep : ∀ index state world trace outcome final,
      Exec host (step index state) world trace outcome final →
        ∃ after, WellBracketed stack trace after ∧
          ∀ value, outcome = .returned value → after = stack)
    (hNext : ∀ state world trace outcome final,
      Exec host (next state) world trace outcome final →
        ∃ after, WellBracketed stack trace after ∧ ∀ value, outcome = .returned value →
          post value after)
    (remaining : Nat) : ∀ {index state world trace outcome final},
      LoopExec host remaining index state test step next world trace outcome final →
        ∃ after, WellBracketed stack trace after ∧
          ∀ value, outcome = .returned value → post value after := by
  induction remaining with
  | zero =>
    intro index state world trace outcome final hRun
    cases hRun with | zero hRun => exact hNext _ _ _ _ _ hRun
  | succ remaining ih =>
    intro index state world trace outcome final hRun
    cases hRun with
    | stop _ hRun => exact hNext _ _ _ _ _ hRun
    | next _ hFirst hRest =>
      obtain ⟨middle, hTrace, hReturn⟩ := hStep _ _ _ _ _ _ hFirst
      obtain ⟨after, hRestTrace, hPost⟩ := ih hRest
      rw [hReturn _ rfl] at hTrace
      exact ⟨after, hTrace.append hRestTrace, hPost⟩
    | exit _ hFirst =>
      obtain ⟨after, hTrace, _⟩ := hStep _ _ _ _ _ _ hFirst
      exact ⟨after, hTrace, fun _ h => nomatch h⟩
    | trap _ hFirst =>
      obtain ⟨after, hTrace, _⟩ := hStep _ _ _ _ _ _ hFirst
      exact ⟨after, hTrace, fun _ h => nomatch h⟩

/-- Every `Exec` run of an action that keeps the discipline is well bracketed, and a normal
return leaves a stack that satisfies the action's `post`. -/
theorem exec_run {World : Type} {host : Host World} (action : Action α) :
    ∀ {stack : List UInt64} {post : α → List UInt64 → Prop} {world trace outcome final},
      Action.Handles stack action post → Exec host action world trace outcome final →
        ∃ after, WellBracketed stack trace after ∧
          ∀ value, outcome = .returned value → post value after := by
  induction action with
  | pure value =>
    intro stack post world trace outcome final h hRun
    cases hRun
    exact ⟨stack, .nil stack, fun _ same => by cases same; exact h⟩
  | read capacity next ih =>
    intro stack post world trace outcome final h hRun
    cases hRun with
    | read_reject _ hRun => exact ih _ (h _) hRun
    | read_return _ _ hRun =>
      obtain ⟨after, hTrace, hPost⟩ := ih _ (h _) hRun
      exact ⟨after, .cons rfl hTrace, hPost⟩
    | read_trap _ _ => exact ⟨stack, .single rfl, fun _ h => nomatch h⟩
  | write output bytes next ih =>
    intro stack post world trace outcome final h hRun
    cases hRun with
    | write_return _ hRun =>
      obtain ⟨after, hTrace, hPost⟩ := ih _ (h _) hRun
      exact ⟨after, .cons rfl hTrace, hPost⟩
    | write_trap _ => exact ⟨stack, .single rfl, fun _ h => nomatch h⟩
  | exit code =>
    intro stack post world trace outcome final h hRun
    cases hRun with
    | exit _ => exact ⟨stack, .single rfl, fun _ h => nomatch h⟩
    | exitTrap _ => exact ⟨stack, .single rfl, fun _ h => nomatch h⟩
  | loop count state test step next ihStep ihNext =>
    intro stack post world trace outcome final h hRun
    cases hRun with
    | loop hRun =>
      exact loopExec (fun index state _ _ _ _ hStep => ihStep index state (h.1 index state) hStep)
        (fun state _ _ _ _ hNext => ihNext state (h.2 state) hNext) count.toNat hRun
  | sys call args next ih =>
    intro stack post world trace outcome final h hRun
    cases hRun with
    | sys_reject hFits hRun => exact ih _ (h.1 hFits) hRun
    | sys_return hFits hHost hRun =>
      obtain ⟨allowed, rest⟩ := h.2 hFits
      obtain ⟨after, hTrace, hPost⟩ :=
        ih _ (rest _ _ ⟨_, (host.sys_bound hHost).1⟩) hRun
      exact ⟨after, .cons (bracketStep_sys allowed) hTrace, hPost⟩
    | sys_trap hFits _ =>
      exact ⟨_, .single (bracketStep_sys (h.2 hFits).1),
        fun _ h => nomatch h⟩

/-- Every `Prefix` run of an action that keeps the discipline is well bracketed and leaves a
residual action that keeps it from the stack it reaches. -/
theorem prefix_run {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} (hPrefix : Prefix host action world trace residual after) :
    ∀ {stack : List UInt64} {post : α → List UInt64 → Prop},
      Action.Handles stack action post →
        ∃ reached, WellBracketed stack trace reached ∧
          Action.Handles reached residual post := by
  induction hPrefix with
  | refl => intro stack post h; exact ⟨stack, .nil stack, h⟩
  | read_reject _ => intro stack post h; exact ⟨stack, .nil stack, h _⟩
  | read_return _ _ => intro stack post h; exact ⟨stack, .single rfl, h _⟩
  | write_return _ => intro stack post h; exact ⟨stack, .single rfl, h _⟩
  | loop =>
    intro stack post h
    exact ⟨stack, .nil stack, resumeLoop h.1 h.2 _ 0 _⟩
  | bind _ ih =>
    intro stack post h
    obtain ⟨reached, hTrace, hResidual⟩ := ih (bind_iff.mp h)
    exact ⟨reached, hTrace, bind_iff.mpr hResidual⟩
  | trans _ _ ihFirst ihRest =>
    intro stack post h
    obtain ⟨middle, hFirst, hMiddle⟩ := ihFirst h
    obtain ⟨reached, hRest, hResidual⟩ := ihRest hMiddle
    exact ⟨reached, hFirst.append hRest, hResidual⟩
  | sys_reject hFits => intro stack post h; exact ⟨stack, .nil stack, h.1 hFits⟩
  | sys_return hFits hHost =>
    intro stack post h
    obtain ⟨allowed, rest⟩ := h.2 hFits
    exact ⟨_, .single (bracketStep_sys allowed),
      rest _ _ ⟨_, (host.sys_bound hHost).1⟩⟩

end Action.Handles

/-- Every run of `action` from no open bracket keeps the discipline of `withOpen`: an `Exec` run is
well bracketed from the empty stack and returns normally only to the empty stack, and a `Prefix`
run, which describes a compiled run that ends in a guest resource trap, is well bracketed from the
empty stack. -/
def Action.BracketRuns (action : Action α) : Prop :=
  (∀ {World : Type} (host : Host World) world trace outcome final,
    Exec host action world trace outcome final →
      ∃ stack, WellBracketed [] trace stack ∧
        ∀ value, outcome = .returned value → stack = []) ∧
  (∀ {World : Type} (host : Host World) world trace residual after,
    Prefix host action world trace residual after → ∃ stack, WellBracketed [] trace stack)

theorem Action.Handles.bracketRuns {action : Action α}
    (h : Action.Handles [] action fun _ after => after = []) : action.BracketRuns := by
  refine ⟨fun host world trace outcome final hRun => ?_,
    fun host world trace residual after hPrefix => ?_⟩
  · exact Action.Handles.exec_run action h hRun
  · obtain ⟨stack, hTrace, _⟩ := Action.Handles.prefix_run hPrefix h
    exact ⟨stack, hTrace⟩

/-- The runs of an action related to one whose runs keep the discipline keep it: related actions
make the same events. -/
theorem Action.BracketRuns.of_rel {relation : α → β → Prop} {left : Action α}
    {right : Action β}
    (related : Action.Rel relation left right) (h : right.BracketRuns) : left.BracketRuns := by
  refine ⟨fun host world trace outcome final hRun => ?_,
    fun host world trace residual after hPrefix => ?_⟩
  · obtain ⟨result, hRight, values⟩ := related.exec _ _ _ _ hRun
    obtain ⟨stack, hTrace, hReturn⟩ := h.1 host _ _ _ _ hRight
    refine ⟨stack, hTrace, fun value same => ?_⟩
    subst same
    cases values with
    | returned _ => exact hReturn _ rfl
  · obtain ⟨target, hRight, _⟩ := related.transportPrefix hPrefix
    exact h.2 host _ _ _ _ hRight

/-! ## Open descriptors -/

/-- The descriptor that a `path_open` reply gives: the little-endian value of its first output. -/
def openedDescriptor (outputs : List Bytes) : UInt64 := (⟨0, outputs⟩ : Reply).word 0

/-- The descriptors open after an event, from the open descriptors `opened`: a `path_open` event
that returns errno 0 opens the descriptor it returns, an `fd_close` event closes its argument
whatever it returns, and other events open and close nothing. -/
def openStep (opened : List UInt64) : Event → List UInt64
  | .sys call args reply =>
    if call.name = "path_open" then
      match reply with
      | .returned errno outputs => if errno = 0 then openedDescriptor outputs :: opened else opened
      | .trapped _ _ => opened
    else if call.name = "fd_close" then opened.filter (· != (args.head?.map Arg.value).getD 0)
    else opened
  | _ => opened

/-- The descriptors open after a trace, from the open descriptors `opened`. -/
def openAfter : List UInt64 → List Event → List UInt64
  | opened, [] => opened
  | opened, event :: trace => openAfter (openStep opened event) trace

/-- The host assumption of `WellBracketed.descriptors`: each `path_open` event of `trace` that
returns errno 0 returns a descriptor that is not open, from the open descriptors `opened`. -/
def FreshOpens : List UInt64 → List Event → Prop
  | _, [] => True
  | opened, event :: trace =>
    (∀ call args outputs, event = .sys call args (.returned 0 outputs) →
      call.name = "path_open" → openedDescriptor outputs ∉ opened) ∧
      FreshOpens (openStep opened event) trace

/-- The descriptors open before the first event: standard input, output, and error, and the
preopened directory. -/
def initialDescriptors : List UInt64 := [0, 1, 2, 3]

/-- An event that uses only open descriptors other than the standard ones: its call is one of the
generated descriptions, each `.handle` argument is open and none of 0, 1, and 2, and an `fd_close`
closes a single open descriptor that is none of 0 to 3, so that a `path_open` event opened it. -/
def UsesOpen (opened : List UInt64) : Event → Prop
  | .sys call args _ =>
    Call.table.contains call = true ∧
      (∀ fd ∈ handleArgs call.params args, fd ∈ opened ∧ fd ∉ [0, 1, 2]) ∧
      (call.name = "fd_close" →
        ∃ fd, args = [.word fd] ∧ fd ∈ opened ∧ fd ∉ initialDescriptors)
  | _ => True

/-- The open brackets `stack` are the open descriptors of `opened` that are none of 0 to 3, each
once. -/
def StackOpen (opened stack : List UInt64) : Prop :=
  stack.Nodup ∧ (∀ fd ∈ stack, fd ∉ initialDescriptors) ∧
    ∀ fd, fd ∈ opened ↔ fd ∈ stack ∨ fd ∈ initialDescriptors

theorem fieldHandles_nil (fields : List Field) : fieldHandles fields [] = [] := by
  cases fields <;> rfl

theorem Param.handleWords_nil (param : Param) : param.handleWords [] = [] := by
  cases param <;> simp [Param.handleWords, fieldHandles_nil]

theorem handleArgs_nil (params : List Param) : handleArgs params [] = [] := by
  induction params with
  | nil => rfl
  | cons param params ih => simp [handleArgs, Param.handleWords_nil, ih]

theorem fieldHandles_single (fields : List Field) (arg : Arg) :
    ∀ fd ∈ fieldHandles fields [arg], fd = arg.value := by
  intro fd member
  cases fields with
  | nil => simp [fieldHandles] at member
  | cons field fields =>
    simp only [fieldHandles, fieldHandles_nil] at member
    split at member <;> simp_all

theorem handleArgs_single (params : List Param) (arg : Arg) :
    ∀ fd ∈ handleArgs params [arg], fd = arg.value := by
  induction params with
  | nil => intro fd member; simp [handleArgs] at member
  | cons param params ih =>
    intro fd member
    simp only [handleArgs, List.mem_append] at member
    rcases member with words | rest
    · cases param <;> simp only [Param.handleWords, List.head?_cons, Option.map_some,
        Option.toList_some, List.mem_singleton, List.not_mem_nil] at words
      · exact words
      · exact fieldHandles_single _ arg fd words
    · cases count : param.argCount with
      | zero => rw [count, List.drop_zero] at rest; exact ih fd rest
      | succ count =>
        rw [count, List.drop_succ_cons, List.drop_nil, handleArgs_nil] at rest
        simp at rest

theorem callAllowed_close {stack : List UInt64} {call : Call} {args : List Arg}
    (close : call.name = "fd_close") (allowed : callAllowed stack call args = true) :
    ∃ top rest, stack = top :: rest ∧ args = [.word top] := by
  simp only [callAllowed, callDiscipline, close, ite_true, Bool.and_eq_true] at allowed
  replace allowed := allowed.2
  cases stack with
  | nil => simp at allowed
  | cons top rest =>
    cases args with
    | nil => simp at allowed
    | cons arg more =>
      cases arg with
      | word fd =>
        cases more with
        | nil =>
          simp only [beq_iff_eq] at allowed
          exact ⟨top, rest, rfl, by rw [allowed]⟩
        | cons _ _ => simp at allowed
      | bytes _ => simp at allowed
      | space _ => simp at allowed

theorem callAllowed_handles {stack : List UInt64} {call : Call} {args : List Arg}
    (close : call.name ≠ "fd_close") (allowed : callAllowed stack call args = true) :
    call.name ≠ "fd_renumber" ∧
      ∀ fd ∈ handleArgs call.params args, fd = 3 ∨ fd ∈ stack := by
  by_cases renumber : call.name = "fd_renumber"
  · simp [callAllowed, callDiscipline, renumber] at allowed
  · simp only [callAllowed, callDiscipline, close, renumber, ite_false, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.and_eq_true] at allowed
    exact ⟨renumber, allowed.2⟩

theorem callAllowed_table {stack : List UInt64} {call : Call} {args : List Arg}
    (allowed : callAllowed stack call args = true) : Call.table.contains call = true := by
  simp only [callAllowed, Bool.and_eq_true] at allowed
  exact allowed.1

theorem callAllowed_close_top {stack : List UInt64} {call : Call} {fd : UInt64}
    (member : Call.table.contains call = true) (close : call.name = "fd_close") :
    callAllowed (fd :: stack) call [.word fd] = true := by
  simp only [callAllowed, callDiscipline, member, close, ↓reduceIte, Bool.true_and,
    beq_self_eq_true]

theorem callStack_close {stack : List UInt64} {call : Call} {reply : Transfer (List Bytes)}
    (close : call.name = "fd_close") : callStack stack call reply = stack.tail := by
  simp [callStack, close]

theorem callStack_open {stack : List UInt64} {call : Call} {errno : UInt64}
    {outputs : List Bytes} (pathOpen : call.name = "path_open") :
    callStack stack call (.returned errno outputs) =
      if errno = 0 then openedDescriptor outputs :: stack else stack := by
  simp [callStack, pathOpen, openedDescriptor]

theorem callStack_open_trap {stack : List UInt64} {call : Call} {message : String}
    {committed : List Bytes} (pathOpen : call.name = "path_open") :
    callStack stack call (.trapped message committed) = stack := by
  simp [callStack, pathOpen]

theorem callStack_other {stack : List UInt64} {call : Call} {reply : Transfer (List Bytes)}
    (close : call.name ≠ "fd_close") (notOpen : call.name ≠ "path_open") :
    callStack stack call reply = stack := by
  simp [callStack, close, notOpen]

theorem openStep_close {opened : List UInt64} {call : Call} {fd : UInt64}
    {reply : Transfer (List Bytes)} (close : call.name = "fd_close") :
    openStep opened (.sys call [.word fd] reply) = opened.filter (· != fd) := by
  simp [openStep, close, Arg.value]

theorem openStep_open {opened : List UInt64} {call : Call} {args : List Arg} {errno : UInt64}
    {outputs : List Bytes} (pathOpen : call.name = "path_open") :
    openStep opened (.sys call args (.returned errno outputs)) =
      if errno = 0 then openedDescriptor outputs :: opened else opened := by
  simp [openStep, pathOpen]

theorem openStep_open_trap {opened : List UInt64} {call : Call} {args : List Arg}
    {message : String} {committed : List Bytes} (pathOpen : call.name = "path_open") :
    openStep opened (.sys call args (.trapped message committed)) = opened := by
  simp [openStep, pathOpen]

theorem openStep_other {opened : List UInt64} {call : Call} {args : List Arg}
    {reply : Transfer (List Bytes)} (close : call.name ≠ "fd_close")
    (notOpen : call.name ≠ "path_open") : openStep opened (.sys call args reply) = opened := by
  simp [openStep, close, notOpen]

theorem standard_initial {fd : UInt64} (h : fd ∈ [0, 1, 2]) : fd ∈ initialDescriptors := by
  simp only [initialDescriptors, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h <;> simp [h]

private theorem stackOpen_close {opened rest : List UInt64} {top : UInt64}
    (hOpen : StackOpen opened (top :: rest)) :
    StackOpen (opened.filter (· != top)) rest := by
  obtain ⟨distinct, outside, members⟩ := hOpen
  obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
  have topOutside := outside top List.mem_cons_self
  refine ⟨restDistinct, fun x member => outside x (List.mem_cons_of_mem _ member), fun x => ?_⟩
  simp only [List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨inside, other⟩
    rcases (members x).mp inside with stacked | initial
    · exact .inl ((List.mem_cons.mp stacked).resolve_left other)
    · exact .inr initial
  · rintro (stacked | initial)
    · exact ⟨(members x).mpr (.inl (List.mem_cons_of_mem _ stacked)),
        by rintro rfl; exact notRest stacked⟩
    · exact ⟨(members x).mpr (.inr initial), by rintro rfl; exact topOutside initial⟩

private theorem stackOpen_open {opened stack : List UInt64} {fd : UInt64}
    (hOpen : StackOpen opened stack) (fresh : fd ∉ opened) :
    StackOpen (fd :: opened) (fd :: stack) := by
  obtain ⟨distinct, outside, members⟩ := hOpen
  have notStacked : fd ∉ stack := fun stacked => fresh ((members _).mpr (.inl stacked))
  have notInitial : fd ∉ initialDescriptors :=
    fun initial => fresh ((members _).mpr (.inr initial))
  refine ⟨List.nodup_cons.mpr ⟨notStacked, distinct⟩, fun x member => ?_, fun x => ?_⟩
  · rcases List.mem_cons.mp member with same | stacked
    · exact same ▸ notInitial
    · exact outside x stacked
  · rw [List.mem_cons, List.mem_cons, members x]
    exact or_assoc.symm

private theorem descriptors_step {opened stack next : List UInt64} {event : Event}
    (hOpen : StackOpen opened stack) (hStep : bracketStep stack event = some next)
    (hFresh : ∀ call args outputs, event = .sys call args (.returned 0 outputs) →
      call.name = "path_open" → openedDescriptor outputs ∉ opened) :
    UsesOpen opened event ∧ StackOpen (openStep opened event) next := by
  cases event with
  | sys call args reply =>
    by_cases allowed : callAllowed stack call args = true
    · rw [bracketStep_sys allowed] at hStep
      cases hStep
      by_cases close : call.name = "fd_close"
      · obtain ⟨top, rest, rfl, rfl⟩ := callAllowed_close close allowed
        have topOutside := hOpen.2.1 top List.mem_cons_self
        have topOpen := (hOpen.2.2 top).mpr (.inl List.mem_cons_self)
        refine ⟨⟨callAllowed_table allowed, fun handle member => ?_,
          fun _ => ⟨top, rfl, topOpen, topOutside⟩⟩, ?_⟩
        · rw [handleArgs_single _ _ handle member]
          exact ⟨topOpen, fun standard => topOutside (standard_initial standard)⟩
        · rw [openStep_close close, callStack_close close, List.tail_cons]
          exact stackOpen_close hOpen
      · obtain ⟨_, handles⟩ := callAllowed_handles close allowed
        refine ⟨⟨callAllowed_table allowed, fun fd member => ?_,
          fun same => absurd same close⟩,
          ?_⟩
        · rcases handles fd member with three | stacked
          · subst three
            exact ⟨(hOpen.2.2 3).mpr (.inr (by decide)), by decide⟩
          · exact ⟨(hOpen.2.2 fd).mpr (.inl stacked),
              fun standard => hOpen.2.1 fd stacked (standard_initial standard)⟩
        · by_cases pathOpen : call.name = "path_open"
          · cases reply with
            | trapped message committed =>
              rw [openStep_open_trap pathOpen, callStack_open_trap pathOpen]
              exact hOpen
            | returned errno outputs =>
              rw [openStep_open pathOpen, callStack_open pathOpen]
              by_cases success : errno = 0
              · subst success
                simp only [ite_true]
                exact stackOpen_open hOpen (hFresh call args outputs rfl pathOpen)
              · simp only [success, ite_false]
                exact hOpen
          · rw [openStep_other close pathOpen, callStack_other close pathOpen]
            exact hOpen
    · simp [bracketStep, allowed] at hStep
  | read capacity reply =>
    cases hStep
    exact ⟨trivial, hOpen⟩
  | write output offered reply =>
    cases hStep
    exact ⟨trivial, hOpen⟩
  | exit code =>
    cases hStep
    exact ⟨trivial, hOpen⟩
  | exitTrap code message =>
    cases hStep
    exact ⟨trivial, hOpen⟩

/-- For a host that never returns from `path_open` a descriptor that is open, a well bracketed
trace from no open bracket uses only open descriptors: every `.handle` argument of every event is
open and none of 0, 1, and 2, and every `fd_close` closes an open descriptor that a `path_open`
event opened.  The open brackets after the trace are distinct, and the open descriptors are they
and 0 to 3, so a trace that returns to the empty stack leaves open exactly 0 to 3. -/
theorem WellBracketed.descriptors {trace : List Event} {stack : List UInt64}
    (h : WellBracketed [] trace stack) (fresh : FreshOpens initialDescriptors trace) :
    (∀ before event after, trace = before ++ event :: after →
      UsesOpen (openAfter initialDescriptors before) event) ∧
      StackOpen (openAfter initialDescriptors trace) stack := by
  suffices general : ∀ (trace : List Event) (opened open' stack : List UInt64),
      StackOpen opened open' → WellBracketed open' trace stack → FreshOpens opened trace →
        (∀ before event after, trace = before ++ event :: after →
          UsesOpen (openAfter opened before) event) ∧ StackOpen (openAfter opened trace) stack by
    refine general trace initialDescriptors [] stack ?_ h fresh
    unfold StackOpen
    exact ⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil, fun fd => by simp⟩
  intro trace
  induction trace with
  | nil =>
    intro opened open' stack hOpen h _
    cases h
    exact ⟨fun before event after same => by simp at same, hOpen⟩
  | cons event trace ih =>
    intro opened open' stack hOpen h fresh
    unfold WellBracketed bracketRun at h
    cases hStep : bracketStep open' event with
    | none => rw [hStep] at h; cases h
    | some next =>
      rw [hStep] at h
      obtain ⟨uses, nextOpen⟩ := descriptors_step hOpen hStep fresh.1
      obtain ⟨rest, final⟩ := ih (openStep opened event) next stack nextOpen h fresh.2
      refine ⟨fun before event' after same => ?_, final⟩
      cases before with
      | nil =>
        cases same
        exact uses
      | cons first before =>
        cases same
        exact rest before event' after rfl

/-- The trace corollary of `Action.BracketRuns` for an `Exec` run against a host that never
returns from `path_open` a descriptor that is open: every event uses only open descriptors, as
`UsesOpen` states, and a normal return leaves open exactly the descriptors 0 to 3. -/
theorem Action.BracketRuns.exec_descriptors {action : Action α} (h : action.BracketRuns)
    {World : Type} {host : Host World} {world : World} {trace : List Event}
    {outcome : Outcome α} {final : World} (run : Exec host action world trace outcome final)
    (fresh : FreshOpens initialDescriptors trace) :
    (∀ before event after, trace = before ++ event :: after →
      UsesOpen (openAfter initialDescriptors before) event) ∧
      ∀ value, outcome = .returned value →
        ∀ fd, fd ∈ openAfter initialDescriptors trace ↔ fd ∈ initialDescriptors := by
  obtain ⟨stack, bracketed, returned⟩ := h.1 host world trace outcome final run
  obtain ⟨uses, ⟨_, _, members⟩⟩ := bracketed.descriptors fresh
  refine ⟨uses, fun value same fd => ?_⟩
  rw [members fd, returned value same]
  simp

/-- The trace corollary of `Action.BracketRuns` for a `Prefix` run against a host that never
returns from `path_open` a descriptor that is open: every event uses only open descriptors. -/
theorem Action.BracketRuns.prefix_descriptors {action residual : Action α}
    (h : action.BracketRuns) {World : Type} {host : Host World} {world after : World}
    {trace : List Event} (run : Prefix host action world trace residual after)
    (fresh : FreshOpens initialDescriptors trace) :
    ∀ before event after, trace = before ++ event :: after →
      UsesOpen (openAfter initialDescriptors before) event := by
  obtain ⟨stack, bracketed⟩ := h.2 host world trace residual after run
  exact (bracketed.descriptors fresh).1

/-! ## Actions without brackets -/

theorem callAllowed_of_handles {stack : List UInt64} {call : Call} {args : List Arg}
    (member : Call.table.contains call = true) (close : call.name ≠ "fd_close")
    (renumber : call.name ≠ "fd_renumber")
    (handles : ∀ fd ∈ handleArgs call.params args, fd = 3 ∨ fd ∈ stack) :
    callAllowed stack call args = true := by
  simp only [callAllowed, callDiscipline, member, close, renumber, ite_false, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.true_and]
  exact handles

/-- A call of one of the generated descriptions other than `fd_close`, `fd_renumber`, and
`path_open` that takes 3 or a number on the stack at each `.handle` position keeps the discipline
when its continuation does for every reply. -/
theorem Action.Handles.sys_other {stack : List UInt64} {call : Call} {args : List Arg}
    {next : Reply → Action α} {post : α → List UInt64 → Prop}
    (member : Call.table.contains call = true) (close : call.name ≠ "fd_close")
    (renumber : call.name ≠ "fd_renumber") (notOpen : call.name ≠ "path_open")
    (handles : ∀ fd ∈ handleArgs call.params args, fd = 3 ∨ fd ∈ stack)
    (h : ∀ reply, Action.Handles stack (next reply) post) :
    Action.Handles stack (.sys call args next) post :=
  ⟨fun _ => h _, fun _ => ⟨callAllowed_of_handles member close renumber handles,
    fun _ _ _ => by rw [callStack_other close notOpen]; exact h _⟩⟩

/-- `readAll` makes only reads, and returns to the stack it starts from. -/
theorem Action.Handles.readAll (stack : List UInt64) (limit : UInt64) :
    Action.Handles stack (LeanExe.Wasi.readAll limit) fun _ after => after = stack := by
  unfold LeanExe.Wasi.readAll
  split
  · exact ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  · rfl

end LeanExe.Wasi
