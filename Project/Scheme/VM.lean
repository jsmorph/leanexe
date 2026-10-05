import LeanExe.Scheme.VM

/-!
Instruction-level specification and proofs for the VM-only milestone. `Transition`
describes successful execution without referring to `step`, `execute`, `enter`, or
`applyProc`. The implementation is proved both sound and complete for these rules.
-/

namespace LeanExe.Scheme.VM

/-- Successful transitions, including absorption at a completed computation. -/
inductive Transition (code : Code) : State → State → Prop where
  | push {pc env stack memory v} (fetch : code[pc]? = some (.push v)) :
    Transition code ⟨.exec pc, env, stack, memory⟩
      ⟨.exec (pc + 1), env, .value v stack, memory⟩
  | load {pc env stack memory name location v}
      (fetch : code[pc]? = some (.load name))
      (binding : lookup name env = some location) (read : memory[location]? = some v) :
    Transition code ⟨.exec pc, env, stack, memory⟩
      ⟨.exec (pc + 1), env, .value v stack, memory⟩
  | store {pc env rest memory name location v old}
      (fetch : code[pc]? = some (.store name))
      (binding : lookup name env = some location) (read : memory[location]? = some old) :
    Transition code ⟨.exec pc, env, .value v rest, memory⟩
      ⟨.exec (pc + 1), env, .value .unit rest, memory.setIfInBounds location v⟩
  | close {pc env stack memory entry params}
      (fetch : code[pc]? = some (.close entry params)) :
    Transition code ⟨.exec pc, env, stack, memory⟩
      ⟨.exec (pc + 1), env, .value (.closure entry params env) stack, memory⟩
  | drop {pc env rest memory v} (fetch : code[pc]? = some .drop) :
    Transition code ⟨.exec pc, env, .value v rest, memory⟩ ⟨.exec (pc + 1), env, rest, memory⟩
  | jump {pc env stack memory target} (fetch : code[pc]? = some (.jump target)) :
    Transition code ⟨.exec pc, env, stack, memory⟩ ⟨.exec target, env, stack, memory⟩
  | branch {pc env rest memory target v} (fetch : code[pc]? = some (.branch target)) :
    Transition code ⟨.exec pc, env, .value v rest, memory⟩
      ⟨.exec (if v.truth then pc + 1 else target), env, rest, memory⟩
  | binary {pc env rest memory op a b} (fetch : code[pc]? = some (.binary op)) :
    Transition code ⟨.exec pc, env, .value (.word b) (.value (.word a) rest), memory⟩
      ⟨.exec (pc + 1), env, .value (op.eval a b) rest, memory⟩
  | call {pc env stack memory arity args proc rest}
      (fetch : code[pc]? = some (.call arity))
      (arguments : takeValues arity stack = some (args, .value proc rest)) :
    Transition code ⟨.exec pc, env, stack, memory⟩
      ⟨.apply proc args.reverse, [], .frame (pc + 1) env rest, memory⟩
  | tailcall {pc env stack memory arity args proc rest}
      (fetch : code[pc]? = some (.tailcall arity))
      (arguments : takeValues arity stack = some (args, .value proc rest))
      (frame : rest.isFrame = true) :
    Transition code ⟨.exec pc, env, stack, memory⟩ ⟨.apply proc args.reverse, [], rest, memory⟩
  | ret {pc env rest memory v} (fetch : code[pc]? = some .ret)
      (frame : rest.isFrame = true) :
    Transition code ⟨.exec pc, env, .value v rest, memory⟩ ⟨.returning v, [], rest, memory⟩
  | closure {env stack memory entry params captured args bound final}
      (frame : stack.isFrame = true)
      (bindings : bind params args captured memory = some (bound, final)) :
    Transition code ⟨.apply (.closure entry params captured) args, env, stack, memory⟩
      ⟨.exec entry, bound, stack, final⟩
  | continuation {env stack memory saved v} (frame : saved.isFrame = true) :
    Transition code ⟨.apply (.continuation saved) [v], env, stack, memory⟩
      ⟨.returning v, [], saved, memory⟩
  | callcc {env stack memory f} (frame : stack.isFrame = true) :
    Transition code ⟨.apply .callcc [f], env, stack, memory⟩
      ⟨.apply f [.continuation stack], [], stack, memory⟩
  | returnFrame {env memory pc savedEnv rest v} :
    Transition code ⟨.returning v, env, .frame pc savedEnv rest, memory⟩
      ⟨.exec pc, savedEnv, .value v rest, memory⟩
  | finish {env memory v} :
    Transition code ⟨.returning v, env, .halt, memory⟩ ⟨.done v, [], .halt, memory⟩
  | finished {env stack memory v} :
    Transition code ⟨.done v, env, stack, memory⟩ ⟨.done v, env, stack, memory⟩

theorem Transition.nonError {code : Code} {s t : State} (h : Transition code s t) : t.NonError := by
  cases h <;> trivial

/-- Completeness prevents the implementation from satisfying the contract by always failing. -/
theorem Transition.step_eq {code : Code} {s t : State} (h : Transition code s t) :
    step code s = t := by
  cases h <;>
    simp_all [step, execute, enter, VM.binary, applyProc, deliver, State.next, Stack.isFrame]

theorem takeValues_depth {n : Nat} {stack rest : Stack} {values : List Value}
    (h : takeValues n stack = some (values, rest)) : stack.depth = rest.depth := by
  induction n generalizing stack values with
  | zero =>
    simp [takeValues] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ n ih =>
    cases stack with
    | halt => simp [takeValues] at h
    | frame pc env next => simp [takeValues] at h
    | value v next =>
      cases ht : takeValues n next with
      | none => simp [takeValues, ht] at h
      | some result =>
        rcases result with ⟨vs, tail⟩
        simp [takeValues, ht] at h
        rcases h with ⟨rfl, rfl⟩
        exact ih (stack := next) ht

/-- A successful ordinary call adds exactly one active return frame. -/
theorem call_depth {pc arity : Nat} {s : State} {args : List Value} {proc : Value} {rest : Stack}
    (h : takeValues arity s.stack = some (args, .value proc rest)) :
    (enter false pc arity s).stack.depth = s.stack.depth + 1 := by
  have hd := takeValues_depth h
  simp only [Stack.depth] at hd
  simp [enter, h, Stack.depth, hd]

/-- A successful tail call retains the exact return frame, with no new frame. -/
theorem tailcall_frame {pc arity : Nat} {s : State} {args : List Value} {proc : Value}
    {rest : Stack} (h : takeValues arity s.stack = some (args, .value proc rest))
    (hf : rest.isFrame = true) : (enter true pc arity s).stack = rest := by
  simp [enter, h, hf]

theorem tailcall_depth {pc arity : Nat} {s : State} {args : List Value} {proc : Value}
    {rest : Stack} (h : takeValues arity s.stack = some (args, .value proc rest))
    (hf : rest.isFrame = true) : (enter true pc arity s).stack.depth = s.stack.depth := by
  rw [tailcall_frame h hf]
  exact (takeValues_depth h).symm

/-- Invoking a continuation restores control but retains the caller's current store. -/
theorem invoke_continuation {code : Code} (saved : Stack) (v : Value) (env : Env)
    (stack : Stack) (memory : Store) (hf : saved.isFrame = true) :
    step code ⟨.apply (.continuation saved) [v], env, stack, memory⟩ =
      ⟨.returning v, [], saved, memory⟩ := by
  simp [step, applyProc, hf]

/-- The callback runs with exactly the captured continuation, including in tail position. -/
theorem capture_continuation {code : Code} (f : Value) (env : Env) (stack : Stack)
    (memory : Store) (hf : stack.isFrame = true) :
    step code ⟨.apply .callcc [f], env, stack, memory⟩ =
      ⟨.apply f [.continuation stack], [], stack, memory⟩ := by
  simp [step, applyProc, hf]

/-- Fuel slices compose exactly, including completion and failure. -/
theorem run_add (code : Code) (m n : Nat) (s : State) :
    run code (m + n) s = run code n (run code m s) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih => simpa [Nat.succ_add, run] using ih (step code s)

theorem run_error (code : Code) (n : Nat) (e : Error) (env : Env) (stack : Stack)
    (memory : Store) :
    run code n ⟨.error e, env, stack, memory⟩ = ⟨.error e, env, stack, memory⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, step] using ih

theorem bad_pc (code : Code) (pc : Nat) (s : State) (hc : s.control = .exec pc)
    (h : code[pc]? = none) : (step code s).control = .error .badPC := by
  simp [step, hc, h, State.fail]

private theorem execute_sound {code : Code} {pc : Nat} {env : Env} {stack : Stack}
    {memory : Store} {instruction : Instr}
    (fetch : code[pc]? = some instruction)
    (normal : (execute pc instruction ⟨.exec pc, env, stack, memory⟩).NonError) :
    Transition code ⟨.exec pc, env, stack, memory⟩
      (execute pc instruction ⟨.exec pc, env, stack, memory⟩) := by
  cases instruction with
  | push v => exact .push fetch
  | load name =>
    cases hl : lookup name env with
    | none => simp [execute, hl, State.NonError, State.fail] at normal
    | some location =>
      cases hr : memory[location]? with
      | none => simp [execute, hl, hr, State.NonError, State.fail] at normal
      | some v =>
        simpa [execute, hl, hr, State.next] using Transition.load fetch hl hr
  | store name =>
    cases stack <;> try (solve | simp [execute, State.NonError, State.fail] at normal)
    case value v rest =>
      cases hl : lookup name env with
      | none => simp [execute, hl, State.NonError, State.fail] at normal
      | some location =>
        cases hr : memory[location]? with
        | none => simp [execute, hl, hr, State.NonError, State.fail] at normal
        | some old =>
          simpa [execute, hl, hr, State.next] using Transition.store fetch hl hr
  | close entry params => exact .close fetch
  | drop =>
    cases stack <;> try (solve | simp [execute, State.NonError, State.fail] at normal)
    case value v rest => exact .drop fetch
  | jump target => exact .jump fetch
  | branch target =>
    cases stack <;> try (solve | simp [execute, State.NonError, State.fail] at normal)
    case value v rest => exact .branch fetch
  | binary op =>
    cases stack <;> try (solve | simp [execute, VM.binary, State.NonError, State.fail] at normal)
    case value top rest =>
      cases top <;> try (solve | simp [execute, VM.binary, State.NonError, State.fail] at normal)
      case word b =>
        cases rest <;> try (solve | simp [execute, VM.binary, State.NonError, State.fail] at normal)
        case value below tail =>
          cases below <;> try (solve | simp [execute, VM.binary, State.NonError, State.fail] at normal)
          case word a => exact .binary fetch
  | call arity =>
    cases hp : takeValues arity stack with
    | none => simp [execute, enter, hp, State.NonError, State.fail] at normal
    | some result =>
      rcases result with ⟨args, remaining⟩
      cases remaining <;> try (solve | simp [execute, enter, hp, State.NonError, State.fail] at normal)
      case value proc rest =>
        simpa [execute, enter, hp] using Transition.call fetch hp
  | tailcall arity =>
    cases hp : takeValues arity stack with
    | none => simp [execute, enter, hp, State.NonError, State.fail] at normal
    | some result =>
      rcases result with ⟨args, remaining⟩
      cases remaining <;> try (solve | simp [execute, enter, hp, State.NonError, State.fail] at normal)
      case value proc rest =>
        cases hf : rest.isFrame with
        | false => simp [execute, enter, hp, hf, State.NonError, State.fail] at normal
        | true => simpa [execute, enter, hp, hf] using Transition.tailcall fetch hp hf
  | ret =>
    cases stack <;> try (solve | simp [execute, State.NonError, State.fail] at normal)
    case value v rest =>
      cases hf : rest.isFrame with
      | false => simp [execute, hf, State.NonError, State.fail] at normal
      | true => simpa [execute, hf] using Transition.ret fetch hf

private theorem apply_sound {code : Code} {proc : Value} {args : List Value} {env : Env}
    {stack : Stack} {memory : Store}
    (normal : (applyProc proc args ⟨.apply proc args, env, stack, memory⟩).NonError) :
    Transition code ⟨.apply proc args, env, stack, memory⟩
      (applyProc proc args ⟨.apply proc args, env, stack, memory⟩) := by
  cases proc <;> try (solve | simp [applyProc, State.NonError, State.fail] at normal)
  case closure entry params captured =>
    cases hf : stack.isFrame with
    | false => simp [applyProc, hf, State.NonError, State.fail] at normal
    | true =>
      cases hb : bind params args captured memory with
      | none => simp [applyProc, hf, hb, State.NonError, State.fail] at normal
      | some result =>
        rcases result with ⟨bound, final⟩
        simpa [applyProc, hf, hb] using Transition.closure hf hb
  case continuation saved =>
    cases args with
    | nil => simp [applyProc, State.NonError, State.fail] at normal
    | cons v remaining =>
      cases remaining with
      | cons _ _ => simp [applyProc, State.NonError, State.fail] at normal
      | nil =>
        cases hf : saved.isFrame with
        | false => simp [applyProc, hf, State.NonError, State.fail] at normal
        | true => simpa [applyProc, hf] using Transition.continuation hf
  case callcc =>
    cases args with
    | nil => simp [applyProc, State.NonError, State.fail] at normal
    | cons f remaining =>
      cases remaining with
      | cons _ _ => simp [applyProc, State.NonError, State.fail] at normal
      | nil =>
        cases hf : stack.isFrame with
        | false => simp [applyProc, hf, State.NonError, State.fail] at normal
        | true => simpa [applyProc, hf] using Transition.callcc hf

/-- Every non-failing implementation step obeys an instruction or control rule. -/
theorem step_sound {code : Code} {s : State} (normal : (step code s).NonError) :
    Transition code s (step code s) := by
  rcases s with ⟨control, env, stack, memory⟩
  cases control with
  | exec pc =>
    cases hf : code[pc]? with
    | none => simp [step, hf, State.NonError, State.fail] at normal
    | some instruction =>
      simp only [step, hf] at normal ⊢
      exact execute_sound hf normal
  | apply proc args => exact apply_sound normal
  | returning v =>
    cases stack with
    | halt => exact .finish
    | frame pc saved rest => exact .returnFrame
    | value top rest => simp [step, deliver, State.NonError, State.fail] at normal
  | done v => exact .finished
  | error e => simp [step, State.NonError] at normal

/-- Exact agreement with the separately stated rules, for every successful outcome. -/
theorem step_iff {code : Code} {s t : State} (normal : t.NonError) :
    step code s = t ↔ Transition code s t := by
  constructor
  · intro h
    have hs := step_sound (code := code) (s := s) (h.symm ▸ normal)
    simpa [h] using hs
  · exact Transition.step_eq

theorem Transition.deterministic {code : Code} {s t u : State}
    (ht : Transition code s t) (hu : Transition code s u) : t = u :=
  ht.step_eq.symm.trans hu.step_eq

/-- Failure occurs exactly when no successful semantic rule is enabled. -/
theorem fails_iff_no_transition (code : Code) (s : State) :
    ¬ (step code s).NonError ↔ ¬ ∃ t, Transition code s t := by
  constructor
  · intro failed ⟨t, ht⟩
    exact failed (ht.step_eq.symm ▸ ht.nonError)
  · intro blocked normal
    exact blocked ⟨step code s, step_sound normal⟩

/-- A finite successful execution, independently assembled from instruction rules. -/
inductive Trace (code : Code) : Nat → State → State → Prop where
  | zero {s} (normal : s.NonError) : Trace code 0 s s
  | succ {n s mid t} (head : Transition code s mid) (tail : Trace code n mid t) :
    Trace code (n + 1) s t

theorem Trace.run_eq {code : Code} {n : Nat} {s t : State} (h : Trace code n s t) :
    run code n s = t := by
  induction h with
  | zero => rfl
  | succ head _ ih => simpa [run, head.step_eq] using ih

theorem run_nonError_source {code : Code} {n : Nat} {s : State}
    (h : (run code n s).NonError) : s.NonError := by
  rcases s with ⟨control, env, stack, memory⟩
  cases control <;> try trivial
  case error e => simp [run_error, State.NonError] at h

/-- The runner and independent semantics agree for every fuel budget and non-error result. -/
theorem run_iff_trace {code : Code} {n : Nat} {s t : State} (normal : t.NonError) :
    run code n s = t ↔ Trace code n s t := by
  constructor
  · induction n generalizing s with
    | zero => intro h; cases h; exact .zero normal
    | succ n ih =>
      intro h
      have next : (step code s).NonError := run_nonError_source (h ▸ normal)
      exact .succ (step_sound next) (ih h)
  · exact Trace.run_eq

/-- Fresh parameter allocation has the advertised arity and exact size. -/
theorem bind_size {params : List Symbol} {args : List Value} {captured bound : Env}
    {memory final : Store} (h : bind params args captured memory = some (bound, final)) :
    params.length = args.length ∧ final.size = memory.size + args.length := by
  induction params generalizing args memory bound final with
  | nil =>
    cases args with
    | nil => simp [bind] at h; rcases h with ⟨rfl, rfl⟩; simp
    | cons _ _ => simp [bind] at h
  | cons name names ih =>
    cases args with
    | nil => simp [bind] at h
    | cons value values =>
      cases hb : bind names values captured (memory.push value) with
      | none => simp [bind, hb] at h
      | some result =>
        rcases result with ⟨env, store⟩
        simp [bind, hb] at h
        rcases h with ⟨rfl, rfl⟩
        rcases ih hb with ⟨arity, size⟩
        constructor
        · simpa using arity
        · simp [size, Nat.add_comm, Nat.add_left_comm]

/-- Applying a closure cannot change any existing mutable location. -/
theorem bind_preserves {params : List Symbol} {args : List Value} {captured bound : Env}
    {memory final : Store} (h : bind params args captured memory = some (bound, final))
    {i : Nat} (hi : i < memory.size) : final[i]? = memory[i]? := by
  induction params generalizing args memory bound final with
  | nil =>
    cases args with
    | nil => simp [bind] at h; rcases h with ⟨rfl, rfl⟩; rfl
    | cons _ _ => simp [bind] at h
  | cons name names ih =>
    cases args with
    | nil => simp [bind] at h
    | cons value values =>
      cases hb : bind names values captured (memory.push value) with
      | none => simp [bind, hb] at h
      | some result =>
        rcases result with ⟨env, store⟩
        simp [bind, hb] at h
        rcases h with ⟨rfl, rfl⟩
        have hip : i < (memory.push value).size := by simp; omega
        exact (ih hb hip).trans (by simp [Array.getElem?_push, Nat.ne_of_lt hi])

/-- A store instruction changes only the selected location, leaving aliases intact. -/
theorem store_other (memory : Store) (location i : Nat) (value : Value) (h : i ≠ location) :
    (memory.setIfInBounds location value)[i]? = memory[i]? :=
  Array.getElem?_setIfInBounds_ne h.symm

/-- A newly bound parameter denotes its fresh location and the supplied value. -/
theorem bind_head {name : Symbol} {names : List Symbol} {value : Value} {values : List Value}
    {captured bound : Env} {memory final : Store}
    (h : bind (name :: names) (value :: values) captured memory = some (bound, final)) :
    lookup name bound = some memory.size ∧ final[memory.size]? = some value := by
  cases hb : bind names values captured (memory.push value) with
  | none => simp [bind, hb] at h
  | some result =>
    rcases result with ⟨env, store⟩
    simp [bind, hb] at h
    rcases h with ⟨rfl, rfl⟩
    constructor
    · simp [lookup]
    · have hi : memory.size < (memory.push value).size := by simp
      exact (bind_preserves hb hi).trans Array.getElem?_push_size

/-- Closure entry after a tail call still uses the exact original return frame. -/
theorem tailcall_closure {code : Code} {pc arity entry : Nat} {s : State}
    {args : List Value} {params : List Symbol} {captured bound : Env}
    {rest : Stack} {final : Store}
    (h : takeValues arity s.stack = some (args, .value (.closure entry params captured) rest))
    (hf : rest.isFrame = true)
    (hb : bind params args.reverse captured s.store = some (bound, final)) :
    step code (enter true pc arity s) = ⟨.exec entry, bound, rest, final⟩ := by
  simp [enter, h, hf, step, applyProc, hb]

/-- Nonlocal return discards the invoker's stack and resumes with the current store. -/
theorem resume_frame {code : Code} (pc : Nat) (savedEnv env : Env) (rest stack : Stack)
    (memory : Store) (v : Value) :
    run code 2 ⟨.apply (.continuation (.frame pc savedEnv rest)) [v], env, stack, memory⟩ =
      ⟨.exec pc, savedEnv, .value v rest, memory⟩ := by
  simp [run, step, applyProc, Stack.isFrame, deliver]

end LeanExe.Scheme.VM
