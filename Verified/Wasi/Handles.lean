import Verified.Wasi.HandleCheck
import Verified.Wasi.SysWords
import LeanExe.Wasi.Bracket

/-! The theorems of the handle check.  `Command.handles` states that the meaning of a command
that passes the check keeps the discipline of `withOpen` from every stack of open brackets that
holds the values of its marked variables, and returns to that stack.  `Command.handles_exec` and
`Command.handles_prefix` derive `WellBracketed` for the `Exec` and `Prefix` runs of the command,
and `EffectProg.bracketRuns` gives `Action.BracketRuns` for an action related to a function of a
program called with no marked argument, which `verified_compile_wasi` states as `p.handles` for
`main` and as `p.f.handles` for each exported function `f`. -/

namespace Verified

variable {pureSigs : List Sig}

/-- The value as a word, when its type is the word. -/
def Ty.word? : (type : Ty) → type.denote → Option UInt64
  | .word, value => some value
  | _, _ => none

/-- The value as a pair of words, when its type is a pair of words. -/
def Ty.pair? : (type : Ty) → type.denote → Option (UInt64 × UInt64)
  | .elem (.prod .word .word), value => some value
  | _, _ => none

/-- The value as a Boolean, when its type is `bool`. -/
def Ty.bool? : (type : Ty) → type.denote → Option Bool
  | .bool, value => some value
  | _, _ => none

/-- The value of variable `index` of an environment as `read` gives it from its type. -/
def Env.at? {β : Type} (read : (type : Ty) → type.denote → Option β) :
    {context : List Ty} → Env context → Nat → Option β
  | _, .nil, _ => none
  | _, .cons value _, 0 => read _ value
  | _, .cons _ env, index + 1 => env.at? read index

theorem Env.at?_get {β : Type} (read : (type : Ty) → type.denote → Option β) :
    ∀ {context : List Ty} {type : Ty} (env : Env context) (x : Var context type),
      env.at? read x.index = read type (env.get x)
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons _ env, .there x => Env.at?_get read env x

theorem Env.at?_ofFn {β : Type} (read : (type : Ty) → type.denote → Option β) :
    ∀ {context : List Ty} (values : (i : Fin context.length) → (context.get i).denote)
      (index : Nat) (bounded : index < context.length),
      (Env.ofFn values).at? read index = read _ (values ⟨index, bounded⟩)
  | [], _, _, bounded => absurd bounded (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: _, values, index + 1, bounded =>
    Env.at?_ofFn read (fun i => values i.succ) index (by simpa using bounded)

theorem Expr.markedVar_var {marks : List Bool} :
    ∀ {context : List Ty} {type : Ty} (e : Expr pureSigs context type),
      e.markedVar marks = true →
      ∃ x : Var context type, e = .var x ∧ marks.getD x.index false = true := by
  intro context type e h
  cases e <;> simp only [Expr.markedVar, Bool.false_eq_true] at h
  exact ⟨_, rfl, h⟩

theorem Expr.isWord_denote (funs : Funs pureSigs) {word : UInt64} :
    ∀ {context : List Ty} {type : Ty} (e : Expr pureSigs context type) (env : Env context),
      e.isWord word = true → Ty.word? type (e.denote funs env) = some word := by
  intro context type e env h
  cases e <;> simp only [Expr.isWord, Bool.false_eq_true, beq_iff_eq] at h
  subst h
  rfl

theorem Path.isPart_get {first : Bool} {errno word : UInt64} :
    ∀ {e e' : Elem} (path : Path e e') (value : e.denote), path.isPart first = true →
      Ty.pair? (.elem e) value = some (errno, word) →
        Ty.word? (.elem e') (path.get value) = some (if first then errno else word)
  | _, _, .here, _, part, _ => by simp [Path.isPart] at part
  | .prod a b, _, .fst path, value, part, pair => by
    cases path with
    | here =>
      simp only [Path.isPart, Path.isHere, Bool.and_true] at part
      subst part
      cases a <;> cases b <;> first
        | (simp only [Ty.pair?, Option.some.injEq] at pair; subst pair; rfl)
        | simp [Ty.pair?] at pair
    | fst _ | snd _ => simp [Path.isPart, Path.isHere] at part
  | .prod a b, _, .snd path, value, part, pair => by
    cases path with
    | here =>
      simp only [Path.isPart, Path.isHere, Bool.and_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at part
      subst part
      cases a <;> cases b <;> first
        | (simp only [Ty.pair?, Option.some.injEq] at pair; subst pair; rfl)
        | simp [Ty.pair?] at pair
    | fst _ | snd _ => simp [Path.isPart, Path.isHere] at part

theorem Expr.isOpenedPart_denote (funs : Funs pureSigs) {first : Bool} {errno word : UInt64} :
    ∀ {context : List Ty} {type : Ty} (e : Expr pureSigs context type) (env : Env context),
      e.isOpenedPart first = true → env.at? Ty.pair? 0 = some (errno, word) →
        Ty.word? type (e.denote funs env) = some (if first then errno else word) := by
  intro context type e env h pair
  cases e with
  | proj x path =>
    simp only [Expr.isOpenedPart, Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.1, Env.at?_get] at pair
    exact Path.isPart_get path _ h.2 pair
  | _ => simp [Expr.isOpenedPart] at h

theorem Expr.isErrnoTest_denote (funs : Funs pureSigs) {errno word : UInt64} :
    ∀ {context : List Ty} {type : Ty} (e : Expr pureSigs context type) (env : Env context),
      e.isErrnoTest = true → env.at? Ty.pair? 0 = some (errno, word) →
        Ty.bool? type (e.denote funs env) = some (errno != 0) := by
  intro context type e env h pair
  cases e <;> simp only [Expr.isErrnoTest, Bool.false_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  case cmp op left right =>
    obtain ⟨⟨same, opened⟩, zero⟩ := h
    subst same
    have hLeft := Expr.isOpenedPart_denote funs left env opened pair
    have hRight := Expr.isWord_denote funs right env zero
    simp only [Ty.word?, ite_true, Option.some.injEq] at hLeft hRight
    simp only [Expr.denote, CmpOp.apply, hLeft, hRight]
    rfl

end Verified

namespace Verified.Wasi

open LeanExe.Wasi

variable {pureSigs : List Sig} {effectSigs : List EffectSig}

/-- The value of a command's result as a word, when it is a word. -/
def ResultTy.word? : (result : ResultTy) → result.denote → Option UInt64
  | .value type, held => Ty.word? type held
  | .unit, _ => none

/-- The value of a command's result as a pair of words, when it is one. -/
def ResultTy.pair? : (result : ResultTy) → result.denote → Option (UInt64 × UInt64)
  | .value type, held => Ty.pair? type held
  | .unit, _ => none

/-- Each marked variable of `env` holds a word that is 3 or a number on `stack`. -/
def EnvMarked (marks : List Bool) (env : Env context) (stack : List UInt64) : Prop :=
  ∀ index, marks.getD index false = true →
    ∃ word, env.at? Ty.word? index = some word ∧ (word = 3 ∨ word ∈ stack)

namespace EnvMarked

theorem mono {marks : List Bool} {env : Env context} {stack stack' : List UInt64}
    (h : EnvMarked marks env stack) (sub : ∀ fd ∈ stack, fd ∈ stack') :
    EnvMarked marks env stack' := by
  intro index marked
  obtain ⟨word, value, ok⟩ := h index marked
  exact ⟨word, value, ok.imp id (sub word)⟩

theorem cons {marks : List Bool} {env : Env context} {stack : List UInt64} {mark : Bool}
    {type : Ty} {value : type.denote} (h : EnvMarked marks env stack)
    (head : mark = true →
      ∃ word, Ty.word? type value = some word ∧ (word = 3 ∨ word ∈ stack)) :
    EnvMarked (mark :: marks) (Env.cons value env) stack := by
  intro index marked
  cases index with
  | zero => exact head marked
  | succ index => exact h index marked

theorem cons_false {marks : List Bool} {env : Env context} {stack : List UInt64} {type : Ty}
    {value : type.denote} (h : EnvMarked marks env stack) :
    EnvMarked (false :: marks) (Env.cons value env) stack :=
  h.cons fun marked => nomatch marked

theorem bindEnv {marks : List Bool} {env : Env context} {stack : List UInt64}
    (h : EnvMarked marks env stack) (result : ResultTy) (value : result.denote) :
    EnvMarked (result.marks false marks) (result.bindEnv value env) stack := by
  cases result with
  | unit => exact h
  | value _ => exact h.cons_false

theorem get {marks : List Bool} {env : Env context} {stack : List UInt64}
    (h : EnvMarked marks env stack) (x : Var context .word)
    (marked : marks.getD x.index false = true) : env.get x = 3 ∨ env.get x ∈ stack := by
  obtain ⟨word, value, ok⟩ := h x.index marked
  rw [Env.at?_get] at value
  cases value
  exact ok

theorem unmarked {marks : List Bool} {env : Env context} {stack : List UInt64}
    (h : marks.all (· == false) = true) : EnvMarked marks env stack := by
  intro index marked
  exfalso
  rw [List.getD_eq_getElem?_getD] at marked
  cases hIndex : marks[index]? with
  | none => simp [hIndex] at marked
  | some mark =>
    rw [hIndex, Option.getD_some] at marked
    have := List.all_eq_true.mp h mark (List.mem_of_getElem? hIndex)
    simp [marked] at this

end EnvMarked

theorem handleArgs_skip {param : Param} {params : List Param} {args : List Arg}
    (skips : param.takesArg = false) :
    handleArgs (param :: params) args = handleArgs params args := by
  cases args with
  | nil => simp [handleArgs, handleArgs_nil]
  | cons _ _ => simp [handleArgs, skips]

theorem handleArgs_flatArgsWith {marks : List Bool} {env : Env context} {stack : List UInt64}
    (hEnv : EnvMarked marks env stack) :
    ∀ (params : List Param) (args : List (Var context .word)) (inputs : List LeanExe.Bytes),
      handlesMarked marks params (args.map Var.index) = true →
        inputs.length = params.count .input →
        ∀ fd ∈ handleArgs params (flatArgsWith params (args.map env.get) inputs),
          fd = 3 ∨ fd ∈ stack
  | [], _, _, _, _ => by
    intro fd member
    simp [flatArgsWith, handleArgs] at member
  | param :: params, args, inputs, marked, count => by
    intro fd member
    cases param with
    | handle =>
      cases args with
      | nil => simp [handlesMarked] at marked
      | cons arg args =>
        simp only [handlesMarked, ite_true, List.map_cons, Bool.and_eq_true] at marked
        simp only [List.map_cons, flatArgsWith, handleArgs, Param.takesArg, ite_true,
          List.headD_cons, List.tail_cons, Arg.value, List.mem_cons] at member
        rcases member with same | member
        · subst same
          exact hEnv.get arg marked.1
        · exact handleArgs_flatArgsWith hEnv params args inputs marked.2
            (by simpa [List.count_cons] using count) fd member
    | input =>
      cases inputs with
      | nil => simp [List.count_cons] at count
      | cons input inputs =>
        simp only [handlesMarked, reduceCtorEq, ite_false, Param.takesWord,
          Bool.false_eq_true] at marked
        simp only [flatArgsWith, handleArgs, Param.takesArg, ite_true, reduceCtorEq,
          ite_false] at member
        exact handleArgs_flatArgsWith hEnv params args inputs marked
          (by simpa [List.count_cons] using count) fd member
    | word32 | word64 | enum32 _ | flags32 _ | flags64 _ | output =>
      simp only [handlesMarked, reduceCtorEq, ite_false, Param.takesWord, Param.takesArg,
        ite_true] at marked
      simp only [flatArgsWith, handleArgs, Param.takesArg, ite_true, reduceCtorEq,
        ite_false] at member
      rw [← List.map_tail] at member marked
      exact handleArgs_flatArgsWith hEnv params args.tail inputs marked
        (by simpa [List.count_cons] using count) fd member
    | result32 | result64 | reported _ _ _ | record _ _ _ =>
      simp only [handlesMarked, reduceCtorEq, ite_false, Param.takesWord, Param.takesArg,
        Bool.false_eq_true] at marked
      simp only [flatArgsWith] at member
      rw [handleArgs_skip (by rfl)] at member
      exact handleArgs_flatArgsWith hEnv params args inputs marked
        (by simpa [List.count_cons] using count) fd member

/-- Each helper, called with arguments whose marked parameters hold 3 or numbers on a stack, keeps
the discipline of `withOpen` and returns to that stack. -/
def EffectFuns.HandlesSafe (helpers : List (List Bool)) (effectFuns : EffectFuns effectSigs) :
    Prop :=
  ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature)
    (args : Env signature.params) (stack : List UInt64),
    EnvMarked (callee.marks helpers) args stack →
      Action.Handles stack (effectFuns.get callee args) fun _ after => after = stack

/-- What the check of a command at a stage gives.  At `plain`, the command keeps the discipline
from every stack that holds the values of its marked variables and returns to it.  At `opened`,
`success`, `body`, and `closing`, the command is a part of a bracket whose open returned the
errno and descriptor in variable 0, and returns to the stack before the open. -/
def StageHandles (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (marks : List Bool) : Stage → Command pureSigs effectSigs context result → Prop
  | .plain, command => ∀ (env : Env context) (stack : List UInt64), EnvMarked marks env stack →
      Action.Handles stack (command.denote pureFuns effectFuns env) fun _ after => after = stack
  | .opened, command => ∀ (env : Env context) (stack : List UInt64) (errno word : UInt64),
      env.at? Ty.pair? 0 = some (errno, word) → EnvMarked marks env stack →
        (errno ≠ 0 → Action.Handles stack (command.denote pureFuns effectFuns env)
          fun _ after => after = stack) ∧
        (errno = 0 → word.toNat < 2 ^ 32 →
          Action.Handles (word :: stack) (command.denote pureFuns effectFuns env)
            fun _ after => after = stack)
  | .success, command => ∀ (env : Env context) (stack : List UInt64) (word : UInt64),
      env.at? Ty.pair? 0 = some (0, word) → word.toNat < 2 ^ 32 → EnvMarked marks env stack →
        Action.Handles (word :: stack) (command.denote pureFuns effectFuns env)
          fun _ after => after = stack
  | .body, command => ∀ (env : Env context) (stack : List UInt64) (word : UInt64),
      env.at? Ty.word? 0 = some word → word.toNat < 2 ^ 32 →
        EnvMarked marks env (word :: stack) →
        Action.Handles (word :: stack) (command.denote pureFuns effectFuns env)
          fun _ after => after = stack
  | .closing bound, command => ∀ (env : Env context) (stack : List UInt64) (word : UInt64),
      env.at? Ty.word? bound = some word → word.toNat < 2 ^ 32 →
        Action.Handles (word :: stack) (command.denote pureFuns effectFuns env)
          fun _ after => after = stack

theorem bracketCallNames_not_mem {name : String}
    (h : (!bracketCallNames.contains name) = true) :
    name ≠ "fd_close" ∧ name ≠ "fd_renumber" ∧ name ≠ "path_open" := by
  refine ⟨?_, ?_, ?_⟩ <;> intro same <;> subst same <;> simp [bracketCallNames] at h

theorem openedDescriptor_lt {call : Call} {args : List Arg} {outputs : List LeanExe.Bytes}
    (pathOpen : call = Call.pathOpen) (fits : ReplyFits call args outputs) :
    (openedDescriptor outputs).toNat < 2 ^ 32 := by
  subst pathOpen
  obtain ⟨sizes, sized⟩ := fits
  have four : outputs.map (·.data.size) = [4] := by
    rw [sized]
    rfl
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by simpa using congrArg List.length four)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at four
  exact littleEndian_four_lt four

theorem Command.isOpen_handles (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    {marks : List Bool} {env : Env context} {stack : List UInt64}
    (first : Command pureSigs effectSigs context intermediate) (hOpen : first.isOpen = true)
    (hMarked : first.openMarked marks = true) (hEnv : EnvMarked marks env stack) :
    Action.Handles stack (first.denote pureFuns effectFuns env) fun value after =>
      ∃ errno word, intermediate.pair? value = some (errno, word) ∧
        (errno ≠ 0 → after = stack) ∧
        (errno = 0 → word.toNat < 2 ^ 32 ∧ after = word :: stack) := by
  cases first <;> simp only [Command.isOpen, Bool.false_eq_true] at hOpen
  case sys operation form args inputs =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hOpen
    obtain ⟨⟨rfl, rfl⟩, single⟩ := hOpen
    obtain ⟨path, rfl⟩ := List.length_eq_one_iff.mp single
    simp only [Command.openMarked] at hMarked
    have handles :=
      handleArgs_flatArgsWith hEnv Call.pathOpen.params args [env.get path] hMarked rfl
    refine And.intro (fun rejected => ⟨Call.pathOpen.reject _, 0, rfl, fun _ => rfl,
      fun zero => absurd zero rejected⟩) (fun _ => And.intro ?_ fun errno outputs fits => ?_)
    · exact callAllowed_of_handles (by decide) (by decide) handles
    · show ∃ errno' word, _ ∧
        (errno' ≠ 0 → callStack stack Call.pathOpen (.returned errno outputs) = stack) ∧
        (errno' = 0 → _ ∧ callStack stack Call.pathOpen (.returned errno outputs) = _)
      rw [callStack_open rfl]
      refine ⟨errno, (sysReply errno outputs).word 0, rfl, fun failed => by simp [failed],
        fun zero => ?_⟩
      subst zero
      exact ⟨openedDescriptor_lt rfl fits, by simp [sysReply, openedDescriptor]⟩

theorem Command.preopened_handles (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    {env : Env context} {stack : List UInt64} (first : Command pureSigs effectSigs context
      intermediate) (h : first.preopened = true) :
    Action.Handles stack (first.denote pureFuns effectFuns env) fun value after =>
      after = stack ∧ intermediate.word? value = some 3 := by
  cases first <;> simp only [Command.preopened, Bool.false_eq_true] at h
  exact And.intro rfl (Expr.isWord_denote pureFuns _ env h)

theorem Command.isHandleRet_handles (pureFuns : Funs pureSigs)
    (effectFuns : EffectFuns effectSigs) {env : Env context} {stack : List UInt64}
    {errno word : UInt64} (first : Command pureSigs effectSigs context intermediate)
    (h : first.isHandleRet = true) (pair : env.at? Ty.pair? 0 = some (errno, word)) :
    Action.Handles stack (first.denote pureFuns effectFuns env) fun value after =>
      after = stack ∧ intermediate.word? value = some word := by
  cases first <;> simp only [Command.isHandleRet, Bool.false_eq_true] at h
  exact And.intro rfl
    (by simpa [ResultTy.word?] using Expr.isOpenedPart_denote pureFuns _ env h pair)

theorem Command.isClose_handles (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    {env : Env context} {stack : List UInt64} {word : UInt64} {bound : Nat}
    (first : Command pureSigs effectSigs context intermediate) (h : first.isClose bound = true)
    (held : env.at? Ty.word? bound = some word) (small : word.toNat < 2 ^ 32) :
    Action.Handles (word :: stack) (first.denote pureFuns effectFuns env)
      fun _ after => after = stack := by
  cases first <;> simp only [Command.isClose, Bool.false_eq_true] at h
  case sys operation form args inputs =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, indices⟩ := h
    obtain ⟨handle, rfl⟩ :=
      List.length_eq_one_iff.mp (by simpa using congrArg List.length indices)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at indices
    rw [← indices, Env.at?_get] at held
    simp only [Ty.word?, Option.some.injEq] at held
    have small' : word.toNat < 4294967296 := small
    have accepted : Call.fdClose.reject [.word word] = 0 := by
      simp [Call.reject, rejectArgs, Call.fdClose, Param.takesArg, Param.reject, Arg.value, small']
    show Action.Handles (word :: stack) (.sys Call.fdClose [.word (env.get handle)] _) _
    rw [held]
    refine And.intro (fun rejected => absurd accepted rejected)
      (fun _ => And.intro ?_ fun _ _ _ => ?_)
    · simp [callAllowed, Call.fdClose]
    · rw [callStack_close rfl]
      rfl

theorem Command.returnsBody_handles (pureFuns : Funs pureSigs)
    (effectFuns : EffectFuns effectSigs) {env : Env context} {stack : List UInt64} {bound : Nat}
    (tail : Command pureSigs effectSigs context result) (h : tail.returnsBody bound = true) :
    Action.Handles stack (tail.denote pureFuns effectFuns env) fun _ after => after = stack := by
  cases tail <;> simp only [Command.returnsBody, Bool.false_eq_true] at h <;> rfl

theorem ResultTy.pair?_bindEnv {result : ResultTy} {value : result.denote} {env : Env context}
    {pair : UInt64 × UInt64} (h : result.pair? value = some pair) :
    (result.bindEnv value env).at? Ty.pair? 0 = some pair := by
  cases result with
  | unit => simp [ResultTy.pair?] at h
  | value _ => exact h

theorem ResultTy.marks_pair {result : ResultTy} {value : result.denote} {env : Env context}
    {marks : List Bool} {stack : List UInt64} {pair : UInt64 × UInt64}
    (h : result.pair? value = some pair) (hEnv : EnvMarked marks env stack) :
    EnvMarked (false :: marks) (result.bindEnv value env) stack := by
  cases result with
  | unit => simp [ResultTy.pair?] at h
  | value _ => exact hEnv.cons_false

theorem ResultTy.word?_bindEnv {result : ResultTy} {value : result.denote} {env : Env context}
    {word : UInt64} (h : result.word? value = some word) :
    (result.bindEnv value env).at? Ty.word? 0 = some word := by
  cases result with
  | unit => simp [ResultTy.word?] at h
  | value _ => exact h

theorem ResultTy.bound_bindEnv (result : ResultTy) (value : result.denote) (env : Env context) :
    (result.bindEnv value env).at? Ty.word? result.bound = env.at? Ty.word? 0 := by
  cases result <;> rfl

/-- The meaning of a command that passes the check at a stage satisfies that stage's
`StageHandles`, given helpers that keep the discipline. -/
theorem Command.handles (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    {helpers : List (List Bool)} (safe : effectFuns.HandlesSafe helpers) :
    ∀ {context : List Ty} {result : ResultTy}
      (command : Command pureSigs effectSigs context result)
      (stage : Stage) (marks : List Bool), command.handleCheck helpers stage marks = true →
        StageHandles pureFuns effectFuns marks stage command := by
  intro context result command
  induction command with
  | unit =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    exact fun _ _ _ => rfl
  | ret value =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    exact fun _ _ _ => rfl
  | @bind _ intermediate _ first next ihFirst ihNext =>
    intro stage marks h
    cases stage with
    | plain =>
      intro env stack hEnv
      simp only [Command.handleCheck] at h
      refine Action.Handles.bind_iff.mpr ?_
      split at h
      · rename_i opens
        simp only [Bool.and_eq_true] at h
        refine (Command.isOpen_handles pureFuns effectFuns first opens h.1 hEnv).mono ?_
        rintro value after ⟨errno, word, pair, failed, opened⟩
        have nextHandles := ihNext .opened (false :: marks) h.2 _ stack errno word
          (ResultTy.pair?_bindEnv pair) (ResultTy.marks_pair pair hEnv)
        by_cases zero : errno = 0
        · obtain ⟨small, rfl⟩ := opened zero
          exact nextHandles.2 zero small
        · rw [failed zero]
          exact nextHandles.1 zero
      · simp only [Bool.and_eq_true] at h
        by_cases preopened : first.preopened = true
        · rw [preopened] at h
          refine (Command.preopened_handles pureFuns effectFuns first preopened).mono ?_
          rintro value after ⟨same, three⟩
          rw [same]
          refine ihNext .plain _ h.2 _ stack ?_
          cases intermediate with
          | unit => simp [ResultTy.word?] at three
          | value _ => exact hEnv.cons fun _ => ⟨3, three, .inl rfl⟩
        · simp only [Bool.not_eq_true] at preopened
          rw [preopened] at h
          refine (ihFirst .plain marks h.1 env stack hEnv).mono ?_
          rintro value after rfl
          exact ihNext .plain _ h.2 _ after (hEnv.bindEnv intermediate value)
    | opened => simp only [Command.handleCheck, Bool.false_eq_true] at h
    | success =>
      intro env stack word pair small hEnv
      simp only [Command.handleCheck, Bool.and_eq_true] at h
      refine Action.Handles.bind_iff.mpr ?_
      refine (Command.isHandleRet_handles pureFuns effectFuns first h.1 pair).mono ?_
      rintro value after ⟨same, handle⟩
      rw [same]
      refine ihNext .body (true :: marks) h.2 _ stack word (ResultTy.word?_bindEnv handle) small ?_
      cases intermediate with
      | unit => simp [ResultTy.word?] at handle
      | value _ =>
        exact (hEnv.mono fun _ member => List.mem_cons_of_mem _ member).cons
          fun _ => ⟨word, handle, .inr List.mem_cons_self⟩
    | body =>
      intro env stack word held small hEnv
      simp only [Command.handleCheck, Bool.and_eq_true] at h
      refine Action.Handles.bind_iff.mpr ?_
      refine (ihFirst .plain marks h.1 env (word :: stack) hEnv).mono ?_
      rintro value after rfl
      exact ihNext (.closing intermediate.bound) _ h.2 _ stack word
        (by rw [ResultTy.bound_bindEnv]; exact held) small
    | closing bound =>
      intro env stack word held small
      simp only [Command.handleCheck, Bool.and_eq_true] at h
      refine Action.Handles.bind_iff.mpr ?_
      refine (Command.isClose_handles pureFuns effectFuns first h.1 held small).mono ?_
      rintro value after rfl
      exact Command.returnsBody_handles pureFuns effectFuns next h.2
  | ite condition yes no ihYes ihNo =>
    intro stage marks h
    cases stage with
    | plain =>
      intro env stack hEnv
      simp only [Command.handleCheck, Bool.and_eq_true] at h
      show Action.Handles stack (bif condition.denote pureFuns env then _ else _) _
      cases condition.denote pureFuns env
      · exact ihNo .plain marks h.2 env stack hEnv
      · exact ihYes .plain marks h.1 env stack hEnv
    | opened =>
      intro env stack errno word pair hEnv
      simp only [Command.handleCheck, Bool.and_eq_true] at h
      have test := Expr.isErrnoTest_denote pureFuns condition env h.1.1 pair
      simp only [Ty.bool?, Option.some.injEq] at test
      refine ⟨fun failed => ?_, fun zero small => ?_⟩
      · show Action.Handles stack (bif condition.denote pureFuns env then _ else _) _
        rw [test, bne_iff_ne.mpr failed]
        exact ihYes .plain marks h.1.2 env stack hEnv
      · subst zero
        show Action.Handles _ (bif condition.denote pureFuns env then _ else _) _
        rw [test]
        exact ihNo .success marks h.2 env stack word pair small hEnv
    | success | body | closing _ => simp only [Command.handleCheck, Bool.false_eq_true] at h
  | @call signature _ callee args =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    intro env stack hEnv
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    refine safe callee _ stack fun index marked => ?_
    by_cases bounded : index < signature.params.length
    · have argument := h.2 index bounded
      rw [dite_cond_eq_true (eq_true bounded)] at argument
      simp only [marked, Bool.not_true, Bool.false_or] at argument
      obtain ⟨x, same, xMarked⟩ := Expr.markedVar_var _ argument
      obtain ⟨word, value, ok⟩ := hEnv x.index xMarked
      refine ⟨word, ?_, ok⟩
      rw [Env.at?_ofFn _ _ index bounded]
      show Ty.word? _ ((args ⟨index, bounded⟩).denote pureFuns env) = some word
      rw [same]
      rw [Env.at?_get] at value
      exact value
    · have beyond : (callee.marks helpers).length ≤ index := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none beyond] at marked
  | read capacity =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    exact fun _ _ _ _ => rfl
  | readAll limit =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    intro env stack _
    refine Action.Handles.bind_iff.mpr ((Action.Handles.readAll stack _).mono ?_)
    rintro _ after rfl
    rfl
  | write output bytes =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    intro env stack _
    cases output <;> exact fun _ => rfl
  | exit code =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    exact fun _ _ _ => trivial
  | loop count initial test step ih =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    intro env stack hEnv
    exact And.intro (fun index state => ih .plain _ h _ stack hEnv.cons_false.cons_false)
      fun _ => rfl
  | sys operation form args inputs =>
    intro stage marks h
    cases stage <;> simp only [Command.handleCheck, Bool.false_eq_true] at h
    intro env stack hEnv
    simp only [sysMarked, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨named, reporter⟩, marked⟩, count⟩ := h
    obtain ⟨close, renumber, notOpen⟩ := bracketCallNames_not_mem named
    obtain ⟨reporterClose, reporterRenumber, reporterOpen⟩ := bracketCallNames_not_mem reporter
    have handles := handleArgs_flatArgsWith hEnv operation.params args (inputs.map env.get) marked
      (by simpa [Call.inputCount] using count)
    cases form with
    | flat words bytes =>
      exact Action.Handles.sys_other close renumber notOpen handles fun _ => rfl
    | record fields =>
      exact Action.Handles.sys_other close renumber notOpen handles fun _ => rfl
    | reported =>
      refine Action.Handles.sys_other reporterClose reporterRenumber reporterOpen
        (by simp [handleArgs_nil]) fun sizes => ?_
      split
      · rfl
      · split
        · rfl
        · refine Action.Handles.sys_other close renumber notOpen (by simp [handleArgs_nil])
            fun got => ?_
          split <;> rfl

theorem Command.handles_plain (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    {helpers : List (List Bool)} (safe : effectFuns.HandlesSafe helpers) {marks : List Bool}
    (command : Command pureSigs effectSigs context result)
    (checked : command.HandleCheck helpers marks) {env : Env context} {stack : List UInt64}
    (hEnv : EnvMarked marks env stack) :
    Action.Handles stack (command.denote pureFuns effectFuns env) fun _ after => after = stack :=
  Command.handles pureFuns effectFuns safe command .plain marks checked env stack hEnv

/-- Every `Exec` run of the meaning of a command that passes the check, from a stack of open
brackets that holds the values of its marked variables, is well bracketed, and a normal return
leaves that stack. -/
theorem Command.handles_exec {World : Type} {host : Host World} (pureFuns : Funs pureSigs)
    (effectFuns : EffectFuns effectSigs) {helpers : List (List Bool)}
    (safe : effectFuns.HandlesSafe helpers) {marks : List Bool}
    (command : Command pureSigs effectSigs context result)
    (checked : command.HandleCheck helpers marks) {env : Env context} {stack : List UInt64}
    (hEnv : EnvMarked marks env stack) {world : World} {trace : List Event}
    {outcome : Outcome result.denote} {final : World}
    (run : Exec host (command.denote pureFuns effectFuns env) world trace outcome final) :
    ∃ stack', WellBracketed stack trace stack' ∧
      ∀ value, outcome = .returned value → stack' = stack :=
  Action.Handles.exec_run _ (command.handles_plain pureFuns effectFuns safe checked hEnv) run

/-- Every `Prefix` run of the meaning of a command that passes the check, from a stack of open
brackets that holds the values of its marked variables, is well bracketed. -/
theorem Command.handles_prefix {World : Type} {host : Host World} (pureFuns : Funs pureSigs)
    (effectFuns : EffectFuns effectSigs) {helpers : List (List Bool)}
    (safe : effectFuns.HandlesSafe helpers) {marks : List Bool}
    (command : Command pureSigs effectSigs context result)
    (checked : command.HandleCheck helpers marks) {env : Env context} {stack : List UInt64}
    (hEnv : EnvMarked marks env stack) {world : World} {trace : List Event}
    {residual : Action result.denote} {after : World}
    (run : Prefix host (command.denote pureFuns effectFuns env) world trace residual after) :
    ∃ stack', WellBracketed stack trace stack' := by
  obtain ⟨stack', hTrace, _⟩ :=
    Action.Handles.prefix_run run (command.handles_plain pureFuns effectFuns safe checked hEnv)
  exact ⟨stack', hTrace⟩

/-- The functions of a program that passes the check keep the discipline. -/
theorem EffectProg.handlesSafe (pureFuns : Funs pureSigs) :
    ∀ {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
      (helpers : List (List Bool)), program.HandleCheck helpers →
        (program.funs pureFuns).HandlesSafe helpers
  | _, .nil, _, _ => by
    intro signature callee
    nomatch callee
  | _, .cons function rest, helpers, checked => by
    simp only [EffectProg.HandleCheck, EffectProg.handleCheck, Bool.and_eq_true] at checked
    have restSafe : (rest.funs pureFuns).HandlesSafe helpers.tail :=
      EffectProg.handlesSafe pureFuns rest helpers.tail checked.2
    intro callee args stack hArgs
    cases callee with
    | here =>
      exact function.body.handles_plain pureFuns (rest.funs pureFuns) restSafe checked.1 hArgs
    | there callee => exact restSafe callee args stack hArgs

/-- Every run of an action related to a function of a program that passes the check, called with
no marked argument, keeps the discipline of `withOpen` from no open bracket.  `p.handles` applies
it to `main`. -/
theorem EffectProg.bracketRuns {α : Type} (pureFuns : Funs pureSigs)
    (program : EffectProg pureSigs effectSigs) (helpers : List (List Bool))
    (checked : program.HandleCheck helpers) {signature : EffectSig}
    (callee : EffectVar effectSigs signature) (args : Env signature.params)
    (unmarked : (callee.marks helpers).all (· == false) = true) {relation : α → _ → Prop}
    (native : Action α)
    (related : Action.Rel relation native ((program.funs pureFuns).get callee args)) :
    native.BracketRuns :=
  Action.BracketRuns.of_rel related (Action.Handles.bracketRuns
    (program.handlesSafe pureFuns helpers checked callee args [] (EnvMarked.unmarked unmarked)))

end Verified.Wasi
