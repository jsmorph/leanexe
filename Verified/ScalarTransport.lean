import Verified.ScalarCalibration

namespace Wasm

def Continuation.withStore (store : Store α) : Continuation α → Continuation α
  | .Fallthrough _ locals => .Fallthrough store locals
  | .Break label _ locals => .Break label store locals
  | .Return _ values => .Return store values
  | .Trap _ message => .Trap store message
  | .Invalid message => .Invalid message
  | .OutOfFuel => .OutOfFuel
  | .ReturnCall entry _ values => .ReturnCall entry store values
  | .Throwing tag values _ locals => .Throwing tag values store locals

def Continuation.noReturnCall : Continuation α → Bool
  | .ReturnCall .. => false
  | _ => true

def OneUniform (m : Module) (instruction : Instruction) : Prop :=
  ∀ (fuel : Nat) (host : HostEnv Unit) (store reference : Store Unit) (locals : Locals),
    execOne fuel m store locals instruction host =
      (execOne fuel m reference locals instruction host).withStore store

def CodeUniform (m : Module) (program : Program) : Prop :=
  ∀ (fuel : Nat) (host : HostEnv Unit) (store reference : Store Unit) (locals : Locals),
    exec fuel m store locals program host =
      (exec fuel m reference locals program host).withStore store

def OneNoReturnCall (m : Module) (instruction : Instruction) : Prop :=
  ∀ (fuel : Nat) (host : HostEnv Unit) (store : Store Unit) (locals : Locals),
    (execOne fuel m store locals instruction host).noReturnCall = true

def CodeNoReturnCall (m : Module) (program : Program) : Prop :=
  ∀ (fuel : Nat) (host : HostEnv Unit) (store : Store Unit) (locals : Locals),
    (exec fuel m store locals program host).noReturnCall = true

theorem exec_append_match (fuel : Nat) (m : Module) (host : HostEnv Unit)
    (store : Store Unit) (locals : Locals) (first next : Program) :
    exec fuel m store locals (first ++ next) host =
      match exec fuel m store locals first host with
      | .Fallthrough state after => exec fuel m state after next host
      | other => other := by
  induction first generalizing store locals with
  | nil => simp only [List.nil_append, exec]
  | cons instruction rest ih =>
    simp only [List.cons_append, exec]
    cases h : execOne fuel m store locals instruction host with
    | Fallthrough state after => exact ih state after
    | Break label state after => rfl
    | Return state values => rfl
    | Trap state message => rfl
    | Invalid message => rfl
    | OutOfFuel => rfl
    | ReturnCall entry state values => rfl
    | Throwing tag values state after => rfl

theorem CodeUniform.nil (m : Module) : CodeUniform m [] := by
  intro fuel host store reference locals
  simp only [exec, Continuation.withStore]

theorem CodeUniform.cons {m : Module} {instruction : Instruction} {rest : Program}
    (first : OneUniform m instruction) (next : CodeUniform m rest) :
    CodeUniform m (instruction :: rest) := by
  intro fuel host store reference locals
  simp only [exec]
  rw [first fuel host store reference locals]
  cases h : execOne fuel m reference locals instruction host with
  | Fallthrough state locals => exact next fuel host store state locals
  | Break label state locals => rfl
  | Return state values => rfl
  | Trap state message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | ReturnCall entry state values => rfl
  | Throwing tag values state locals => rfl

theorem CodeNoReturnCall.nil (m : Module) : CodeNoReturnCall m [] := by
  intro fuel host store locals
  simp only [exec, Continuation.noReturnCall]

theorem CodeUniform.append {m : Module} {first next : Program}
    (hFirst : CodeUniform m first) (hNext : CodeUniform m next) :
    CodeUniform m (first ++ next) := by
  intro fuel host store reference locals
  rw [exec_append_match, exec_append_match, hFirst fuel host store reference locals]
  cases h : exec fuel m reference locals first host with
  | Fallthrough state after => exact hNext fuel host store state after
  | Break label state after => rfl
  | Return state values => rfl
  | Trap state message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | ReturnCall entry state values => rfl
  | Throwing tag values state after => rfl

theorem CodeNoReturnCall.append {m : Module} {first next : Program}
    (hFirst : CodeNoReturnCall m first) (hNext : CodeNoReturnCall m next) :
    CodeNoReturnCall m (first ++ next) := by
  intro fuel host store locals
  have hSafe := hFirst fuel host store locals
  rw [exec_append_match]
  cases h : exec fuel m store locals first host with
  | Fallthrough state after => exact hNext fuel host state after
  | Break label state after => rfl
  | Return state values => rfl
  | Trap state message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | ReturnCall entry state values => simp only [h, Continuation.noReturnCall, Bool.false_eq_true] at hSafe
  | Throwing tag values state after => rfl

theorem CodeNoReturnCall.cons {m : Module} {instruction : Instruction} {rest : Program}
    (first : OneNoReturnCall m instruction) (next : CodeNoReturnCall m rest) :
    CodeNoReturnCall m (instruction :: rest) := by
  intro fuel host store locals
  have hFirst := first fuel host store locals
  simp only [exec]
  cases h : execOne fuel m store locals instruction host with
  | Fallthrough state locals => exact next fuel host state locals
  | Break label state locals => rfl
  | Return state values => rfl
  | Trap state message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | ReturnCall entry state values => simp only [h, Continuation.noReturnCall, Bool.false_eq_true] at hFirst
  | Throwing tag values state locals => rfl

theorem EntryUniform.of_code {m : Module} {entry : Nat} {function : Function}
    (hImports : m.imports = []) (hFunction : m.funcs[entry]? = some function)
    (uniform : CodeUniform m function.body) (noReturnCall : CodeNoReturnCall m function.body) :
    EntryUniform m entry := by
  intro fuel host store reference args
  simp only [run, hImports, List.getElem?_nil, List.length_nil, Nat.sub_zero, hFunction]
  rw [uniform fuel host store reference]
  have hNoReturnCall := noReturnCall fuel host reference
    (function.toLocals (args.take function.numParams).reverse)
  cases h : exec fuel m reference
      (function.toLocals (args.take function.numParams).reverse) function.body host with
  | Fallthrough state locals => rfl
  | Break label state locals => cases label <;> rfl
  | Return state values => rfl
  | Trap state message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | ReturnCall entry state values => simp only [h, Continuation.noReturnCall, Bool.false_eq_true] at hNoReturnCall
  | Throwing tag values state locals => rfl

#print axioms CodeUniform.cons
#print axioms EntryUniform.of_code

end Wasm
