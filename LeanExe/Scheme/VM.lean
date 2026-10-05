import Std

/-!
A VM-only semantic milestone. Code is supplied directly, without a Scheme reader or
compiler. The unified immutable stack contains operand values and return frames.
Environments name mutable locations in a store, which continuation invocation does
not restore. This model is not yet a lowering to the LeanExe source dialect.
-/

namespace LeanExe.Scheme.VM

abbrev Symbol := UInt64
abbrev Env := List (Symbol × Nat)

mutual
  inductive Value where
    | word (value : UInt64)
    | boolean (value : Bool)
    | unit
    | closure (entry : Nat) (params : List Symbol) (env : Env)
    | continuation (saved : Stack)
    | callcc
    deriving Repr

  inductive Stack where
    | halt
    | value (value : Value) (rest : Stack)
    | frame (pc : Nat) (env : Env) (rest : Stack)
    deriving Repr
end

abbrev Store := Array Value

/-- Scheme conditionals treat only `#f` as false. -/
def Value.truth : Value → Bool
  | .boolean false => false
  | _ => true

inductive BinOp where
  | add | sub | less | equal
  deriving Repr

def BinOp.eval : BinOp → UInt64 → UInt64 → Value
  | .add, a, b => .word (a + b)
  | .sub, a, b => .word (a - b)
  | .less, a, b => .boolean (a < b)
  | .equal, a, b => .boolean (a == b)

inductive Instr where
  | push (value : Value)
  | load (name : Symbol)
  | store (name : Symbol)
  | close (entry : Nat) (params : List Symbol)
  | drop
  | jump (target : Nat)
  | branch (ifFalse : Nat)
  | binary (op : BinOp)
  | call (arity : Nat)
  | tailcall (arity : Nat)
  | ret
  deriving Repr

abbrev Code := Array Instr

inductive Error where
  | badPC | unbound | badLocation | underflow | expectedWords
  | expectedFrame | notCallable | arity
  deriving Repr, DecidableEq

/-- Application and return are explicit transitions, including primitive callbacks. -/
inductive Control where
  | exec (pc : Nat)
  | apply (proc : Value) (args : List Value)
  | returning (value : Value)
  | done (value : Value)
  | error (reason : Error)
  deriving Repr

structure State where
  control : Control
  env : Env
  stack : Stack
  store : Store
  deriving Repr

def Stack.isFrame : Stack → Bool
  | .halt | .frame .. => true
  | .value .. => false

/-- Counts active return frames, excluding any saved continuation inside a value. -/
def Stack.depth : Stack → Nat
  | .halt => 0
  | .value _ rest => rest.depth
  | .frame _ _ rest => rest.depth + 1

/-- Arguments occur above the procedure, in reverse source order. Never crosses a frame. -/
def takeValues : Nat → Stack → Option (List Value × Stack)
  | 0, stack => some ([], stack)
  | n + 1, .value v rest =>
    match takeValues n rest with
    | some (vs, tail) => some (v :: vs, tail)
    | none => none
  | _ + 1, _ => none

def lookup (name : Symbol) : Env → Option Nat
  | [] => none
  | (key, location) :: rest => if name = key then some location else lookup name rest

/-- Allocates fresh parameter locations; the captured environment supplies outer bindings. -/
def bind : List Symbol → List Value → Env → Store → Option (Env × Store)
  | [], [], env, store => some (env, store)
  | name :: names, value :: values, env, store =>
    match bind names values env (store.push value) with
    | some (bound, final) => some ((name, store.size) :: bound, final)
    | none => none
  | _, _, _, _ => none

def State.fail (s : State) (e : Error) : State := { s with control := .error e }

def State.next (s : State) (pc : Nat) (stack : Stack) : State :=
  { s with control := .exec (pc + 1), stack }

/-- CALL and TAILCALL differ only in construction of the return frame. -/
def enter (tail : Bool) (pc arity : Nat) (s : State) : State :=
  match takeValues arity s.stack with
  | some (args, .value proc rest) =>
    if tail && !rest.isFrame then s.fail .expectedFrame
    else
      { s with
        control := .apply proc args.reverse
        env := []
        stack := if tail then rest else .frame (pc + 1) s.env rest }
  | _ => s.fail .underflow

def binary (pc : Nat) (op : UInt64 → UInt64 → Value) (s : State) : State :=
  match s.stack with
  | .value (.word b) (.value (.word a) rest) => s.next pc (.value (op a b) rest)
  | _ => s.fail .expectedWords

def execute (pc : Nat) (instruction : Instr) (s : State) : State :=
  match instruction with
  | .push v => s.next pc (.value v s.stack)
  | .load name =>
    match lookup name s.env with
    | none => s.fail .unbound
    | some location =>
      match s.store[location]? with
      | none => s.fail .badLocation
      | some v => s.next pc (.value v s.stack)
  | .store name =>
    match s.stack with
    | .value v rest =>
      match lookup name s.env with
      | none => s.fail .unbound
      | some location =>
        match s.store[location]? with
        | none => s.fail .badLocation
        | some _ =>
          { s.next pc (.value .unit rest) with store := s.store.setIfInBounds location v }
    | _ => s.fail .underflow
  | .close entry params => s.next pc (.value (.closure entry params s.env) s.stack)
  | .drop =>
    match s.stack with
    | .value _ rest => s.next pc rest
    | _ => s.fail .underflow
  | .jump target => { s with control := .exec target }
  | .branch target =>
    match s.stack with
    | .value v rest =>
      { s with control := .exec (if v.truth then pc + 1 else target), stack := rest }
    | _ => s.fail .underflow
  | .binary op => binary pc op.eval s
  | .call arity => enter false pc arity s
  | .tailcall arity => enter true pc arity s
  | .ret =>
    match s.stack with
    | .value v rest =>
      if rest.isFrame then
        { s with control := .returning v, env := [], stack := rest }
      else s.fail .expectedFrame
    | _ => s.fail .underflow

def applyProc (proc : Value) (args : List Value) (s : State) : State :=
  match proc with
  | .closure entry params captured =>
    if s.stack.isFrame then
      match bind params args captured s.store with
      | some (env, store) => { s with control := .exec entry, env, store }
      | none => s.fail .arity
    else s.fail .expectedFrame
  | .continuation saved =>
    match args with
    | [v] =>
      if saved.isFrame then
        { s with control := .returning v, env := [], stack := saved }
      else s.fail .expectedFrame
    | _ => s.fail .arity
  | .callcc =>
    match args with
    | [f] =>
      if s.stack.isFrame then
        { s with control := .apply f [.continuation s.stack], env := [] }
      else s.fail .expectedFrame
    | _ => s.fail .arity
  | _ => s.fail .notCallable

def deliver (v : Value) (s : State) : State :=
  match s.stack with
  | .halt => { s with control := .done v, env := [] }
  | .frame pc env rest => { s with control := .exec pc, env, stack := .value v rest }
  | .value .. => s.fail .expectedFrame

def step (code : Code) (s : State) : State :=
  match s.control with
  | .exec pc =>
    match code[pc]? with
    | some instruction => execute pc instruction s
    | none => s.fail .badPC
  | .apply proc args => applyProc proc args s
  | .returning v => deliver v s
  | .done _ | .error _ => s

/-- Exact transition budget. Finished and failed states are absorbing. -/
def run (code : Code) : Nat → State → State
  | 0, s => s
  | n + 1, s => run code n (step code s)

def initial (env : Env := []) (store : Store := #[]) : State :=
  ⟨.exec 0, env, .halt, store⟩

/-- This is an outcome test, rather than a well-formedness invariant. -/
def State.NonError (s : State) : Prop :=
  match s.control with
  | .error _ => False
  | _ => True

end LeanExe.Scheme.VM
