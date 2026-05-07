import Lean

namespace LeanExe.IR

inductive Ty where
  | unit
  | bool
  | u8
  | u32
  | u64
  | nat
  | byteArray
  | array (item : Ty)
  | product (left right : Ty)
  | sum (left right : Ty)
  deriving BEq, Repr

inductive U64Op where
  | add
  | sub
  | mul
  | divU
  | modU
  | bitAnd
  deriving BEq, Repr

def Store := Nat → UInt64

def Store.empty : Store :=
  fun _ => 0

def Store.set (store : Store) (index : Nat) (value : UInt64) : Store :=
  fun candidate => if candidate == index then value else store candidate

mutual
  inductive Expr where
    | local (index : Nat)
    | u64 (value : Nat)
    | u64Bin (op : U64Op) (left right : Expr)
    | ite (cond : Cond) (thenValue elseValue : Expr)
    | letE (slot : Nat) (value body : Expr)
    | arrayAlloc (cells : Expr)
    | arrayReplicate (cells value : Expr)
    | arraySize (array : Expr)
    | arrayGet (array index : Expr)
    | arraySet (array index value : Expr)
    | arrayPush (array value : Expr)
    | byteArrayGet (ptr len index : Expr)
    | call (index : Nat) (args : List Expr)
    deriving BEq, Repr

  inductive Cond where
    | true
    | false
    | eqU64 (left right : Expr)
    | ltU64 (left right : Expr)
    | leU64 (left right : Expr)
    | not (cond : Cond)
    | and (left right : Cond)
    | or (left right : Cond)
    deriving BEq, Repr
end

mutual
  inductive Stmt where
    | skip
    | assign (index : Nat) (value : Expr)
    | seq (first second : Stmt)
    | while (cond : Cond) (body : Stmt)
    deriving BEq, Repr

  structure Func where
    sourceName : Lean.Name
    exportName : Option String
    params : Nat
    locals : Nat
    body : Stmt
    result : Expr
    deriving BEq, Repr

  structure Module where
    funcs : Array Func
    deriving BEq, Repr
end

def Module.getFunc? (module_ : Module) (index : Nat) : Option Func :=
  module_.funcs[index]?

def seqList : List Stmt → Stmt
  | [] => .skip
  | stmt :: rest => rest.foldl Stmt.seq stmt

mutual
  partial def Expr.eval (module_ : Module) (store : Store) : Expr → UInt64
    | .local index => store index
    | .u64 value => UInt64.ofNat value
    | .u64Bin op left right =>
        let leftValue := left.eval module_ store
        let rightValue := right.eval module_ store
        match op with
        | .add => leftValue + rightValue
        | .sub => leftValue - rightValue
        | .mul => leftValue * rightValue
        | .divU => leftValue / rightValue
        | .modU => leftValue % rightValue
        | .bitAnd => UInt64.land leftValue rightValue
    | .ite cond thenValue elseValue =>
        if cond.eval module_ store then
          thenValue.eval module_ store
        else
          elseValue.eval module_ store
    | .letE slot value body =>
        body.eval module_ (store.set slot (value.eval module_ store))
    | .arrayAlloc _ => 0
    | .arrayReplicate _ _ => 0
    | .arraySize _ => 0
    | .arrayGet _ _ => 0
    | .arraySet array _ _ => array.eval module_ store
    | .arrayPush array _ => array.eval module_ store
    | .byteArrayGet _ _ _ => 0
    | .call index args =>
        match module_.getFunc? index with
        | some func => func.eval module_ (args.map (fun arg => arg.eval module_ store))
        | none => 0

  partial def Cond.eval (module_ : Module) (store : Store) : Cond → Bool
    | .true => true
    | .false => false
    | .eqU64 left right => left.eval module_ store == right.eval module_ store
    | .ltU64 left right => left.eval module_ store < right.eval module_ store
    | .leU64 left right => left.eval module_ store <= right.eval module_ store
    | .not cond => !cond.eval module_ store
    | .and left right => left.eval module_ store && right.eval module_ store
    | .or left right => left.eval module_ store || right.eval module_ store

  partial def Stmt.eval (module_ : Module) : Stmt → Store → Store
    | .skip, store => store
    | .assign index value, store => store.set index (value.eval module_ store)
    | .seq first second, store => second.eval module_ (first.eval module_ store)
    | .while cond body, store =>
        let rec loop : Nat → Store → Store
          | 0, current => current
          | fuel + 1, current =>
              if cond.eval module_ current then
                loop fuel (body.eval module_ current)
              else
                current
        loop 1000000 store

  partial def Func.eval (func : Func) (module_ : Module) (args : List UInt64) : UInt64 :=
    let store :=
      args.foldl
        (fun (state : Nat × Store) arg =>
          let index := state.fst
          (index + 1, state.snd.set index arg))
        (0, Store.empty)
    func.result.eval module_ (func.body.eval module_ store.snd)
end

def Module.evalFunc (module_ : Module) (index : Nat) (args : List UInt64) : UInt64 :=
  match module_.getFunc? index with
  | some func => func.eval module_ args
  | none => 0

end LeanExe.IR
