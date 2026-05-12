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
  | struct (name : Lean.Name) (fields : List Ty)
  | variant (name : Lean.Name) (ctors : List (List Ty))
  | recVariant (name : Lean.Name) (params : List Ty)
  deriving BEq, Repr

inductive U64Op where
  | add
  | natAdd
  | sub
  | natSub
  | mul
  | natMul
  | divU
  | modU
  | bitAnd
  | bitOr
  | bitXor
  | shiftLeft
  | shiftRight
  deriving BEq, Repr

def Store := Nat → UInt64

def Store.empty : Store :=
  fun _ => 0

def Store.set (store : Store) (index : Nat) (value : UInt64) : Store :=
  fun candidate => if candidate == index then value else store candidate

mutual
  inductive Expr where
    | local (index : Nat)
    | trap
    | u64 (value : Nat)
    | u64Bin (op : U64Op) (left right : Expr)
    | ite (cond : Cond) (thenValue elseValue : Expr)
    | letE (slot : Nat) (value body : Expr)
    | letCall (slots : List Nat) (index : Nat) (args : List Expr) (body : Expr)
    | arrayAlloc (cells : Expr)
    | arrayAllocSlots (width : Nat) (cells : Expr)
    | heapAllocSlots (values : List Expr)
    | heapLoadSlot (ptr : Expr) (slot : Nat)
    | arrayReplicate (cells value : Expr)
    | arrayReplicateSlots (width : Nat) (cells : Expr) (values : List Expr)
    | arraySize (array : Expr)
    | arrayGet (array index : Expr)
    | arrayGetSlot (width slot : Nat) (array index : Expr)
    | arraySet (array index value : Expr)
    | arraySetSlots (width : Nat) (array index : Expr) (values : List Expr)
    | arrayPush (array value : Expr)
    | arrayPushSlots (width : Nat) (array : Expr) (values : List Expr)
    | arrayPop (array : Expr)
    | arrayPopSlots (width : Nat) (array : Expr)
    | arrayAppend (left right : Expr)
    | arrayAppendSlots (width : Nat) (left right : Expr)
    | arrayExtract (array start stop : Expr)
    | arrayExtractSlots (width : Nat) (array start stop : Expr)
    | arrayMap (array : Expr) (itemSlot : Nat) (body : Expr)
    | arrayMapSlots (sourceWidth resultWidth : Nat) (array : Expr) (itemStart : Nat)
        (bodyValues : List Expr)
    | arrayFoldSlots (sourceWidth : Nat) (array start stop init : Expr)
        (accSlot itemStart : Nat) (body : Expr)
    | arrayFoldMultiSlot (sourceWidth resultWidth : Nat) (array start stop : Expr)
        (initValues : List Expr) (accStart itemStart : Nat) (bodyValues : List Expr)
        (bodyDone : Expr) (resultSlot : Nat)
    | arrayFindIdxSlots (sourceWidth : Nat) (array : Expr) (itemStart : Nat)
        (predicate : Expr) (returnPayload : Bool)
    | arrayFindSlot (sourceWidth : Nat) (array : Expr) (itemStart : Nat)
        (predicate : Expr) (slot : Nat)
    | arrayAnySlots (sourceWidth : Nat) (array start stop : Expr) (itemStart : Nat)
        (predicate : Expr) (forAll : Bool)
    | arrayFilterSlots (sourceWidth : Nat) (array start stop : Expr) (itemStart : Nat)
        (predicate : Expr)
    | arrayInsertIfInBounds (array index value : Expr)
    | arrayInsertIfInBoundsSlots (width : Nat) (array index : Expr) (values : List Expr)
    | arrayEraseIfInBounds (array index : Expr)
    | arrayEraseIfInBoundsSlots (width : Nat) (array index : Expr)
    | arraySwapIfInBounds (array left right : Expr)
    | arraySwapIfInBoundsSlots (width : Nat) (array left right : Expr)
    | arrayReverse (array : Expr)
    | arrayReverseSlots (width : Nat) (array : Expr)
    | byteArrayGet (ptr len index : Expr)
    | byteArrayPushPtr (ptr len value : Expr)
    | byteArrayAppendPtr (leftPtr leftLen rightPtr rightLen : Expr)
    | byteArraySetPtr (ptr len index value : Expr)
    | byteArrayFromArrayPtr (array : Expr)
    | byteArrayCopySlicePtr
        (srcPtr srcLen srcOff destPtr destLen destOff copyLen : Expr)
    | byteArrayFindIdx (ptr len start : Expr) (byteSlot : Nat) (predicate : Expr)
        (returnPayload : Bool)
    | byteArrayFold (ptr len start stop init : Expr) (accSlot byteSlot : Nat) (body : Expr)
    | byteArrayFoldMultiSlot (resultWidth : Nat) (ptr len start stop : Expr)
        (initValues : List Expr) (accStart byteSlot : Nat) (bodyValues : List Expr)
        (bodyDone : Expr) (resultSlot : Nat)
    | rangeFoldMultiSlot (resultWidth : Nat) (start stop step : Expr)
        (initValues : List Expr) (accStart itemSlot : Nat) (bodyValues : List Expr)
        (bodyDone : Expr) (resultSlot : Nat)
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
    | call (slots : List Nat) (index : Nat) (args : List Expr)
    | arrayFoldMultiSlotAssign (sourceWidth resultWidth : Nat) (array start stop : Expr)
        (initValues : List Expr) (accStart itemStart : Nat) (bodyValues : List Expr)
        (bodyDone : Expr) (targets : List Nat)
    | byteArrayFoldMultiSlotAssign (resultWidth : Nat) (ptr len start stop : Expr)
        (initValues : List Expr) (accStart byteSlot : Nat) (bodyValues : List Expr)
        (bodyDone : Expr) (targets : List Nat)
    | rangeFoldMultiSlotAssign (resultWidth : Nat) (start stop step : Expr)
        (initValues : List Expr) (accStart itemSlot : Nat) (bodyValues : List Expr)
        (bodyDone : Expr) (targets : List Nat)
    | ite (cond : Cond) (thenStmt elseStmt : Stmt)
    | seq (first second : Stmt)
    | while (cond : Cond) (body : Stmt)
    deriving BEq, Repr

  structure Func where
    sourceName : Lean.Name
    exportName : Option String
    params : Nat
    locals : Nat
    body : Stmt
    results : List Expr
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
    | .trap => 0
    | .u64 value => UInt64.ofNat value
    | .u64Bin op left right =>
        let leftValue := left.eval module_ store
        let rightValue := right.eval module_ store
        match op with
        | .add => leftValue + rightValue
        | .natAdd => leftValue + rightValue
        | .sub => leftValue - rightValue
        | .natSub => if leftValue < rightValue then 0 else leftValue - rightValue
        | .mul => leftValue * rightValue
        | .natMul => leftValue * rightValue
        | .divU => leftValue / rightValue
        | .modU => leftValue % rightValue
        | .bitAnd => UInt64.land leftValue rightValue
        | .bitOr => UInt64.lor leftValue rightValue
        | .bitXor => UInt64.xor leftValue rightValue
        | .shiftLeft => UInt64.shiftLeft leftValue rightValue
        | .shiftRight => UInt64.shiftRight leftValue rightValue
    | .ite cond thenValue elseValue =>
        if cond.eval module_ store then
          thenValue.eval module_ store
        else
          elseValue.eval module_ store
    | .letE slot value body =>
        body.eval module_ (store.set slot (value.eval module_ store))
    | .letCall slots index args body =>
        let results :=
          match module_.getFunc? index with
          | some func => func.evalResults module_ (args.map (fun arg => arg.eval module_ store))
          | none => []
        let callStore :=
          slots.zip results |>.foldl
            (fun current item => current.set item.fst item.snd)
            store
        body.eval module_ callStore
    | .arrayAlloc _ => 0
    | .arrayAllocSlots _ _ => 0
    | .heapAllocSlots _ => 0
    | .heapLoadSlot _ _ => 0
    | .arrayReplicate _ _ => 0
    | .arrayReplicateSlots _ _ _ => 0
    | .arraySize _ => 0
    | .arrayGet _ _ => 0
    | .arrayGetSlot _ _ _ _ => 0
    | .arraySet array _ _ => array.eval module_ store
    | .arraySetSlots _ array _ _ => array.eval module_ store
    | .arrayPush array _ => array.eval module_ store
    | .arrayPushSlots _ array _ => array.eval module_ store
    | .arrayPop array => array.eval module_ store
    | .arrayPopSlots _ array => array.eval module_ store
    | .arrayAppend left _ => left.eval module_ store
    | .arrayAppendSlots _ left _ => left.eval module_ store
    | .arrayExtract array _ _ => array.eval module_ store
    | .arrayExtractSlots _ array _ _ => array.eval module_ store
    | .arrayMap array _ _ => array.eval module_ store
    | .arrayMapSlots _ _ array _ _ => array.eval module_ store
    | .arrayFoldSlots _ _ _ _ init _ _ _ => init.eval module_ store
    | .arrayFoldMultiSlot _ _ _ _ _ initValues _ _ _ _ resultSlot =>
        match initValues[resultSlot]? with
        | some init => init.eval module_ store
        | none => 0
    | .arrayFindIdxSlots _ _ _ _ _ => 0
    | .arrayFindSlot _ _ _ _ _ => 0
    | .arrayAnySlots _ _ _ _ _ _ forAll => if forAll then 1 else 0
    | .arrayFilterSlots _ array _ _ _ _ => array.eval module_ store
    | .arrayInsertIfInBounds array _ _ => array.eval module_ store
    | .arrayInsertIfInBoundsSlots _ array _ _ => array.eval module_ store
    | .arrayEraseIfInBounds array _ => array.eval module_ store
    | .arrayEraseIfInBoundsSlots _ array _ => array.eval module_ store
    | .arraySwapIfInBounds array _ _ => array.eval module_ store
    | .arraySwapIfInBoundsSlots _ array _ _ => array.eval module_ store
    | .arrayReverse array => array.eval module_ store
    | .arrayReverseSlots _ array => array.eval module_ store
    | .byteArrayGet _ _ _ => 0
    | .byteArrayPushPtr ptr _ _ => ptr.eval module_ store
    | .byteArrayAppendPtr leftPtr _ _ _ => leftPtr.eval module_ store
    | .byteArraySetPtr ptr _ _ _ => ptr.eval module_ store
    | .byteArrayFromArrayPtr array => array.eval module_ store
    | .byteArrayCopySlicePtr _ _ _ destPtr _ _ _ => destPtr.eval module_ store
    | .byteArrayFindIdx _ _ _ _ _ _ => 0
    | .byteArrayFold _ _ _ _ init _ _ _ => init.eval module_ store
    | .byteArrayFoldMultiSlot _ _ _ _ _ initValues _ _ _ _ resultSlot =>
        match initValues[resultSlot]? with
        | some init => init.eval module_ store
        | none => 0
    | .rangeFoldMultiSlot _ _ _ _ initValues _ _ _ _ resultSlot =>
        match initValues[resultSlot]? with
        | some init => init.eval module_ store
        | none => 0
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
    | .call slots index args, store =>
        let results :=
          match module_.getFunc? index with
          | some func => func.evalResults module_ (args.map (fun arg => arg.eval module_ store))
          | none => []
        (slots.zip results).foldl (fun current item => current.set item.fst item.snd) store
    | .arrayFoldMultiSlotAssign _ _ _ _ _ initValues _ _ _ _ targets, store =>
        (targets.zip (initValues.map (fun value => value.eval module_ store))).foldl
          (fun current item => current.set item.fst item.snd)
          store
    | .byteArrayFoldMultiSlotAssign _ _ _ _ _ initValues _ _ _ _ targets, store =>
        (targets.zip (initValues.map (fun value => value.eval module_ store))).foldl
          (fun current item => current.set item.fst item.snd)
          store
    | .rangeFoldMultiSlotAssign _ _ _ _ initValues _ _ _ _ targets, store =>
        (targets.zip (initValues.map (fun value => value.eval module_ store))).foldl
          (fun current item => current.set item.fst item.snd)
          store
    | .ite cond thenStmt elseStmt, store =>
        if cond.eval module_ store then
          thenStmt.eval module_ store
        else
          elseStmt.eval module_ store
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

  partial def Func.evalResults (func : Func) (module_ : Module) (args : List UInt64) :
      List UInt64 :=
    let store :=
      args.foldl
        (fun (state : Nat × Store) arg =>
          let index := state.fst
          (index + 1, state.snd.set index arg))
        (0, Store.empty)
    let store := func.body.eval module_ store.snd
    func.results.map (fun result => result.eval module_ store)

  partial def Func.eval (func : Func) (module_ : Module) (args : List UInt64) : UInt64 :=
    let results := func.evalResults module_ args
    match results with
    | result :: _ => result
    | [] => 0
end

def Module.evalFunc (module_ : Module) (index : Nat) (args : List UInt64) : UInt64 :=
  match module_.getFunc? index with
  | some func => func.eval module_ args
  | none => 0

end LeanExe.IR
