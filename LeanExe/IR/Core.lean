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
  | struct (name : Lean.Name) (params : List Ty) (fields : List Ty)
  | variant (name : Lean.Name) (params : List Ty) (ctors : List (List Ty))
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

inductive RuntimeStat where
  | allocs
  | retains
  | releases
  | frees
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
    | letLets (lets : List LocalLet) (body : Expr)
    | runtimeStat (stat : RuntimeStat)
    | release (ptr : Expr)
    | arrayAllocSlots (width : Nat) (cells : Expr)
    | heapAllocSlots (childMask : Nat) (values : List Expr)
    | heapLoadSlot (ptr : Expr) (slot : Nat)
    | arrayReplicateSlots (width : Nat) (cells : Expr) (values : List Expr)
    | arraySize (array : Expr)
    | arrayGetSlot (width slot : Nat) (array index : Expr)
    | arraySetSlots (width : Nat) (array index : Expr) (values : List Expr)
    | arrayPushSlots (width : Nat) (array : Expr) (values : List Expr)
    | arrayPopSlots (width : Nat) (array : Expr)
    | arrayAppendSlots (width : Nat) (left right : Expr)
    | arrayExtractSlots (width : Nat) (array start stop : Expr)
    | arrayMapSlots (sourceWidth resultWidth : Nat) (array : Expr) (itemStart : Nat)
        (bodyValues : List Expr)
    | arrayFoldMultiSlot (sourceWidth resultWidth : Nat) (array start stop : Expr)
        (initValues : List Expr) (accStart itemStart : Nat) (bodyValues : List Expr)
        (bodyLets : List LocalLet) (bodyDone : Expr) (resultSlot : Nat)
    | arrayFindIdxSlots (sourceWidth : Nat) (array : Expr) (itemStart : Nat)
        (predicate : Expr) (returnPayload : Bool)
    | arrayFindSlot (sourceWidth : Nat) (array : Expr) (itemStart : Nat)
        (predicate : Expr) (slot : Nat)
    | arrayEqSlots (width : Nat) (left right : Expr) (leftStart rightStart : Nat)
        (predicate : Expr)
    | arrayAnySlots (sourceWidth : Nat) (array start stop : Expr) (itemStart : Nat)
        (predicate : Expr) (forAll : Bool)
    | arrayFilterSlots (sourceWidth : Nat) (array start stop : Expr) (itemStart : Nat)
        (predicate : Expr)
    | arrayInsertIfInBoundsSlots (width : Nat) (array index : Expr) (values : List Expr)
    | arrayEraseIfInBoundsSlots (width : Nat) (array index : Expr)
    | arraySwapIfInBoundsSlots (width : Nat) (array left right : Expr)
    | arrayReverseSlots (width : Nat) (array : Expr)
    | byteArrayGet (ptr len index : Expr)
    | byteArrayPushPtr (ptr len value : Expr)
    | byteArrayAppendPtr (leftPtr leftLen rightPtr rightLen : Expr)
    | byteArraySetPtr (ptr len index value : Expr)
    | byteArrayFromArrayPtr (array : Expr)
    | byteArrayCopySlicePtr
        (srcPtr srcLen srcOff destPtr destLen destOff copyLen : Expr)
    | byteArrayEq (leftPtr leftLen rightPtr rightLen : Expr)
    | byteArrayFindIdx (ptr len start : Expr) (byteSlot : Nat) (predicate : Expr)
        (returnPayload : Bool)
    | byteArrayFoldMultiSlot (resultWidth : Nat) (ptr len start stop : Expr)
        (initValues : List Expr) (accStart byteSlot : Nat) (bodyValues : List Expr)
        (bodyLets : List LocalLet) (bodyDone : Expr) (resultSlot : Nat)
    | rangeFoldMultiSlot (resultWidth : Nat) (start stop step : Expr)
        (initValues : List Expr) (accStart itemSlot : Nat) (bodyValues : List Expr)
        (bodyLets : List LocalLet) (bodyDone : Expr) (resultSlot : Nat)
    | heapLinearPredicate (ptr : Expr)
        (continueTag fieldSlotCount recursiveFieldOffset fieldStart : Nat)
        (predicate : Expr) (stopWhenTrue terminalValue : Bool)
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

  inductive LocalLet where
    | expr (slot : Nat) (value : Expr)
    | call (slots : List Nat) (index : Nat) (args : List Expr)
    | slots (slots : List Nat) (values : List Expr)
    | branch (cond : Cond) (thenLets elseLets : List LocalLet)
    deriving BEq, Repr
end

mutual
  inductive Stmt where
    | skip
    | assign (index : Nat) (value : Expr)
    | call (slots : List Nat) (index : Nat) (args : List Expr)
    | release (ptr : Expr)
    | arrayFoldMultiSlotAssign (sourceWidth resultWidth : Nat) (array start stop : Expr)
        (initValues : List Expr) (accStart itemStart : Nat) (bodyValues : List Expr)
        (bodyLets : List LocalLet) (bodyDone : Expr) (targets : List Nat)
    | byteArrayFoldMultiSlotAssign (resultWidth : Nat) (ptr len start stop : Expr)
        (initValues : List Expr) (accStart byteSlot : Nat) (bodyValues : List Expr)
        (bodyLets : List LocalLet) (bodyDone : Expr) (targets : List Nat)
    | rangeFoldMultiSlotAssign (resultWidth : Nat) (start stop step : Expr)
        (initValues : List Expr) (accStart itemSlot : Nat) (bodyValues : List Expr)
        (bodyLets : List LocalLet) (bodyDone : Expr) (targets : List Nat)
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
    | .letLets lets body => body.eval module_ (evalLocalLets module_ lets store)
    | .runtimeStat _ => 0
    | .release _ => 0
    | .arrayAllocSlots _ _ => 0
    | .heapAllocSlots _ _ => 0
    | .heapLoadSlot _ _ => 0
    | .arrayReplicateSlots _ _ _ => 0
    | .arraySize _ => 0
    | .arrayGetSlot _ _ _ _ => 0
    | .arraySetSlots _ array _ _ => array.eval module_ store
    | .arrayPushSlots _ array _ => array.eval module_ store
    | .arrayPopSlots _ array => array.eval module_ store
    | .arrayAppendSlots _ left _ => left.eval module_ store
    | .arrayExtractSlots _ array _ _ => array.eval module_ store
    | .arrayMapSlots _ _ array _ _ => array.eval module_ store
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone resultSlot =>
        let resultStore :=
          evalCountedFold module_ resultWidth initValues accStart itemStart sourceWidth
            (fun _index => 0)
            (start.eval module_ store)
            (min (stop.eval module_ store) ((.arraySize array : Expr).eval module_ store))
            1 bodyValues bodyLets bodyDone store
        resultStore (accStart + resultSlot)
    | .arrayFindIdxSlots _ _ _ _ _ => 0
    | .arrayFindSlot _ _ _ _ _ => 0
    | .arrayEqSlots _ _ _ _ _ _ => 0
    | .arrayAnySlots _ _ _ _ _ _ forAll => if forAll then 1 else 0
    | .arrayFilterSlots _ array _ _ _ _ => array.eval module_ store
    | .arrayInsertIfInBoundsSlots _ array _ _ => array.eval module_ store
    | .arrayEraseIfInBoundsSlots _ array _ => array.eval module_ store
    | .arraySwapIfInBoundsSlots _ array _ _ => array.eval module_ store
    | .arrayReverseSlots _ array => array.eval module_ store
    | .byteArrayGet _ _ _ => 0
    | .byteArrayPushPtr ptr _ _ => ptr.eval module_ store
    | .byteArrayAppendPtr leftPtr _ _ _ => leftPtr.eval module_ store
    | .byteArraySetPtr ptr _ _ _ => ptr.eval module_ store
    | .byteArrayFromArrayPtr array => array.eval module_ store
    | .byteArrayCopySlicePtr _ _ _ destPtr _ _ _ => destPtr.eval module_ store
    | .byteArrayEq _ _ _ _ => 0
    | .byteArrayFindIdx _ _ _ _ _ _ => 0
    | .byteArrayFoldMultiSlot resultWidth _ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone resultSlot =>
        let resultStore :=
          evalCountedFold module_ resultWidth initValues accStart byteSlot 1
            (fun _index => 0)
            (start.eval module_ store)
            (min (stop.eval module_ store) (len.eval module_ store))
            1 bodyValues bodyLets bodyDone store
        resultStore (accStart + resultSlot)
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone resultSlot =>
        let resultStore :=
          evalCountedFold module_ resultWidth initValues accStart itemSlot 1
            (fun index => index)
            (start.eval module_ store) (stop.eval module_ store) (step.eval module_ store)
            bodyValues bodyLets bodyDone store
        resultStore (accStart + resultSlot)
    | .heapLinearPredicate _ _ _ _ _ _ _ terminalValue => if terminalValue then 1 else 0
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

  partial def assignValues (module_ : Module) (targets : List Nat) (values : List Expr)
      (store : Store) : Store :=
    (targets.zip values).foldl
      (fun current item => current.set item.fst (item.snd.eval module_ current))
      store

  partial def setSlotsToZero (start width : Nat) (store : Store) : Store :=
    (List.range width).foldl
      (fun current offset => current.set (start + offset) 0)
      store

  partial def setSlotsFromValues (start : Nat) (values : List UInt64) (store : Store) :
      Store :=
    (List.range values.length).zip values |>.foldl
      (fun current item => current.set (start + item.fst) item.snd)
      store

  partial def evalLocalLet (module_ : Module) (localLet : LocalLet) (store : Store) :
      Store :=
    match localLet with
    | .expr slot value => store.set slot (value.eval module_ store)
    | .call slots index args =>
        let results :=
          match module_.getFunc? index with
          | some func => func.evalResults module_ (args.map (fun arg => arg.eval module_ store))
          | none => []
        (slots.zip results).foldl (fun current item => current.set item.fst item.snd) store
    | .slots slots values => assignValues module_ slots values store
    | .branch cond thenLets elseLets =>
        if cond.eval module_ store then
          evalLocalLets module_ thenLets store
        else
          evalLocalLets module_ elseLets store

  partial def evalLocalLets (module_ : Module) (lets : List LocalLet) (store : Store) :
      Store :=
    lets.foldl (fun current localLet => evalLocalLet module_ localLet current) store

  partial def evalCountedFold
      (module_ : Module)
      (resultWidth : Nat)
      (initValues : List Expr)
      (accStart itemStart itemWidth : Nat)
      (itemValue : UInt64 → UInt64)
      (start stop step : UInt64)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (store : Store) : Store :=
    let initStore :=
      assignValues module_ ((List.range resultWidth).map fun offset => accStart + offset)
        initValues store
    let rec loop : Nat → UInt64 → Store → Store
      | 0, _, current => current
      | fuel + 1, index, current =>
          if index >= stop then
            current
          else
            let itemStore :=
              if itemWidth == 1 then
                current.set itemStart (itemValue index)
              else
                setSlotsToZero itemStart itemWidth current
            let letStore := evalLocalLets module_ bodyLets itemStore
            let nextValues := bodyValues.map fun value => value.eval module_ letStore
            let nextStore := setSlotsFromValues accStart nextValues letStore
            if bodyDone.eval module_ letStore != 0 || step == 0 then
              nextStore
            else
              loop fuel (index + step) nextStore
    loop 1000000 start initStore

  partial def Stmt.eval (module_ : Module) : Stmt → Store → Store
    | .skip, store => store
    | .assign index value, store => store.set index (value.eval module_ store)
    | .call slots index args, store =>
        let results :=
          match module_.getFunc? index with
          | some func => func.evalResults module_ (args.map (fun arg => arg.eval module_ store))
          | none => []
        (slots.zip results).foldl (fun current item => current.set item.fst item.snd) store
    | .release _, store => store
    | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone targets, store =>
        let resultStore :=
          evalCountedFold module_ resultWidth initValues accStart itemStart sourceWidth
            (fun _index => 0)
            (start.eval module_ store)
            (min (stop.eval module_ store) ((.arraySize array : Expr).eval module_ store))
            1 bodyValues bodyLets bodyDone store
        (targets.zip (List.range resultWidth)).foldl
          (fun current item => current.set item.fst (resultStore (accStart + item.snd)))
          store
    | .byteArrayFoldMultiSlotAssign resultWidth _ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone targets, store =>
        let resultStore :=
          evalCountedFold module_ resultWidth initValues accStart byteSlot 1
            (fun _index => 0)
            (start.eval module_ store)
            (min (stop.eval module_ store) (len.eval module_ store))
            1 bodyValues bodyLets bodyDone store
        (targets.zip (List.range resultWidth)).foldl
          (fun current item => current.set item.fst (resultStore (accStart + item.snd)))
          store
    | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone targets, store =>
        let resultStore :=
          evalCountedFold module_ resultWidth initValues accStart itemSlot 1
            (fun index => index)
            (start.eval module_ store) (stop.eval module_ store) (step.eval module_ store)
            bodyValues bodyLets bodyDone store
        (targets.zip (List.range resultWidth)).foldl
          (fun current item => current.set item.fst (resultStore (accStart + item.snd)))
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
