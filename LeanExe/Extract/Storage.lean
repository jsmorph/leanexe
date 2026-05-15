import Lean
import LeanExe.Extract.Values
import LeanExe.IR.Core

open Lean

namespace LeanExe.Extract.Core

mutual
  partial def heapLoadValueAt (ptr : IRExpr) : Ty → Nat → Except String (ExtractedValue × Nat)
    | .unit, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .bool, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .u8, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .u32, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .u64, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .nat, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .array item, slot =>
        if supportedArrayElementType item then
          .ok
            (.array
              (.heapLoadSlot ptr slot)
              (.heapLoadSlot ptr (slot + 1)),
              slot + 2)
        else
          .error s!"unsupported heap field array type: {reprStr ((.array item : Ty))}"
    | .byteArray, slot =>
        .ok
          (.byteArray
            (.heapLoadSlot ptr slot)
            (.heapLoadSlot ptr (slot + 1))
            (.heapLoadSlot ptr (slot + 2)),
            slot + 3)
    | .product left right, slot => do
        let leftLoaded ← heapLoadValueAt ptr left slot
        let rightLoaded ← heapLoadValueAt ptr right leftLoaded.snd
        .ok (.product leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .sum left right, slot => do
        let leftLoaded ← heapLoadValueAt ptr left (slot + 1)
        let rightLoaded ← heapLoadValueAt ptr right leftLoaded.snd
        .ok (.sum (.heapLoadSlot ptr slot) leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .struct name _ fields, slot => do
        let loaded ← heapLoadFieldsAt ptr fields slot
        .ok (.struct name loaded.fst, loaded.snd)
    | .variant name _ ctors, slot => do
        let loaded ← heapLoadCtorsAt ptr ctors (slot + 1)
        .ok (.variant name (.heapLoadSlot ptr slot) loaded.fst, loaded.snd)
    | .recVariant name _, slot => .ok (.heapVariant name (.heapLoadSlot ptr slot), slot + 1)

  partial def heapLoadFieldsAt (ptr : IRExpr) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← heapLoadValueAt ptr field slot
        let tail ← heapLoadFieldsAt ptr rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def heapLoadCtorsAt (ptr : IRExpr) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← heapLoadFieldsAt ptr fields slot
        let tail ← heapLoadCtorsAt ptr rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

partial def flattenFieldsFromKinds
    (typeName : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String (List IRExpr) := do
  let rec loop :
      List (Option Ty) → List ExtractedValue → List (List IRExpr) →
        Except String (List IRExpr)
    | [], [], acc => .ok acc.reverse.flatten
    | [], _ :: _, _ => .error s!"too many runtime fields for {typeName}"
    | some ty :: restKinds, field :: restFields, acc => do
        let flattened ← flattenInternalValue ty field
        loop restKinds restFields (flattened :: acc)
    | some _ :: _, [], _ => .error s!"too few runtime fields for {typeName}"
    | none :: restKinds, fields, acc =>
        loop restKinds fields acc
  loop fieldKinds runtimeFields []

partial def defaultCtorSlotValues (ctors : List VariantCtorLayout) :
    Except String (List (List IRExpr)) :=
  ctors.mapM fun ctor => do
    let defaults ← runtimeTypesFromKinds ctor.fields |>.mapM defaultValue
    flattenFieldsFromKinds ctor.name ctor.fields defaults

partial def heapRuntimeFieldsFromKinds
    (ptr : IRExpr)
    (fieldKinds : List (Option Ty))
    (slot : Nat) :
    Except String (List ExtractedValue × Nat) :=
  let rec loop :
      List (Option Ty) → Nat → List ExtractedValue →
        Except String (List ExtractedValue × Nat)
    | [], next, acc => .ok (acc.reverse, next)
    | some ty :: rest, next, acc => do
        let loaded ← heapLoadValueAt ptr ty next
        loop rest loaded.snd (loaded.fst :: acc)
    | none :: rest, next, acc =>
        loop rest next acc
  loop fieldKinds slot []

partial def flattenArrayElementValue
    (ty : Ty)
    (value : ExtractedValue) :
    Except String (List IRExpr) :=
  match ty with
  | .unit => scalarValue value |>.map (fun expr => [expr])
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [expr])
  | .u32 => scalarValue value |>.map (fun expr => [expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .byteArray => do
      let parts ← byteArrayFullParts value
      .ok [parts.owner, parts.ptr, parts.len]
  | .array item =>
      if supportedArrayElementType item then do
        let parts ← arrayFullParts value
        .ok [parts.owner, parts.ptr]
      else
        .error s!"unsupported array element value type: {reprStr ((.array item : Ty))}"
  | .recVariant name _ =>
      match value with
      | .heapVariant actual ptr =>
          if actual == name then
            .ok [ptr]
          else
            .error s!"recursive inductive array element shape mismatch: {name}"
      | .recursiveVariant actual tag ctors =>
          if actual == name then do
            let flattened ← ctors.mapM fun fields =>
              fields.mapM (fun field => flattenInternalValue field.fst field.snd)
            .ok [(.heapAllocSlots (heapChildMaskForCtors ctors) (tag :: flattened.flatten.flatten))]
          else
            .error s!"recursive inductive array element shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ =>
          .error s!"non-recursive value used where recursive inductive array element is required: {name}"
  | .product left right =>
      match value with
      | .product leftValue rightValue => do
          let leftSlots ← flattenArrayElementValue left leftValue
          let rightSlots ← flattenArrayElementValue right rightValue
          .ok (leftSlots ++ rightSlots)
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ => .error "non-product value used where product array element is required"
  | .sum left right =>
      match value with
      | .sum tag leftValue rightValue => do
          let leftSlots ← flattenArrayElementValue left leftValue
          let rightSlots ← flattenArrayElementValue right rightValue
          .ok (tag :: leftSlots ++ rightSlots)
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ => .error "non-sum value used where sum array element is required"
  | .struct name _ fields =>
      match value with
      | .struct actual values =>
          if actual == name && values.length == fields.length then do
            let flattened ← (fields.zip values).mapM fun item =>
              flattenArrayElementValue item.fst item.snd
            .ok flattened.flatten
          else
            .error s!"structure array element shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ =>
          .error s!"non-structure value used where structure array element is required: {name}"
  | .variant name _ ctors =>
      match value with
      | .variant actual tag values =>
          if actual == name && values.length == ctors.length then do
            let flattened ← (ctors.zip values).mapM fun ctorPair =>
              if ctorPair.fst.length == ctorPair.snd.length then do
                let fields ← (ctorPair.fst.zip ctorPair.snd).mapM (fun item =>
                  flattenArrayElementValue item.fst item.snd)
                .ok fields.flatten
              else
                .error s!"inductive array element payload shape mismatch: {name}"
            .ok (tag :: flattened.flatten)
          else
            .error s!"inductive array element shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ => .error s!"non-inductive value used where inductive array element is required: {name}"

partial def materializeStrictSlotsWith
    (flatten : ExtractedValue → Except String (List IRExpr))
    (value : ExtractedValue)
    (nextLocal : Nat) :
    Except String StrictSlots := do
  match value with
  | .letE slot expr body => do
      let result ← materializeStrictSlotsWith flatten body nextLocal
      .ok { result with lets := .expr slot expr :: result.lets }
  | .letCall slots index args body => do
      let result ← materializeStrictSlotsWith flatten body nextLocal
      .ok { result with lets := .call slots index args :: result.lets }
  | .letLocal _ _ =>
      .ok { lets := [], slots := ← flatten value, nextLocal := nextLocal }
  | _ =>
      .ok { lets := [], slots := ← flatten value, nextLocal := nextLocal }

def materializeStrictInternalSlots
    (ty : Ty)
    (value : ExtractedValue)
    (nextLocal : Nat) :
    Except String StrictSlots :=
  materializeStrictSlotsWith (flattenInternalValue ty) value nextLocal

def materializeStrictArrayElementSlots
    (ty : Ty)
    (value : ExtractedValue)
    (nextLocal : Nat) :
    Except String StrictSlots :=
  materializeStrictSlotsWith (flattenArrayElementValue ty) value nextLocal

mutual
  partial def arrayLoadValueAt
      (width : Nat)
      (array index : IRExpr) :
      Ty → Nat → Except String (ExtractedValue × Nat)
    | .unit, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .bool, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .u8, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .u32, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .u64, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .nat, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .byteArray, slot =>
        .ok
          (.byteArray
            (.arrayGetSlot width slot array index)
            (.arrayGetSlot width (slot + 1) array index)
            (.arrayGetSlot width (slot + 2) array index),
            slot + 3)
    | .array item, slot =>
        if supportedArrayElementType item then
          .ok
            (.array
              (.arrayGetSlot width slot array index)
              (.arrayGetSlot width (slot + 1) array index),
              slot + 2)
        else
          .error s!"unsupported array element load type: {reprStr ((.array item : Ty))}"
    | .recVariant name _, slot =>
        .ok (.heapVariant name (.arrayGetSlot width slot array index), slot + 1)
    | .product left right, slot => do
        let leftLoaded ← arrayLoadValueAt width array index left slot
        let rightLoaded ← arrayLoadValueAt width array index right leftLoaded.snd
        .ok (.product leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .sum left right, slot => do
        let leftLoaded ← arrayLoadValueAt width array index left (slot + 1)
        let rightLoaded ← arrayLoadValueAt width array index right leftLoaded.snd
        .ok (.sum (.arrayGetSlot width slot array index) leftLoaded.fst rightLoaded.fst,
          rightLoaded.snd)
    | .struct name _ fields, slot => do
        let result ← arrayLoadFieldsAt width array index fields slot
        .ok (.struct name result.fst, result.snd)
    | .variant name _ ctors, slot => do
        let tag := .arrayGetSlot width slot array index
        let result ← arrayLoadCtorsAt width array index ctors (slot + 1)
        .ok (.variant name tag result.fst, result.snd)

  partial def arrayLoadFieldsAt
      (width : Nat)
      (array index : IRExpr) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← arrayLoadValueAt width array index field slot
        let tail ← arrayLoadFieldsAt width array index rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def arrayLoadCtorsAt
      (width : Nat)
      (array index : IRExpr) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← arrayLoadFieldsAt width array index fields slot
        let tail ← arrayLoadCtorsAt width array index rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

def arrayLoadValue
    (itemTy : Ty)
    (array index : IRExpr) :
    Except String ExtractedValue := do
  let width ←
    match arrayElementSlots? itemTy with
    | some width => .ok width
    | none => .error s!"unsupported array element type: {reprStr itemTy}"
  let loaded ← arrayLoadValueAt width array index itemTy 0
  .ok loaded.fst

mutual
  partial def arrayFindValueAt
      (width : Nat)
      (array : IRExpr)
      (itemStart : Nat)
      (predicate : IRExpr) :
      Ty → Nat → Except String (ExtractedValue × Nat)
    | .unit, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .bool, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .u8, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .u32, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .u64, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .nat, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .byteArray, slot =>
        .ok
          (.byteArray
            (.arrayFindSlot width array itemStart predicate slot)
            (.arrayFindSlot width array itemStart predicate (slot + 1))
            (.arrayFindSlot width array itemStart predicate (slot + 2)),
            slot + 3)
    | .array item, slot =>
        if supportedArrayElementType item then
          .ok
            (.array
              (.arrayFindSlot width array itemStart predicate slot)
              (.arrayFindSlot width array itemStart predicate (slot + 1)),
              slot + 2)
        else
          .error s!"unsupported array find element type: {reprStr ((.array item : Ty))}"
    | .recVariant name _, slot =>
        .ok (.heapVariant name (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .product left right, slot => do
        let leftLoaded ← arrayFindValueAt width array itemStart predicate left slot
        let rightLoaded ← arrayFindValueAt width array itemStart predicate right leftLoaded.snd
        .ok (.product leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .sum left right, slot => do
        let leftLoaded ← arrayFindValueAt width array itemStart predicate left (slot + 1)
        let rightLoaded ← arrayFindValueAt width array itemStart predicate right leftLoaded.snd
        .ok (.sum (.arrayFindSlot width array itemStart predicate slot) leftLoaded.fst
          rightLoaded.fst, rightLoaded.snd)
    | .struct name _ fields, slot => do
        let result ← arrayFindFieldsAt width array itemStart predicate fields slot
        .ok (.struct name result.fst, result.snd)
    | .variant name _ ctors, slot => do
        let tag := .arrayFindSlot width array itemStart predicate slot
        let result ← arrayFindCtorsAt width array itemStart predicate ctors (slot + 1)
        .ok (.variant name tag result.fst, result.snd)

  partial def arrayFindFieldsAt
      (width : Nat)
      (array : IRExpr)
      (itemStart : Nat)
      (predicate : IRExpr) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← arrayFindValueAt width array itemStart predicate field slot
        let tail ← arrayFindFieldsAt width array itemStart predicate rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def arrayFindCtorsAt
      (width : Nat)
      (array : IRExpr)
      (itemStart : Nat)
      (predicate : IRExpr) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← arrayFindFieldsAt width array itemStart predicate fields slot
        let tail ← arrayFindCtorsAt width array itemStart predicate rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

def arrayFindValue
    (itemTy : Ty)
    (width : Nat)
    (array : IRExpr)
    (itemStart : Nat)
    (predicate : IRExpr) :
    Except String ExtractedValue := do
  let loaded ← arrayFindValueAt width array itemStart predicate itemTy 0
  .ok loaded.fst

mutual
  partial def arrayLocalValueAt (start : Nat) :
      Ty → Nat → Except String (ExtractedValue × Nat)
    | .unit, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .bool, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .u8, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .u32, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .u64, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .nat, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .byteArray, slot =>
        .ok
          (.byteArray
            (.local (start + slot))
            (.local (start + slot + 1))
            (.local (start + slot + 2)),
            slot + 3)
    | .array item, slot =>
        if supportedArrayElementType item then
          .ok (.array (.local (start + slot)) (.local (start + slot + 1)), slot + 2)
        else
          .error s!"unsupported array local element type: {reprStr ((.array item : Ty))}"
    | .recVariant name _, slot => .ok (.heapVariant name (.local (start + slot)), slot + 1)
    | .product left right, slot => do
        let leftLoaded ← arrayLocalValueAt start left slot
        let rightLoaded ← arrayLocalValueAt start right leftLoaded.snd
        .ok (.product leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .sum left right, slot => do
        let leftLoaded ← arrayLocalValueAt start left (slot + 1)
        let rightLoaded ← arrayLocalValueAt start right leftLoaded.snd
        .ok (.sum (.local (start + slot)) leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .struct name _ fields, slot => do
        let result ← arrayLocalFieldsAt start fields slot
        .ok (.struct name result.fst, result.snd)
    | .variant name _ ctors, slot => do
        let tag := .local (start + slot)
        let result ← arrayLocalCtorsAt start ctors (slot + 1)
        .ok (.variant name tag result.fst, result.snd)

  partial def arrayLocalFieldsAt (start : Nat) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← arrayLocalValueAt start field slot
        let tail ← arrayLocalFieldsAt start rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def arrayLocalCtorsAt (start : Nat) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← arrayLocalFieldsAt start fields slot
        let tail ← arrayLocalCtorsAt start rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

def arrayLocalValue (itemTy : Ty) (start : Nat) : Except String ExtractedValue := do
  let loaded ← arrayLocalValueAt start itemTy 0
  .ok loaded.fst

mutual
  partial def valueFromInternalSlotsAt (slotExpr : Nat → IRExpr) :
      Ty → Nat → ExtractedValue × Nat
    | .array item, slot =>
        if supportedArrayElementType item then
          (.array (slotExpr slot) (slotExpr (slot + 1)), slot + 2)
        else
          (.scalar .trap, slot + 1)
    | .byteArray, slot =>
        (.byteArray (slotExpr slot) (slotExpr (slot + 1)) (slotExpr (slot + 2)), slot + 3)
    | .product left right, slot =>
        let leftValue := valueFromInternalSlotsAt slotExpr left slot
        let rightValue := valueFromInternalSlotsAt slotExpr right leftValue.snd
        (.product leftValue.fst rightValue.fst, rightValue.snd)
    | .sum left right, slot =>
        let leftValue := valueFromInternalSlotsAt slotExpr left (slot + 1)
        let rightValue := valueFromInternalSlotsAt slotExpr right leftValue.snd
        (.sum (slotExpr slot) leftValue.fst rightValue.fst, rightValue.snd)
    | .struct name _ fields, slot =>
        let fieldsValue := valuesFromInternalSlotsAt slotExpr fields slot
        (.struct name fieldsValue.fst, fieldsValue.snd)
    | .variant name _ ctors, slot =>
        let ctorsValue := ctorValuesFromInternalSlotsAt slotExpr ctors (slot + 1)
        (.variant name (slotExpr slot) ctorsValue.fst, ctorsValue.snd)
    | .recVariant name _, slot =>
        (.heapVariant name (slotExpr slot), slot + 1)
    | _, slot =>
        (.scalar (slotExpr slot), slot + 1)

  partial def valuesFromInternalSlotsAt (slotExpr : Nat → IRExpr) :
      List Ty → Nat → List ExtractedValue × Nat
    | [], slot => ([], slot)
    | ty :: rest, slot =>
        let head := valueFromInternalSlotsAt slotExpr ty slot
        let tail := valuesFromInternalSlotsAt slotExpr rest head.snd
        (head.fst :: tail.fst, tail.snd)

  partial def ctorValuesFromInternalSlotsAt (slotExpr : Nat → IRExpr) :
      List (List Ty) → Nat → List (List ExtractedValue) × Nat
    | [], slot => ([], slot)
    | fields :: rest, slot =>
        let head := valuesFromInternalSlotsAt slotExpr fields slot
        let tail := ctorValuesFromInternalSlotsAt slotExpr rest head.snd
        (head.fst :: tail.fst, tail.snd)
end

def valueFromInternalSlots (ty : Ty) (slotExpr : Nat → IRExpr) : ExtractedValue :=
  (valueFromInternalSlotsAt slotExpr ty 0).fst

def arrayElementWidth (context : String) (itemTy : Ty) : Except String Nat :=
  match arrayElementSlots? itemTy with
  | some width => .ok width
  | none => .error s!"unsupported {context} item type: {reprStr itemTy}"

mutual
  partial def extractedValueForParam (slot : Nat) : Ty → ExtractedValue
    | .u8 => .scalar (u8WrapExpr (.local slot))
    | .u32 => .scalar (u32WrapExpr (.local slot))
    | .byteArray => .byteArray (.u64 0) (.local slot) (.local (slot + 1))
    | .array item =>
        if supportedArrayElementType item then
          .array (.u64 0) (.local slot)
        else
          .scalar .trap
    | .sum left right =>
        .sum (.local slot)
          (extractedValueForParam (slot + 1) left)
          (extractedValueForParam (slot + 1 + abiSlots left) right)
    | .struct name _ fields => .struct name (extractedStructFieldsForParam slot fields)
    | .variant name _ ctors =>
        .variant name (.local slot) (extractedVariantCtorsForParam (slot + 1) ctors)
    | .recVariant name _ => .heapVariant name (.local slot)
    | _ => .scalar (.local slot)

  partial def extractedStructFieldsForParam (slot : Nat) : List Ty → List ExtractedValue
    | [] => []
    | ty :: rest =>
        extractedValueForParam slot ty :: extractedStructFieldsForParam (slot + abiSlots ty) rest

  partial def extractedVariantCtorsForParam (slot : Nat) :
      List (List Ty) → List (List ExtractedValue)
    | [] => []
    | fields :: rest =>
        extractedStructFieldsForParam slot fields ::
          extractedVariantCtorsForParam
            (slot + fields.foldl (fun total field => total + abiSlots field) 0)
            rest
end

def bindingForParam (slot : Nat) : Ty → Binding
  | .u8 => .value (.scalar (u8WrapExpr (.local slot)))
  | .u32 => .value (.scalar (u32WrapExpr (.local slot)))
  | .byteArray => .value (.byteArray (.u64 0) (.local slot) (.local (slot + 1)))
  | .array item =>
      if supportedArrayElementType item then
        .value (.array (.u64 0) (.local slot))
      else
        .value (.scalar .trap)
  | .sum left right =>
      .value
        (.sum (.local slot)
          (extractedValueForParam (slot + 1) left)
          (extractedValueForParam (slot + 1 + abiSlots left) right))
  | .struct name _ fields => .value (.struct name (extractedStructFieldsForParam slot fields))
  | .variant name _ ctors =>
      .value (.variant name (.local slot) (extractedVariantCtorsForParam (slot + 1) ctors))
  | .recVariant name _ => .value (.heapVariant name (.local slot))
  | _ => .slot slot

def bindingForInternalParam (slot : Nat) (ty : Ty) : Binding :=
  .value (valueFromInternalSlots ty fun offset => .local (slot + offset))

partial def sourceParamBindingsFrom (slot : Nat) : List Ty → List Binding
  | [] => []
  | ty :: rest => bindingForParam slot ty :: sourceParamBindingsFrom (slot + abiSlots ty) rest

def sourceParamBindings (params : List Ty) : List Binding :=
  sourceParamBindingsFrom 0 params

partial def internalParamBindingsFrom (slot : Nat) : List Ty → List Binding
  | [] => []
  | ty :: rest =>
      bindingForInternalParam slot ty :: internalParamBindingsFrom (slot + internalSlots ty) rest

def internalParamBindings (params : List Ty) : List Binding :=
  internalParamBindingsFrom 0 params

def functionParamBindings (useAbi : Bool) (params : List Ty) : List Binding :=
  if useAbi then sourceParamBindings params else internalParamBindings params

partial def abiTargetsFrom (slot : Nat) : List Ty → List (Ty × List Nat)
  | [] => []
  | ty :: rest =>
      let slots := (List.range (abiSlots ty)).map (fun offset => slot + offset)
      (ty, slots) :: abiTargetsFrom (slot + abiSlots ty) rest

def abiTargets (params : List Ty) : List (Ty × List Nat) :=
  abiTargetsFrom 0 params

partial def internalTargetsFrom (slot : Nat) : List Ty → List (Ty × List Nat)
  | [] => []
  | ty :: rest =>
      let slots := (List.range (internalSlots ty)).map (fun offset => slot + offset)
      (ty, slots) :: internalTargetsFrom (slot + internalSlots ty) rest

def internalTargets (params : List Ty) : List (Ty × List Nat) :=
  internalTargetsFrom 0 params

def functionParamTargets (useAbi : Bool) (params : List Ty) : List (Ty × List Nat) :=
  if useAbi then abiTargets params else internalTargets params

def sourceFieldBindingsFromKinds
    (typeName : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String (List Binding) := do
  let rec loop :
      List (Option Ty) → List ExtractedValue → List Binding →
        Except String (List Binding)
    | [], [], acc => .ok acc.reverse
    | [], _ :: _, _ => .error s!"too many runtime fields for {typeName}"
    | some _ :: restKinds, field :: restFields, acc =>
        loop restKinds restFields (.value field :: acc)
    | some _ :: _, [], _ => .error s!"too few runtime fields for {typeName}"
    | none :: restKinds, fields, acc =>
        loop restKinds fields (.value (.scalar (.u64 0)) :: acc)
  loop fieldKinds runtimeFields []

partial def defaultCtorValues (ctors : List VariantCtorLayout) :
    Except String (List (List ExtractedValue)) :=
  ctors.mapM fun ctor => runtimeTypesFromKinds ctor.fields |>.mapM defaultValue

def typedFieldsFromKinds
    (typeName : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String (List (Ty × ExtractedValue)) := do
  let rec loop :
      List (Option Ty) → List ExtractedValue → List (Ty × ExtractedValue) →
        Except String (List (Ty × ExtractedValue))
    | [], [], acc => .ok acc.reverse
    | [], _ :: _, _ => .error s!"too many runtime fields for {typeName}"
    | some ty :: restKinds, field :: restFields, acc =>
        loop restKinds restFields ((ty, field) :: acc)
    | some _ :: _, [], _ => .error s!"too few runtime fields for {typeName}"
    | none :: restKinds, fields, acc =>
        loop restKinds fields acc
  loop fieldKinds runtimeFields []

partial def defaultCtorTypedValues (ctors : List VariantCtorLayout) :
    Except String (List (List (Ty × ExtractedValue))) :=
  ctors.mapM fun ctor => do
    let values ← runtimeTypesFromKinds ctor.fields |>.mapM fun ty => do
      let value ← defaultValue ty
      .ok (ty, value)
    .ok values

end LeanExe.Extract.Core
