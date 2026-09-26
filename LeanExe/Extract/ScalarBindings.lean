import LeanExe.Util.ListRelation
import LeanExe.Source.ScalarValues
import LeanExe.IR.ScalarSemantics

namespace LeanExe.Extract.Core

/-- Compile-time lexical bindings. A function closes over compiled bindings;
its application recursively compiles only its original, smaller source body. -/
inductive ScalarBinding where
  | word (expression : LeanExe.IR.Expr)
  | boolean (expression : LeanExe.IR.Expr)
  | natural (expression : LeanExe.IR.Expr)
  | unit
  | function (withUnit : Bool) (apply : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | booleanFunction (apply : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | binaryFunction (apply : LeanExe.IR.Expr → LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | manyFunction (arity : Nat) (apply : List LeanExe.IR.Expr → Option LeanExe.IR.Expr)

def ScalarBinding.kind : ScalarBinding → LeanExe.Source.Scalar.BindingKind
  | .word _ => .word
  | .boolean _ => .boolean
  | .natural _ => .natural
  | .unit => .unit
  | .function withUnit _ => .function withUnit
  | .booleanFunction _ => .booleanFunction
  | .binaryFunction _ => .binaryFunction
  | .manyFunction arity _ => .manyFunction arity

def ScalarBinding.word? : ScalarBinding → Option LeanExe.IR.Expr
  | .word expression => some expression
  | .boolean _ | .natural _ | .unit | .function _ _ | .booleanFunction _ | .binaryFunction _ | .manyFunction _ _ => none

def ScalarBinding.boolean? : ScalarBinding → Option LeanExe.IR.Expr
  | .boolean expression => some expression
  | _ => none

@[simp] theorem ScalarBinding.boolean?_some {binding : ScalarBinding} {target : LeanExe.IR.Expr} :
    binding.boolean? = some target ↔ binding = .boolean target := by
  cases binding <;> simp [boolean?]

/-- A Nat loop index is represented by its explicit UInt64 conversion. -/
def ScalarBinding.natural? : ScalarBinding → Option LeanExe.IR.Expr
  | .natural expression => some expression
  | _ => none

def ScalarBinding.function? (withUnit : Bool) : ScalarBinding → Option (LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | .function shape f => if shape == withUnit then some f else none
  | _ => none

@[simp] theorem ScalarBinding.word?_some {binding : ScalarBinding} {target : LeanExe.IR.Expr} :
    binding.word? = some target ↔ binding = .word target := by
  cases binding <;> simp [word?]

@[simp] theorem ScalarBinding.natural?_some {binding : ScalarBinding} {target : LeanExe.IR.Expr} :
    binding.natural? = some target ↔ binding = .natural target := by
  cases binding <;> simp [natural?]

@[simp] theorem ScalarBinding.function?_some {binding : ScalarBinding} {withUnit : Bool}
    {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr} :
    binding.function? withUnit = some f ↔ binding = .function withUnit f := by
  cases binding with
  | booleanFunction _ => simp [function?]
  | boolean _ | word _ | natural _ | unit | binaryFunction _ | manyFunction _ _ => simp [function?]
  | function shape g => cases shape <;> cases withUnit <;> simp [function?]

def ScalarBinding.Total : ScalarBinding → Prop
  | .word _ | .boolean _ | .natural _ => True
  | .unit => True
  | .function _ f => ∀ argument, ∃ target, f argument = some target
  | .booleanFunction f => ∀ argument, ∃ target, f argument = some target
  | .binaryFunction f => ∀ first second, ∃ target, f first second = some target
  | .manyFunction arity f => ∀ arguments, arguments.length = arity → ∃ target, f arguments = some target

def ScalarBinding.Holds (P : LeanExe.IR.Expr → Prop) : ScalarBinding → Prop
  | .word expression | .boolean expression | .natural expression => P expression
  | .unit => True
  | .function _ f => ∀ argument target, P argument → f argument = some target → P target
  | .booleanFunction f => ∀ argument target, P argument → f argument = some target → P target
  | .binaryFunction f => ∀ first second target, P first → P second → f first second = some target → P target
  | .manyFunction arity f => ∀ arguments target, arguments.length = arity →
      (∀ argument ∈ arguments, P argument) → f arguments = some target → P target

def ScalarBinding.Matches (store : LeanExe.IR.ScalarStore) :
    ScalarBinding → LeanExe.Source.Scalar.Value → Prop
  | .word expression, .word value => expression.ScalarEval store value store
  | .boolean expression, .boolean value => expression.ScalarEval store (Bool.toUInt64 value) store
  | .natural expression, .natural value => expression.ScalarEval store (UInt64.ofNat value) store
  | .unit, .unit => True
  | .function _ compile, .function _ apply =>
      ∀ argument value target, argument.ScalarEval store value store → compile argument = some target →
        target.ScalarEval store (apply value) store
  | .booleanFunction compile, .booleanFunction apply =>
      ∀ argument value target, argument.ScalarEval store (Bool.toUInt64 value) store → compile argument = some target →
        target.ScalarEval store (apply value) store
  | .binaryFunction compile, .binaryFunction apply =>
      ∀ first x second y target, first.ScalarEval store x store → second.ScalarEval store y store →
        compile first second = some target → target.ScalarEval store (apply x y) store
  | .manyFunction arity compile, .manyFunction _ apply =>
      ∀ arguments values target, arguments.length = arity →
        LeanExe.ListRelation (fun argument value => argument.ScalarEval store value store) arguments values →
        compile arguments = some target → target.ScalarEval store (apply values) store
  | _, _ => False

def ScalarBindingsMatch (locals : List ScalarBinding) (values : List LeanExe.Source.Scalar.Value)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index : Nat) (binding : ScalarBinding) (value : LeanExe.Source.Scalar.Value), locals[index]? = some binding → values[index]? = some value →
    binding.Matches store value

theorem ScalarBindingsMatch.cons {locals values store binding value}
    (tail : ScalarBindingsMatch locals values store) (head : binding.Matches store value) :
    ScalarBindingsMatch (binding :: locals) (value :: values) store := by
  intro index target source ht hs
  cases index with
  | zero => cases ht; cases hs; exact head
  | succ index => exact tail index target source ht hs

theorem ScalarBindingsMatch.word {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat} {target : LeanExe.IR.Expr} {value : UInt64}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarBinding.word?) = some target)
    (source : values[index]? = some (.word value)) : target.ScalarEval store value store := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.word?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem ScalarBindingsMatch.boolean {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat} {target : LeanExe.IR.Expr} {value : Bool}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarBinding.boolean?) = some target)
    (source : values[index]? = some (.boolean value)) : target.ScalarEval store (Bool.toUInt64 value) store := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.boolean?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem ScalarBindingsMatch.natural {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat} {target : LeanExe.IR.Expr} {value : Nat}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarBinding.natural?) = some target)
    (source : values[index]? = some (.natural value)) : target.ScalarEval store (UInt64.ofNat value) store := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.natural?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem ScalarBindingsMatch.function {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat}
    {compile : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {apply : UInt64 → UInt64} {withUnit : Bool}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind (ScalarBinding.function? withUnit)) = some compile)
    (source : values[index]? = some (.function withUnit apply)) :
    (ScalarBinding.function withUnit compile).Matches store (.function withUnit apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.function?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem scalarWord_kind {locals : List ScalarBinding} {index : Nat} {target : LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.word?) = some target) :
    (locals.map ScalarBinding.kind)[index]? = some .word := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.word?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarBoolean_kind {locals : List ScalarBinding} {index : Nat} {target : LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.boolean?) = some target) :
    (locals.map ScalarBinding.kind)[index]? = some .boolean := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.boolean?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarNatural_kind {locals : List ScalarBinding} {index : Nat} {target : LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.natural?) = some target) :
    (locals.map ScalarBinding.kind)[index]? = some .natural := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.natural?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarFunction_kind {locals : List ScalarBinding} {index : Nat} {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {withUnit : Bool}
    (found : (locals[index]?.bind (ScalarBinding.function? withUnit)) = some f) :
    (locals.map ScalarBinding.kind)[index]? = some (.function withUnit) := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.function?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarWord_lookup {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .word) :
    ∃ target, (locals[index]?.bind ScalarBinding.word?) = some target := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction _ => cases kind
  | word target => exact ⟨target, by simp [found, ScalarBinding.word?]⟩
  | boolean _ | natural _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem scalarBoolean_lookup {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .boolean) :
    ∃ target, (locals[index]?.bind ScalarBinding.boolean?) = some target := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction _ => cases kind
  | boolean target => exact ⟨target, by simp [found, ScalarBinding.boolean?]⟩
  | word _ | natural _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem scalarNatural_lookup {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .natural) :
    ∃ target, (locals[index]?.bind ScalarBinding.natural?) = some target := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction _ => cases kind
  | natural target => exact ⟨target, by simp [found, ScalarBinding.natural?]⟩
  | boolean _ | word _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem scalarFunction_lookup {locals : List ScalarBinding} {index : Nat} {withUnit : Bool}
    (present : (locals.map ScalarBinding.kind)[index]? = some (.function withUnit)) :
    ∃ f, locals[index]? = some (.function withUnit f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction _ => cases kind
  | boolean _ | word _ | natural _ | unit | binaryFunction _ | manyFunction _ _ => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

def ScalarBinding.booleanFunction? : ScalarBinding → Option (LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | .booleanFunction f => some f
  | _ => none

@[simp] theorem ScalarBinding.booleanFunction?_some {binding : ScalarBinding}
    {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr} :
    binding.booleanFunction? = some f ↔ binding = .booleanFunction f := by
  cases binding <;> simp [booleanFunction?]

theorem ScalarBindingsMatch.booleanFunction {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat}
    {compile : LeanExe.IR.Expr → Option LeanExe.IR.Expr}
    {apply : Bool → UInt64}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarBinding.booleanFunction?) = some compile)
    (source : values[index]? = some (.booleanFunction apply)) :
    (ScalarBinding.booleanFunction compile).Matches store (.booleanFunction apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.booleanFunction?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem scalarBooleanFunction_kind {locals : List ScalarBinding} {index : Nat}
    {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.booleanFunction?) = some f) :
    (locals.map ScalarBinding.kind)[index]? = some .booleanFunction := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.booleanFunction?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarBooleanFunction_lookup {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .booleanFunction) :
    ∃ f, locals[index]? = some (.booleanFunction f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction f => exact ⟨f, found⟩
  | boolean _ | word _ | natural _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem scalarBooleanFunction_not_word {locals : List ScalarBinding} {index : Nat}
    {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.booleanFunction?) = some f) :
    (locals[index]?.bind (ScalarBinding.function? false)) = none := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.booleanFunction?_some.mp matched
  subst binding
  simp [present, ScalarBinding.function?]

theorem ScalarBindingsMatch.no_booleanFunction_of_function
    {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat} {withUnit : Bool}
    {f : UInt64 → UInt64} (bindings : ScalarBindingsMatch locals values store)
    (source : values[index]? = some (.function withUnit f)) :
    (locals[index]?.bind ScalarBinding.booleanFunction?) = none := by
  cases found : locals[index]?.bind ScalarBinding.booleanFunction? with
  | none => rfl
  | some compile =>
    obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.booleanFunction?_some.mp matched
    subst binding
    exact False.elim (bindings index _ _ present source)

theorem ScalarBindingsMatch.no_wordFunction_of_boolean
    {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat}
    {f : Bool → UInt64} (bindings : ScalarBindingsMatch locals values store)
    (source : values[index]? = some (.booleanFunction f)) :
    (locals[index]?.bind (ScalarBinding.function? false)) = none := by
  cases found : locals[index]?.bind (ScalarBinding.function? false) with
  | none => rfl
  | some compile =>
    obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.function?_some.mp matched
    subst binding
    exact False.elim (bindings index _ _ present source)

def ScalarBinding.binaryFunction? : ScalarBinding → Option (LeanExe.IR.Expr → LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | .binaryFunction f => some f
  | _ => none

@[simp] theorem ScalarBinding.binaryFunction?_some {binding : ScalarBinding}
    {f : LeanExe.IR.Expr → LeanExe.IR.Expr → Option LeanExe.IR.Expr} :
    binding.binaryFunction? = some f ↔ binding = .binaryFunction f := by
  cases binding <;> simp [binaryFunction?]

theorem ScalarBindingsMatch.binaryFunction {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat}
    {compile : LeanExe.IR.Expr → LeanExe.IR.Expr → Option LeanExe.IR.Expr}
    {apply : UInt64 → UInt64 → UInt64}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarBinding.binaryFunction?) = some compile)
    (source : values[index]? = some (.binaryFunction apply)) :
    (ScalarBinding.binaryFunction compile).Matches store (.binaryFunction apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.binaryFunction?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem scalarBinaryFunction_kind {locals : List ScalarBinding} {index : Nat}
    {f : LeanExe.IR.Expr → LeanExe.IR.Expr → Option LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.binaryFunction?) = some f) :
    (locals.map ScalarBinding.kind)[index]? = some .binaryFunction := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.binaryFunction?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarBinaryFunction_lookup {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .binaryFunction) :
    ∃ f, locals[index]? = some (.binaryFunction f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction _ => cases kind
  | binaryFunction f => exact ⟨f, found⟩
  | boolean _ | word _ | natural _ | unit | function _ _ | manyFunction _ _ => cases kind

def ScalarBinding.manyFunction? (arity : Nat) : ScalarBinding → Option (List LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | .manyFunction count f => if count == arity then some f else none
  | _ => none

@[simp] theorem ScalarBinding.manyFunction?_some {binding : ScalarBinding} {arity : Nat}
    {f : List LeanExe.IR.Expr → Option LeanExe.IR.Expr} :
    binding.manyFunction? arity = some f ↔ binding = .manyFunction arity f := by
  cases binding with
  | booleanFunction _ => simp [manyFunction?]
  | manyFunction count g => by_cases same : count = arity <;> simp [manyFunction?, same]
  | boolean _ | word _ | natural _ | unit | function _ _ | binaryFunction _ => simp [manyFunction?]

theorem ScalarBindingsMatch.manyFunction {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index arity : Nat}
    {compile : List LeanExe.IR.Expr → Option LeanExe.IR.Expr} {apply : List UInt64 → UInt64}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind (ScalarBinding.manyFunction? arity)) = some compile)
    (source : values[index]? = some (.manyFunction arity apply)) :
    (ScalarBinding.manyFunction arity compile).Matches store (.manyFunction arity apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.manyFunction?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem scalarManyFunction_kind {locals : List ScalarBinding} {index arity : Nat}
    {f : List LeanExe.IR.Expr → Option LeanExe.IR.Expr}
    (found : (locals[index]?.bind (ScalarBinding.manyFunction? arity)) = some f) :
    (locals.map ScalarBinding.kind)[index]? = some (.manyFunction arity) := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.manyFunction?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarManyFunction_lookup {locals : List ScalarBinding} {index arity : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some (.manyFunction arity)) :
    ∃ f, locals[index]? = some (.manyFunction arity f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction _ => cases kind
  | manyFunction count f => cases kind; exact ⟨f, found⟩
  | boolean _ | word _ | natural _ | unit | function _ _ | binaryFunction _ => cases kind

theorem ScalarBindingsMatch.words {locals values store} {arguments : List LeanExe.IR.Expr} {native : List UInt64}
    (tail : ScalarBindingsMatch locals values store)
    (heads : LeanExe.ListRelation (fun argument value => argument.ScalarEval store value store) arguments native) :
    ScalarBindingsMatch (arguments.map ScalarBinding.word ++ locals)
      (native.map LeanExe.Source.Scalar.Value.word ++ values) store := by
  induction heads with
  | nil => exact tail
  | cons head _ ih => exact ih.cons head

end LeanExe.Extract.Core

namespace LeanExe.Extract.Core

theorem scalarWords_total {locals : List ScalarBinding} (arguments : List LeanExe.IR.Expr)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∀ binding ∈ arguments.map ScalarBinding.word ++ locals, binding.Total := by
  intro binding member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨argument, _, rfl⟩ := List.mem_map.mp member
    trivial
  · exact total binding member

theorem scalarWords_holds {locals : List ScalarBinding} {P : LeanExe.IR.Expr → Prop}
    {arguments : List LeanExe.IR.Expr} (heads : ∀ argument ∈ arguments, P argument)
    (tail : ∀ binding ∈ locals, binding.Holds P) :
    ∀ binding ∈ arguments.map ScalarBinding.word ++ locals, binding.Holds P := by
  intro binding member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact heads argument argumentMember
  · exact tail binding member

end LeanExe.Extract.Core
