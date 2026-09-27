import Project.Core.Compile
import Project.Encoding.Spec.Validity
import Project.Encoding.Domain

namespace Project.Core.Validity

open LeanExe.Wasm.ScalarDescriptor (Expr Cond U64Op)
open Project.Compiler.ScalarLowering (expression condition operation)

def Reads (count : Nat) (indices : List Nat) : Prop :=
  ∀ index ∈ indices, index < count

theorem numeric_nil : Wasm.Encoding.Spec.Validity.Types [] := by simp [Wasm.Encoding.Spec.Validity.Types]
theorem numeric_i32 : Wasm.Encoding.Spec.Validity.Types [.i32] := by simp [Wasm.Encoding.Spec.Validity.Types, Wasm.Encoding.Numeric]
theorem numeric_i64 : Wasm.Encoding.Spec.Validity.Types [.i64] := by simp [Wasm.Encoding.Spec.Validity.Types, Wasm.Encoding.Numeric]
theorem numeric_words (count : Nat) : Wasm.Encoding.Spec.Validity.Types (List.replicate count .i64) := by
  simp [Wasm.Encoding.Spec.Validity.Types, Wasm.Encoding.Numeric]

theorem append {context : Wasm.Encoding.Spec.Validity.Context} {a b : Wasm.Program}
    {inputs middle outputs : List Wasm.ValueType}
    (first : Wasm.Encoding.Spec.Validity.Program context a inputs middle) (second : Wasm.Encoding.Spec.Validity.Program context b middle outputs) :
    Wasm.Encoding.Spec.Validity.Program context (a ++ b) inputs outputs := by
  induction a generalizing inputs with
  | nil => cases first; exact second
  | cons instr code ih =>
      cases first with
      | cons head tail => exact .cons head (ih tail)

theorem frame {context : Wasm.Encoding.Spec.Validity.Context} {code : Wasm.Program}
    {inputs outputs : List Wasm.ValueType}
    (typed : Wasm.Encoding.Spec.Validity.Program context code inputs outputs) (stack : List Wasm.ValueType)
    (numeric : Wasm.Encoding.Spec.Validity.Types stack) :
    Wasm.Encoding.Spec.Validity.Program context code (stack ++ inputs) (stack ++ outputs) := by
  induction code generalizing inputs with
  | nil =>
      cases typed with
      | nil valid =>
          apply Wasm.Encoding.Spec.Validity.Program.nil
          intro type member
          rcases List.mem_append.mp member with left | right
          · exact numeric type left
          · exact valid type right
  | cons instr code ih =>
      cases typed with
      | cons head tail => exact .cons (.frame head numeric) (ih tail)

theorem singleton {context : Wasm.Encoding.Spec.Validity.Context} {instr : Wasm.Instruction}
    {inputs outputs : List Wasm.ValueType}
    (typed : Wasm.Encoding.Spec.Validity.Instruction context instr inputs outputs) (numeric : Wasm.Encoding.Spec.Validity.Types outputs) :
    Wasm.Encoding.Spec.Validity.Program context [instr] inputs outputs := .cons typed (.nil numeric)

theorem word_get (context : Wasm.Encoding.Spec.Validity.Context) (count index : Nat)
    (locals : context.locals = List.replicate count .i64) (bound : index < count) :
    Wasm.Encoding.Spec.Validity.Program context [.localGet index] [] [.i64] :=
  singleton (.localGet index (by simp [locals, bound])) numeric_i64

theorem word_set (context : Wasm.Encoding.Spec.Validity.Context) (count index : Nat)
    (locals : context.locals = List.replicate count .i64) (bound : index < count) :
    Wasm.Encoding.Spec.Validity.Program context [.localSet index] [.i64] [] :=
  singleton (.localSet index (by simp [locals, bound])) numeric_nil

theorem word_const (context : Wasm.Encoding.Spec.Validity.Context) (value : UInt64) :
    Wasm.Encoding.Spec.Validity.Program context [.constI64 value] [] [.i64] :=
  singleton (.const64 value) numeric_i64

theorem bool_const (context : Wasm.Encoding.Spec.Validity.Context) (value : UInt32) :
    Wasm.Encoding.Spec.Validity.Program context [.const value] [] [.i32] :=
  singleton (.const32 value) numeric_i32

theorem operation_typed (context : Wasm.Encoding.Spec.Validity.Context) (op : U64Op) :
    Wasm.Encoding.Spec.Validity.Program context [(operation op).instruction] [.i64, .i64] [.i64] := by
  cases op with
  | add => exact singleton (.binary .addI64) numeric_i64
  | sub => exact singleton (.binary .subI64) numeric_i64
  | mul => exact singleton (.binary .mulI64) numeric_i64
  | divU => exact singleton (.binary .divUI64) numeric_i64
  | remU => exact singleton (.binary .remUI64) numeric_i64
  | bitAnd => exact singleton (.binary .andI64) numeric_i64
  | bitOr => exact singleton (.binary .orI64) numeric_i64
  | bitXor => exact singleton (.binary .xorI64) numeric_i64
  | shiftLeft => exact singleton (.binary .shlI64) numeric_i64
  | shiftRight => exact singleton (.binary .shrUI64) numeric_i64

theorem binary_typed {context : Wasm.Encoding.Spec.Validity.Context} {left right : Wasm.Program}
    {instr : Wasm.Instruction} {output : Wasm.ValueType}
    (a : Wasm.Encoding.Spec.Validity.Program context left [] [.i64]) (b : Wasm.Encoding.Spec.Validity.Program context right [] [.i64])
    (op : Wasm.Encoding.Spec.Validity.Binary instr .i64 output) (numeric : Wasm.Encoding.Spec.Validity.Types [output]) :
    Wasm.Encoding.Spec.Validity.Program context (left ++ right ++ [instr]) [] [output] :=
  append (append a (frame b [.i64] numeric_i64)) (singleton (.binary op) numeric)

theorem iff_typed {context : Wasm.Encoding.Spec.Validity.Context} {yes no : Wasm.Program}
    {outputs : List Wasm.ValueType} (form : Wasm.Encoding.BlockForm outputs)
    (numeric : Wasm.Encoding.Spec.Validity.Types outputs)
    (a : Wasm.Encoding.Spec.Validity.Program { context with labels := outputs :: context.labels } yes [] outputs)
    (b : Wasm.Encoding.Spec.Validity.Program { context with labels := outputs :: context.labels } no [] outputs) :
    Wasm.Encoding.Spec.Validity.Program context [.iff 0 outputs.length yes no [] outputs] [.i32] outputs :=
  singleton (.iff form a b) numeric

mutual
  theorem expression_typed (value : Expr) (context : Wasm.Encoding.Spec.Validity.Context) (count scratch : Nat)
      (locals : context.locals = List.replicate count .i64)
      (reads : Reads count value.reads) (room : scratch + value.scratchWidth ≤ count) :
      Wasm.Encoding.Spec.Validity.Program context ((expression value).program scratch) [] [.i64] := by
    cases value with
    | get index =>
        exact word_get context count index locals (reads index (by simp [Expr.reads]))
    | const value => exact word_const context (UInt64.ofNat value)
    | bin op left right =>
        have leftReads : Reads count left.reads := by
          intro index member; exact reads index (by simp [Expr.reads, member])
        have rightReads : Reads count right.reads := by
          intro index member; exact reads index (by simp [Expr.reads, member])
        by_cases checked : operation op = .divU ∨ operation op = .remU
        · have slots : scratch + (max left.scratchWidth right.scratchWidth + 2) ≤ count := by
            simpa only [Expr.scratchWidth, Project.Compiler.ScalarLowering.scratch_guard,
              checked, decide_true, ite_true] using room
          have a := expression_typed left context count (scratch + 2) locals leftReads (by omega)
          have b := expression_typed right context count (scratch + 2) locals rightReads (by omega)
          let branch := { context with labels := [.i64] :: context.labels }
          have zero : Wasm.Encoding.Spec.Validity.Program branch
              (if operation op = .divU then [.constI64 0] else [.localGet scratch]) [] [.i64] := by
            split
            · exact word_const branch 0
            · exact word_get branch count scratch locals (by omega)
          have nonzero := append
            (word_get branch count scratch locals (by omega))
            (append (frame (word_get branch count (scratch + 1) locals (by omega))
              [.i64] numeric_i64) (operation_typed branch op))
          have test := binary_typed
            (word_get context count (scratch + 1) locals (by omega))
            (word_const context 0) Wasm.Encoding.Spec.Validity.Binary.eqI64 numeric_i32
          have choose := iff_typed (.value .i64 (by simp [Wasm.Encoding.Numeric])) numeric_i64
            zero nonzero
          simpa only [expression, Project.ProofKit.ScalarTransition.Expr.program, checked, ite_true,
            List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
            List.length_singleton] using
            append (append a (word_set context count scratch locals (by omega)))
              (append (append b (word_set context count (scratch + 1) locals (by omega)))
                (append test choose))
        · have space : scratch + max left.scratchWidth right.scratchWidth ≤ count := by
            simpa only [Expr.scratchWidth, Project.Compiler.ScalarLowering.scratch_guard,
              checked, decide_false, Bool.false_eq_true, ite_false] using room
          have a := expression_typed left context count scratch locals leftReads (by omega)
          have b := expression_typed right context count scratch locals rightReads (by omega)
          simpa only [expression, Project.ProofKit.ScalarTransition.Expr.program, checked, ite_false, List.append_assoc] using
            append a (append (frame b [.i64] numeric_i64) (operation_typed context op))
    | ite test yes no =>
        have testReads : Reads count test.reads := by
          intro index member; exact reads index (by simp [Expr.reads, member])
        have yesReads : Reads count yes.reads := by
          intro index member; exact reads index (by simp [Expr.reads, member])
        have noReads : Reads count no.reads := by
          intro index member; exact reads index (by simp [Expr.reads, member])
        simp only [Expr.scratchWidth] at room
        have t := condition_typed test context count scratch locals testReads (by omega)
        have y := expression_typed yes { context with labels := [.i64] :: context.labels }
          count scratch locals yesReads (by omega)
        have n := expression_typed no { context with labels := [.i64] :: context.labels }
          count scratch locals noReads (by omega)
        exact append t (iff_typed (.value .i64 (by simp [Wasm.Encoding.Numeric])) numeric_i64 y n)
  termination_by sizeOf value

  theorem condition_typed (test : Cond) (context : Wasm.Encoding.Spec.Validity.Context) (count scratch : Nat)
      (locals : context.locals = List.replicate count .i64)
      (reads : Reads count test.reads) (room : scratch + test.scratchWidth ≤ count) :
      Wasm.Encoding.Spec.Validity.Program context ((condition test).program scratch) [] [.i32] := by
    cases test with
    | true => exact bool_const context 1
    | false => exact bool_const context 0
    | eq left right | ne left right | ltU left right | leU left right =>
        have leftReads : Reads count left.reads := by
          intro index member; exact reads index (by simp [Cond.reads, member])
        have rightReads : Reads count right.reads := by
          intro index member; exact reads index (by simp [Cond.reads, member])
        simp only [Cond.scratchWidth] at room
        have a := expression_typed left context count scratch locals leftReads (by omega)
        have b := expression_typed right context count scratch locals rightReads (by omega)
        first
        | exact binary_typed a b Wasm.Encoding.Spec.Validity.Binary.eqI64 numeric_i32
        | exact binary_typed a b Wasm.Encoding.Spec.Validity.Binary.neI64 numeric_i32
        | exact binary_typed a b Wasm.Encoding.Spec.Validity.Binary.ltUI64 numeric_i32
        | exact binary_typed a b Wasm.Encoding.Spec.Validity.Binary.leUI64 numeric_i32
    | not test =>
        exact append (condition_typed test context count scratch locals reads room)
          (singleton (.unary .eqz) numeric_i32)
    | and left right | or left right =>
        have leftReads : Reads count left.reads := by
          intro index member; exact reads index (by simp [Cond.reads, member])
        have rightReads : Reads count right.reads := by
          intro index member; exact reads index (by simp [Cond.reads, member])
        simp only [Cond.scratchWidth] at room
        have a := condition_typed left context count scratch locals leftReads (by omega)
        let branch := { context with labels := [.i32] :: context.labels }
        have b := condition_typed right branch count scratch locals rightReads (by omega)
        first
        | exact append a (iff_typed (.value .i32 (by simp [Wasm.Encoding.Numeric])) numeric_i32
            b (bool_const branch 0))
        | exact append a (iff_typed (.value .i32 (by simp [Wasm.Encoding.Numeric])) numeric_i32
            (bool_const branch 1) b)
  termination_by sizeOf test
end

open Wasm.Encoding.Spec.Validity
open LeanExe.Core (Stmt)

theorem Reads.mono {small large : Nat} {indices : List Nat}
    (reads : Reads small indices) (bound : small ≤ large) : Reads large indices := by
  intro index member
  exact Nat.lt_of_lt_of_le (reads index member) bound

theorem arguments_typed (expressions : List Expr) (context : Context) (count scratch : Nat)
    (locals : context.locals = List.replicate count .i64)
    (reads : ∀ value ∈ expressions, Reads count value.reads)
    (room : scratch + argumentsWidth expressions ≤ count) :
    Program context (argumentsCode expressions scratch) [] (List.replicate expressions.length .i64) := by
  induction expressions with
  | nil => exact .nil numeric_nil
  | cons value values ih =>
      simp only [argumentsWidth] at room
      have head := expression_typed value context count scratch locals
        (reads value (by simp)) (by omega)
      have tail := ih (by intro e member; exact reads e (by simp [member])) (by omega)
      simpa only [argumentsCode_cons, List.length_cons, List.replicate_succ,
        List.nil_append, List.singleton_append] using append head (frame tail [.i64] numeric_i64)

/-- Source bounds and call signatures. Every constructor is accepted independently
of any target typing derivation. -/
inductive WellFormed (source : LeanExe.Core.Module) (effectArity : Nat → Option Nat)
    (count : Nat) : Stmt → Prop
  | skip : WellFormed source effectArity count .skip
  | assign (destination : Nat) (value : Expr) (bound : destination < count)
      (reads : Reads count value.reads) :
      WellFormed source effectArity count (.assign destination value)
  | seq {a b : Stmt} (first : WellFormed source effectArity count a)
      (second : WellFormed source effectArity count b) :
      WellFormed source effectArity count (.seq a b)
  | branch {test : Cond} {a b : Stmt} (reads : Reads count test.reads)
      (yes : WellFormed source effectArity count a)
      (no : WellFormed source effectArity count b) :
      WellFormed source effectArity count (.branch test a b)
  | loop {test : Cond} {statement : Stmt} (reads : Reads count test.reads)
      (body : WellFormed source effectArity count statement) :
      WellFormed source effectArity count (.loop test statement)
  | call (destination callee : Nat) (arguments : List Expr)
      (function : LeanExe.Core.Function) (bound : destination < count)
      (found : source[callee]? = some function) (arity : arguments.length = function.params)
      (reads : ∀ value ∈ arguments, Reads count value.reads) :
      WellFormed source effectArity count (.call destination callee arguments)
  | effect (destination operation : Nat) (arguments : List Expr) (bound : destination < count)
      (arity : effectArity operation = some arguments.length)
      (reads : ∀ value ∈ arguments, Reads count value.reads) :
      WellFormed source effectArity count (.effect destination operation arguments)

def callableTypes (source : LeanExe.Core.Module) (imports : List Wasm.ImportDecl) :
    List Wasm.FuncType :=
  imports.map (fun decl => { params := decl.params, results := decl.results }) ++
    source.map (fun function => functionSignature function.params)

theorem callableTypes_lookup {source : LeanExe.Core.Module} (imports : List Wasm.ImportDecl)
    {callee : Nat} {function : LeanExe.Core.Function} (found : source[callee]? = some function) :
    (callableTypes source imports)[imports.length + callee]? = some (functionSignature function.params) := by
  simp [callableTypes, List.getElem?_append_right, List.getElem?_map, found]

/-- A primitive implementation is typed for its declared source arity. Labels
and local declarations may vary because the same primitive can occur in any body. -/
def PrimitiveTyping (signatures : List Wasm.FuncType)
    (memory : Option Wasm.MemDecl) (effectArity : Nat → Option Nat)
    (effectCode : Nat → Wasm.Program) : Prop :=
  ∀ operation arity, effectArity operation = some arity → ∀ context : Context,
    context.functions = signatures →
    context.hasMemory = memory.isSome →
    Program context (effectCode operation) (List.replicate arity .i64) [.i64]

theorem statement_typed {source : LeanExe.Core.Module} {effectArity : Nat → Option Nat}
    {live : Nat} {stmt : Stmt} (formed : WellFormed source effectArity live stmt)
    (imports : List Wasm.ImportDecl) (memory : Option Wasm.MemDecl)
    (effectCode : Nat → Wasm.Program)
    (signatures : List Wasm.FuncType)
    (resolved : ∀ callee function, source[callee]? = some function →
      signatures[imports.length + callee]? = some (functionSignature function.params))
    (primitive : PrimitiveTyping signatures memory effectArity effectCode)
    (context : Context) (count scratch : Nat)
    (locals : context.locals = List.replicate count .i64)
    (functions : context.functions = signatures)
    (hasMemory : context.hasMemory = memory.isSome)
    (liveRoom : live ≤ count) (room : scratch + width stmt ≤ count) :
    Program context (statement imports.length effectCode scratch stmt) [] [] := by
  induction formed generalizing context scratch with
  | skip => exact .nil numeric_nil
  | assign destination value bound reads =>
      exact append (expression_typed value context count scratch locals (reads.mono liveRoom) room)
        (word_set context count destination locals (by omega))
  | seq first second ihFirst ihSecond =>
      simp only [width] at room
      exact append (ihFirst context scratch locals functions hasMemory (by omega))
        (ihSecond context scratch locals functions hasMemory (by omega))
  | @branch test a b reads yes no ihYes ihNo =>
      simp only [width] at room
      have tested := condition_typed test context count scratch locals (reads.mono liveRoom) (by omega)
      have a := ihYes { context with labels := [] :: context.labels } scratch
        locals functions hasMemory (by omega)
      have b := ihNo { context with labels := [] :: context.labels } scratch
        locals functions hasMemory (by omega)
      exact append tested (iff_typed .empty numeric_nil a b)
  | @loop test body reads formed ih =>
      simp only [width] at room
      let inner := { context with labels := [] :: [] :: context.labels }
      have tested := condition_typed test inner count scratch locals (reads.mono liveRoom) (by omega)
      have executed := ih inner scratch locals functions hasMemory (by omega)
      have testTail : Program inner [.eqz, .br_if 1] [.i32] [] :=
        .cons (.unary .eqz) (.cons (.brIf (results := []) 1 rfl) (.nil numeric_nil))
      have branchBack : Program inner [.br 0] [] [] :=
        singleton (.br (inputs := []) (results := []) 0 rfl numeric_nil numeric_nil) numeric_nil
      have loopBody := append (append (append tested testTail) executed) branchBack
      exact singleton (.block .empty
        (singleton (.loop .empty (by simpa only [List.append_assoc] using loopBody)) numeric_nil)) numeric_nil
  | call destination callee arguments function bound found arity reads =>
      have prepared := arguments_typed arguments context count scratch locals
        (by intro value member; exact (reads value member).mono liveRoom) room
      have signature : context.functions[imports.length + callee]? =
          some (functionSignature function.params) := by
        rw [functions]
        exact resolved callee function found
      have invoked := singleton
        (Instruction.call (imports.length + callee) (functionSignature function.params) signature)
        numeric_i64
      simpa only [statement, List.append_assoc, List.singleton_append] using
        append (append (by simpa only [functionSignature, arity] using prepared) invoked)
          (word_set context count destination locals (by omega))
  | effect destination operation arguments bound arity reads =>
      have prepared := arguments_typed arguments context count scratch locals
        (by intro value member; exact (reads value member).mono liveRoom) room
      simpa only [statement, List.append_assoc, List.singleton_append] using
        append (append prepared (primitive operation arguments.length arity context functions hasMemory))
          (word_set context count destination locals (by omega))

theorem maxParams_bound {source : LeanExe.Core.Module} {function : LeanExe.Core.Function}
    (member : function ∈ source) : function.params ≤ maxParams source := by
  induction source with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · subst function; exact Nat.le_max_left _ _
      · exact (ih rest).trans (Nat.le_max_right _ _)

theorem signature_lookup {source : LeanExe.Core.Module} (imports : List Wasm.ImportDecl)
    {function : LeanExe.Core.Function} (member : function ∈ source) :
    (signatures source imports)[function.params]? = some (functionSignature function.params) := by
  have bound := maxParams_bound member
  unfold signatures
  rw [List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_map, List.getElem?_range (by omega : function.params < maxParams source + 1)]

theorem compile_shape (source : LeanExe.Core.Module) (effectCode : Nat → Wasm.Program)
    (imports : List Wasm.ImportDecl) (exports : List Wasm.Export) (memory : Option Wasm.MemDecl) :
    Wasm.Encoding.Spec.Shape (compile source effectCode imports exports memory) := by
  constructor <;> rfl

theorem compile_functionTypes (source : LeanExe.Core.Module) (effectCode : Nat → Wasm.Program)
    (imports : List Wasm.ImportDecl) (exports : List Wasm.Export) (memory : Option Wasm.MemDecl) :
    functionTypes (compile source effectCode imports exports memory) = callableTypes source imports := by
  simp [functionTypes, compile, callableTypes, Wasm.Encoding.Spec.signature,
    compileFunction, functionSignature, List.map_map]

/-- A compiled source function remains valid when the target also contains proved
runtime helpers. Only source call resolution and primitive typing depend on that
larger target; the compiler's function body is unchanged. -/
theorem function_valid_in (source : LeanExe.Core.Module) (target : Wasm.Module)
    (effectCode : Nat → Wasm.Program) (effectArity : Nat → Option Nat)
    (function : LeanExe.Core.Function)
    (bodyForm : WellFormed source effectArity (function.params + function.locals) function.body)
    (resultReads : Reads (function.params + function.locals) function.result.reads)
    (declared : target.types[function.params]? = some (functionSignature function.params))
    (resolved : ∀ callee foundFunction, source[callee]? = some foundFunction →
      (functionTypes target)[target.imports.length + callee]? =
        some (functionSignature foundFunction.params))
    (primitive : PrimitiveTyping (functionTypes target) target.memory effectArity effectCode)
    (bound : function.params + function.locals +
      max (width function.body) function.result.scratchWidth < 2 ^ 32) :
    Wasm.Encoding.Spec.Validity.Function target
      (compileFunction target.imports.length effectCode function) := by
  let count := function.params + function.locals + max (width function.body) function.result.scratchWidth
  let context := functionContext target (compileFunction target.imports.length effectCode function)
  have locals : context.locals = List.replicate count .i64 := by
    simp [context, functionContext, compileFunction, count, List.replicate_append_replicate, Nat.add_assoc]
  have liveRoom : function.params + function.locals ≤ count := by dsimp [count]; omega
  have body := statement_typed bodyForm target.imports target.memory effectCode
    (functionTypes target) resolved primitive context count
    (function.params + function.locals) locals rfl rfl liveRoom (by dsimp [count]; omega)
  have result := expression_typed function.result context count (function.params + function.locals)
    locals (resultReads.mono liveRoom) (by dsimp [count]; omega)
  exact ⟨⟨function.params, rfl, declared⟩, numeric_words _,
    by simpa [compileFunction, Nat.add_assoc] using bound, append body result⟩

/-- All accepted source functions have valid locals, expression reads and direct
call signatures. The remaining premises concern primitive implementations and
the format's numeric limits and export declarations. -/
theorem compile_valid (source : LeanExe.Core.Module) (effectCode : Nat → Wasm.Program)
    (imports : List Wasm.ImportDecl) (exports : List Wasm.Export) (memory : Option Wasm.MemDecl)
    (effectArity : Nat → Option Nat)
    (formed : ∀ function ∈ source,
      WellFormed source effectArity (function.params + function.locals) function.body ∧
      Reads (function.params + function.locals) function.result.reads)
    (primitive : PrimitiveTyping (callableTypes source imports) memory effectArity effectCode)
    (importTypes : ∀ decl ∈ imports, Types decl.params ∧ Types decl.results)
    (localBound : ∀ function ∈ source,
      function.params + function.locals + max (width function.body) function.result.scratchWidth < 2 ^ 32)
    (memoryValid : ∀ decl ∈ memory, Memory decl)
    (functionBound : imports.length + source.length < 2 ^ 32)
    (exportBound : ∀ entry ∈ exports, entry.funcIdx < imports.length + source.length)
    (exportNames : (exports.map Wasm.Export.name).Nodup) :
    Wasm.Encoding.Spec.Validity.Module (compile source effectCode imports exports memory) := by
  let target := compile source effectCode imports exports memory
  refine ⟨compile_shape source effectCode imports exports memory, ?_, ?_, ?_,
    memoryValid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro type member
    change type ∈ signatures source imports at member
    rcases List.mem_append.mp member with standard | imported
    · obtain ⟨arity, _, rfl⟩ := List.mem_map.mp standard
      exact ⟨numeric_words arity, numeric_i64⟩
    · obtain ⟨decl, declMember, rfl⟩ := List.mem_map.mp imported
      exact importTypes decl declMember
  · intro decl member
    change ({ params := decl.params, results := decl.results } : Wasm.FuncType) ∈ signatures source imports
    apply List.mem_append.mpr
    right
    exact List.mem_map.mpr ⟨decl, member, rfl⟩
  · intro compiled member
    obtain ⟨function, functionMember, rfl⟩ := List.mem_map.mp member
    let count := function.params + function.locals + max (width function.body) function.result.scratchWidth
    let context := functionContext target (compileFunction imports.length effectCode function)
    have locals : context.locals = List.replicate count .i64 := by
      simp [context, functionContext, compileFunction, count, List.replicate_append_replicate, Nat.add_assoc]
    have functions : context.functions = callableTypes source imports :=
      compile_functionTypes source effectCode imports exports memory
    have hasMemory : context.hasMemory = memory.isSome := rfl
    have liveRoom : function.params + function.locals ≤ count := by dsimp [count]; omega
    obtain ⟨bodyForm, resultReads⟩ := formed function functionMember
    have body := statement_typed bodyForm imports memory effectCode (callableTypes source imports)
      (fun _ _ found => callableTypes_lookup imports found) primitive context count
      (function.params + function.locals) locals functions hasMemory liveRoom (by dsimp [count]; omega)
    have result := expression_typed function.result context count (function.params + function.locals)
      locals (resultReads.mono liveRoom) (by dsimp [count]; omega)
    refine ⟨⟨function.params, rfl, ?_⟩, numeric_words _, ?_, append body result⟩
    · exact signature_lookup imports functionMember
    · simpa [compileFunction, Nat.add_assoc] using localBound function functionMember
  · simp [compile]
  · simpa [compile] using functionBound
  · simpa [compile] using exportBound
  · simp [compile]
  · simp [compile]
  · simpa [Wasm.Encoding.Spec.exports, compile, List.map_map, Function.comp_def] using exportNames

end Project.Core.Validity
