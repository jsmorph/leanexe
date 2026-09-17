import Project.Artifact.Binary.Validate

namespace Wasm.Binary

/-- Convert successful validation's Boolean observation into its exact result. -/
theorem ok_unit_of_isSome {error : Type} {result : Except error Unit}
    (h : result.toOption.isSome = true) : result = .ok () := by
  cases result with
  | error e => simp [Except.toOption] at h
  | ok value => cases value; rfl

#print axioms ok_unit_of_isSome

/-- Split validation at an instruction-list boundary, preserving the exact
operand stack and source index used by the validator. -/
theorem validateInstrs_eq_append {context : Validator.Context} {path : List Nat}
    {base index : Nat} {start middle finish : Validator.StackState}
    {first rest : List Instr}
    (head : Validator.validateInstrs context path base start index first = .ok middle)
    (tail : Validator.validateInstrs context path base middle (index+first.length) rest = .ok finish) :
    Validator.validateInstrs context path base start index (first++rest) = .ok finish := by
  induction first generalizing start index with
  | nil =>
      simp only [Validator.validateInstrs, Pure.pure, Except.pure] at head
      cases head
      simpa only [List.nil_append, List.length_nil, Nat.add_zero] using tail
  | cons instruction instructions ih =>
      simp only [Validator.validateInstrs, Bind.bind, Except.bind] at head
      cases hstep : Validator.validateInstr context (path++[index]) base start instruction with
      | error error => simp [hstep] at head
      | ok next =>
          simp only [hstep] at head
          simp only [List.cons_append, Validator.validateInstrs, Bind.bind, Except.bind, hstep]
          apply ih head
          simpa only [List.length_cons, Nat.add_succ, Nat.succ_add, Nat.add_zero] using tail

theorem validateFunctionPairs_eq_cons
    {raw : RawModule} {functions : List FuncType} {index : Nat}
    {type : FuncType} {types : List FuncType} {code : Code} {codes : List Code}
    (head : Validator.validateFunction raw functions index type code = .ok ())
    (tail : Validator.validateFunctionPairs raw functions (index + 1) types codes = .ok ()) :
    Validator.validateFunctionPairs raw functions index (type :: types) (code :: codes) = .ok () := by
  simp [Validator.validateFunctionPairs, Bind.bind, Except.bind, head, tail]

theorem validateRaw_eq_of_parts {raw : RawModule} {functions : List FuncType}
    (sections : Validator.validateSections raw = .ok ())
    (memory : raw.memories.length = 1)
    (limits : Validator.validateLimits raw.memories.head!.limits = .ok ())
    (globals : Validator.validateGlobals raw.globals = .ok ())
    (exports : Validator.validateExports raw = .ok ())
    (types : Validator.resolveFunctionTypes raw = .ok functions)
    (bodies : Validator.validateFunctions raw functions = .ok ()) :
    Validator.validateRaw raw = .ok () := by
  simp [Validator.validateRaw, Bind.bind, Except.bind,
    sections, memory, limits, globals, exports, types, bodies]

#print axioms validateFunctionPairs_eq_cons
#print axioms validateInstrs_eq_append
#print axioms validateRaw_eq_of_parts
end Wasm.Binary
