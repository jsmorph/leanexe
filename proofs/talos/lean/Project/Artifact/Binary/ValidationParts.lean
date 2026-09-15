import Project.Artifact.Binary.Validate

namespace Wasm.Binary

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
#print axioms validateRaw_eq_of_parts
end Wasm.Binary
