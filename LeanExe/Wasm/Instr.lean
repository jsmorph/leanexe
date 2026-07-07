namespace LeanExe.Wasm

/-- The structured instruction set of the generated WASM subset.  This is the
single lowering target: the binary encoder and any text printer serialize
values of this type, so the two cannot diverge in content.  Control flow nests
instruction lists the way the WASM text format nests them, matching the shape
Talos decodes.  `iff` carries an optional else so the encoder can reproduce
both the `if ... end` and `if ... else ... end` byte forms exactly. -/
inductive Instr where
  | constI64 (value : Nat)
  | constI32 (value : Nat)
  | constI32NegOne
  | localGet (index : Nat)
  | localSet (index : Nat)
  | localTee (index : Nat)
  | globalGet (index : Nat)
  | globalSet (index : Nat)
  | call (index : Nat)
  | addI64
  | subI64
  | mulI64
  | divUI64
  | remUI64
  | andI64
  | orI64
  | xorI64
  | shlI64
  | shrUI64
  | eqI64
  | neI64
  | ltUI64
  | leUI64
  | geUI64
  | eqzI64
  | eqI32
  | eqzI32
  | andI32
  | wrapI64
  | extendUI32
  | load64
  | load32
  | load8U
  | store64
  | store32
  | store8
  | memorySize
  | memoryGrow
  | unreachable
  | ret
  | drop
  | block (body : List Instr)
  | loop (body : List Instr)
  | iff (resultI64 : Bool) (thn : List Instr) (els : Option (List Instr))
  | iffI32 (thn : List Instr) (els : Option (List Instr))
  | br (depth : Nat)
  | brIf (depth : Nat)
  deriving BEq, Repr, Inhabited

end LeanExe.Wasm
