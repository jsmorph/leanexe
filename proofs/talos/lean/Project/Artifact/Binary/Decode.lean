import Project.Artifact.Binary.Primitives

namespace Wasm.Binary

open Parser

def valType : Parser ValType := do
  let code ← readByte
  if code = 127 then
    pure .i32
  else if code = 126 then
    pure .i64
  else
    fail (.unsupportedType code)

def funcType : Parser FuncType := do
  expectByte 96
  let params ← vector valType
  let results ← vector valType
  pure { params, results }

def limits : Parser Limits := do
  let flags ← readByte
  if flags = 0 then
    let min ← Leb.u32
    pure { min, max := none }
  else if flags = 1 then
    let min ← Leb.u32
    let max ← Leb.u32
    pure { min, max := some max }
  else
    fail (.malformed "unsupported limits flags")

def memoryType : Parser MemoryType := do
  pure { limits := ← limits }

def mutability : Parser Mutability := do
  let code ← readByte
  if code = 0 then
    pure .immutable
  else if code = 1 then
    pure .mutable
  else
    fail (.malformed "invalid global mutability")

def globalType : Parser GlobalType := do
  pure { type := ← valType, mutability := ← mutability }

def constExpr : Parser ConstExpr := do
  let opcode ← readByte
  if opcode = 65 then
    let value ← Leb.s32
    expectByte 11
    pure (.i32Const value)
  else if opcode = 66 then
    let value ← Leb.s64
    expectByte 11
    pure (.i64Const value)
  else
    fail (.unsupportedOpcode opcode)

def global : Parser Global := do
  pure { type := ← globalType, init := ← constExpr }

def blockType : Parser BlockType := do
  let code ← readByte
  if code = 64 then
    pure .empty
  else if code = 127 then
    pure (.value .i32)
  else if code = 126 then
    pure (.value .i64)
  else
    fail (.unsupportedType code)

def memArg : Parser MemArg := do
  pure { align := ← Leb.u32, offset := ← Leb.u32 }

inductive Op where
  | unreachable
  | block
  | loop
  | iff
  | br
  | brIf
  | ret
  | call
  | drop
  | localGet
  | localSet
  | localTee
  | globalGet
  | globalSet
  | i32Load
  | i64Load
  | i32Load8U
  | i32Store
  | i64Store
  | i32Store8
  | memorySize
  | memoryGrow
  | i32Const
  | i64Const
  | i32Eqz
  | i32Eq
  | i64Eqz
  | i64Eq
  | i64Ne
  | i64LtU
  | i64LeU
  | i64GeU
  | i32And
  | i64Add
  | i64Sub
  | i64Mul
  | i64DivU
  | i64RemU
  | i64And
  | i64Or
  | i64Xor
  | i64Shl
  | i64ShrU
  | i32WrapI64
  | i64ExtendI32U
  | f64Add
  | f64Mul
  | i64ReinterpretF64
  | f64ReinterpretI64
  deriving DecidableEq

def Op.opcode : Op → UInt8
  | .unreachable => 0
  | .block => 2
  | .loop => 3
  | .iff => 4
  | .br => 12
  | .brIf => 13
  | .ret => 15
  | .call => 16
  | .drop => 26
  | .localGet => 32
  | .localSet => 33
  | .localTee => 34
  | .globalGet => 35
  | .globalSet => 36
  | .i32Load => 40
  | .i64Load => 41
  | .i32Load8U => 45
  | .i32Store => 54
  | .i64Store => 55
  | .i32Store8 => 58
  | .memorySize => 63
  | .memoryGrow => 64
  | .i32Const => 65
  | .i64Const => 66
  | .i32Eqz => 69
  | .i32Eq => 70
  | .i64Eqz => 80
  | .i64Eq => 81
  | .i64Ne => 82
  | .i64LtU => 84
  | .i64LeU => 88
  | .i64GeU => 90
  | .i32And => 113
  | .i64Add => 124
  | .i64Sub => 125
  | .i64Mul => 126
  | .i64DivU => 128
  | .i64RemU => 130
  | .i64And => 131
  | .i64Or => 132
  | .i64Xor => 133
  | .i64Shl => 134
  | .i64ShrU => 136
  | .f64Add => 160
  | .f64Mul => 162
  | .i32WrapI64 => 167
  | .i64ExtendI32U => 173
  | .i64ReinterpretF64 => 189
  | .f64ReinterpretI64 => 191

def Op.all : List Op :=
  [.unreachable, .block, .loop, .iff, .br, .brIf, .ret, .call, .drop,
    .localGet, .localSet, .localTee, .globalGet, .globalSet, .i32Load,
    .i64Load, .i32Load8U, .i32Store, .i64Store, .i32Store8, .memorySize,
    .memoryGrow, .i32Const, .i64Const, .i32Eqz, .i32Eq, .i64Eqz, .i64Eq,
    .i64Ne, .i64LtU, .i64LeU, .i64GeU, .i32And, .i64Add, .i64Sub,
    .i64Mul, .i64DivU, .i64RemU, .i64And, .i64Or, .i64Xor, .i64Shl,
    .i64ShrU, .f64Add, .f64Mul, .i32WrapI64, .i64ExtendI32U,
    .i64ReinterpretF64, .f64ReinterpretI64]

def classifyLoop (byte : UInt8) : List Op → Option Op
  | [] => none
  | opcode :: rest =>
      if opcode.opcode = byte then some opcode else classifyLoop byte rest

def classify (byte : UInt8) : Option Op :=
  classifyLoop byte Op.all

inductive Terminator where
  | end
  | otherwise

mutual
  def instruction : Nat → Parser Instr
    | 0 => fail (.malformed "instruction nesting exceeds body size")
    | fuel + 1 => do
        let opcodeByte ← readByte
        match classify opcodeByte with
        | none => fail (.unsupportedOpcode opcodeByte)
        | some opcode =>
          match opcode with
          | .unreachable => pure .unreachable
          | .block =>
            let type ← blockType
            let (body, terminator) ← instructionSequence fuel false
            match terminator with
            | .end => pure (.block type body)
            | .otherwise => fail (.malformed "else terminates a block")
          | .loop =>
            let type ← blockType
            let (body, terminator) ← instructionSequence fuel false
            match terminator with
            | .end => pure (.loop type body)
            | .otherwise => fail (.malformed "else terminates a loop")
          | .iff =>
            let type ← blockType
            let (thenBody, terminator) ← instructionSequence fuel true
            match terminator with
            | .end => pure (.iff type thenBody none)
            | .otherwise =>
                let (elseBody, elseTerminator) ← instructionSequence fuel false
                match elseTerminator with
                | .end => pure (.iff type thenBody (some elseBody))
                | .otherwise => fail (.malformed "second else in if")
          | .br => pure (.br (← Leb.u32))
          | .brIf => pure (.brIf (← Leb.u32))
          | .ret => pure .ret
          | .call => pure (.call (← Leb.u32))
          | .drop => pure .drop
          | .localGet => pure (.localGet (← Leb.u32))
          | .localSet => pure (.localSet (← Leb.u32))
          | .localTee => pure (.localTee (← Leb.u32))
          | .globalGet => pure (.globalGet (← Leb.u32))
          | .globalSet => pure (.globalSet (← Leb.u32))
          | .i32Load => pure (.i32Load (← memArg))
          | .i64Load => pure (.i64Load (← memArg))
          | .i32Load8U => pure (.i32Load8U (← memArg))
          | .i32Store => pure (.i32Store (← memArg))
          | .i64Store => pure (.i64Store (← memArg))
          | .i32Store8 => pure (.i32Store8 (← memArg))
          | .memorySize => pure (.memorySize (← Leb.u32))
          | .memoryGrow => pure (.memoryGrow (← Leb.u32))
          | .i32Const => pure (.i32Const (← Leb.s32))
          | .i64Const => pure (.i64Const (← Leb.s64))
          | .i32Eqz => pure .i32Eqz
          | .i32Eq => pure .i32Eq
          | .i64Eqz => pure .i64Eqz
          | .i64Eq => pure .i64Eq
          | .i64Ne => pure .i64Ne
          | .i64LtU => pure .i64LtU
          | .i64LeU => pure .i64LeU
          | .i64GeU => pure .i64GeU
          | .i32And => pure .i32And
          | .i64Add => pure .i64Add
          | .i64Sub => pure .i64Sub
          | .i64Mul => pure .i64Mul
          | .i64DivU => pure .i64DivU
          | .i64RemU => pure .i64RemU
          | .i64And => pure .i64And
          | .i64Or => pure .i64Or
          | .i64Xor => pure .i64Xor
          | .i64Shl => pure .i64Shl
          | .i64ShrU => pure .i64ShrU
          | .f64Add => pure .f64Add
          | .f64Mul => pure .f64Mul
          | .i32WrapI64 => pure .i32WrapI64
          | .i64ExtendI32U => pure .i64ExtendI32U
          | .i64ReinterpretF64 => pure .i64ReinterpretF64
          | .f64ReinterpretI64 => pure .f64ReinterpretI64

  def instructionSequence : Nat → Bool → Parser (List Instr × Terminator)
    | 0, _ => fail (.malformed "unterminated instruction sequence")
    | fuel + 1, allowElse => do
        let next ← peekByte
        if next = 11 then
          let _ ← readByte
          pure ([], .end)
        else if next = 5 then
          if allowElse then
            let _ ← readByte
            pure ([], .otherwise)
          else
            fail (.malformed "unexpected else")
        else
          let first ← instruction fuel
          let (rest, terminator) ← instructionSequence fuel allowElse
          pure (first :: rest, terminator)
end

def expression : Parser (List Instr) :=
  fun cursor =>
    match instructionSequence cursor.remaining false cursor with
    | .error error => .error error
    | .ok ((body, terminator), cursor') =>
        match terminator with
        | .end => .ok (body, cursor')
        | .otherwise => .error { offset := cursor'.pos, kind := .malformed "unexpected else" }

def localDecl : Parser LocalDecl := do
  pure { count := ← Leb.u32, type := ← valType }

def codeBody : Parser Code := do
  let locals ← vector localDecl
  let body ← expression
  pure { locals, body }

def code : Parser Code :=
  sized codeBody

def exportDesc : Parser ExportDesc := do
  let kind ← readByte
  if kind = 0 then
    pure (.func (← Leb.u32))
  else if kind = 2 then
    pure (.memory (← Leb.u32))
  else if kind = 3 then
    pure (.global (← Leb.u32))
  else
    fail (.malformed "unsupported export descriptor")

def exportEntry : Parser Export := do
  pure { name := ← name, desc := ← exportDesc }

def sectionInfo (byte : UInt8) : Except ErrorKind (SectionId × Nat) :=
  if byte = SectionId.type.byte then .ok (.type, SectionId.type.rank)
  else if byte = SectionId.function.byte then .ok (.function, SectionId.function.rank)
  else if byte = SectionId.memory.byte then .ok (.memory, SectionId.memory.rank)
  else if byte = SectionId.global.byte then .ok (.global, SectionId.global.rank)
  else if byte = SectionId.export.byte then .ok (.export, SectionId.export.rank)
  else if byte = SectionId.code.byte then .ok (.code, SectionId.code.rank)
  else .error (.unsupportedSection byte)

def parseSection (id : SectionId) (module_ : RawModule) : Parser RawModule :=
  match id with
  | .type => do
      let types ← sized (vector funcType)
      pure { module_ with types }
  | .function => do
      let functionTypeIndices ← sized (vector Leb.u32)
      pure { module_ with functionTypeIndices }
  | .memory => do
      let memories ← sized (vector memoryType)
      pure { module_ with memories }
  | .global => do
      let globals ← sized (vector global)
      pure { module_ with globals }
  | .export => do
      let exports ← sized (vector exportEntry)
      pure { module_ with exports }
  | .code => do
      let codes ← sized (vector code)
      pure { module_ with codes }

def remainingBytes : Parser Nat :=
  fun cursor => .ok (cursor.remaining, cursor)

def sectionStep (next : Nat → RawModule → Parser RawModule)
    (lastRank : Nat) (module_ : RawModule) : Parser RawModule := do
  let rawId ← readByte
  match sectionInfo rawId with
  | .error kind => fail kind
  | .ok (id, rank) =>
      if id ∈ module_.sections then
        fail (.duplicateSection id)
      else if rank ≤ lastRank then
        fail (.sectionOutOfOrder id)
      else
        let module_' ← parseSection id module_
        next rank { module_' with sections := module_'.sections ++ [id] }

def sectionLoop : Nat → Nat → RawModule → Parser RawModule
  | 0, _, module_ => do
      let remaining ← remainingBytes
      if remaining = 0 then pure module_ else fail (.malformed "section count exceeds input size")
  | fuel + 1, lastRank, module_ => do
      let remaining ← remainingBytes
      if remaining = 0 then
        pure module_
      else
        sectionStep (sectionLoop fuel) lastRank module_

def moduleParser : Parser RawModule := do
  expectBytes [0, 97, 115, 109]
  expectBytes [1, 0, 0, 0]
  let remaining ← remainingBytes
  sectionLoop remaining 0 default

def decode (bytes : ByteArray) : Except Error RawModule :=
  Parser.runAll moduleParser bytes

end Wasm.Binary
