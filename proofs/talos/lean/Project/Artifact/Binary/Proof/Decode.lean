import Project.Artifact.Binary.Decode
import Project.Artifact.Binary.Proof.Primitives

namespace Wasm.Binary.Proof

open Parser

theorem valType_sound :
    Sound valType Grammar.ValType := by
  intro start value finish hstart hrun
  unfold valType at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hread
    rcases pair with ⟨code, middle⟩
    split at hrun
    · rename_i hi32
      cases hrun
      rcases readByte_sound start code middle hstart hread with
        ⟨bytes, hconsumed, hbytes⟩
      simp at hi32
      rw [hbytes, hi32] at hconsumed
      exact ⟨[127], hconsumed, Grammar.ValType.i32⟩
    · split at hrun
      · rename_i hi64
        cases hrun
        rcases readByte_sound start code middle hstart hread with
          ⟨bytes, hconsumed, hbytes⟩
        simp at hi64
        rw [hbytes, hi64] at hconsumed
        exact ⟨[126], hconsumed, Grammar.ValType.i64⟩
      · contradiction

theorem blockType_sound :
    Sound blockType Grammar.BlockType := by
  intro start value finish hstart hrun
  unfold blockType at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hread
    rcases pair with ⟨code, middle⟩
    split at hrun
    · rename_i hempty
      cases hrun
      rcases readByte_sound start code middle hstart hread with
        ⟨bytes, hconsumed, hbytes⟩
      simp at hempty
      rw [hbytes, hempty] at hconsumed
      exact ⟨[64], hconsumed, Grammar.BlockType.empty⟩
    · split at hrun
      · rename_i hi32
        cases hrun
        rcases readByte_sound start code middle hstart hread with
          ⟨bytes, hconsumed, hbytes⟩
        simp at hi32
        rw [hbytes, hi32] at hconsumed
        exact ⟨[127], hconsumed, Grammar.BlockType.i32⟩
      · split at hrun
        · rename_i hi64
          cases hrun
          rcases readByte_sound start code middle hstart hread with
            ⟨bytes, hconsumed, hbytes⟩
          simp at hi64
          rw [hbytes, hi64] at hconsumed
          exact ⟨[126], hconsumed, Grammar.BlockType.i64⟩
        · contradiction

theorem mutability_sound :
    Sound mutability Grammar.Mutability := by
  intro start value finish hstart hrun
  unfold mutability at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hread
    rcases pair with ⟨code, middle⟩
    split at hrun
    · rename_i himmutable
      cases hrun
      rcases readByte_sound start code middle hstart hread with
        ⟨bytes, hconsumed, hbytes⟩
      simp at himmutable
      rw [hbytes, himmutable] at hconsumed
      exact ⟨[0], hconsumed, Grammar.Mutability.immutable⟩
    · split at hrun
      · rename_i hmutable
        cases hrun
        rcases readByte_sound start code middle hstart hread with
          ⟨bytes, hconsumed, hbytes⟩
        simp at hmutable
        rw [hbytes, hmutable] at hconsumed
        exact ⟨[1], hconsumed, Grammar.Mutability.mutable⟩
      · contradiction

theorem memArg_sound :
    Sound memArg Grammar.MemArg := by
  intro start value finish hstart hrun
  unfold memArg at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedAlign alignPair halignRun
    rcases alignPair with ⟨align, middle⟩
    split at hrun
    · contradiction
    · rename_i parsedOffset offsetPair hoffsetRun
      rcases offsetPair with ⟨offset, tail⟩
      cases hrun
      rcases Leb.Proof.u32_sound start align middle hstart halignRun with
        ⟨alignBytes, halignConsumed, halignEncoding⟩
      rcases Leb.Proof.u32_sound middle offset tail
          (halignConsumed.finish_wellFormed hstart) hoffsetRun with
        ⟨offsetBytes, hoffsetConsumed, hoffsetEncoding⟩
      exact ⟨alignBytes ++ offsetBytes,
        halignConsumed.trans hoffsetConsumed,
        Grammar.MemArg.intro alignBytes offsetBytes align offset
          halignEncoding hoffsetEncoding⟩

theorem globalType_sound :
    Sound globalType Grammar.GlobalType := by
  intro start value finish hstart hrun
  unfold globalType at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedType typePair htypeRun
    rcases typePair with ⟨type, middle⟩
    split at hrun
    · contradiction
    · rename_i parsedMutability mutabilityPair hmutabilityRun
      rcases mutabilityPair with ⟨mutabilityValue, tail⟩
      cases hrun
      rcases valType_sound start type middle hstart htypeRun with
        ⟨typeBytes, htypeConsumed, htypeEncoding⟩
      rcases mutability_sound middle mutabilityValue tail
          (htypeConsumed.finish_wellFormed hstart) hmutabilityRun with
        ⟨mutabilityBytes, hmutabilityConsumed, hmutabilityEncoding⟩
      exact ⟨typeBytes ++ mutabilityBytes,
        htypeConsumed.trans hmutabilityConsumed,
        Grammar.GlobalType.intro typeBytes mutabilityBytes type
          mutabilityValue htypeEncoding hmutabilityEncoding⟩

theorem localDecl_sound :
    Sound localDecl Grammar.LocalDecl := by
  intro start value finish hstart hrun
  unfold localDecl at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedCount countPair hcountRun
    rcases countPair with ⟨count, middle⟩
    split at hrun
    · contradiction
    · rename_i parsedType typePair htypeRun
      rcases typePair with ⟨type, tail⟩
      cases hrun
      rcases Leb.Proof.u32_sound start count middle hstart hcountRun with
        ⟨countBytes, hcountConsumed, hcountEncoding⟩
      rcases valType_sound middle type tail
          (hcountConsumed.finish_wellFormed hstart) htypeRun with
        ⟨typeBytes, htypeConsumed, htypeEncoding⟩
      exact ⟨countBytes ++ typeBytes, hcountConsumed.trans htypeConsumed,
        Grammar.LocalDecl.intro countBytes typeBytes count type
          hcountEncoding htypeEncoding⟩

theorem funcType_sound :
    Sound funcType Grammar.FuncType := by
  intro start value finish hstart hrun
  unfold funcType at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedTag tagPair htagRun
    rcases tagPair with ⟨tagValue, afterTag⟩
    split at hrun
    · contradiction
    · rename_i parsedParams paramsPair hparamsRun
      rcases paramsPair with ⟨params, afterParams⟩
      split at hrun
      · contradiction
      · rename_i parsedResults resultsPair hresultsRun
        rcases resultsPair with ⟨results, tail⟩
        cases hrun
        rcases expectByte_sound 96 start tagValue afterTag hstart htagRun with
          ⟨tagBytes, htagConsumed, htagBytes⟩
        rcases vector_sound valType_sound afterTag params afterParams
            (htagConsumed.finish_wellFormed hstart) hparamsRun with
          ⟨paramBytes, hparamsConsumed, hparamsEncoding⟩
        rcases vector_sound valType_sound afterParams results tail
            (hparamsConsumed.finish_wellFormed
              (htagConsumed.finish_wellFormed hstart)) hresultsRun with
          ⟨resultBytes, hresultsConsumed, hresultsEncoding⟩
        rw [htagBytes] at htagConsumed
        refine ⟨96 :: (paramBytes ++ resultBytes), ?_, ?_⟩
        · simpa using (htagConsumed.trans
            (hparamsConsumed.trans hresultsConsumed))
        · exact Grammar.FuncType.intro paramBytes resultBytes params results
            hparamsEncoding hresultsEncoding

theorem limits_sound :
    Sound limits Grammar.Limits := by
  intro start value finish hstart hrun
  unfold limits at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedFlags flagsPair hflagsRun
    rcases flagsPair with ⟨flags, afterFlags⟩
    split at hrun
    · rename_i hminOnly
      dsimp only at hrun
      split at hrun
      · contradiction
      · rename_i parsedMin minPair hminRun
        rcases minPair with ⟨min, tail⟩
        cases hrun
        rcases readByte_sound start flags afterFlags hstart hflagsRun with
          ⟨flagBytes, hflagConsumed, hflagBytes⟩
        rcases Leb.Proof.u32_sound afterFlags min tail
            (hflagConsumed.finish_wellFormed hstart) hminRun with
          ⟨minBytes, hminConsumed, hminEncoding⟩
        simp at hminOnly
        rw [hflagBytes, hminOnly] at hflagConsumed
        exact ⟨0 :: minBytes, hflagConsumed.trans hminConsumed,
          Grammar.Limits.min minBytes min hminEncoding⟩
    · split at hrun
      · rename_i hminMax
        dsimp only at hrun
        split at hrun
        · contradiction
        · rename_i parsedMin minPair hminRun
          rcases minPair with ⟨min, afterMin⟩
          split at hrun
          · contradiction
          · rename_i parsedMax maxPair hmaxRun
            rcases maxPair with ⟨max, tail⟩
            cases hrun
            rcases readByte_sound start flags afterFlags hstart hflagsRun with
              ⟨flagBytes, hflagConsumed, hflagBytes⟩
            rcases Leb.Proof.u32_sound afterFlags min afterMin
                (hflagConsumed.finish_wellFormed hstart) hminRun with
              ⟨minBytes, hminConsumed, hminEncoding⟩
            rcases Leb.Proof.u32_sound afterMin max tail
                (hminConsumed.finish_wellFormed
                  (hflagConsumed.finish_wellFormed hstart)) hmaxRun with
              ⟨maxBytes, hmaxConsumed, hmaxEncoding⟩
            simp at hminMax
            rw [hflagBytes, hminMax] at hflagConsumed
            exact ⟨0x01 :: (minBytes ++ maxBytes),
              hflagConsumed.trans (hminConsumed.trans hmaxConsumed),
              Grammar.Limits.minMax minBytes maxBytes min max
                hminEncoding hmaxEncoding⟩
      · contradiction

theorem memoryType_sound :
    Sound memoryType Grammar.MemoryType := by
  intro start value finish hstart hrun
  unfold memoryType at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedLimits limitsPair hlimitsRun
    rcases limitsPair with ⟨limitsValue, tail⟩
    cases hrun
    rcases limits_sound start limitsValue tail hstart hlimitsRun with
      ⟨bytes, hconsumed, hencoding⟩
    exact ⟨bytes, hconsumed, Grammar.MemoryType.intro bytes limitsValue hencoding⟩

theorem constExpr_sound :
    Sound constExpr Grammar.ConstExpr := by
  intro start value finish hstart hrun
  unfold constExpr at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedOpcode opcodePair hopcodeRun
    rcases opcodePair with ⟨opcode, afterOpcode⟩
    split at hrun
    · rename_i hi32
      dsimp only at hrun
      split at hrun
      · contradiction
      · rename_i parsedValue valuePair hvalueRun
        rcases valuePair with ⟨integer, afterValue⟩
        split at hrun
        · contradiction
        · rename_i parsedEnd endPair hendRun
          rcases endPair with ⟨endValue, tail⟩
          cases hrun
          rcases readByte_sound start opcode afterOpcode hstart hopcodeRun with
            ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
          rcases Leb.Proof.s32_sound afterOpcode integer afterValue
              (hopcodeConsumed.finish_wellFormed hstart) hvalueRun with
            ⟨valueBytes, hvalueConsumed, hvalueEncoding⟩
          rcases expectByte_sound 11 afterValue endValue tail
              (hvalueConsumed.finish_wellFormed
                (hopcodeConsumed.finish_wellFormed hstart)) hendRun with
            ⟨endBytes, hendConsumed, hendBytes⟩
          simp at hi32
          rw [hopcodeBytes, hi32] at hopcodeConsumed
          rw [hendBytes] at hendConsumed
          refine ⟨65 :: (valueBytes ++ [11]), ?_, ?_⟩
          · simpa using hopcodeConsumed.trans
              (hvalueConsumed.trans hendConsumed)
          · exact Grammar.ConstExpr.i32 valueBytes integer hvalueEncoding
    · split at hrun
      · rename_i hi64
        dsimp only at hrun
        split at hrun
        · contradiction
        · rename_i parsedValue valuePair hvalueRun
          rcases valuePair with ⟨integer, afterValue⟩
          split at hrun
          · contradiction
          · rename_i parsedEnd endPair hendRun
            rcases endPair with ⟨endValue, tail⟩
            cases hrun
            rcases readByte_sound start opcode afterOpcode hstart hopcodeRun with
              ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
            rcases Leb.Proof.s64_sound afterOpcode integer afterValue
                (hopcodeConsumed.finish_wellFormed hstart) hvalueRun with
              ⟨valueBytes, hvalueConsumed, hvalueEncoding⟩
            rcases expectByte_sound 11 afterValue endValue tail
                (hvalueConsumed.finish_wellFormed
                  (hopcodeConsumed.finish_wellFormed hstart)) hendRun with
              ⟨endBytes, hendConsumed, hendBytes⟩
            simp at hi64
            rw [hopcodeBytes, hi64] at hopcodeConsumed
            rw [hendBytes] at hendConsumed
            refine ⟨66 :: (valueBytes ++ [11]), ?_, ?_⟩
            · simpa using hopcodeConsumed.trans
                (hvalueConsumed.trans hendConsumed)
            · exact Grammar.ConstExpr.i64 valueBytes integer hvalueEncoding
      · contradiction

theorem global_sound :
    Sound global Grammar.Global := by
  intro start value finish hstart hrun
  unfold global at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedType typePair htypeRun
    rcases typePair with ⟨type, middle⟩
    split at hrun
    · contradiction
    · rename_i parsedInit initPair hinitRun
      rcases initPair with ⟨init, tail⟩
      cases hrun
      rcases globalType_sound start type middle hstart htypeRun with
        ⟨typeBytes, htypeConsumed, htypeEncoding⟩
      rcases constExpr_sound middle init tail
          (htypeConsumed.finish_wellFormed hstart) hinitRun with
        ⟨initBytes, hinitConsumed, hinitEncoding⟩
      exact ⟨typeBytes ++ initBytes, htypeConsumed.trans hinitConsumed,
        Grammar.Global.intro typeBytes initBytes type init
          htypeEncoding hinitEncoding⟩

theorem exportDesc_sound :
    Sound exportDesc Grammar.ExportDesc := by
  intro start value finish hstart hrun
  unfold exportDesc at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedKind kindPair hkindRun
    rcases kindPair with ⟨kind, afterKind⟩
    split at hrun
    · rename_i hfunc
      dsimp only at hrun
      split at hrun
      · contradiction
      · rename_i parsedIndex indexPair hindexRun
        rcases indexPair with ⟨index, tail⟩
        cases hrun
        rcases readByte_sound start kind afterKind hstart hkindRun with
          ⟨kindBytes, hkindConsumed, hkindBytes⟩
        rcases Leb.Proof.u32_sound afterKind index tail
            (hkindConsumed.finish_wellFormed hstart) hindexRun with
          ⟨indexBytes, hindexConsumed, hindexEncoding⟩
        simp at hfunc
        rw [hkindBytes, hfunc] at hkindConsumed
        exact ⟨0 :: indexBytes, hkindConsumed.trans hindexConsumed,
          Grammar.ExportDesc.func indexBytes index hindexEncoding⟩
    · split at hrun
      · rename_i hmemory
        dsimp only at hrun
        split at hrun
        · contradiction
        · rename_i parsedIndex indexPair hindexRun
          rcases indexPair with ⟨index, tail⟩
          cases hrun
          rcases readByte_sound start kind afterKind hstart hkindRun with
            ⟨kindBytes, hkindConsumed, hkindBytes⟩
          rcases Leb.Proof.u32_sound afterKind index tail
              (hkindConsumed.finish_wellFormed hstart) hindexRun with
            ⟨indexBytes, hindexConsumed, hindexEncoding⟩
          simp at hmemory
          rw [hkindBytes, hmemory] at hkindConsumed
          exact ⟨2 :: indexBytes, hkindConsumed.trans hindexConsumed,
            Grammar.ExportDesc.memory indexBytes index hindexEncoding⟩
      · split at hrun
        · rename_i hglobal
          dsimp only at hrun
          split at hrun
          · contradiction
          · rename_i parsedIndex indexPair hindexRun
            rcases indexPair with ⟨index, tail⟩
            cases hrun
            rcases readByte_sound start kind afterKind hstart hkindRun with
              ⟨kindBytes, hkindConsumed, hkindBytes⟩
            rcases Leb.Proof.u32_sound afterKind index tail
                (hkindConsumed.finish_wellFormed hstart) hindexRun with
              ⟨indexBytes, hindexConsumed, hindexEncoding⟩
            simp at hglobal
            rw [hkindBytes, hglobal] at hkindConsumed
            exact ⟨3 :: indexBytes, hkindConsumed.trans hindexConsumed,
              Grammar.ExportDesc.global indexBytes index hindexEncoding⟩
        · contradiction

theorem exportEntry_sound :
    Sound exportEntry Grammar.Export := by
  intro start value finish hstart hrun
  unfold exportEntry at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedName namePair hnameRun
    rcases namePair with ⟨nameValue, middle⟩
    split at hrun
    · contradiction
    · rename_i parsedDesc descPair hdescRun
      rcases descPair with ⟨desc, tail⟩
      cases hrun
      rcases name_sound start nameValue middle hstart hnameRun with
        ⟨nameBytes, hnameConsumed, hnameEncoding⟩
      rcases exportDesc_sound middle desc tail
          (hnameConsumed.finish_wellFormed hstart) hdescRun with
        ⟨descBytes, hdescConsumed, hdescEncoding⟩
      exact ⟨nameBytes ++ descBytes, hnameConsumed.trans hdescConsumed,
        Grammar.Export.intro nameBytes descBytes nameValue desc
          hnameEncoding hdescEncoding⟩

theorem classifyLoop_sound
    {byte : UInt8} {opcodes : List Op} {opcode : Op}
    (h : classifyLoop byte opcodes = some opcode) :
    opcode.opcode = byte := by
  induction opcodes with
  | nil => contradiction
  | cons head rest ih =>
      unfold classifyLoop at h
      split at h
      · rename_i hequal
        cases h
        exact hequal
      · exact ih h

theorem classify_sound
    {byte : UInt8} {opcode : Op}
    (h : classify byte = some opcode) :
    opcode.opcode = byte := by
  exact classifyLoop_sound h

theorem plainInstruction_sound
    {start middle finish : Cursor} {byte : UInt8} {opcode : Op}
    {instructionValue result : Instr}
    (hstart : start.WellFormed)
    (hread : readByte start = .ok (byte, middle))
    (hclassify : classify byte = some opcode)
    (hrun : (Except.ok (instructionValue, middle) :
      Except Error (Instr × Cursor)) = .ok (result, finish))
    (hencoding : Grammar.Instr [opcode.opcode] instructionValue) :
    ∃ bytes, start.Consumed finish bytes ∧ Grammar.Instr bytes result := by
  cases hrun
  rcases readByte_sound start byte middle hstart hread with
    ⟨bytes, hconsumed, hbytes⟩
  have hopcode := classify_sound hclassify
  rw [hbytes, ← hopcode] at hconsumed
  exact ⟨[opcode.opcode], hconsumed, hencoding⟩

theorem operandInstruction_sound
    {start middle finish : Cursor} {byte : UInt8} {opcode : Op}
    {parser : Parser α} {relation : List UInt8 → α → Prop}
    {build : α → Instr} {result : Instr}
    (hstart : start.WellFormed)
    (hread : readByte start = .ok (byte, middle))
    (hclassify : classify byte = some opcode)
    (hparser : Sound parser relation)
    (hrun : (do pure (build (← parser))) middle = .ok (result, finish))
    (hencoding : ∀ bytes value,
      relation bytes value → Grammar.Instr (opcode.opcode :: bytes) (build value)) :
    ∃ bytes, start.Consumed finish bytes ∧ Grammar.Instr bytes result := by
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hoperandRun
    rcases pair with ⟨operand, tail⟩
    cases hrun
    rcases readByte_sound start byte middle hstart hread with
      ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
    rcases hparser middle operand tail
        (hopcodeConsumed.finish_wellFormed hstart) hoperandRun with
      ⟨operandBytes, hoperandConsumed, hoperandEncoding⟩
    have hopcode := classify_sound hclassify
    rw [hopcodeBytes, ← hopcode] at hopcodeConsumed
    exact ⟨opcode.opcode :: operandBytes,
      hopcodeConsumed.trans hoperandConsumed,
      hencoding operandBytes operand hoperandEncoding⟩

def SequenceEncoding (allowElse : Bool)
    (bytes : List UInt8) (result : List Instr × Terminator) : Prop :=
  match result.2 with
  | .end =>
      ∃ bodyBytes,
        bytes = bodyBytes ++ [11] ∧
        Grammar.Instrs bodyBytes result.1
  | .otherwise =>
      allowElse = true ∧
      ∃ bodyBytes,
        bytes = bodyBytes ++ [5] ∧
        Grammar.Instrs bodyBytes result.1

theorem instructionPair_sound (fuel : Nat) :
    Sound (instruction fuel) Grammar.Instr ∧
    ∀ allowElse, Sound (instructionSequence fuel allowElse)
      (SequenceEncoding allowElse) := by
  induction fuel with
  | zero =>
      constructor
      · intro start value finish hstart hrun
        unfold instruction at hrun
        contradiction
      · intro allowElse start value finish hstart hrun
        unfold instructionSequence at hrun
        contradiction
  | succ fuel ih =>
      constructor
      · intro start value finish hstart hrun
        unfold instruction at hrun
        dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
        split at hrun
        · contradiction
        · rename_i parsedByte bytePair hread
          rcases bytePair with ⟨byte, middle⟩
          dsimp only at hrun
          cases hclassify : classify byte with
          | none =>
            rw [hclassify] at hrun
            contradiction
          | some opcode =>
            rw [hclassify] at hrun
            cases opcode with
            | unreachable =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.unreachable
            | block =>
                dsimp only at hrun
                split at hrun
                · contradiction
                · rename_i parsedType typePair htypeRun
                  rcases typePair with ⟨type, afterType⟩
                  dsimp only at hrun
                  split at hrun
                  · contradiction
                  · rename_i parsedBody bodyPair hbodyRun
                    rcases bodyPair with ⟨bodyResult, tail⟩
                    rcases bodyResult with ⟨body, terminator⟩
                    cases terminator <;> try contradiction
                    cases hrun
                    rcases readByte_sound start byte middle hstart hread with
                      ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
                    rcases blockType_sound middle type afterType
                        (hopcodeConsumed.finish_wellFormed hstart) htypeRun with
                      ⟨typeBytes, htypeConsumed, htypeEncoding⟩
                    rcases ih.2 false afterType (body, .end) tail
                        (htypeConsumed.finish_wellFormed
                          (hopcodeConsumed.finish_wellFormed hstart)) hbodyRun with
                      ⟨sequenceBytes, hsequenceConsumed, hsequenceEncoding⟩
                    rcases hsequenceEncoding with
                      ⟨bodyBytes, hsequenceBytes, bodyEncoding⟩
                    rw [hsequenceBytes] at hsequenceConsumed
                    have hopcode := classify_sound hclassify
                    rw [hopcodeBytes, ← hopcode] at hopcodeConsumed
                    refine ⟨2 :: (typeBytes ++ bodyBytes ++ [11]), ?_, ?_⟩
                    · simpa [List.append_assoc, Op.opcode] using hopcodeConsumed.trans
                        (htypeConsumed.trans hsequenceConsumed)
                    · exact Grammar.Instr.block typeBytes bodyBytes type body
                        htypeEncoding bodyEncoding
            | loop =>
                dsimp only at hrun
                split at hrun
                · contradiction
                · rename_i parsedType typePair htypeRun
                  rcases typePair with ⟨type, afterType⟩
                  dsimp only at hrun
                  split at hrun
                  · contradiction
                  · rename_i parsedBody bodyPair hbodyRun
                    rcases bodyPair with ⟨bodyResult, tail⟩
                    rcases bodyResult with ⟨body, terminator⟩
                    cases terminator <;> try contradiction
                    cases hrun
                    rcases readByte_sound start byte middle hstart hread with
                      ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
                    rcases blockType_sound middle type afterType
                        (hopcodeConsumed.finish_wellFormed hstart) htypeRun with
                      ⟨typeBytes, htypeConsumed, htypeEncoding⟩
                    rcases ih.2 false afterType (body, .end) tail
                        (htypeConsumed.finish_wellFormed
                          (hopcodeConsumed.finish_wellFormed hstart)) hbodyRun with
                      ⟨sequenceBytes, hsequenceConsumed, hsequenceEncoding⟩
                    rcases hsequenceEncoding with
                      ⟨bodyBytes, hsequenceBytes, bodyEncoding⟩
                    rw [hsequenceBytes] at hsequenceConsumed
                    have hopcode := classify_sound hclassify
                    rw [hopcodeBytes, ← hopcode] at hopcodeConsumed
                    refine ⟨3 :: (typeBytes ++ bodyBytes ++ [11]), ?_, ?_⟩
                    · simpa [List.append_assoc, Op.opcode] using hopcodeConsumed.trans
                        (htypeConsumed.trans hsequenceConsumed)
                    · exact Grammar.Instr.loop typeBytes bodyBytes type body
                        htypeEncoding bodyEncoding
            | iff =>
                dsimp only at hrun
                split at hrun
                · contradiction
                · rename_i parsedType typePair htypeRun
                  rcases typePair with ⟨type, afterType⟩
                  dsimp only at hrun
                  split at hrun
                  · contradiction
                  · rename_i parsedThen thenPair hthenRun
                    rcases thenPair with ⟨thenResult, afterThen⟩
                    rcases thenResult with ⟨thenBody, thenTerminator⟩
                    cases thenTerminator with
                    | «end» =>
                        cases hrun
                        rcases readByte_sound start byte middle hstart hread with
                          ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
                        rcases blockType_sound middle type afterType
                            (hopcodeConsumed.finish_wellFormed hstart) htypeRun with
                          ⟨typeBytes, htypeConsumed, htypeEncoding⟩
                        rcases ih.2 true afterType (thenBody, .end) afterThen
                            (htypeConsumed.finish_wellFormed
                              (hopcodeConsumed.finish_wellFormed hstart)) hthenRun with
                          ⟨sequenceBytes, hsequenceConsumed, hsequenceEncoding⟩
                        rcases hsequenceEncoding with
                          ⟨thenBytes, hsequenceBytes, thenEncoding⟩
                        rw [hsequenceBytes] at hsequenceConsumed
                        have hopcode := classify_sound hclassify
                        rw [hopcodeBytes, ← hopcode] at hopcodeConsumed
                        refine ⟨4 :: (typeBytes ++ thenBytes ++ [11]), ?_, ?_⟩
                        · simpa [List.append_assoc, Op.opcode] using hopcodeConsumed.trans
                            (htypeConsumed.trans hsequenceConsumed)
                        · exact Grammar.Instr.iffNoElse typeBytes thenBytes type
                            thenBody htypeEncoding thenEncoding
                    | otherwise =>
                        dsimp only at hrun
                        split at hrun
                        · contradiction
                        · rename_i parsedElse elsePair helseRun
                          rcases elsePair with ⟨elseResult, tail⟩
                          rcases elseResult with ⟨elseBody, elseTerminator⟩
                          cases elseTerminator <;> try contradiction
                          cases hrun
                          rcases readByte_sound start byte middle hstart hread with
                            ⟨opcodeBytes, hopcodeConsumed, hopcodeBytes⟩
                          rcases blockType_sound middle type afterType
                              (hopcodeConsumed.finish_wellFormed hstart) htypeRun with
                            ⟨typeBytes, htypeConsumed, htypeEncoding⟩
                          rcases ih.2 true afterType (thenBody, .otherwise) afterThen
                              (htypeConsumed.finish_wellFormed
                                (hopcodeConsumed.finish_wellFormed hstart)) hthenRun with
                            ⟨thenSequenceBytes, hthenConsumed, hthenEncoding⟩
                          rcases ih.2 false afterThen (elseBody, .end) tail
                              (hthenConsumed.finish_wellFormed
                                (htypeConsumed.finish_wellFormed
                                  (hopcodeConsumed.finish_wellFormed hstart))) helseRun with
                            ⟨elseSequenceBytes, helseConsumed, helseEncoding⟩
                          rcases hthenEncoding with
                            ⟨allowed, thenBytes, hthenBytes, thenEncoding⟩
                          rcases helseEncoding with
                            ⟨elseBytes, helseBytes, elseEncoding⟩
                          rw [hthenBytes] at hthenConsumed
                          rw [helseBytes] at helseConsumed
                          have hopcode := classify_sound hclassify
                          rw [hopcodeBytes, ← hopcode] at hopcodeConsumed
                          refine ⟨4 :: (typeBytes ++ thenBytes ++
                            5 :: elseBytes ++ [11]), ?_, ?_⟩
                          · simpa [List.append_assoc, Op.opcode] using hopcodeConsumed.trans
                              (htypeConsumed.trans
                                (hthenConsumed.trans helseConsumed))
                          · exact Grammar.Instr.iffElse typeBytes thenBytes elseBytes
                              type thenBody elseBody htypeEncoding
                              thenEncoding elseEncoding
            | br =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.br bytes value h)
            | brIf =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.brIf bytes value h)
            | ret =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.ret
            | call =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.call bytes value h)
            | drop =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.drop
            | localGet =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.localGet bytes value h)
            | localSet =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.localSet bytes value h)
            | localTee =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.localTee bytes value h)
            | globalGet =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.globalGet bytes value h)
            | globalSet =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.globalSet bytes value h)
            | i32Load =>
                exact operandInstruction_sound hstart hread hclassify memArg_sound hrun
                  (fun bytes value h => Grammar.Instr.i32Load bytes value h)
            | i64Load =>
                exact operandInstruction_sound hstart hread hclassify memArg_sound hrun
                  (fun bytes value h => Grammar.Instr.i64Load bytes value h)
            | i32Load8U =>
                exact operandInstruction_sound hstart hread hclassify memArg_sound hrun
                  (fun bytes value h => Grammar.Instr.i32Load8U bytes value h)
            | i32Store =>
                exact operandInstruction_sound hstart hread hclassify memArg_sound hrun
                  (fun bytes value h => Grammar.Instr.i32Store bytes value h)
            | i64Store =>
                exact operandInstruction_sound hstart hread hclassify memArg_sound hrun
                  (fun bytes value h => Grammar.Instr.i64Store bytes value h)
            | i32Store8 =>
                exact operandInstruction_sound hstart hread hclassify memArg_sound hrun
                  (fun bytes value h => Grammar.Instr.i32Store8 bytes value h)
            | memorySize =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.memorySize bytes value h)
            | memoryGrow =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.u32_sound hrun
                  (fun bytes value h => Grammar.Instr.memoryGrow bytes value h)
            | i32Const =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.s32_sound hrun
                  (fun bytes value h => Grammar.Instr.i32Const bytes value h)
            | i64Const =>
                exact operandInstruction_sound hstart hread hclassify
                  Leb.Proof.s64_sound hrun
                  (fun bytes value h => Grammar.Instr.i64Const bytes value h)
            | i32Eqz =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i32Eqz
            | i32Eq =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i32Eq
            | i64Eqz =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Eqz
            | i64Eq =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Eq
            | i64Ne =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Ne
            | i64LtU =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64LtU
            | i64LeU =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64LeU
            | i64GeU =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64GeU
            | i32And =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i32And
            | i64Add =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Add
            | i64Sub =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Sub
            | i64Mul =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Mul
            | i64DivU =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64DivU
            | i64RemU =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64RemU
            | i64And =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64And
            | i64Or =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Or
            | i64Xor =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Xor
            | i64Shl =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64Shl
            | i64ShrU =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64ShrU
            | i32WrapI64 =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i32WrapI64
            | i64ExtendI32U =>
                exact plainInstruction_sound hstart hread hclassify hrun
                  Grammar.Instr.i64ExtendI32U
      · intro allowElse start value finish hstart hrun
        unfold instructionSequence at hrun
        dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
        split at hrun
        · contradiction
        · rename_i parsedNext nextPair hpeek
          rcases nextPair with ⟨next, afterPeek⟩
          split at hrun
          · rename_i hend
            dsimp only at hrun
            split at hrun
            · contradiction
            · rename_i parsedEnd endPair hread
              rcases endPair with ⟨read, tail⟩
              cases hrun
              have hsame := peekByte_readByte_eq hstart hpeek hread
              rcases hsame with ⟨hafterPeek, hreadValue⟩
              subst afterPeek
              rcases readByte_sound start read tail hstart hread with
                ⟨bytes, hconsumed, hbytes⟩
              simp at hend
              rw [hbytes, hreadValue, hend] at hconsumed
              exact ⟨[11], hconsumed, [], rfl, Grammar.Instrs.nil⟩
          · split at hrun
            · rename_i helse
              split at hrun
              · rename_i hallowed
                dsimp only at hrun
                split at hrun
                · contradiction
                · rename_i parsedElse elsePair hread
                  rcases elsePair with ⟨read, tail⟩
                  cases hrun
                  have hsame := peekByte_readByte_eq hstart hpeek hread
                  rcases hsame with ⟨hafterPeek, hreadValue⟩
                  subst afterPeek
                  rcases readByte_sound start read tail hstart hread with
                    ⟨bytes, hconsumed, hbytes⟩
                  simp at helse hallowed
                  rw [hbytes, hreadValue, helse] at hconsumed
                  exact ⟨[5], hconsumed, hallowed, [], rfl, Grammar.Instrs.nil⟩
              · contradiction
            · dsimp only at hrun
              split at hrun
              · contradiction
              · rename_i parsedFirst firstPair hfirstRun
                rcases firstPair with ⟨first, afterFirst⟩
                split at hrun
                · contradiction
                · rename_i parsedRest restPair hrestRun
                  rcases restPair with ⟨restResult, tail⟩
                  rcases restResult with ⟨rest, terminator⟩
                  cases hrun
                  rcases peekByte_sound start next afterPeek hstart hpeek with
                    ⟨peekBytes, hpeekConsumed, hpeekBytes⟩
                  rw [hpeekBytes] at hpeekConsumed
                  have hafterPeek := hpeekConsumed.eq_of_nil hstart
                  subst afterPeek
                  rcases ih.1 start first afterFirst hstart hfirstRun with
                    ⟨firstBytes, hfirstConsumed, hfirstEncoding⟩
                  rcases ih.2 allowElse afterFirst (rest, terminator) tail
                      (hfirstConsumed.finish_wellFormed hstart) hrestRun with
                    ⟨restBytes, hrestConsumed, hrestEncoding⟩
                  cases terminator with
                  | «end» =>
                    rcases hrestEncoding with
                      ⟨bodyBytes, hrestBytes, bodyEncoding⟩
                    rw [hrestBytes] at hrestConsumed
                    refine ⟨(firstBytes ++ bodyBytes) ++ [11], ?_, ?_⟩
                    · simpa [List.append_assoc] using
                        hfirstConsumed.trans hrestConsumed
                    · exact ⟨firstBytes ++ bodyBytes, rfl,
                        (Grammar.Instrs.cons firstBytes bodyBytes first rest
                          hfirstEncoding bodyEncoding)⟩
                  | otherwise =>
                    rcases hrestEncoding with
                      ⟨allowed, bodyBytes, hrestBytes, bodyEncoding⟩
                    rw [hrestBytes] at hrestConsumed
                    refine ⟨(firstBytes ++ bodyBytes) ++ [5], ?_, ?_⟩
                    · simpa [List.append_assoc] using
                        hfirstConsumed.trans hrestConsumed
                    · exact ⟨allowed, firstBytes ++ bodyBytes, rfl,
                        (Grammar.Instrs.cons firstBytes bodyBytes first rest
                          hfirstEncoding bodyEncoding)⟩

theorem instruction_sound (fuel : Nat) :
    Sound (instruction fuel) Grammar.Instr :=
  (instructionPair_sound fuel).1

theorem instructionSequence_sound (fuel : Nat) (allowElse : Bool) :
    Sound (instructionSequence fuel allowElse) (SequenceEncoding allowElse) :=
  (instructionPair_sound fuel).2 allowElse

def ExpressionEncoding (bytes : List UInt8) (body : List Instr) : Prop :=
  ∃ bodyBytes,
    bytes = bodyBytes ++ [11] ∧
    Grammar.Instrs bodyBytes body

theorem expression_sound :
    Sound expression ExpressionEncoding := by
  intro start body finish hstart hrun
  unfold expression at hrun
  cases hsequenceRun : instructionSequence start.remaining false start with
  | error error =>
    rw [hsequenceRun] at hrun
    contradiction
  | ok pair =>
    rcases pair with ⟨bodyResult, tail⟩
    rcases bodyResult with ⟨parsedBody, terminator⟩
    rw [hsequenceRun] at hrun
    cases terminator with
    | «end» =>
        cases hrun
        rcases instructionSequence_sound start.remaining false
            start (body, .end) finish hstart hsequenceRun with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, hencoding⟩
    | otherwise => contradiction

theorem codeBody_sound :
    Sound codeBody Grammar.CodeBody := by
  intro start value finish hstart hrun
  unfold codeBody at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedLocals localsPair hlocalsRun
    rcases localsPair with ⟨locals, middle⟩
    split at hrun
    · contradiction
    · rename_i parsedBody bodyPair hbodyRun
      rcases bodyPair with ⟨body, tail⟩
      cases hrun
      rcases vector_sound localDecl_sound start locals middle hstart hlocalsRun with
        ⟨localBytes, hlocalsConsumed, hlocalsEncoding⟩
      rcases expression_sound middle body tail
          (hlocalsConsumed.finish_wellFormed hstart) hbodyRun with
        ⟨expressionBytes, hexpressionConsumed, instructionBytes,
          hexpressionBytes, hinstructionsEncoding⟩
      rw [hexpressionBytes] at hexpressionConsumed
      exact ⟨localBytes ++ instructionBytes ++ [11],
        by simpa [List.append_assoc] using
          hlocalsConsumed.trans hexpressionConsumed,
        Grammar.CodeBody.intro localBytes instructionBytes locals body
          hlocalsEncoding hinstructionsEncoding⟩

theorem code_sound :
    Sound code Grammar.Code := by
  unfold code
  exact sized_sound codeBody_sound

def SectionUpdate (before : RawModule) (bytes : List UInt8)
    (id : SectionId) (after : RawModule) : Prop :=
  match id with
  | .type => ∃ values,
      after = { before with types := values } ∧
      Grammar.Sized (Grammar.Vector Grammar.FuncType) bytes values
  | .function => ∃ values,
      after = { before with functionTypeIndices := values } ∧
      Grammar.Sized (Grammar.Vector fun bs value => Grammar.U32 bs value.toNat)
        bytes values
  | .memory => ∃ values,
      after = { before with memories := values } ∧
      Grammar.Sized (Grammar.Vector Grammar.MemoryType) bytes values
  | .global => ∃ values,
      after = { before with globals := values } ∧
      Grammar.Sized (Grammar.Vector Grammar.Global) bytes values
  | .export => ∃ values,
      after = { before with exports := values } ∧
      Grammar.Sized (Grammar.Vector Grammar.Export) bytes values
  | .code => ∃ values,
      after = { before with codes := values } ∧
      Grammar.Sized (Grammar.Vector Grammar.Code) bytes values

theorem parseSection_sound (id : SectionId) (before : RawModule) :
    Sound (parseSection id before) (fun bytes after =>
      SectionUpdate before bytes id after) := by
  cases id with
  | type =>
      intro start after finish hstart hrun
      unfold parseSection at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hparse
        rcases pair with ⟨values, middle⟩
        cases hrun
        rcases sized_sound (vector_sound funcType_sound)
            start values middle hstart hparse with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, values, rfl, hencoding⟩
  | function =>
      intro start after finish hstart hrun
      unfold parseSection at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hparse
        rcases pair with ⟨values, middle⟩
        cases hrun
        rcases sized_sound (vector_sound Leb.Proof.u32_sound)
            start values middle hstart hparse with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, values, rfl, hencoding⟩
  | memory =>
      intro start after finish hstart hrun
      unfold parseSection at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hparse
        rcases pair with ⟨values, middle⟩
        cases hrun
        rcases sized_sound (vector_sound memoryType_sound)
            start values middle hstart hparse with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, values, rfl, hencoding⟩
  | global =>
      intro start after finish hstart hrun
      unfold parseSection at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hparse
        rcases pair with ⟨values, middle⟩
        cases hrun
        rcases sized_sound (vector_sound global_sound)
            start values middle hstart hparse with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, values, rfl, hencoding⟩
  | «export» =>
      intro start after finish hstart hrun
      unfold parseSection at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hparse
        rcases pair with ⟨values, middle⟩
        cases hrun
        rcases sized_sound (vector_sound exportEntry_sound)
            start values middle hstart hparse with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, values, rfl, hencoding⟩
  | code =>
      intro start after finish hstart hrun
      unfold parseSection at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hparse
        rcases pair with ⟨values, middle⟩
        cases hrun
        rcases sized_sound (vector_sound code_sound)
            start values middle hstart hparse with
          ⟨bytes, hconsumed, hencoding⟩
        exact ⟨bytes, hconsumed, values, rfl, hencoding⟩

theorem sectionInfo_sound {raw : UInt8} {id : SectionId} {rank : Nat}
    (h : sectionInfo raw = .ok (id, rank)) :
    raw = id.byte ∧ rank = id.rank := by
  unfold sectionInfo at h
  split at h
  · cases h
    exact ⟨‹raw = SectionId.type.byte›, rfl⟩
  · split at h
    · cases h
      exact ⟨‹raw = SectionId.function.byte›, rfl⟩
    · split at h
      · cases h
        exact ⟨‹raw = SectionId.memory.byte›, rfl⟩
      · split at h
        · cases h
          exact ⟨‹raw = SectionId.global.byte›, rfl⟩
        · split at h
          · cases h
            exact ⟨‹raw = SectionId.export.byte›, rfl⟩
          · split at h
            · cases h
              exact ⟨‹raw = SectionId.code.byte›, rfl⟩
            · contradiction

def SameField (id : SectionId) (first second : RawModule) : Prop :=
  match id with
  | .type => first.types = second.types
  | .function => first.functionTypeIndices = second.functionTypeIndices
  | .memory => first.memories = second.memories
  | .global => first.globals = second.globals
  | .export => first.exports = second.exports
  | .code => first.codes = second.codes

def FieldsAgree (ids : List SectionId) (first second : RawModule) : Prop :=
  ∀ id, id ∈ ids → SameField id first second

theorem FieldsAgree.refl (ids : List SectionId) (module_ : RawModule) :
    FieldsAgree ids module_ module_ := by
  intro id _
  cases id <;> rfl

theorem FieldsAgree.trans {ids : List SectionId} {first middle last : RawModule}
    (hfirst : FieldsAgree ids first middle)
    (hlast : FieldsAgree ids middle last) :
    FieldsAgree ids first last := by
  intro id hid
  have h₁ := hfirst id hid
  have h₂ := hlast id hid
  cases id <;> exact h₁.trans h₂

theorem SectionUpdate.sections_eq {before after : RawModule}
    {bytes : List UInt8} {id : SectionId}
    (h : SectionUpdate before bytes id after) :
    after.sections = before.sections := by
  cases id <;> simp only [SectionUpdate] at h <;>
    rcases h with ⟨values, rfl, _⟩ <;> rfl

theorem SectionUpdate.same_other {before after : RawModule}
    {bytes : List UInt8} {id other : SectionId}
    (h : SectionUpdate before bytes id after) (hne : other ≠ id) :
    SameField other before after := by
  cases id <;> simp only [SectionUpdate] at h <;>
    rcases h with ⟨values, rfl, _⟩ <;>
    cases other <;> simp_all [SameField]

theorem SectionUpdate.section {before after final : RawModule}
    {bytes : List UInt8} {id : SectionId}
    (hupdate : SectionUpdate before bytes id after)
    (hfield : SameField id after final) :
    Grammar.Section final (id.byte :: bytes) id := by
  cases id <;> simp only [SectionUpdate, SameField] at hupdate hfield <;>
    rcases hupdate with ⟨values, rfl, hencoding⟩
  · exact Grammar.Section.type bytes (hfield ▸ hencoding)
  · exact Grammar.Section.function bytes (hfield ▸ hencoding)
  · exact Grammar.Section.memory bytes (hfield ▸ hencoding)
  · exact Grammar.Section.global bytes (hfield ▸ hencoding)
  · exact Grammar.Section.export bytes (hfield ▸ hencoding)
  · exact Grammar.Section.code bytes (hfield ▸ hencoding)

theorem SameField.refl (id : SectionId) (module_ : RawModule) :
    SameField id module_ module_ := by
  cases id <;> rfl

theorem SameField.trans {id : SectionId} {first middle last : RawModule}
    (hfirst : SameField id first middle)
    (hlast : SameField id middle last) :
    SameField id first last := by
  cases id <;> exact Eq.trans hfirst hlast

theorem sameField_setSections (id : SectionId) (module_ : RawModule)
    (sections : List SectionId) :
    SameField id module_ { module_ with sections } := by
  cases id <;> rfl

def LoopEncoding (lastRank : Nat) (before : RawModule)
    (bytes : List UInt8) (after : RawModule) : Prop :=
  ∃ ids,
    after.sections = before.sections ++ ids ∧
    Grammar.Sections after bytes ids ∧
    Grammar.OrderedAfter lastRank ids ∧
    FieldsAgree before.sections before after ∧
    (∀ id, id ∉ ids → SameField id before after)

theorem sectionLoop_sound (fuel lastRank : Nat) (before : RawModule) :
    Sound (sectionLoop fuel lastRank before)
      (LoopEncoding lastRank before) := by
  induction fuel generalizing lastRank before with
  | zero =>
      intro start after finish hstart hrun
      unfold sectionLoop at hrun
      dsimp [remainingBytes, Bind.bind, Monad.toBind, Parser.instMonad,
        Except.bind] at hrun
      split at hrun
      · cases hrun
        exact ⟨[], Cursor.consumed_refl start hstart, [], by simp,
          Grammar.Sections.nil, Grammar.OrderedAfter.nil lastRank,
          FieldsAgree.refl before.sections before,
          fun id _ => SameField.refl id before⟩
      · contradiction
  | succ fuel ih =>
      intro start final finish hstart hrun
      unfold sectionLoop at hrun
      dsimp [remainingBytes, Bind.bind, Monad.toBind, Parser.instMonad,
        Except.bind] at hrun
      split at hrun
      · cases hrun
        exact ⟨[], Cursor.consumed_refl start hstart, [], by simp,
          Grammar.Sections.nil, Grammar.OrderedAfter.nil lastRank,
          FieldsAgree.refl before.sections before,
          fun id _ => SameField.refl id before⟩
      · rename_i hremaining
        unfold sectionStep at hrun
        dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
        cases hrawRun : readByte start with
        | error error =>
          simp only [hrawRun] at hrun
          contradiction
        | ok rawPair =>
          simp only [hrawRun] at hrun
          rcases rawPair with ⟨raw, afterRaw⟩
          cases hinfo : sectionInfo raw with
          | error error =>
              simp only [hinfo] at hrun
              contradiction
          | ok info =>
              rcases info with ⟨id, rank⟩
              simp only [hinfo] at hrun
              split at hrun
              · contradiction
              · rename_i hidFresh
                split at hrun
                · contradiction
                · rename_i hrank
                  cases hsectionRun : parseSection id before afterRaw with
                  | error error =>
                      simp only [hsectionRun] at hrun
                      contradiction
                  | ok sectionPair =>
                    simp only [hsectionRun] at hrun
                    rcases sectionPair with ⟨parsedModule, afterSection⟩
                    let nextModule : RawModule :=
                      { parsedModule with
                        sections := parsedModule.sections ++ [id] }
                    have hrecursive :
                        sectionLoop fuel rank nextModule afterSection =
                          .ok (final, finish) := by
                      simpa [nextModule] using hrun
                    rcases readByte_sound start raw afterRaw hstart hrawRun with
                      ⟨rawBytes, hrawConsumed, hrawBytes⟩
                    rcases parseSection_sound id before afterRaw parsedModule
                        afterSection (hrawConsumed.finish_wellFormed hstart)
                        hsectionRun with
                      ⟨payloadBytes, hpayloadConsumed, hupdate⟩
                    rcases ih rank nextModule afterSection final finish
                        (hpayloadConsumed.finish_wellFormed
                          (hrawConsumed.finish_wellFormed hstart))
                        hrecursive with
                      ⟨restBytes, hrestConsumed, ids, hfinalSections,
                        hrestEncoding, hrestOrder, hrestAgree,
                        hrestOutside⟩
                    rcases sectionInfo_sound hinfo with ⟨hrawId, hrankId⟩
                    rw [hrawBytes, hrawId] at hrawConsumed
                    have hparsedSections := hupdate.sections_eq
                    have hnextSections :
                        nextModule.sections = before.sections ++ [id] := by
                      simp [nextModule, hparsedSections]
                    have hidNext : id ∈ nextModule.sections := by
                      simp [hnextSections]
                    have hparsedNext :
                        SameField id parsedModule nextModule := by
                      exact sameField_setSections id parsedModule
                        (parsedModule.sections ++ [id])
                    have hcurrentField : SameField id parsedModule final :=
                      hparsedNext.trans (hrestAgree id hidNext)
                    have hcurrentSection :
                        Grammar.Section final (id.byte :: payloadBytes) id :=
                      hupdate.section hcurrentField
                    refine ⟨id.byte :: payloadBytes ++ restBytes,
                      hrawConsumed.trans
                        (hpayloadConsumed.trans hrestConsumed),
                      id :: ids, ?_, ?_, ?_, ?_, ?_⟩
                    · rw [hfinalSections, hnextSections]
                      simp [List.append_assoc]
                    · exact Grammar.Sections.cons
                        (id.byte :: payloadBytes) restBytes id ids
                        hcurrentSection hrestEncoding
                    · apply Grammar.OrderedAfter.cons lastRank id ids
                      · rw [← hrankId]
                        omega
                      · rw [hrankId] at hrestOrder
                        exact hrestOrder
                    · intro other hother
                      have hne : other ≠ id := by
                        intro hequal
                        subst other
                        exact hidFresh hother
                      have hbeforeParsed := hupdate.same_other hne
                      have hparsedNextOther :
                          SameField other parsedModule nextModule :=
                        sameField_setSections other parsedModule
                          (parsedModule.sections ++ [id])
                      have hotherNext : other ∈ nextModule.sections := by
                        rw [hnextSections]
                        simp [hother]
                      exact hbeforeParsed.trans
                        (hparsedNextOther.trans (hrestAgree other hotherNext))
                    · intro other houtside
                      have hne : other ≠ id := by
                        intro hequal
                        subst other
                        exact houtside (by simp)
                      have hnotRest : other ∉ ids := by
                        intro hin
                        exact houtside (by simp [hin])
                      have hbeforeParsed := hupdate.same_other hne
                      have hparsedNextOther :
                          SameField other parsedModule nextModule :=
                        sameField_setSections other parsedModule
                          (parsedModule.sections ++ [id])
                      exact hbeforeParsed.trans
                        (hparsedNextOther.trans (hrestOutside other hnotRest))

theorem loopDefault_absent {bytes : List UInt8} {module_ : RawModule}
    (hloop : LoopEncoding 0 default bytes module_) :
    Grammar.AbsentFieldsEmpty module_ := by
  rcases hloop with ⟨ids, hsections, _, _, _, houtside⟩
  have hids : module_.sections = ids := by
    change module_.sections = ([] : List SectionId) ++ ids at hsections
    simpa using hsections
  constructor
  · by_cases hpresent : SectionId.type ∈ module_.sections
    · exact Or.inl hpresent
    · right
      have hnotIds : SectionId.type ∉ ids := by
        intro hin
        apply hpresent
        rwa [hids]
      have hfield := houtside .type hnotIds
      change ([] : List FuncType) = module_.types at hfield
      exact hfield.symm
  · constructor
    · by_cases hpresent : SectionId.function ∈ module_.sections
      · exact Or.inl hpresent
      · right
        have hnotIds : SectionId.function ∉ ids := by
          intro hin
          apply hpresent
          rwa [hids]
        have hfield := houtside .function hnotIds
        change ([] : List UInt32) = module_.functionTypeIndices at hfield
        exact hfield.symm
    · constructor
      · by_cases hpresent : SectionId.memory ∈ module_.sections
        · exact Or.inl hpresent
        · right
          have hnotIds : SectionId.memory ∉ ids := by
            intro hin
            apply hpresent
            rwa [hids]
          have hfield := houtside .memory hnotIds
          change ([] : List MemoryType) = module_.memories at hfield
          exact hfield.symm
      · constructor
        · by_cases hpresent : SectionId.global ∈ module_.sections
          · exact Or.inl hpresent
          · right
            have hnotIds : SectionId.global ∉ ids := by
              intro hin
              apply hpresent
              rwa [hids]
            have hfield := houtside .global hnotIds
            change ([] : List Global) = module_.globals at hfield
            exact hfield.symm
        · constructor
          · by_cases hpresent : SectionId.export ∈ module_.sections
            · exact Or.inl hpresent
            · right
              have hnotIds : SectionId.export ∉ ids := by
                intro hin
                apply hpresent
                rwa [hids]
              have hfield := houtside .export hnotIds
              change ([] : List Export) = module_.exports at hfield
              exact hfield.symm
          · by_cases hpresent : SectionId.code ∈ module_.sections
            · exact Or.inl hpresent
            · right
              have hnotIds : SectionId.code ∉ ids := by
                intro hin
                apply hpresent
                rwa [hids]
              have hfield := houtside .code hnotIds
              change ([] : List Code) = module_.codes at hfield
              exact hfield.symm

theorem remainingBytes_run {start finish : Cursor} {value : Nat}
    (h : remainingBytes start = .ok (value, finish)) :
    value = start.remaining ∧ finish = start := by
  unfold remainingBytes at h
  cases h
  exact ⟨rfl, rfl⟩

theorem moduleParser_sound :
    Sound moduleParser Grammar.ModuleBytes := by
  intro start module_ finish hstart hrun
  unfold moduleParser at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedMagic magicPair hmagicRun
    rcases magicPair with ⟨magicValue, afterMagic⟩
    split at hrun
    · contradiction
    · rename_i parsedVersion versionPair hversionRun
      rcases versionPair with ⟨versionValue, afterVersion⟩
      split at hrun
      · contradiction
      · rename_i parsedRemaining remainingPair hremainingRun
        rcases remainingPair with ⟨remaining, afterRemaining⟩
        rcases expectBytes_sound [0, 97, 115, 109]
            start magicValue afterMagic hstart hmagicRun with
          ⟨magicBytes, hmagicConsumed, hmagicBytes⟩
        rcases expectBytes_sound [1, 0, 0, 0]
            afterMagic versionValue afterVersion
            (hmagicConsumed.finish_wellFormed hstart) hversionRun with
          ⟨versionBytes, hversionConsumed, hversionBytes⟩
        rcases remainingBytes_run hremainingRun with
          ⟨hremainingValue, hremainingCursor⟩
        subst afterRemaining
        rcases sectionLoop_sound remaining 0 default afterVersion module_
            finish
            (hversionConsumed.finish_wellFormed
              (hmagicConsumed.finish_wellFormed hstart)) hrun with
          ⟨sectionBytes, hsectionConsumed, hloop⟩
        have habsent := loopDefault_absent hloop
        rcases hloop with
          ⟨ids, hsections, hsectionEncoding, horder, _, _⟩
        have hmoduleSections : module_.sections = ids := by
          change module_.sections = ([] : List SectionId) ++ ids at hsections
          simpa using hsections
        rw [hmagicBytes] at hmagicConsumed
        rw [hversionBytes] at hversionConsumed
        refine ⟨[0, 97, 115, 109, 1, 0, 0, 0] ++ sectionBytes, ?_, ?_⟩
        · simpa [List.append_assoc] using hmagicConsumed.trans
            (hversionConsumed.trans hsectionConsumed)
        · refine ⟨sectionBytes, rfl, ?_, ?_, habsent⟩
          · rw [hmoduleSections]
            exact hsectionEncoding
          · rw [hmoduleSections]
            exact horder

theorem decode_sound {bytes : ByteArray} {module_ : RawModule}
    (h : decode bytes = .ok module_) :
    Grammar.Encodes bytes module_ := by
  exact Parser.runAll_sound moduleParser_sound h

end Wasm.Binary.Proof
