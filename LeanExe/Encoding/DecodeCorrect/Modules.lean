import LeanExe.Encoding.DecodeCorrect.Instructions
import LeanExe.Encoding.Spec.Modules

namespace Wasm.Encoding.Decoder

open Wasm.Encoding.Spec

theorem Parses.run_bind {p : Parser α} {f : α → Parser β} {bytes rest : List UInt8} {value : α}
    (h : Parses p bytes value) :
    StateT.run (p >>= f) (bytes ++ rest) = StateT.run (f value) rest := by
  rw [StateT.run_bind, h rest]
  rfl

theorem run_remaining_bind (f : Nat → Parser α) (input : List UInt8) :
    StateT.run (remaining >>= f) input = StateT.run (f input.length) input :=
  rfl

theorem run_byte_bind (f : UInt8 → Parser α) (b : UInt8) (input : List UInt8) :
    StateT.run (byte >>= f) (b :: input) = StateT.run (f b) input :=
  rfl

theorem Parses.remaining {f : Nat → Parser α} {bytes : List UInt8} {value : α}
    (h : ∀ n, bytes.length ≤ n → Parses (f n) bytes value) :
    Parses (Decoder.remaining >>= f) bytes value := by
  intro rest
  rw [run_remaining_bind]
  exact h (bytes ++ rest).length (by simp) rest

theorem parses_many_map_mem {item : Parser β} {relation : List UInt8 → α → Prop} {g : α → β}
    {bytes : List UInt8} {values : List α} (h : Items relation bytes values)
    (hItem : ∀ bytes value, value ∈ values → relation bytes value → Parses item bytes (g value)) :
    Parses (many item values.length) bytes (values.map g) := by
  induction h with
  | nil => exact Parses.pure' _
  | cons headBytes tailBytes head tail headEncoding tailEncoding ih =>
      rw [List.length_cons, many, List.map_cons]
      refine Parses.bind (hItem _ _ (List.mem_cons_self ..) headEncoding) ?_
      refine Parses.bind_nil (ih fun b v hMem hRel => hItem b v (List.mem_cons_of_mem _ hMem) hRel) ?_
      exact Parses.pure' _

theorem parses_vec_map_mem {item : Parser β} {relation : List UInt8 → α → Prop} {g : α → β}
    {bytes : List UInt8} {values : List α} (h : Vector relation bytes values)
    (hItem : ∀ bytes value, value ∈ values → relation bytes value → Parses item bytes (g value))
    (hNonempty : ∀ bytes value, relation bytes value → bytes ≠ []) :
    Parses (vec item) bytes (values.map g) := by
  cases h with
  | intro countBytes body values count items =>
      intro rest
      have hLength := items_length_le hNonempty items
      have hNot : ¬ (body ++ rest).length < values.length := by
        simp only [List.length_append]
        omega
      show StateT.run (vec item) (countBytes ++ body ++ rest) = _
      unfold vec
      rw [StateT.run_bind, List.append_assoc,
        parses_unsigned count 32 (Nat.le_refl _) (body ++ rest)]
      show StateT.run (Decoder.remaining >>= fun available =>
        if available < values.length then malformed "unexpected end"
        else many item values.length) (body ++ rest) = _
      rw [run_remaining_bind]
      show StateT.run (if (body ++ rest).length < values.length then malformed "unexpected end"
        else many item values.length) (body ++ rest) = _
      rw [ite_eq_right hNot]
      exact parses_many_map_mem items hItem rest

theorem ones_sum (types : List ValueType) :
    ((types.map fun type => (1, type)).map (·.1)).sum = types.length := by
  induction types with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

theorem ones_flatMap (types : List ValueType) :
    (types.map fun type => (1, type)).flatMap
      (fun (count, type) => List.replicate count type) = types := by
  induction types with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      rfl

theorem parses_codeBody {bytes : List UInt8} {func : Wasm.Function} (h : CodeBody bytes func)
    (hLocals : func.locals.length ≤ maxLocals) :
    Parses codeBody bytes (func.locals, func.body) := by
  match h with
  | .intro localBytes instructionBytes func localsEncoding instructionsEncoding =>
      have hVec := parses_vec_map (g := fun type => (1, type)) (fun _ _ h => parses_local h)
        (fun _ _ h => local_nonempty h) localsEncoding
      have hCount : ¬ 2 ^ 32 ≤ func.locals.length :=
        Nat.not_le.mpr (vector_length_lt localsEncoding)
      have hLimit : ¬ maxLocals < func.locals.length := Nat.not_lt.mpr hLocals
      unfold codeBody
      rw [List.append_assoc]
      refine Parses.bind hVec ?_
      dsimp only
      rw [ones_sum, ite_eq_right hCount, ite_eq_right hLimit, ones_flatMap]
      refine Parses.remaining fun n hn => ?_
      have hFuel : instructionBytes.length < n := by
        simp only [List.length_append, List.length_singleton] at hn
        omega
      exact Parses.bind_nil (instrs_seq instructionsEncoding n hFuel).1 (Parses.pure' _)

theorem parses_code {bytes : List UInt8} {func : Wasm.Function} (h : Sized CodeBody bytes func)
    (hLocals : func.locals.length ≤ maxLocals) :
    Parses code bytes (func.locals, func.body) := by
  match h with
  | .intro countBytes body _ count payload =>
      unfold code
      exact Parses.bind (parses_unsigned count 32 (Nat.le_refl _))
        (parses_within (parses_codeBody payload hLocals))

theorem sized_nonempty {relation : List UInt8 → α → Prop} {bytes : List UInt8} {value : α}
    (h : Sized relation bytes value) : bytes ≠ [] := by
  match h with
  | .intro countBytes _ _ count _ =>
      have := unsigned_nonempty count
      cases countBytes with
      | nil => exact absurd rfl this
      | cons _ _ => simp

theorem function_indices {types : List Wasm.FuncType} {bytes : List UInt8}
    {funcs : List Wasm.Function} (h : Items (FunctionIndex types) bytes funcs) :
    ∀ f ∈ funcs, ∃ index, f.typeIdx = some index ∧ types[index]? = some (signature f) := by
  induction h with
  | nil => simp
  | cons headBytes tailBytes head tail headEncoding tailEncoding ih =>
      intro f hMem
      rcases List.mem_cons.mp hMem with rfl | hTail
      · match headEncoding with
        | .intro _ index _ _ declaredIndex declaredType => exact ⟨index, declaredIndex, declaredType⟩
      · exact ih f hTail

theorem parses_functions {types : List Wasm.FuncType} {funcs : List Wasm.Function}
    (h : ∀ f ∈ funcs, ∃ index, f.typeIdx = some index ∧ types[index]? = some (signature f)) :
    Parses (functions types (funcs.map (·.typeIdx.getD 0))
      (funcs.map fun f => (f.locals, f.body))) [] funcs := by
  induction funcs with
  | nil => exact Parses.pure' _
  | cons f rest ih =>
      obtain ⟨index, hIndex, hType⟩ := h f (List.mem_cons_self ..)
      have hRest := ih fun g hMem => h g (List.mem_cons_of_mem _ hMem)
      simp only [List.map_cons]
      rw [functions]
      refine Parses.bind_nil (p := function types (f.typeIdx.getD 0) (f.locals, f.body))
        (v₁ := f) ?_ (Parses.bind_nil hRest (Parses.pure' _))
      unfold function
      rw [hIndex, Option.getD_some, hType]
      dsimp only
      have hRecord :
          ({ params := (signature f).params, locals := f.locals, body := f.body,
             results := (signature f).results, typeIdx := some index } : Wasm.Function) = f := by
        cases f
        simp only at hIndex
        simp [signature, hIndex]
      rw [hRecord]
      exact Parses.pure' _

theorem contents_types {acc : Sections} {payload : List UInt8} {value : List Wasm.FuncType}
    (h : Parses (vec funcType) payload value) :
    Parses (sectionContents 1 payload.length acc) payload { acc with types := value } := by
  show Parses (do return { acc with types := ← within payload.length (vec funcType) }) payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem contents_imports {acc : Sections} {payload : List UInt8} {value : List ImportDecl}
    (h : Parses (vec (importDecl acc.types)) payload value) :
    Parses (sectionContents 2 payload.length acc) payload { acc with imports := value } := by
  show Parses (do
    return { acc with imports := ← within payload.length (vec (importDecl acc.types)) })
    payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem contents_functions {acc : Sections} {payload : List UInt8} {value : List Nat}
    (h : Parses (vec (unsigned 32)) payload value) :
    Parses (sectionContents 3 payload.length acc) payload { acc with functions := value } := by
  show Parses (do
    return { acc with functions := ← within payload.length (vec (unsigned 32)) }) payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem contents_memory {acc : Sections} {payload : List UInt8} {value : Option MemDecl}
    (h : Parses memories payload value) :
    Parses (sectionContents 5 payload.length acc) payload { acc with memory := value } := by
  show Parses (do return { acc with memory := ← within payload.length memories }) payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem contents_globals {acc : Sections} {payload : List UInt8} {value : List GlobalDecl}
    (h : Parses (vec global) payload value) :
    Parses (sectionContents 6 payload.length acc) payload { acc with globals := value } := by
  show Parses (do return { acc with globals := ← within payload.length (vec global) }) payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem contents_exports {acc : Sections} {payload : List UInt8}
    {value : List (UInt8 × String × Nat)} (h : Parses (vec exportEntry) payload value) :
    Parses (sectionContents 7 payload.length acc) payload { acc with exports := value } := by
  show Parses (do
    return { acc with exports := ← within payload.length (vec exportEntry) }) payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem contents_codes {acc : Sections} {payload : List UInt8}
    {value : List (List ValueType × Program)} (h : Parses (vec code) payload value) :
    Parses (sectionContents 10 payload.length acc) payload { acc with codes := value } := by
  show Parses (do return { acc with codes := ← within payload.length (vec code) }) payload _
  exact Parses.bind_nil (parses_within h) (Parses.pure' _)

theorem sections_step {fuel last : Nat} {acc acc' : Sections} {id : UInt8}
    {sizeBytes payload tail : List UInt8}
    (hId : id ≠ 0) (hKnown : sectionOrder id ≠ 0) (hOrder : ¬ sectionOrder id ≤ last)
    (hSize : Unsigned 32 sizeBytes payload.length)
    (hContents : Parses (sectionContents id payload.length acc) payload acc') :
    StateT.run (sections (fuel + 1) last acc) (id :: (sizeBytes ++ payload) ++ tail) =
      StateT.run (sections fuel (sectionOrder id) acc') tail := by
  rw [sections, run_remaining_bind]
  try dsimp only
  rw [ite_eq_right (by simp), List.cons_append, run_byte_bind]
  try dsimp only
  rw [List.append_assoc, Parses.run_bind (parses_unsigned hSize 32 (Nat.le_refl _))]
  try dsimp only
  rw [ite_eq_right hId, ite_eq_right hKnown, ite_eq_right hOrder, Parses.run_bind hContents]

theorem sections_done (fuel last : Nat) (acc : Sections) :
    StateT.run (sections (fuel + 1) last acc) [] = .ok (acc, []) := by
  rw [sections, run_remaining_bind]
  rfl

theorem section_length {relation : List UInt8 → α → Prop} {id : UInt8} {bytes : List UInt8}
    {value : α} (h : Section id relation bytes value) : 2 ≤ bytes.length := by
  match h with
  | .intro sizeBytes payload _ size _ =>
      have := unsigned_nonempty size
      cases sizeBytes with
      | nil => exact absurd rfl this
      | cons _ _ => simp

def expected (m : Wasm.Module) : Sections :=
  { types := m.types, imports := m.imports,
    functions := m.funcs.map (·.typeIdx.getD 0), memory := m.memory, globals := m.globals,
    exports := exports m, codes := m.funcs.map fun f => (f.locals, f.body) }

theorem sections_run {m : Wasm.Module}
    {types imports functions memories globals exportBytes codes : List UInt8}
    (typeSection : Section 1 (Vector Spec.FuncType) types m.types)
    (importSection : Section 2 (Vector (Import m.types)) imports m.imports)
    (functionSection : Section 3 (Vector (FunctionIndex m.types)) functions m.funcs)
    (memorySection : Section 5 (Vector Memory) memories m.memory.toList)
    (globalSection : Section 6 (Vector Global) globals m.globals)
    (exportSection : Section 7 (Vector Spec.Export) exportBytes (exports m))
    (codeSection : Section 10 (Vector (Sized CodeBody)) codes m.funcs)
    (hLocals : ∀ f ∈ m.funcs, f.locals.length ≤ maxLocals) (fuel : Nat) :
    StateT.run (sections (fuel + 8) 0 {})
      (types ++ (imports ++ (functions ++ (memories ++ (globals ++ (exportBytes ++ codes)))))) =
        .ok (expected m, []) := by
  match typeSection, importSection, functionSection, memorySection, globalSection,
      exportSection, codeSection with
  | .intro typeSize typePayload _ typeSizeEncoding typeEncoding,
    .intro importSize importPayload _ importSizeEncoding importEncoding,
    .intro functionSize functionPayload _ functionSizeEncoding functionEncoding,
    .intro memorySize memoryPayload _ memorySizeEncoding memoryEncoding,
    .intro globalSize globalPayload _ globalSizeEncoding globalEncoding,
    .intro exportSize exportPayload _ exportSizeEncoding exportEncoding,
    .intro codeSize codePayload _ codeSizeEncoding codeEncoding =>
      have hTypes := parses_vec_map (g := id) (fun _ _ h => parses_funcType h)
        (fun _ _ h => funcType_nonempty h) typeEncoding
      have hImports := parses_vec_map (g := id) (fun _ _ h => parses_importDecl h)
        (fun _ _ h => import_nonempty h) importEncoding
      have hFunctions := parses_vec_map (g := fun f => f.typeIdx.getD 0)
        (fun _ _ h => parses_functionIndex h) (fun _ _ h => functionIndex_nonempty h)
        functionEncoding
      have hMemories := parses_memories memoryEncoding
      have hGlobals := parses_vec_map (g := id) (fun _ _ h => parses_global h)
        (fun _ _ h => global_nonempty h) globalEncoding
      have hExports := parses_vec_map (g := id) (fun _ _ h => parses_exportEntry h)
        (fun _ _ h => export_nonempty h) exportEncoding
      have hCodes := parses_vec_map_mem (g := fun f => (f.locals, f.body)) codeEncoding
        (fun _ f hMem h => parses_code h (hLocals f hMem)) (fun _ _ h => sized_nonempty h)
      simp only [List.map_id] at hTypes hImports hGlobals hExports
      let acc1 : Sections := { types := m.types }
      let acc2 : Sections := { acc1 with imports := m.imports }
      let acc3 : Sections := { acc2 with functions := m.funcs.map (·.typeIdx.getD 0) }
      let acc4 : Sections := { acc3 with memory := m.memory }
      let acc5 : Sections := { acc4 with globals := m.globals }
      let acc6 : Sections := { acc5 with exports := exports m }
      rw [show fuel + 8 = fuel + 7 + 1 by rfl,
        sections_step (id := 1) (acc := {}) (by decide) (by decide) (by decide) typeSizeEncoding
          (contents_types hTypes),
        sections_step (id := 2) (acc := acc1) (by decide) (by decide) (by decide)
          importSizeEncoding (contents_imports hImports),
        sections_step (id := 3) (acc := acc2) (by decide) (by decide) (by decide)
          functionSizeEncoding (contents_functions hFunctions),
        sections_step (id := 5) (acc := acc3) (by decide) (by decide) (by decide)
          memorySizeEncoding (contents_memory hMemories),
        sections_step (id := 6) (acc := acc4) (by decide) (by decide) (by decide)
          globalSizeEncoding (contents_globals hGlobals),
        sections_step (id := 7) (acc := acc5) (by decide) (by decide) (by decide)
          exportSizeEncoding (contents_exports hExports),
        ← List.append_nil (10 :: (codeSize ++ codePayload)),
        sections_step (id := 10) (acc := acc6) (by decide) (by decide) (by decide)
          codeSizeEncoding (contents_codes hCodes),
        sections_done]
      rfl

theorem filterMap_funcs (entries : List Wasm.Export) :
    (entries.map fun e => ((0 : UInt8), e.name, e.funcIdx)).filterMap
      (fun (kind, exportName, index) =>
        if kind = 0x00 then some ({ name := exportName, funcIdx := index } : Wasm.Export)
        else none) = entries := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, List.filterMap_cons, ih]
      rfl

theorem filterMap_funcs_pairs (kind : UInt8) (hKind : kind ≠ 0) (entries : List (String × Nat)) :
    (entries.map fun e => (kind, e.1, e.2)).filterMap
      (fun (kind, exportName, index) =>
        if kind = 0x00 then some ({ name := exportName, funcIdx := index } : Wasm.Export)
        else none) = [] := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, List.filterMap_cons, ih]
      simp [hKind]

theorem filterMap_pairs_self (kind : UInt8) (entries : List (String × Nat)) :
    (entries.map fun e => (kind, e.1, e.2)).filterMap
      (fun (kind', exportName, index) =>
        if kind' = kind then some (exportName, index) else none) = entries := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, List.filterMap_cons, ih]
      simp

theorem filterMap_pairs_other (kind other : UInt8) (hOther : other ≠ kind)
    (entries : List (String × Nat)) :
    (entries.map fun e => (other, e.1, e.2)).filterMap
      (fun (kind', exportName, index) =>
        if kind' = kind then some (exportName, index) else none) = [] := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, List.filterMap_cons, ih]
      simp [hOther]

theorem filterMap_pairs_funcs (kind : UInt8) (hKind : (0 : UInt8) ≠ kind)
    (entries : List Wasm.Export) :
    (entries.map fun e => ((0 : UInt8), e.name, e.funcIdx)).filterMap
      (fun (kind', exportName, index) =>
        if kind' = kind then some (exportName, index) else none) = [] := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, List.filterMap_cons, ih]
      simp [hKind]

theorem assemble_expected {m : Wasm.Module} (shape : Shape m) :
    assemble (expected m) m.funcs = m := by
  obtain ⟨hExtra, hData, hStart, hGc, hTables, hElements, hImportedGlobals, hImportedTables,
    hImportedMemories, hImportedTags, hTableExports, hTagExports, hTags⟩ := shape
  cases m
  dsimp only at hExtra hData hStart hGc hTables hElements hImportedGlobals
  dsimp only at hImportedTables hImportedMemories hImportedTags hTableExports hTagExports hTags
  subst hExtra hData hStart hGc hTables hElements hImportedGlobals hImportedTables
  subst hImportedMemories hImportedTags hTableExports hTagExports hTags
  simp only [assemble, expected, exports, List.filterMap_append, filterMap_funcs,
    filterMap_funcs_pairs 3 (by decide), filterMap_funcs_pairs 2 (by decide),
    filterMap_pairs_self, filterMap_pairs_other 3 2 (by decide),
    filterMap_pairs_other 2 3 (by decide), filterMap_pairs_funcs 3 (by decide),
    filterMap_pairs_funcs 2 (by decide), List.append_nil, List.nil_append]

theorem moduleParser_run {bytes : List UInt8} {m : Wasm.Module} (h : ModuleBytes bytes m)
    (hLocals : ∀ f ∈ m.funcs, f.locals.length ≤ maxLocals) :
    StateT.run moduleParser bytes = .ok (m, []) := by
  match h with
  | .intro m types imports functions memories globals exportBytes codes shape typeSection
      importSection functionSection memorySection globalSection exportSection codeSection =>
      have hLength : 8 ≤ (types ++ (imports ++ (functions ++ (memories ++
          (globals ++ (exportBytes ++ codes)))))).length := by
        have := section_length typeSection
        have := section_length importSection
        have := section_length functionSection
        have := section_length memorySection
        simp only [List.length_append]
        omega
      obtain ⟨fuel, hFuel⟩ : ∃ fuel, (types ++ (imports ++ (functions ++ (memories ++
          (globals ++ (exportBytes ++ codes)))))).length = fuel + 8 :=
        ⟨_ - 8, (Nat.sub_add_cancel hLength).symm⟩
      have hSections := sections_run typeSection importSection functionSection memorySection
        globalSection exportSection codeSection hLocals fuel
      have hIndices : ∀ f ∈ m.funcs, ∃ index, f.typeIdx = some index ∧
          m.types[index]? = some (signature f) := by
        match functionSection with
        | .intro _ _ _ _ encoding =>
            match encoding with
            | .intro _ _ _ _ items => exact function_indices items
      have hFunctions := parses_functions hIndices
      simp only [List.append_assoc]
      rw [show [(0 : UInt8), 97, 115, 109, 1, 0, 0, 0] ++
          (types ++ (imports ++ (functions ++ (memories ++ (globals ++ (exportBytes ++ codes)))))) =
          [0, 97, 115, 109] ++ ([1, 0, 0, 0] ++
          (types ++ (imports ++ (functions ++ (memories ++ (globals ++ (exportBytes ++ codes))))))) from rfl]
      unfold moduleParser
      rw [Parses.run_bind (p := take 4) (parses_take [0, 97, 115, 109])]
      rw [ite_eq_right (by decide)]
      rw [Parses.run_bind (p := take 4) (parses_take [1, 0, 0, 0])]
      rw [ite_eq_right (by decide)]
      rw [run_remaining_bind, hFuel, StateT.run_bind, hSections]
      show StateT.run (Decoder.functions m.types (m.funcs.map (·.typeIdx.getD 0))
        (m.funcs.map fun f => (f.locals, f.body)) >>=
          fun funcs => pure (assemble (expected m) funcs)) ([] ++ []) = Except.ok (m, [])
      rw [Parses.run_bind hFunctions, assemble_expected shape]
      rfl

end Wasm.Encoding.Decoder
