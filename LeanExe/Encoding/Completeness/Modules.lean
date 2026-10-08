import LeanExe.Encoding.Completeness.Instructions

namespace Wasm.Encoding

theorem limits_produces (minimum : UInt32) (maximum : Option UInt32) :
    ∃ output, limits minimum maximum = .ok output ∧
      output.val.length = Size.limits minimum maximum := by
  obtain ⟨lower, hl, hls⟩ := u32_produces minimum.toNat minimum.toNat_lt
  cases maximum with
  | none =>
      simp only [limits, hl]
      refine ⟨_, rfl, ?_⟩
      simp [Size.limits, hls, Nat.add_comm]
  | some maximum =>
      obtain ⟨upper, hu, hus⟩ := u32_produces maximum.toNat maximum.toNat_lt
      simp only [limits, hl, hu]
      refine ⟨_, rfl, ?_⟩
      simp [Size.limits, hls, hus, Nat.add_assoc, Nat.add_comm]

theorem memory_produces (decl : Wasm.MemDecl)
    (form : decl.data = [] ∧ decl.is64 = false) :
    Produces (memory decl) (Size.memory decl) := by
  rcases decl with ⟨minimum, maximum, data, is64⟩
  rcases form with ⟨rfl, rfl⟩
  obtain ⟨encoded, he, hes⟩ := limits_produces minimum maximum
  simp only [Produces, memory, he]
  exact ⟨_, rfl, hes⟩

theorem dataSegment_produces (segment : Wasm.DataSegment) (ready : DataReady segment) :
    Produces (dataSegment segment) (Size.dataSegment segment) := by
  cases ready with
  | intro offset bytes length =>
      obtain ⟨encodedLength, hl, hls⟩ := u32_produces bytes.length length
      simp only [Produces, dataSegment, hl]
      refine ⟨_, rfl, ?_⟩
      simp [signed32, Size.dataSegment, Size.s32, hls]
      omega

theorem global_produces (decl : Wasm.GlobalDecl) (ready : GlobalReady decl) :
    Produces (global decl) (Size.global decl) := by
  cases ready with
  | i32 value mutable =>
      simp only [Produces, global]
      refine ⟨_, rfl, ?_⟩
      cases mutable <;> simp [mutability, signed32, Size.global, Size.s32, Nat.add_comm] <;> omega
  | i64 value mutable =>
      simp only [Produces, global]
      refine ⟨_, rfl, ?_⟩
      cases mutable <;> simp [mutability, signed64, Size.global, Size.s64, Nat.add_comm] <;> omega

theorem localEntry_produces (type : Wasm.ValueType) (numeric : Numeric type) :
    Produces (localEntry type) 2 := by
  obtain ⟨encoded, he, hes⟩ := valueType_produces type numeric
  simp only [Produces, localEntry, he]
  exact ⟨_, rfl, by simp [hes]⟩

theorem functionBody_produces (types : List Wasm.FuncType) (func : Wasm.Function)
    (ready : FunctionReady types func) :
    Produces (functionBody func) (Size.functionBody func) := by
  obtain ⟨locals, hl, hls⟩ := vector_produces localEntry (fun _ => 2) func.locals
    ready.localCount (fun t member => localEntry_produces t (ready.locals t member))
  obtain ⟨body, hb, hbs⟩ := program_produces func.body ready.body
  simp only [functionBody, hl, hb, Except.bind, bind]
  apply sized_produces _ (Size.bodyPayload func) _ ready.bodySize
  simp only [List.length_append, List.length_singleton, hls, hbs, Size.vector,
    List.length_map, sum_const, Size.bodyPayload]

theorem signatureIndex_produces (signature : Wasm.FuncType) (types : List Wasm.FuncType)
    (member : signature ∈ types) :
    ∃ index, signatureIndex signature types = .ok index ∧
      index.val = Size.typeIndex signature types := by
  induction types with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : head = signature
      · simp only [signatureIndex, same, dite_true, Size.typeIndex, ite_true]
        exact ⟨_, rfl, rfl⟩
      · have rest : signature ∈ tail := by simpa [List.mem_cons, Ne.symm same] using member
        obtain ⟨index, hi, his⟩ := ih rest
        simp only [signatureIndex, same, dite_false, hi, Size.typeIndex, ite_false]
        exact ⟨_, rfl, by simp [his]⟩

theorem importFunction_produces (types : List Wasm.FuncType) (decl : Wasm.ImportDecl)
    (ready : ImportReady types decl) :
    Produces (importFunction types decl) (Size.importFunction types decl) := by
  obtain ⟨index, hi, his⟩ := signatureIndex_produces _ types ready.signature
  obtain ⟨moduleName, hm, hms⟩ := name_produces decl.module ready.moduleName
  obtain ⟨fieldName, hn, hns⟩ := name_produces decl.name ready.fieldName
  obtain ⟨encodedIndex, he, hes⟩ := u32_produces index.val (by simpa [his] using ready.index)
  simp only [Produces, importFunction, hi, hm, hn, Except.bind, bind, he]
  refine ⟨_, rfl, ?_⟩
  simp [hms, hns, hes, his, Size.importFunction, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem functionIndex_produces (types : List Wasm.FuncType) (func : Wasm.Function)
    (ready : FunctionReady types func) :
    Produces (functionIndex types func) (Size.u32 (func.typeIdx.getD 0)) := by
  obtain ⟨index, declared, agrees, bound⟩ := ready.typeIndex
  obtain ⟨encoded, he, hes⟩ := u32_produces index bound
  unfold functionIndex
  split
  · rename_i absent
    simp [absent] at declared
  · rename_i found present
    have same : found = index := by simpa [present] using declared
    subst found
    simp only [Produces, agrees, dite_true, he, present, Option.getD_some]
    exact ⟨_, rfl, hes⟩

theorem exportEntry_produces (entry : UInt8 × String × Nat) (ready : ExportReady entry) :
    Produces (exportEntry entry) (Size.exportEntry entry) := by
  rcases entry with ⟨kind, exportName, index⟩
  obtain ⟨encodedName, hn, hns⟩ := name_produces exportName ready.name
  obtain ⟨encodedIndex, hi, his⟩ := u32_produces index ready.index
  simp only [Produces, exportEntry, ready.kind, dite_true, hn, hi]
  refine ⟨_, rfl, ?_⟩
  simp [hns, his, Size.exportEntry, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem require_produces (condition : Prop) [Decidable condition] (message : String)
    (holds : condition) : require condition message = .ok ⟨holds⟩ := by
  simp [require, holds]

theorem requireEmpty_produces (message : String) (values : List α) (empty : values = []) :
    requireEmpty message values = .ok ⟨empty⟩ := by
  subst values
  rfl

theorem shape_produces (m : Wasm.Module) (ready : Spec.Shape m) :
    shape m = .ok ⟨ready⟩ := by
  simp only [shape, require_produces _ _ ready.dataWithoutMemory,
    require_produces _ _ ready.start, require_produces _ _ ready.gcTypes,
    requireEmpty_produces _ _ ready.extraMemories,
    requireEmpty_produces _ _ ready.tables, requireEmpty_produces _ _ ready.elements,
    requireEmpty_produces _ _ ready.importedGlobals,
    requireEmpty_produces _ _ ready.importedTables,
    requireEmpty_produces _ _ ready.importedMemories,
    requireEmpty_produces _ _ ready.importedTags,
    requireEmpty_produces _ _ ready.tableExports,
    requireEmpty_produces _ _ ready.tagExports, requireEmpty_produces _ _ ready.tags]
  rfl

theorem vectorSection_complete (id : UInt8) (encode : (value : α) → Result relation value)
    (size : α → Nat) (values : List α) (count : values.length < 2 ^ 32)
    (bound : Size.vector (values.map size) < 2 ^ 32)
    (accepted : ∀ value ∈ values, Produces (encode value) (size value)) :
    ∃ output, (vector encode values >>= sectionBytes id) = .ok output := by
  obtain ⟨payload, hp, hps⟩ := vector_produces encode size values count accepted
  obtain ⟨output, ho, _⟩ := section_produces id payload _ hps bound
  exact ⟨output, by simpa only [hp, Except.bind, bind] using ho⟩

theorem dataSection_complete (segments : List Wasm.DataSegment)
    (count : segments.length < 2 ^ 32)
    (bound : Size.vector (segments.map Size.dataSegment) < 2 ^ 32)
    (accepted : ∀ segment ∈ segments, DataReady segment) :
    ∃ output, dataSection segments = .ok output := by
  cases segments with
  | nil => exact ⟨_, rfl⟩
  | cons segment rest =>
      obtain ⟨output, ho⟩ := vectorSection_complete 11 dataSegment Size.dataSegment
        (segment :: rest) count bound fun s member => dataSegment_produces s (accepted s member)
      simp only [dataSection, ho]
      exact ⟨_, rfl⟩

theorem memoryDecls_form {m : Wasm.Module} (ready : Ready m) :
    ∀ decl ∈ Spec.memoryDecls m, decl.data = [] ∧ decl.is64 = false := by
  intro decl member
  simp only [Spec.memoryDecls, List.mem_map] at member
  obtain ⟨original, hMember, rfl⟩ := member
  exact ⟨rfl, ready.memories original hMember⟩

theorem module_complete (m : Wasm.Module) (ready : Ready m) :
    ∃ output, module m = .ok output := by
  obtain ⟨types, ht⟩ := vectorSection_complete 1 functionType Size.functionType m.types
    ready.typeCount ready.typeSize (fun t member => functionType_produces t (ready.types t member))
  obtain ⟨imports, hi⟩ := vectorSection_complete 2 (importFunction m.types)
    (Size.importFunction m.types) m.imports ready.importCount ready.importSize
    (fun d member => importFunction_produces m.types d (ready.imports d member))
  obtain ⟨functions, hf⟩ := vectorSection_complete 3 (functionIndex m.types)
    (fun f => Size.u32 (f.typeIdx.getD 0)) m.funcs ready.functionCount ready.functionSize
    (fun f member => functionIndex_produces m.types f (ready.functions f member))
  obtain ⟨memories, hm⟩ := vectorSection_complete 5 memory Size.memory (Spec.memoryDecls m)
    (by cases h : m.memory <;> simp [Spec.memoryDecls, h]) ready.memorySize
    (fun d member => memory_produces d (memoryDecls_form ready d member))
  obtain ⟨globals, hg⟩ := vectorSection_complete 6 global Size.global m.globals
    ready.globalCount ready.globalSize (fun d member => global_produces d (ready.globals d member))
  obtain ⟨exports, he⟩ := vectorSection_complete 7 exportEntry Size.exportEntry (Spec.exports m)
    ready.exportCount ready.exportSize (fun e member => exportEntry_produces e (ready.exports e member))
  obtain ⟨codes, hc⟩ := vectorSection_complete 10 functionBody Size.functionBody m.funcs
    ready.functionCount ready.codeSize
    (fun f member => functionBody_produces m.types f (ready.functions f member))
  obtain ⟨datas, hd⟩ := dataSection_complete (Spec.dataSegments m) ready.dataCount
    ready.dataSize ready.data
  simp only [module, shape_produces m ready.shape, ht, hi, hf, hm, hg, he, hc, hd]
  exact ⟨_, rfl⟩

theorem encode_complete (m : Wasm.Module) (ready : Ready m) :
    ∃ bytes, encode m = .ok bytes ∧ Encodes m bytes := by
  obtain ⟨output, success⟩ := module_complete m ready
  have encoded : encode m = .ok ⟨output.val.toArray⟩ := by
    simp [encode, success, Except.map]
  exact ⟨_, encoded, encode_correct _ _ encoded⟩

end Wasm.Encoding
