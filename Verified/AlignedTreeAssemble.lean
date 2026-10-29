import Verified.AlignedTreeNode
import Verified.TreeAssembleTyped

/-!
The stores that assemble a record under the flag.  Every store of the assembly writes a slot of
the record or a word of its header, at the record's pointer plus or minus a multiple of 8, so
each statement takes the alignment of the pointer, `hpAl`, as its one new premise.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- `wp_recordStoreCode` under the flag. -/
theorem wpX_recordStoreCode {strict : Bool} {m : Module} {host : HostEnv Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0) :
    ∀ (i : Nat) (srcs : List Nat) (tys : List ValueType) (words : List UInt64)
      (store : Store Unit),
      SourcesHold s s.positions srcs tys words →
      p.toNat + 8 * (i + words.length) < 4294967296 →
      p.toNat + 8 * (i + words.length) ≤ store.mem.pages * 65536 →
      wpX strict m rest Q (recordWriteValues p i words store) s host →
      wpX strict m (recordStoreCode s.positions ptr i srcs tys ++ rest) Q store s host
  | _, [], _, [], _, _, _, _, hNext => hNext
  | i, src :: srcs, tys, word :: words, store, hold, hAddress, hMemory, hNext => by
    obtain ⟨hValue, hWord, hold⟩ := hold
    have hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      simp only [List.length_cons] at hMemory
      omega
    change (p + UInt64.ofNat (8 * i)).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 at hRoom
    have hRest := wpX_recordStoreCode hPtr hpAl (i + 1) srcs tys.tail words
      { store with mem := store.mem.write64 (slotAddress p i) word } hold
      (by simp only [List.length_cons] at hAddress; omega)
      (by simp only [Mem.write64_pages]; simp only [List.length_cons] at hMemory; omega) hNext
    have hStore : wpX strict m (.store64 0 :: (recordStoreCode s.positions ptr (i + 1) srcs tys.tail ++
        rest)) Q store
        { s with
          values := .i64 (Value.word (typedValue (tys.headD .i64) word)) ::
            .i32 (p + UInt64.ofNat (8 * i)).toUInt32 :: s.values } host := by
      rw [hWord]
      simp only [wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        ite_eq_right (Nat.not_lt.mpr hRoom)]
      exact ⟨fun hs => slotAddress_mod8 (hpAl hs) i, by simpa only [slotAddress] using hRest⟩
    have hConvert := (wpX_toWordCode (strict := strict) (m := m) (st := store) (env' := host) (s := s)
      (vs := .i32 (p + UInt64.ofNat (8 * i)).toUInt32 :: s.values)
      (rest := .store64 0 :: (recordStoreCode s.positions ptr (i + 1) srcs tys.tail ++ rest))
      (Q := Q) (tys.headD .i64) word).mpr hStore
    simpa only [recordStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wpX_localGet_cons, Locals.get_values, hPtr, hValue, wpX_constI64_cons, wpX_addI64_cons,
      wpX_wrapI64_cons, wrap_toUInt32] using hConvert

theorem wp_recordStoreCode {m : Module} {host : HostEnv Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) :
    ∀ (i : Nat) (srcs : List Nat) (tys : List ValueType) (words : List UInt64)
      (store : Store Unit),
      SourcesHold s s.positions srcs tys words →
      p.toNat + 8 * (i + words.length) < 4294967296 →
      p.toNat + 8 * (i + words.length) ≤ store.mem.pages * 65536 →
      wp m rest Q (recordWriteValues p i words store) s host →
      wp m (recordStoreCode s.positions ptr i srcs tys ++ rest) Q store s host :=
  wpX_recordStoreCode (strict := false) hPtr nofun

/-- `wp_sealRecord` under the flag. -/
theorem wpX_sealRecord {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {width : Nat} {store : Store Unit} {s : Locals} {ptr : Nat} {p mask : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q (recordSeal width store p mask) s host) :
    wpX strict m (sealRecordCode width ptr mask ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hTop := hAt.top
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h24 : back.toNat ≤ 24) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  simp only [sealRecordCode, List.append_assoc]
  refine wpX_headerStoreWord hPtr (hRoom 24 (by decide) (by decide)) (fun hs => ⟨hpAl hs, rfl⟩) ?_
  refine wpX_headerStoreWord hPtr ?_ (fun hs => ⟨hpAl hs, rfl⟩) ?_
  · simpa only [Mem.write64_pages] using hRoom 16 (by decide) (by decide)
  refine wpX_headerStoreWord hPtr ?_ (fun hs => ⟨hpAl hs, rfl⟩) ?_
  · simpa only [Mem.write64_pages] using hRoom 8 (by decide) (by decide)
  exact hNext

theorem wp_sealRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {width : Nat} {store : Store Unit} {s : Locals} {ptr : Nat} {p mask : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (recordSeal width store p mask) s host) :
    wp m (sealRecordCode width ptr mask ++ rest) Q store s host :=
  wpX_sealRecord (strict := false) hRaw hAt hPtr nofun hNext

/-- `wp_tagStore` under the flag. -/
theorem wpX_tagStore {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap} {width : Nat}
    {shape : TreeShape} (r : Fin shape.records) {store : Store Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hAt : heap.At store) (hPos : 0 < width) (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q (recordWriteValues p 0 (shape.tagWords r) store) s host) :
    wpX strict m (shape.tagStoreCode r ptr ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hCapacity := hRaw.capacity
  have hTop := hAt.top
  unfold TreeShape.tagStoreCode
  unfold TreeShape.tagWords at hNext
  by_cases ht : shape.tagged = true
  · rw [ite_eq_left ht] at hNext ⊢
    have hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [UInt64.toNat_toUInt32]; omega
    simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hPtr, wpX_wrapI64_cons,
      wrap_toUInt32, wpX_constI64_cons, wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero,
      UInt32.add_zero, ite_eq_right (Nat.not_lt.mpr hRoom)]
    refine ⟨fun hs => UInt64.toUInt32_mod8 (hpAl hs), ?_⟩
    simpa [recordWriteValues, slotAddress] using hNext
  · rw [ite_eq_right ht] at hNext ⊢
    simpa only [List.nil_append, recordWriteValues] using hNext

/-- The store of the tag of record constructor `r` into slot 0 of a record of positive width. -/
theorem wp_tagStore {m : Module} {host : HostEnv Unit} {heap : Heap} {width : Nat}
    {shape : TreeShape} (r : Fin shape.records) {store : Store Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hAt : heap.At store) (hPos : 0 < width) (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (recordWriteValues p 0 (shape.tagWords r) store) s host) :
    wp m (shape.tagStoreCode r ptr ++ rest) Q store s host :=
  wpX_tagStore (strict := false) r hRaw hAt hPos hPtr nofun hNext

/-- `wp_assembleRecord` under the flag. -/
theorem wpX_assembleRecord {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {width : Nat} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {pre words : List UInt64} {slots : List LeanExe.Pipeline.Slot} {srcs : List Nat}
    {tys : List ValueType}
    {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage width heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0) (hLength : (pre ++ words).length = width)
    (hShort : width ≤ 64) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) (pre ++ words)
      slots) (hLengths : BufferLengths slots)
    (hLocals : SourcesHold s s.positions srcs tys words)
    (hApart : (block store p :: fieldBlocks store (pre ++ words) slots).Pairwise regionsDisjoint)
    (hNext : ∀ store', heap.At store' → NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) =
        block store p :: fieldBlocks store (pre ++ words) slots →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wpX strict m rest Q store' s host) :
    wpX strict m (recordStoreCode s.positions ptr pre.length srcs tys ++
      sealRecordCode width ptr (maskOf slots) ++ rest)
      Q (recordWriteValues p 0 pre store) s host := by
  have hAddress := hRaw.address
  have hRoom := hRaw.capacity
  have hBelow := hRaw.below
  have hTop := hAt.top
  have hLength' := hLength
  simp only [List.length_append] at hLength'
  have hPreWrites := recordWriteValues_range p 0 pre store (by omega)
  obtain ⟨hAt1, hRaw1, _, _⟩ := hRaw.writeValues hAt 0 (pre ++ words) (by omega)
  obtain ⟨hAt2, hNode2, hBlocks2, hStep2⟩ :=
    hRaw.assemble hAt hLength hShort hCount hValues hLengths hApart
  have hAppend := recordWriteValues_append p 0 pre words store
  rw [Nat.zero_add] at hAppend
  rw [List.append_assoc]
  refine wpX_recordStoreCode hPtr hpAl pre.length srcs tys words (recordWriteValues p 0 pre store)
    hLocals (by omega) (by rw [hPreWrites.2.1]; omega) ?_
  rw [← hAppend]
  exact wpX_sealRecord hRaw1 hAt1 hPtr hpAl (hNext _ hAt2 hNode2 hBlocks2 hStep2)

/-- The stores of the words `words` after the words `pre` already in the record, and the seal of
its header. -/
theorem wp_assembleRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {width : Nat} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {pre words : List UInt64} {slots : List LeanExe.Pipeline.Slot} {srcs : List Nat}
    {tys : List ValueType}
    {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage width heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLength : (pre ++ words).length = width)
    (hShort : width ≤ 64) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) (pre ++ words)
      slots) (hLengths : BufferLengths slots)
    (hLocals : SourcesHold s s.positions srcs tys words)
    (hApart : (block store p :: fieldBlocks store (pre ++ words) slots).Pairwise regionsDisjoint)
    (hNext : ∀ store', heap.At store' → NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) =
        block store p :: fieldBlocks store (pre ++ words) slots →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (recordStoreCode s.positions ptr pre.length srcs tys ++
      sealRecordCode width ptr (maskOf slots) ++ rest)
      Q (recordWriteValues p 0 pre store) s host :=
  wpX_assembleRecord (strict := false) hRaw hAt hPtr nofun hLength hShort hCount hValues hLengths
    hLocals hApart hNext

/-- `wp_assembleTree` under the flag. -/
theorem wpX_assembleTree {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {r : Fin shape.records} {store : Store Unit} {s : Locals}
    {h ptr fieldBase : Nat} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {ws : List Value} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h)
    (hRaw : RecordStorage (shape.width r) heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hRep : Env.Rep (fun _ => .owned) heap store ws
      (shape.fieldEnv r words arrays buffers children))
    (hNormal : FieldsNormal (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))) ws)
    (hLocals : LocalsHold s fieldBase (shape.fieldTypes r) ws)
    (hApart : (block store p ::
      (shape.fieldEnv r words arrays buffers children).blocks store ws).Pairwise
        regionsDisjoint)
    (hNext : ∀ store', heap.At store' →
      (Ty.tree shape).Rep .owned heap store' [.i64 p] (.node r words arrays buffers children) →
      ((Ty.tree shape).blocks store' [.i64 p] (.node r words arrays buffers children)).Perm
        (block store p :: (shape.fieldEnv r words arrays buffers children).blocks store ws) →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wpX strict m rest Q store' s host) :
    wpX strict m (shape.tagStoreCode r ptr ++
      treeStoreFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
        shape.fieldStart (shape.fields r) ++
      treeStoreHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      sealRecordCode (shape.width r) ptr (shape.mask r) ++ rest) Q store s host := by
  subst hh
  obtain ⟨childWords, hWords, hChildRep, hWordBlocks⟩ := Env.Rep.wordFields _
    (shape.words r) (shape.elem r) (shape.elem_width r) words (fun _ => .owned) ws hRep
  obtain ⟨pointers, heapWords, hPointers, hNodes, hHeapRep, hChildBlocks⟩ :=
    Env.Rep.treeFields _ (shape.children r) children (fun _ => .owned) childWords hChildRep
  obtain ⟨arrayPtrs, bufferWords, hArrayWords, hArrays, hBufferRep, hArrayBlocks⟩ :=
    Env.Rep.arrayFields _ (shape.arrays r) (shape.arrayElem r) arrays (fun _ => .owned)
      heapWords hHeapRep
  obtain ⟨roots, lengths, tail, hBufferWords, hBuffersRep, hTail, hBufferBlocks⟩ :=
    Env.Rep.bytesFields Env.nil (shape.buffers r) buffers (fun _ => .owned) bufferWords
      hBufferRep
  have hTail' : tail = [] := hTail
  subst hTail'
  rw [List.append_nil] at hBufferWords
  subst hBufferWords
  subst hArrayWords
  subst hPointers
  rw [hWords] at hLocals hNormal hApart hNext
  have hWordLen : (List.ofFn fun i =>
      typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))).length =
      (shape.wordTypes r).length := by simp [TreeShape.wordTypes]
  -- Each buffer has root 0 when it is empty.
  have hNormalBuffers : ∀ i, lengths i = 0 → roots i = 0 := by
    have h1 := FieldsNormal.drop_prefix (tysOfFn (shape.words r) (shape.wordTy r)) _ _
      (by rw [tysOfFn_widthSum (shape.words r) (shape.wordTy r) (fun i => shape.elem_width r i)]
          simp) hNormal
    have h2 := FieldsNormal.drop_prefix (List.replicate (shape.children r) (.tree shape)) _ _
      (by rw [replicate_widthSum, show (Ty.tree shape).width = 1 from rfl]; simp) h1
    have h3 := FieldsNormal.drop_prefix (tysOfFn (shape.arrays r) (shape.arrayTy r)) _ _
      (by rw [tysOfFn_widthSum (shape.arrays r) (shape.arrayTy r) (fun _ => rfl)]; simp) h2
    exact FieldsNormal.bytesFields (ps := []) _ roots lengths [] (by simpa using h3)
  have hRecordBuffers : ∀ i, RecordBuffer heap store (roots i) (lengths i) (buffers i) :=
    fun i => (hBuffersRep i).recordBuffer (hNormalBuffers i)
  obtain ⟨hWordLocals, hRestLocals⟩ := (LocalsHold.append hWordLen).mp hLocals
  obtain ⟨hChildLocals, hArrayLocals⟩ := (LocalsHold.append (by simp)).mp hRestLocals
  obtain ⟨hArrayLocals, hBufferLocals⟩ := (LocalsHold.append (by simp)).mp hArrayLocals
  have hWordGet := hWordLocals.treeWords
  have hChildGet : ∀ i, s.get (fieldBase + shape.words r + i.val) = some (.i64 (pointers i)) := by
    simpa only [hWordLen, TreeShape.wordTypes, List.length_ofFn] using hChildLocals.ofFn_i64
  have hArrayGet : ∀ i, s.get (fieldBase + shape.words r + shape.children r + i.val) =
      some (.i64 (arrayPtrs i)) := by
    have := hArrayLocals.ofFn_i64
    simpa only [hWordLen, TreeShape.wordTypes, List.length_ofFn, Nat.add_assoc] using this
  have hBufferGet : ∀ i,
      s.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
        some (.i64 (roots i)) ∧
      s.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
        some (.i64 (lengths i)) := by
    have := LocalsHold.ofFn_pairs _ _ roots lengths hBufferLocals
    simpa only [hWordLen, TreeShape.wordTypes, List.length_ofFn, Nat.add_assoc] using this
  have hTreeValues := treeFieldValues_owned (shape.fields r) (shape.slotWords r words) pointers
    (fun i => (children i).toNode) (fun i => (hNodes i).1)
  have hHeapValues := heapValues_owned (heap := heap) (store := store) (shape.kinds r) arrayPtrs
    (shape.arrayWords r arrays) roots lengths buffers (fun i => hArrays i) hRecordBuffers
  have hValues := tagWords_values (r := r) (forall₂_append hTreeValues hHeapValues)
  have hTreeLocals := treeFieldLocs_values (s := s) (h := s.positions) (shape.fields r)
    (shape.wordTypes r) fieldBase (fieldBase + shape.words r) (shape.slotWords r words) pointers
    hWordGet hChildGet
  have hHeapLocals := heapLocs_values (s := s) (h := s.positions) (shape.kinds r)
    (fieldBase + shape.words r + shape.children r)
    (fieldBase + shape.words r + shape.children r + shape.arrays r) arrayPtrs roots lengths
    hArrayGet hBufferGet
  have hTypesLen : (treeFieldTypes (shape.fields r) (shape.wordTypes r)).length =
      (treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)).length := by
    rw [treeFieldTypes_length, treeFieldLocs_length]
  have hPayloadLocals := SourcesHold.append hTypesLen hTreeLocals hHeapLocals
  have hTreeLength := treeFieldValues_length (shape.fields r) (shape.slotWords r words) pointers
  have hTreeBlocks := treeFieldBlocks_eq store (shape.fields r) (shape.slotWords r words)
    pointers (fun i => (children i).toNode)
  have hHeapBlocks := heapFieldBlocks_perm store (shape.kinds r) arrayPtrs
    (shape.arrayWords r arrays) roots lengths buffers hRecordBuffers
  have hEnvBlocks : (shape.fieldEnv r words arrays buffers children).blocks store
      ((List.ofFn fun i =>
        typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))) ++
        ((List.ofFn fun i => Value.i64 (pointers i)) ++
          ((List.ofFn fun i => Value.i64 (arrayPtrs i)) ++
            (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten))) =
      (List.ofFn fun i => (children i).toNode.blocks store (pointers i)).flatten ++
        ((List.ofFn fun i => [block store (arrayPtrs i)]).flatten ++
          (List.ofFn fun i => Bytes.regions store (roots i)).flatten) := by
    have hw := hWordBlocks
    rw [hWords] at hw
    refine hw.trans (hChildBlocks.trans (congrArg (_ ++ ·) (hArrayBlocks.trans ?_)))
    rw [hBufferBlocks]
    simp [Env.blocks]
  have hFieldBlocks : (fieldBlocks store
      (shape.tagWords r ++ (treeFieldValues (shape.fields r) (shape.slotWords r words) pointers ++
        heapValues (shape.kinds r) arrayPtrs roots lengths))
      (shape.tagSlots r ++ (treeSlots (shape.fields r) (shape.slotWords r words)
        (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers))).Perm
      ((shape.fieldEnv r words arrays buffers children).blocks store
        ((List.ofFn fun i =>
          typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))) ++
          ((List.ofFn fun i => Value.i64 (pointers i)) ++
            ((List.ofFn fun i => Value.i64 (arrayPtrs i)) ++
              (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten)))) := by
    rw [(tagWords_fieldBlocks store shape r _ _).trans ((fieldBlocks_append store
      (hTreeLength.trans (treeSlots_length (shape.fields r) _ _).symm)).trans
      (congrArg (· ++ _) hTreeBlocks)), hEnvBlocks]
    exact hHeapBlocks.append_left _
  have hPayloadApart : (block store p :: fieldBlocks store
      (shape.tagWords r ++ (treeFieldValues (shape.fields r) (shape.slotWords r words) pointers ++
        heapValues (shape.kinds r) arrayPtrs roots lengths))
      (shape.tagSlots r ++ (treeSlots (shape.fields r) (shape.slotWords r words)
        (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers))).Pairwise
        regionsDisjoint :=
    hApart.perm (hFieldBlocks.symm.cons _) (fun h => regionsDisjoint_symm h)
  have hLength : (shape.tagWords r ++
      (treeFieldValues (shape.fields r) (shape.slotWords r words) pointers ++
        heapValues (shape.kinds r) arrayPtrs roots lengths)).length = shape.width r := by
    rw [List.length_append, List.length_append, shape.tagWords_length, hTreeLength,
      heapValues_length]
    simp only [TreeShape.width, TreeShape.heapWidth]
    omega
  have hSlots : shape.tagSlots r ++ (treeSlots (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode) ++
      heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) =
      shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
        (fun i => (children i).toNode) :=
    (List.append_assoc _ _ _).symm
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine wpX_tagStore r hRaw hAt (shape.width_pos r) hPtr hpAl ?_
  rw [treeStoreFields_eq, treeStoreHeaps_eq s.positions,
    ← shape.mask_eq r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
      (fun i => (children i).toNode), ← hSlots, shape.fieldStart_eq r, ← List.append_assoc,
    show (shape.tagWords r).length + (shape.fields r).length =
      (shape.tagWords r).length +
        (treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)).length by
      rw [treeFieldLocs_length],
    ← recordStoreCode_append _ _ _ _ _ _ [] hTypesLen, List.append_nil, ← List.append_assoc]
  have hLengths : BufferLengths (shape.tagSlots r ++ (treeSlots (shape.fields r)
      (shape.slotWords r words) (fun i => (children i).toNode) ++
      heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers)) := by
    rw [hSlots]
    exact NodeLayout.lengths (Tree.toNode_layout (Tree.node r words arrays buffers children))
  refine wpX_assembleRecord hRaw hAt hPtr hpAl hLength (shape.width_le r) hCount hValues hLengths
    hPayloadLocals hPayloadApart fun store' hAt' hNode hNewBlocks hStep => ?_
  have hResultBlocks : ((Ty.tree shape).blocks store' [.i64 p]
      (.node r words arrays buffers children)).Perm
      (block store p :: (shape.fieldEnv r words arrays buffers children).blocks store
        ((List.ofFn fun i =>
          typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))) ++
          ((List.ofFn fun i => Value.i64 (pointers i)) ++
            ((List.ofFn fun i => Value.i64 (arrayPtrs i)) ++
              (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten)))) := by
    change (Node.blocks store' p (.record (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)))).Perm _
    rw [← hSlots, hNewBlocks]
    exact hFieldBlocks.cons _
  refine hNext store' hAt' ⟨p, rfl, ?_, ?_⟩ hResultBlocks hStep
  · have hNode' : NodeOwned heap store' p (.record (shape.recordSlots r (shape.slotWords r words)
        (shape.arrayWords r arrays) buffers (fun i => (children i).toNode))) := hSlots ▸ hNode
    exact hNode'
  · exact hApart.perm hResultBlocks.symm (fun h => regionsDisjoint_symm h)

theorem wp_assembleTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {r : Fin shape.records} {store : Store Unit} {s : Locals}
    {h ptr fieldBase : Nat} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {ws : List Value} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h)
    (hRaw : RecordStorage (shape.width r) heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hRep : Env.Rep (fun _ => .owned) heap store ws
      (shape.fieldEnv r words arrays buffers children))
    (hNormal : FieldsNormal (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))) ws)
    (hLocals : LocalsHold s fieldBase (shape.fieldTypes r) ws)
    (hApart : (block store p ::
      (shape.fieldEnv r words arrays buffers children).blocks store ws).Pairwise
        regionsDisjoint)
    (hNext : ∀ store', heap.At store' →
      (Ty.tree shape).Rep .owned heap store' [.i64 p] (.node r words arrays buffers children) →
      ((Ty.tree shape).blocks store' [.i64 p] (.node r words arrays buffers children)).Perm
        (block store p :: (shape.fieldEnv r words arrays buffers children).blocks store ws) →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (shape.tagStoreCode r ptr ++
      treeStoreFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
        shape.fieldStart (shape.fields r) ++
      treeStoreHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      sealRecordCode (shape.width r) ptr (shape.mask r) ++ rest) Q store s host :=
  wpX_assembleTree (strict := false) hh hRaw hAt hPtr nofun hCount hRep hNormal hLocals hApart hNext

end Verified
