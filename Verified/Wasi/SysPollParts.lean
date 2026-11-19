import Verified.Wasi.SysIovecCall

/-! The parts of the code of a `poll` call.  Its parameters are the subscriptions of `records` and
the result word.  The code writes the subscriptions into a block: it zeroes their `48 n` bytes and
stores each field, in order, with stores of its width.  `BlockAt` describes the memory that these
stores leave, and the subscriptions that they leave are `subscriptionBytes records args`. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## Parameters -/

theorem poll_wordCount {call : Call} {records : List (List Field)}
    (hParams : call.params = [.subscriptions records, .result32]) :
    call.wordCount = (argFields records).length := by
  rw [Call.wordCount, hParams]
  simp [Param.wordCount, Param.takesBytes, Param.argCount]

theorem poll_inputCount {call : Call} {records : List (List Field)}
    (hParams : call.params = [.subscriptions records, .result32]) : call.inputCount = 0 := by
  rw [Call.inputCount, hParams]
  rfl

theorem poll_args (records : List (List Field)) (values : List UInt64)
    (hLength : values.length = (argFields records).length) :
    flatArgsWith [.subscriptions records, .result32] values [] = values.map .word := by
  simp [flatArgsWith, ← hLength]

theorem poll_reject (records : List (List Field)) (values : List UInt64) :
    rejectArgs [.subscriptions records, .result32] (values.map .word) =
      rejectFields (argFields records) (values.map .word) := by
  simp only [rejectArgs, Param.takesArg, Bool.false_eq_true, ite_false]
  split <;> simp_all

theorem argFieldsFit_of_reject : ∀ (fields : List Field) (values : List UInt64),
    values.length = fields.length → rejectFields fields (values.map .word) = 0 →
    argFieldsFit fields (values.map .word) = true
  | [], [], _, _ => rfl
  | field :: fields, value :: values, length, rejected => by
    simp only [List.map_cons, rejectFields] at rejected
    by_cases small : (Arg.word value).value.toNat < 2 ^ (8 * field.width)
    · rw [ite_eq_left small] at rejected
      simp only [List.map_cons, argFieldsFit, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨small, argFieldsFit_of_reject fields values (by simpa using length) rejected⟩
    · rw [ite_eq_right small] at rejected
      exact absurd rejected (by decide)

theorem poll_lower (records : List (List Field)) (args : List Arg) (subscriptions events : UInt32) :
    lowerArgs [.subscriptions records, .result32] args [subscriptions, events, 0] =
      [.i32 subscriptions, .i32 events, .i32 (UInt32.ofNat records.length), .i32 0] := by
  simp [lowerArgs]

theorem poll_places (records : List (List Field)) (args : List Arg)
    (subscriptions events : UInt32) :
    inputPlaces [.subscriptions records, .result32] args [subscriptions, events, 0] =
      [(subscriptions, subscriptionBytes records args)] := by
  simp [inputPlaces]

theorem poll_regions (records : List (List Field)) (sizes : List Nat) (args : List Arg)
    (subscriptions events : UInt32) :
    outputRegions [.subscriptions records, .result32] sizes args [subscriptions, events, 0] =
      [⟨events, 32 * records.length, 8, true⟩, ⟨0, 4, 4, true⟩] := by
  simp [outputRegions]

theorem poll_sizes (records : List (List Field)) (sizes : List Nat) (args : List Arg) :
    outputSizesOf [.subscriptions records, .result32] sizes args = [32 * records.length, 4] := by
  simp [outputSizesOf]

/-- The facts that `subscriptionsFit` gives: there is a record, the records fit, and each placed
field has a width of 1, 2, 4, or 8 bytes and lies inside the subscriptions. -/
theorem subscriptionsFit_facts {records : List (List Field)}
    (h : subscriptionsFit records = true) :
    0 < records.length ∧ recordsFit records = true ∧
      (∀ field ∈ placedFields 0 records,
        (field.width = 1 ∨ field.width = 2 ∨ field.width = 4 ∨ field.width = 8) ∧
          field.offset + field.width ≤ 48 * records.length) := by
  simp only [subscriptionsFit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨nonempty, fits⟩, widths⟩ := h
  refine ⟨nonempty, fits, fun field member => ⟨?_, ?_⟩⟩
  · have hPlaced : ∀ (base : Nat) (records : List (List Field)),
        (∀ fields ∈ records, ∀ field ∈ fields,
          ((field.width = 1 ∨ field.width = 2) ∨ field.width = 4) ∨ field.width = 8) →
        ∀ field ∈ placedFields base records,
          ((field.width = 1 ∨ field.width = 2) ∨ field.width = 4) ∨ field.width = 8 := by
      intro base records
      induction records generalizing base with
      | nil => intro _ field member; simp [placedFields] at member
      | cons fields records ih =>
        intro widths field member
        simp only [placedFields, List.mem_append, List.mem_map] at member
        rcases member with ⟨original, originalMember, rfl⟩ | there
        · exact widths fields List.mem_cons_self original originalMember
        · exact ih (base + 48) (fun other otherMember => widths other
            (List.mem_cons_of_mem _ otherMember)) field there
    have := hPlaced 0 records widths field member
    omega
  · have := ((placedFields_fit fits 0).1 field member).2.1
    omega

/-! ## The bytes of stores -/

theorem write64_byte (mem : Mem) (address : UInt32) (value : UInt64) (k : Nat) (hk : k < 8) :
    (mem.write64 address value).bytes (address.toNat + k) = byteOf value.toNat k := by
  interval_cases k <;> simp [Mem.write64, toUInt8_byteOf64, byteOf_and255,
    byteOf_and_shift _ 8 1 rfl, byteOf_and_shift _ 16 2 rfl, byteOf_and_shift _ 24 3 rfl,
    byteOf_and_shift _ 32 4 rfl, byteOf_and_shift _ 40 5 rfl, byteOf_and_shift _ 48 6 rfl,
    byteOf_and_shift _ 56 7 rfl]

theorem write32_byte (mem : Mem) (address value : UInt32) (k : Nat) (hk : k < 4) :
    (mem.write32 address value).bytes (address.toNat + k) = byteOf value.toNat k := by
  interval_cases k <;> simp [Mem.write32, toUInt8_byteOf32, byteOf_and255,
    byteOf_and_shift _ 8 1 rfl, byteOf_and_shift _ 16 2 rfl, byteOf_and_shift _ 24 3 rfl]

theorem write8_bytes_outside (mem : Mem) (address : UInt32) (value : UInt8) {index : Nat}
    (h : index ≠ address.toNat) : (mem.write8 address value).bytes index = mem.bytes index := by
  simp [Mem.write8, h]

/-- The bytes of a wrapped word are those of the word, below byte 4. -/
theorem wrap_byteOf (v : UInt64) (k : Nat) (hk : k < 4) :
    byteOf v.toUInt32.toNat k = byteOf v.toNat k := by
  apply UInt8.toNat_inj.mp
  rw [byteOf_toNat, byteOf_toNat, UInt64.toNat_toUInt32]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul] <;> omega

theorem store8_byte (v : UInt64) : v.toUInt32.toUInt8 = byteOf v.toNat 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt64.toNat_toUInt32, byteOf_toNat]
  omega

theorem store8_byte1 (v : UInt64) : (v >>> 8).toUInt32.toUInt8 = byteOf v.toNat 1 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, byteOf_toNat]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  omega

theorem byteOf_zero_value (k : Nat) : byteOf 0 k = 0 := by
  simp [byteOf]

/-! ## The memory of a block of stores -/

/-- The memory `mem` has the pages of `before`, holds `byte i` at `pointer + i` for each
`i < size`, and agrees with `before` outside these `size` bytes. -/
structure BlockAt (before mem : Mem) (pointer size : Nat) (byte : Nat → UInt8) : Prop where
  pages : mem.pages = before.pages
  inside : ∀ i, i < size → mem.bytes (pointer + i) = byte i
  outside : ∀ address, address < pointer ∨ pointer + size ≤ address →
    mem.bytes address = before.bytes address

/-- `byte` with the `width` little-endian bytes of `value` at `offset`. -/
def writeByte (byte : Nat → UInt8) (offset width value : Nat) (index : Nat) : UInt8 :=
  if offset ≤ index ∧ index < offset + width then byteOf value (index - offset) else byte index

theorem BlockAt.refl (mem : Mem) (pointer size : Nat) :
    BlockAt mem mem pointer size fun i => mem.bytes (pointer + i) :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem BlockAt.write64 {before mem : Mem} {pointer size offset : Nat} {byte : Nat → UInt8}
    (h : BlockAt before mem pointer size byte) (hRange : offset + 8 ≤ size) {address : UInt32}
    (hAddress : address.toNat = pointer + offset) (value : UInt64) :
    BlockAt before (mem.write64 address value) pointer size
      (writeByte byte offset 8 value.toNat) := by
  refine ⟨by simpa [Mem.write64] using h.pages, fun i hi => ?_, fun a ha => ?_⟩
  · unfold writeByte
    split
    · rename_i inside
      rw [show pointer + i = address.toNat + (i - offset) by omega]
      exact write64_byte mem address value _ (by omega)
    · rename_i outside
      rw [Memory.write64_bytes_outside mem address value (by omega)]
      exact h.inside i hi
  · rw [Memory.write64_bytes_outside mem address value (by omega)]
    exact h.outside a ha

theorem BlockAt.write32 {before mem : Mem} {pointer size offset : Nat} {byte : Nat → UInt8}
    (h : BlockAt before mem pointer size byte) (hRange : offset + 4 ≤ size) {address : UInt32}
    (hAddress : address.toNat = pointer + offset) (value : UInt64) :
    BlockAt before (mem.write32 address value.toUInt32) pointer size
      (writeByte byte offset 4 value.toNat) := by
  refine ⟨by simpa [Mem.write32] using h.pages, fun i hi => ?_, fun a ha => ?_⟩
  · unfold writeByte
    split
    · rename_i inside
      rw [show pointer + i = address.toNat + (i - offset) by omega,
        write32_byte mem address _ _ (by omega), wrap_byteOf value _ (by omega)]
    · rename_i outside
      rw [write32_bytes_outside mem address _ (by omega)]
      exact h.inside i hi
  · rw [write32_bytes_outside mem address _ (by omega)]
    exact h.outside a ha

theorem BlockAt.write8 {before mem : Mem} {pointer size offset : Nat} {byte : Nat → UInt8}
    (h : BlockAt before mem pointer size byte) (hRange : offset + 1 ≤ size) {address : UInt32}
    (hAddress : address.toNat = pointer + offset) (value : Nat) (stored : UInt8)
    (hStored : stored = byteOf value 0) :
    BlockAt before (mem.write8 address stored) pointer size (writeByte byte offset 1 value) := by
  refine ⟨by simpa [Mem.write8] using h.pages, fun i hi => ?_, fun a ha => ?_⟩
  · unfold writeByte
    split
    · rename_i inside
      rw [show pointer + i = address.toNat by omega, show i - offset = 0 by omega, hStored]
      simp [Mem.write8]
    · rename_i outside
      rw [write8_bytes_outside mem address _ (by omega)]
      exact h.inside i hi
  · rw [write8_bytes_outside mem address _ (by omega)]
    exact h.outside a ha

theorem writeByte_two (byte : Nat → UInt8) (offset value : Nat) :
    writeByte (writeByte byte offset 1 value) (offset + 1) 1 (value / 256) =
      writeByte byte offset 2 value := by
  funext i
  unfold writeByte
  by_cases first : i = offset
  · subst first
    simp
  · by_cases second : i = offset + 1
    · subst second
      simp [byteOf_succ]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The block's memory holds bytes whose byte `i` is `byte i`. -/
theorem BlockAt.at_ {before mem : Mem} {pointer size : Nat} {byte : Nat → UInt8}
    {bytes : LeanExe.Bytes} (h : BlockAt before mem pointer size byte)
    (hSize : bytes.data.size = size) (hBytes : ∀ i (hi : i < bytes.data.size), byte i = bytes.data[i])
    (hAddress : pointer + size ≤ 4294967296) (hMemory : pointer + size ≤ before.pages * 65536) :
    Bytes.At mem (UInt64.ofNat pointer) bytes := by
  have hPointer : (UInt64.ofNat pointer).toNat = pointer :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [hPointer, hSize]; exact hAddress
  · rw [hPointer, hSize, h.pages]; exact hMemory
  · rw [hPointer, h.inside i (by omega), hBytes i hi]

/-- The block's stores change the memory only in the block. -/
theorem BlockAt.frame {World : Type} {before : Store World} {mem : Mem} {pointer size : Nat}
    {byte : Nat → UInt8} (h : BlockAt before.mem mem pointer size byte) :
    GuestFrame before { before with mem := mem } [(pointer, size)] := by
  refine ⟨rfl, h.pages, fun address outside => ?_⟩
  have apart := outside (pointer, size) (List.mem_singleton_self _)
  simp only [InRange] at apart
  exact h.outside address (by omega)

theorem BlockAt.congr {before mem : Mem} {pointer size : Nat} {byte other : Nat → UInt8}
    (h : BlockAt before mem pointer size byte) (same : ∀ i, i < size → byte i = other i) :
    BlockAt before mem pointer size other :=
  ⟨h.pages, fun i hi => (h.inside i hi).trans (same i hi), h.outside⟩

/-! ## The code of the stores -/

/-- Whether `code` pushes the word `value`: a constant, or the word of a local. -/
def PushesWord (s : Locals) (code : Program) (value : UInt64) : Prop :=
  code = [.constI64 value] ∨ ∃ place, code = [.localGet place] ∧ s.get place = some (.i64 value)

theorem wp_pushes_word {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {vs : List Value} {code : Program} {value : UInt64} {rest : Program} {Q : Assertion α}
    (h : PushesWord s code value)
    (hNext : wp m rest Q st { s with values := .i64 value :: vs } env) :
    wp m (code ++ rest) Q st { s with values := vs } env := by
  rcases h with rfl | ⟨place, rfl, hPlace⟩
  · simpa only [List.cons_append, List.nil_append, wp_constI64_cons] using hNext
  · simpa only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get_values, hPlace]
      using hNext

/-- The code of one field stores its `width` bytes at `offset` of the block. -/
theorem wp_field_store {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {pointerLocal offset width size : Nat} {pointer : UInt64} {code : Program} {value : UInt64}
    {before : Mem} {byte : Nat → UInt8} {rest : Program} {Q : Assertion α}
    (hPointer : s.get pointerLocal = some (.i64 pointer)) (hValue : PushesWord s code value)
    (hBlock : BlockAt before st.mem pointer.toNat size byte)
    (hWidth : width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8) (hRange : offset + width ≤ size)
    (hFits : pointer.toNat + size ≤ before.pages * 65536)
    (hAddress : pointer.toNat + size < 4294967296)
    (h : ∀ mem, BlockAt before mem pointer.toNat size (writeByte byte offset width value.toNat) →
      wp m rest Q { st with mem := mem } s env) :
    wp m (fieldStoreCode pointerLocal offset width code ++ rest) Q st s env := by
  have hPointer32 : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hOffsetNat : ∀ k, k < 4294967296 → (UInt32.ofNat k).toNat = k := fun k hk =>
    UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega)
  have hAdd : ∀ k, pointer.toNat + k < 4294967296 →
      (pointer.toUInt32 + UInt32.ofNat k).toNat = pointer.toNat + k := by
    intro k hk
    rw [UInt32.toNat_add, hPointer32, hOffsetNat k (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hPages := hBlock.pages
  have hValue' : PushesWord { s with values := .i32 pointer.toUInt32 :: s.values } code value := by
    rcases hValue with h | ⟨place, h, hPlace⟩
    · exact .inl h
    · exact .inr ⟨place, h, by rw [Locals.get_values]; exact hPlace⟩
  rcases hWidth with rfl | rfl | rfl | rfl
  · simp only [fieldStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, hPointer, wp_wrapI64_cons, wrap_toUInt32]
    refine wp_pushes_word hValue' ?_
    simp only [wp_wrapI64_cons, wrap_toUInt32, wp_store8_cons, hPointer32,
      hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    exact h _ (hBlock.write8 (by omega) (hAdd offset (by omega)) value.toNat _ (store8_byte value))
  · simp only [fieldStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, hPointer, wp_wrapI64_cons, wrap_toUInt32]
    refine wp_pushes_word hValue' ?_
    simp only [wp_wrapI64_cons, wrap_toUInt32, wp_store8_cons, hPointer32,
      hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    have first := hBlock.write8 (by omega) (hAdd offset (by omega)) value.toNat _
      (store8_byte value)
    simp only [wp_localGet_cons, hPointer, wp_wrapI64_cons, wrap_toUInt32]
    refine wp_pushes_word (st := { st with mem := _ }) hValue' ?_
    simp only [wp_constI64_cons, wp_shrUI64_cons, wp_wrapI64_cons, wrap_toUInt32, wp_store8_cons,
      hPointer32, hOffsetNat (offset + 1) (by omega)]
    rw [ite_eq_right (by simp only [Mem.write8]; omega)]
    try rw [show (8 : UInt64) % 64 = 8 from rfl]
    have second := first.write8 (offset := offset + 1) (by omega) (hAdd (offset + 1) (by omega))
      (value.toNat / 256) ((value >>> 8).toUInt32.toUInt8) (by rw [store8_byte1, byteOf_succ])
    rw [writeByte_two] at second
    exact h _ second
  · simp only [fieldStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, hPointer, wp_wrapI64_cons, wrap_toUInt32]
    refine wp_pushes_word hValue' ?_
    simp only [wp_wrapI64_cons, wrap_toUInt32, wp_store32_cons, hPointer32,
      hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    exact h _ (hBlock.write32 (by omega) (hAdd offset (by omega)) value)
  · simp only [fieldStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, hPointer, wp_wrapI64_cons, wrap_toUInt32]
    refine wp_pushes_word hValue' ?_
    simp only [wp_store64_cons, hPointer32, hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    exact h _ (hBlock.write64 (by omega) (hAdd offset (by omega)) value)

/-- The code of the zero words stores 0 into `8 count` bytes from `offset` of the block. -/
theorem wp_zero_words {α : Type} {m : Module} {env : HostEnv α} {s : Locals}
    {pointerLocal size : Nat} {pointer : UInt64} {before : Mem} {rest : Program}
    {Q : Assertion α}
    (hPointer : s.get pointerLocal = some (.i64 pointer))
    (hFits : pointer.toNat + size ≤ before.pages * 65536)
    (hAddress : pointer.toNat + size < 4294967296) :
    ∀ (count offset : Nat) (st : Store α) (byte : Nat → UInt8),
      BlockAt before st.mem pointer.toNat size byte → offset + 8 * count ≤ size →
      (∀ mem, BlockAt before mem pointer.toNat size
          (fun i => if offset ≤ i ∧ i < offset + 8 * count then 0 else byte i) →
        wp m rest Q { st with mem := mem } s env) →
      wp m (zeroWordsCode pointerLocal offset count ++ rest) Q st s env
  | 0, offset, st, byte, hBlock, _, h => by
    simp only [zeroWordsCode, List.nil_append]
    exact h st.mem (hBlock.congr fun i _ => by simp)
  | count + 1, offset, st, byte, hBlock, hRange, h => by
    rw [show zeroWordsCode pointerLocal offset (count + 1) =
      fieldStoreCode pointerLocal offset 8 [.constI64 0] ++
        zeroWordsCode pointerLocal (offset + 8) count from rfl, List.append_assoc]
    refine wp_field_store hPointer (.inl rfl) hBlock (by omega) (by omega) hFits hAddress ?_
    intro mem hMem
    refine wp_zero_words hPointer hFits hAddress count (offset + 8) { st with mem := mem } _ hMem
      (by omega) fun mem' hMem' => h mem' (hMem'.congr fun i _ => ?_)
    unfold writeByte
    simp only [UInt64.toNat_zero, byteOf_zero_value]
    split <;> split <;> (try split) <;> first | rfl | omega

/-- The bytes of a block after the fields `pairs` are stored, in order, into zero bytes. -/
def blockFold (pairs : List (Field × UInt64)) (index : Nat) : UInt8 :=
  pairs.foldl (fun byte placed =>
    if placed.1.offset ≤ index ∧ index < placed.1.offset + placed.1.width then
      byteOf placed.2.toNat (index - placed.1.offset)
    else byte) 0

theorem blockFold_snoc (pairs : List (Field × UInt64)) (field : Field) (value : UInt64) :
    blockFold (pairs ++ [(field, value)]) =
      writeByte (blockFold pairs) field.offset field.width value.toNat := by
  funext index
  simp [blockFold, writeByte, List.foldl_append]

/-- The code of the fields stores each field of `fields`, in order: a constant's value, and the word
of the next local of `locs` for a word or a handle field. -/
theorem wp_field_stores {α : Type} {m : Module} {env : HostEnv α} {s : Locals}
    {pointerLocal size : Nat} {pointer : UInt64} {before : Mem} {rest : Program}
    {Q : Assertion α}
    (hPointer : s.get pointerLocal = some (.i64 pointer))
    (hFits : pointer.toNat + size ≤ before.pages * 65536)
    (hAddress : pointer.toNat + size < 4294967296) :
    ∀ (fields : List Field) (locs : List Nat) (values : List UInt64) (st : Store α)
      (done : List (Field × UInt64)),
      List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
      values.length = (fields.filter Field.takesArg).length →
      (∀ field ∈ fields, (field.width = 1 ∨ field.width = 2 ∨ field.width = 4 ∨
        field.width = 8) ∧ field.offset + field.width ≤ size) →
      BlockAt before st.mem pointer.toNat size (blockFold done) →
      (∀ mem, BlockAt before mem pointer.toNat size
          (blockFold (done ++ fields.zip (fieldValues fields (values.map .word)))) →
        wp m rest Q { st with mem := mem } s env) →
      wp m (fieldStoresCode pointerLocal fields locs ++ rest) Q st s env
  | [], _, _, st, done, _, _, _, hBlock, h => by
    simp only [fieldStoresCode, List.nil_append]
    exact h st.mem (by simpa using hBlock)
  | field :: fields, locs, values, st, done, hHeld, hLength, hWidths, hBlock, h => by
    have hHead := hWidths field List.mem_cons_self
    have hTail : ∀ other ∈ fields, (other.width = 1 ∨ other.width = 2 ∨ other.width = 4 ∨
        other.width = 8) ∧ other.offset + other.width ≤ size := fun other member =>
      hWidths other (List.mem_cons_of_mem _ member)
    cases hSource : field.source with
    | const value =>
      have hTakes : field.takesArg = false := by simp [Field.takesArg, hSource]
      simp only [fieldStoresCode, hSource, List.append_assoc]
      refine wp_field_store hPointer (.inl rfl) hBlock hHead.1 hHead.2 hFits hAddress ?_
      intro mem hMem
      rw [← blockFold_snoc] at hMem
      refine wp_field_stores hPointer hFits hAddress fields locs values { st with mem := mem }
        (done ++ [(field, value)]) hHeld
        (by simpa [List.filter_cons, hTakes] using hLength) hTail hMem fun mem' hMem' => h mem' ?_
      simpa [fieldValues, hSource, List.append_assoc] using hMem'
    | word | handle =>
      have hTakes : field.takesArg = true := by simp [Field.takesArg, hSource]
      cases hHeld with
      | nil => simp [hTakes] at hLength
      | @cons place value locs values hPlace hHeld =>
        simp only [fieldStoresCode, hSource, List.append_assoc, List.headD_cons,
          List.tail_cons]
        refine wp_field_store hPointer (.inr ⟨place, rfl, hPlace⟩) hBlock hHead.1 hHead.2 hFits
          hAddress ?_
        intro mem hMem
        rw [← blockFold_snoc] at hMem
        refine wp_field_stores hPointer hFits hAddress fields locs values { st with mem := mem }
          (done ++ [(field, value)]) hHeld
          (by simpa [List.filter_cons, hTakes] using hLength) hTail hMem
          fun mem' hMem' => h mem' ?_
        simpa [fieldValues, hSource, List.append_assoc, Arg.value] using hMem'

end Verified.Wasi
