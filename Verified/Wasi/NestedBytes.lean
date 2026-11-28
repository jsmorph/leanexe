module

public import Verified.Wasi.HostMemory
public import Verified.Wasi.SysWords

@[expose] public section

/-! The bytes of the nested parameters: the little-endian bytes of a value, the element of an iovec,
and the subscription array.  The element and each field of a subscription read back as the words
that they hold, and a subscription array's byte inside a field is the field's byte when the fields
lie apart. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi

theorem byteOf_toNat (value index : Nat) :
    (byteOf value index).toNat = value / 2 ^ (8 * index) % 256 := by
  simp [byteOf]

theorem byteOf_succ (value index : Nat) :
    byteOf value (index + 1) = byteOf (value / 256) index := by
  unfold byteOf
  congr 1
  rw [show 8 * (index + 1) = 8 + 8 * index by omega, Nat.pow_add, Nat.div_div_eq_div_mul]

theorem byteOf_zero (value : Nat) : (byteOf value 0).toNat = value % 256 := by
  simp [byteOf_toNat]

/-- The little-endian value of the bytes of a value of at most eight bytes. -/
theorem foldr_bytes (value : Nat) :
    ∀ (count : Nat) (f : Nat → UInt64), count ≤ 8 → value < 2 ^ (8 * count) →
      (∀ index, index < count → (f index).toNat = (byteOf value index).toNat) →
      ((List.range count).foldr (fun index acc => f index + acc * 256) 0).toNat = value
  | 0, _, _, small, _ => by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.lt_one_iff] at small
    simp [small]
  | count + 1, f, bound, small, bytes => by
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    have hSmall : value / 256 < 2 ^ (8 * count) := by
      rw [show 8 * (count + 1) = 8 * count + 8 by omega, Nat.pow_add] at small
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr small
    have rest := foldr_bytes (value / 256) count (fun index => f (index + 1)) (by omega) hSmall
      (fun index h => by rw [bytes (index + 1) (by omega), byteOf_succ])
    have head := bytes 0 (by omega)
    rw [byteOf_zero] at head
    have hWide : value < 2 ^ 64 :=
      Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [Nat.reducePow] at hWide
    rw [UInt64.toNat_add, UInt64.toNat_mul, rest, head]
    simp only [UInt64.reduceToNat]
    omega

/-- Bytes of at most eight bytes whose byte `k` is byte `k` of `value` have the little-endian value
`value`. -/
theorem littleEndian_of_bytes {bytes : LeanExe.Bytes} {value : Nat} (hSize : bytes.data.size ≤ 8)
    (hSmall : value < 2 ^ (8 * bytes.data.size))
    (hBytes : ∀ index (h : index < bytes.data.size), bytes.data[index] = byteOf value index) :
    littleEndian bytes = UInt64.ofNat value := by
  have hWide : value < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hSmall (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [Nat.reducePow] at hWide
  apply UInt64.toNat_inj.mp
  rw [littleEndian, foldr_bytes value _ _ hSize hSmall (fun index h => by
    rw [UInt8.toNat_toUInt64, getElem!_pos bytes.data index h, hBytes index h])]
  rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]

/-- The bytes that `Mem.readBytes` reads. -/
theorem readBytes_get (mem : Mem) (offset length index : Nat)
    (h : index < (bytesOfList (mem.readBytes offset length)).data.size) :
    (bytesOfList (mem.readBytes offset length)).data[index] = mem.bytes (offset + index) := by
  simp only [bytesOfList_size, Mem.readBytes, List.length_map, List.length_range] at h
  simp [bytesOfList, Mem.readBytes, ByteArray.getElem_eq_getElem_data]

/-- Bytes in memory that hold byte `k` of `value` at `offset + k` read back as `value`. -/
theorem readBytes_value_of {mem : Mem} {offset width value : Nat} (hWidth : width ≤ 8)
    (hSmall : value < 2 ^ (8 * width))
    (hBytes : ∀ k, k < width → mem.bytes (offset + k) = byteOf value k) :
    littleEndian (bytesOfList (mem.readBytes offset width)) = UInt64.ofNat value := by
  have hSize : (bytesOfList (mem.readBytes offset width)).data.size = width := by
    simp [Mem.readBytes]
  refine littleEndian_of_bytes (by omega) (by rw [hSize]; exact hSmall) ?_
  intro index h
  rw [readBytes_get, hBytes index (by omega)]

/-! ## The element of an iovec -/

theorem elementBytes_size (pointer : UInt32) (length : Nat) :
    (elementBytes pointer length).data.size = 8 := by
  simp [elementBytes, ByteArray.size]

theorem elementBytes_get (pointer : UInt32) (length index : Nat)
    (h : index < (elementBytes pointer length).data.size) :
    (elementBytes pointer length).data[index] =
      if index < 4 then byteOf pointer.toNat index else byteOf (length % 2 ^ 32) (index - 4) := by
  simp [elementBytes, ByteArray.getElem_eq_getElem_data]

/-- An element at `root` holds the buffer's pointer at `root` and its length at `root + 4`. -/
theorem element_read {mem : Mem} {root : UInt64} {pointer : UInt32} {length : Nat}
    (h : Bytes.At mem root (elementBytes pointer length)) :
    mem.read32 root.toUInt32 = pointer ∧
      mem.read32 (root.toUInt32 + 4) = UInt32.ofNat length := by
  have hAddress := h.address
  rw [elementBytes_size] at hAddress
  have hRoot : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hFour : (root.toUInt32 + 4).toNat = root.toNat + 4 := by
    rw [UInt32.toNat_add, hRoot]
    simp only [UInt32.reduceToNat]
    omega
  have byte : ∀ index (hi : index < 8), (mem.bytes (root.toNat + index)).toNat =
      if index < 4 then pointer.toNat / 2 ^ (8 * index) % 256
      else length % 2 ^ 32 / 2 ^ (8 * (index - 4)) % 256 := by
    intro index hi
    have hSize : index < (elementBytes pointer length).data.size := by
      rw [elementBytes_size]; exact hi
    rw [h.contents index hSize, elementBytes_get]
    split <;> rw [byteOf_toNat]
  have b0 := byte 0 (by omega)
  have b1 := byte 1 (by omega)
  have b2 := byte 2 (by omega)
  have b3 := byte 3 (by omega)
  have b4 := byte 4 (by omega)
  have b5 := byte 5 (by omega)
  have b6 := byte 6 (by omega)
  have b7 := byte 7 (by omega)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, ite_true,
    ite_false, show (1 : Nat) < 4 from by decide, show (2 : Nat) < 4 from by decide,
    show (3 : Nat) < 4 from by decide, show ¬(4 : Nat) < 4 from by decide,
    show ¬(5 : Nat) < 4 from by decide, show ¬(6 : Nat) < 4 from by decide,
    show ¬(7 : Nat) < 4 from by decide, show (0 : Nat) < 4 from by decide]
    at b0 b1 b2 b3 b4 b5 b6 b7
  have hPointer := pointer.toNat_lt
  constructor
  · apply UInt32.toNat_inj.mp
    rw [toNat_read32, hRoot, b0, b1, b2, b3]
    simp only [Nat.reducePow, Nat.reduceMul] at hPointer ⊢
    omega
  · apply UInt32.toNat_inj.mp
    rw [toNat_read32, hFour, show root.toNat + 4 + 1 = root.toNat + 5 by omega,
      show root.toNat + 4 + 2 = root.toNat + 6 by omega,
      show root.toNat + 4 + 3 = root.toNat + 7 by omega, b4, b5, b6, b7,
      UInt32.toNat_ofNat']
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub]
    omega

/-! ## The subscription array -/

/-- Two fields lie apart. -/
def _root_.LeanExe.Wasi.Field.Apart (field other : Field) : Prop :=
  field.offset + field.width ≤ other.offset ∨ other.offset + other.width ≤ field.offset

/-- A field covers a byte index. -/
def _root_.LeanExe.Wasi.Field.Covers (field : Field) (index : Nat) : Prop :=
  field.offset ≤ index ∧ index < field.offset + field.width

theorem _root_.LeanExe.Wasi.Field.Apart.symm {field other : Field} (h : field.Apart other) :
    other.Apart field :=
  Or.symm h

theorem _root_.LeanExe.Wasi.Field.Apart.not_covers {field other : Field} {index : Nat}
    (h : field.Apart other)
    (covers : field.Covers index) : ¬other.Covers index := by
  intro other'
  simp only [Field.Apart, Field.Covers] at h covers other'
  omega

theorem fieldsApart_pairwise : ∀ {fields : List Field}, fieldsApart fields = true →
    fields.Pairwise Field.Apart
  | [], _ => List.Pairwise.nil
  | field :: fields, h => by
    simp only [fieldsApart, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    exact List.Pairwise.cons (fun other member => h.1 other member) (fieldsApart_pairwise h.2)

/-- The fields of records that fit lie inside their records, apart from one another. -/
theorem placedFields_fit {records : List (List Field)} (fits : recordsFit records = true) :
    ∀ (base : Nat), (∀ field ∈ placedFields base records,
      base ≤ field.offset ∧ field.offset + field.width ≤ base + 48 * records.length ∧
        field.width ≤ 8) ∧
      (placedFields base records).Pairwise Field.Apart := by
  induction records with
  | nil => intro base; exact ⟨fun _ member => by simp [placedFields] at member, .nil⟩
  | cons fields records ih =>
    intro base
    simp only [recordsFit, List.all_cons, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at fits
    obtain ⟨⟨inside, apart⟩, rest⟩ := fits
    have restFit : recordsFit records = true := by
      simp only [recordsFit, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact rest
    obtain ⟨bounds, pairwise⟩ := ih restFit (base + 48)
    have shifted : ∀ field ∈ fields.map (fun field => { field with offset := base + field.offset }),
        base ≤ field.offset ∧ field.offset + field.width ≤ base + 48 ∧ field.width ≤ 8 := by
      intro field member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      have := inside original originalMember
      simp only
      omega
    refine ⟨fun field member => ?_, ?_⟩
    · simp only [placedFields, List.mem_append] at member
      rcases member with here | there
      · have := shifted field here
        simp only [List.length_cons]
        omega
      · have := bounds field there
        simp only [List.length_cons]
        omega
    · simp only [placedFields]
      refine List.pairwise_append.mpr ⟨?_, pairwise, ?_⟩
      · refine List.pairwise_map.mpr ((fieldsApart_pairwise apart).imp ?_)
        intro field other h
        simp only [Field.Apart] at h ⊢
        omega
      · intro field here other there
        have h1 := shifted field here
        have h2 := bounds other there
        simp only [Field.Apart]
        omega

/-- The steps of `blockByte` from `byte` over pairs whose fields do not cover `index` leave
`byte`. -/
theorem blockByte_skip (index : Nat) : ∀ (pairs : List (Field × UInt64)) (byte : UInt8),
    (∀ pair ∈ pairs, ¬pair.1.Covers index) →
    pairs.foldl (fun byte placed =>
      if placed.1.offset ≤ index ∧ index < placed.1.offset + placed.1.width then
        byteOf placed.2.toNat (index - placed.1.offset)
      else byte) byte = byte
  | [], _, _ => rfl
  | pair :: pairs, byte, skips => by
    rw [List.foldl_cons, ite_eq_right (show ¬(pair.1.offset ≤ index ∧
      index < pair.1.offset + pair.1.width) from skips pair List.mem_cons_self)]
    exact blockByte_skip index pairs byte fun other member =>
      skips other (List.mem_cons_of_mem _ member)

theorem pairwise_zip_fst {α β : Type} {R : α → α → Prop} :
    ∀ {items : List α}, items.Pairwise R → ∀ (others : List β),
      ((items.zip others).map Prod.fst).Pairwise R
  | [], _, _ => by simp
  | _ :: _, _, [] => by simp
  | item :: items, pairwise, other :: others => by
    rw [List.zip_cons_cons, List.map_cons]
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp pairwise
    refine List.Pairwise.cons (fun first member => ?_) (pairwise_zip_fst tail others)
    obtain ⟨pair, inZip, rfl⟩ := List.mem_map.mp member
    exact head pair.1 (List.of_mem_zip inZip).1

/-- A byte inside a field of fields that lie apart is the field's byte. -/
theorem blockByte_at {fields : List Field} {values : List UInt64} {field : Field} {value : UInt64}
    {index : Nat} (apart : fields.Pairwise Field.Apart)
    (member : (field, value) ∈ fields.zip values)
    (covers : field.Covers index) :
    blockByte fields values index = byteOf value.toNat (index - field.offset) := by
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  have firsts : ((fields.zip values).map Prod.fst).Pairwise Field.Apart :=
    pairwise_zip_fst apart values
  rw [split, List.map_append, List.map_cons] at firsts
  obtain ⟨_, middle, _⟩ := List.pairwise_append.mp firsts
  have tail := (List.pairwise_cons.mp middle).1
  unfold blockByte
  rw [split, List.foldl_append, List.foldl_cons]
  dsimp only
  rw [ite_eq_left (show field.offset ≤ index ∧ index < field.offset + field.width from covers)]
  apply blockByte_skip
  intro pair inAfter
  exact (tail pair.1 (List.mem_map.mpr ⟨pair, inAfter, rfl⟩)).not_covers covers

theorem subscriptionBytes_size (records : List (List Field)) (args : List Arg) :
    (subscriptionBytes records args).data.size = 48 * records.length := by
  simp [subscriptionBytes, ByteArray.size]

theorem subscriptionBytes_get (records : List (List Field)) (args : List Arg) (index : Nat)
    (h : index < (subscriptionBytes records args).data.size) :
    (subscriptionBytes records args).data[index] =
      blockByte (placedFields 0 records) (fieldValues (placedFields 0 records) args) index := by
  simp [subscriptionBytes, ByteArray.getElem_eq_getElem_data]

/-- The subscriptions of records that fit, at `root`, hold each field's value at `root` plus the
field's offset. -/
theorem subscription_fields_at {mem : Mem} {root : UInt64} {records : List (List Field)}
    {args : List Arg} (fits : recordsFit records = true)
    (h : Bytes.At mem root (subscriptionBytes records args)) :
    ∀ pair ∈ (placedFields 0 records).zip (fieldValues (placedFields 0 records) args),
      ∀ k, k < pair.1.width →
        mem.bytes (root.toNat + pair.1.offset + k) = byteOf pair.2.toNat k := by
  intro pair member k hk
  obtain ⟨bounds, apart⟩ := placedFields_fit fits 0
  have inside := bounds pair.1 (List.of_mem_zip member).1
  have hIndex : pair.1.offset + k < (subscriptionBytes records args).data.size := by
    rw [subscriptionBytes_size]; omega
  rw [Nat.add_assoc, h.contents _ hIndex, subscriptionBytes_get,
    blockByte_at apart member ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- The words of the fields of `fields` that take arguments, read from `mem` at `base` plus their
offsets as the little-endian values of their widths. -/
def readFields (mem : Mem) (base : Nat) : List Field → List Arg
  | [] => []
  | field :: fields =>
    if field.takesArg then
      .word (littleEndian (bytesOfList (mem.readBytes (base + field.offset) field.width))) ::
        readFields mem base fields
    else readFields mem base fields

/-- Fields whose values lie in memory read back as the arguments that gave the values. -/
theorem readFields_args {mem : Mem} {base : Nat} :
    ∀ (fields : List Field) (args : List Arg), (∀ field ∈ fields, field.width ≤ 8) →
      argFieldsFit (fields.filter Field.takesArg) args = true →
      (∀ pair ∈ fields.zip (fieldValues fields args), ∀ k, k < pair.1.width →
        mem.bytes (base + pair.1.offset + k) = byteOf pair.2.toNat k) →
      readFields mem base fields = args.take (fields.filter Field.takesArg).length
  | [], _, _, _, _ => by simp [readFields]
  | field :: fields, args, widths, fit, placed => by
    have restWidths : ∀ other ∈ fields, other.width ≤ 8 := fun other member =>
      widths other (List.mem_cons_of_mem _ member)
    cases hSource : field.source with
    | const value =>
      have hTakes : field.takesArg = false := by simp [Field.takesArg, hSource]
      simp only [List.filter_cons, hTakes, Bool.false_eq_true, ite_false] at fit ⊢
      simp only [readFields, hTakes, Bool.false_eq_true, ite_false]
      simp only [fieldValues, hSource, List.zip_cons_cons] at placed
      exact readFields_args fields args restWidths fit fun pair member =>
        placed pair (List.mem_cons_of_mem _ member)
    | word | handle =>
      have hTakes : field.takesArg = true := by simp [Field.takesArg, hSource]
      simp only [List.filter_cons, hTakes, ite_true] at fit ⊢
      cases args with
      | nil => simp [argFieldsFit] at fit
      | cons arg args =>
        cases arg with
        | bytes _ | space _ => simp [argFieldsFit] at fit
        | word word =>
          simp only [argFieldsFit, Bool.and_eq_true, decide_eq_true_eq] at fit
          simp only [fieldValues, hSource, List.head?_cons, Option.map_some, Option.getD_some,
            Arg.value, List.tail_cons, List.zip_cons_cons] at placed
          simp only [readFields, hTakes, ite_true, List.length_cons, List.take_succ_cons]
          have hWord :
              littleEndian (bytesOfList (mem.readBytes (base + field.offset) field.width)) =
                word := by
            rw [readBytes_value_of (widths field List.mem_cons_self) fit.1
              (fun k hk => placed (field, word) List.mem_cons_self k hk), UInt64.ofNat_toNat]
          rw [hWord, readFields_args fields args restWidths fit.2 fun pair member =>
            placed pair (List.mem_cons_of_mem _ member)]

end Verified.Wasi
