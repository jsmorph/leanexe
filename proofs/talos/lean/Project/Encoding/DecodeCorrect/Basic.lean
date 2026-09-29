import Project.Encoding.Decode
import Project.Encoding.Spec.Values

namespace Wasm.Encoding.Decoder

open Wasm.Encoding.Spec

/-- `parser` reads exactly `bytes` and returns `value`, whatever input follows. -/
def Parses (parser : Parser α) (bytes : List UInt8) (value : α) : Prop :=
  ∀ rest, parser.run (bytes ++ rest) = .ok (value, rest)

theorem Parses.cast {parser : Parser α} {bytes bytes' : List UInt8} {value : α}
    (h : Parses parser bytes value) (same : bytes = bytes') : Parses parser bytes' value :=
  same ▸ h

theorem Parses.pure' (value : α) : Parses (pure value : Parser α) [] value :=
  fun _ => rfl

theorem Parses.bind {p : Parser α} {f : α → Parser β} {b₁ b₂ : List UInt8} {v₁ : α} {v₂ : β}
    (h₁ : Parses p b₁ v₁) (h₂ : Parses (f v₁) b₂ v₂) : Parses (p >>= f) (b₁ ++ b₂) v₂ := by
  intro rest
  show StateT.run (p >>= f) (b₁ ++ b₂ ++ rest) = _
  rw [StateT.run_bind, List.append_assoc, h₁ (b₂ ++ rest)]
  exact h₂ rest

theorem Parses.bind_nil {p : Parser α} {f : α → Parser β} {b₁ : List UInt8} {v₁ : α} {v₂ : β}
    (h₁ : Parses p b₁ v₁) (h₂ : Parses (f v₁) [] v₂) : Parses (p >>= f) b₁ v₂ :=
  (Parses.bind h₁ h₂).cast (List.append_nil b₁)

theorem Parses.bind_cons {p : Parser α} {f : α → Parser β} {b : UInt8} {bytes : List UInt8}
    {v₁ : α} {v₂ : β} (h₁ : Parses p [b] v₁) (h₂ : Parses (f v₁) bytes v₂) :
    Parses (p >>= f) (b :: bytes) v₂ :=
  Parses.bind h₁ h₂

theorem Parses.map {p : Parser α} {f : α → β} {bytes : List UInt8} {value : α}
    (h : Parses p bytes value) : Parses (f <$> p) bytes (f value) := by
  intro rest
  show StateT.run (f <$> p) (bytes ++ rest) = _
  rw [StateT.run_map, h rest]
  rfl

theorem parses_byte (b : UInt8) : Parses byte [b] b :=
  fun _ => rfl

theorem parses_take (bytes : List UInt8) : Parses (take bytes.length) bytes bytes := by
  intro rest
  simp [take, StateT.run, get, set, getThe, MonadStateOf.get, MonadStateOf.set,
    StateT.get, StateT.set, pure, StateT.pure, bind, StateT.bind, Except.pure, Except.bind]

theorem unsigned_lt {width : Nat} {bytes : List UInt8} {n : Nat}
    (h : Unsigned width bytes n) : n < 2 ^ width := by
  induction h with
  | terminal width byte positive low fits => exact fits
  | next width byte tail value positive high rest ih =>
      have hByte := byte.toNat_lt
      have hPow : 2 ^ (width + 7) = 2 ^ width * 128 := by rw [Nat.pow_add]
      rw [hPow]
      omega

theorem unsigned_nonempty {width : Nat} {bytes : List UInt8} {n : Nat}
    (h : Unsigned width bytes n) : bytes ≠ [] := by
  cases h <;> simp

theorem parses_unsigned {width : Nat} {bytes : List UInt8} {n : Nat}
    (h : Unsigned width bytes n) : ∀ width', width ≤ width' → Parses (unsigned width') bytes n := by
  induction h with
  | terminal width byte positive low fits =>
      intro width' hw
      have hFits : byte.toNat < 2 ^ width' :=
        Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) hw)
      rw [unsigned]
      refine Parses.bind_nil (parses_byte byte) ?_
      simp only [low, hFits, ite_true]
      exact Parses.pure' _
  | next width byte tail value positive high rest ih =>
      intro width' hw
      have hWide : 7 < width' := by omega
      rw [unsigned]
      refine (Parses.bind (parses_byte byte) ?_).cast rfl
      simp only [show ¬ byte.toNat < 128 by omega, ite_false, hWide, dite_true]
      exact Parses.bind_nil (ih (width' - 7) (by omega)) (Parses.pure' _)

theorem parses_signed {width : Nat} {bytes : List UInt8} {n : Int}
    (h : Signed width bytes n) : Parses (signed width) bytes n := by
  induction h with
  | terminal width byte positive low lower upper =>
      rw [signed]
      refine Parses.bind_nil (parses_byte byte) ?_
      unfold signedDigit at lower upper
      by_cases small : byte.toNat < 64
      · have hUpper : byte.toNat < 2 ^ (width - 1) := by
          simp only [small, ite_true] at upper
          exact_mod_cast upper
        simp only [small, ite_true, hUpper, signedDigit]
        exact Parses.pure' _
      · simp only [small, ite_false] at lower upper
        have hLower : 128 - 2 ^ (width - 1) ≤ byte.toNat := by
          have : ((2 ^ (width - 1) : Nat) : Int) = (2 ^ (width - 1) : Int) := by push_cast; rfl
          omega
        simp only [small, ite_false, low, ite_true, hLower, signedDigit]
        exact Parses.pure' _
  | next width byte tail value positive high rest ih =>
      have hWide : 7 < width + 7 := by omega
      rw [signed]
      refine Parses.bind (parses_byte byte) ?_
      simp only [show ¬ byte.toNat < 64 by omega, show ¬ byte.toNat < 128 by omega, ite_false,
        hWide, dite_true, Nat.add_sub_cancel]
      exact Parses.bind_nil ih (Parses.pure' _)

theorem wrap32_toInt (x : UInt32) : wrap32 x.toBitVec.toInt = x := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := x.toBitVec))
  simp only [BitVec.toNat_ofInt] at h
  unfold wrap32
  have hModulus : (4294967296 : Int) = ((2 ^ 32 : Nat) : Int) := rfl
  rw [hModulus, h]
  exact UInt32.ofNat_toNat

theorem wrap64_toInt (x : UInt64) : wrap64 x.toBitVec.toInt = x := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := x.toBitVec))
  simp only [BitVec.toNat_ofInt] at h
  unfold wrap64
  have hModulus : (18446744073709551616 : Int) = ((2 ^ 64 : Nat) : Int) := rfl
  rw [hModulus, h]
  exact UInt64.ofNat_toNat

theorem parses_many {item : Parser α} {relation : List UInt8 → α → Prop}
    (hItem : ∀ bytes value, relation bytes value → Parses item bytes value)
    {bytes : List UInt8} {values : List α} (h : Items relation bytes values) :
    Parses (many item values.length) bytes values := by
  induction h with
  | nil => exact Parses.pure' _
  | cons headBytes tailBytes head tail headEncoding tailEncoding ih =>
      rw [List.length_cons, many]
      exact Parses.bind (hItem _ _ headEncoding) (Parses.bind_nil ih (Parses.pure' _))

theorem items_length_le {relation : List UInt8 → α → Prop}
    (hNonempty : ∀ bytes value, relation bytes value → bytes ≠ [])
    {bytes : List UInt8} {values : List α} (h : Items relation bytes values) :
    values.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons headBytes tailBytes head tail headEncoding tailEncoding ih =>
      have hHead : headBytes ≠ [] := hNonempty _ _ headEncoding
      have hPositive : 0 < headBytes.length := by
        cases headBytes with
        | nil => exact absurd rfl hHead
        | cons _ _ => simp
      simp only [List.length_cons, List.length_append]
      omega

theorem parses_vec {item : Parser α} {relation : List UInt8 → α → Prop}
    (hItem : ∀ bytes value, relation bytes value → Parses item bytes value)
    (hNonempty : ∀ bytes value, relation bytes value → bytes ≠ [])
    {bytes : List UInt8} {values : List α} (h : Vector relation bytes values) :
    Parses (vec item) bytes values := by
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
      show StateT.run (remaining >>= fun available =>
        if available < values.length then malformed "unexpected end"
        else many item values.length) (body ++ rest) = _
      rw [StateT.run_bind]
      show StateT.run (if (body ++ rest).length < values.length then malformed "unexpected end"
        else many item values.length) (body ++ rest) = _
      rw [ite_eq_right hNot]
      exact parses_many hItem items rest

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray, String.fromUTF8]
  rw [dite_eq_left s.isValidUTF8]

theorem parses_name {bytes : List UInt8} {value : String} (h : Name bytes value) :
    Parses name bytes value := by
  cases h with
  | intro countBytes value count =>
      unfold name
      refine Parses.bind (parses_unsigned count 32 (Nat.le_refl _)) ?_
      have hLength : value.toUTF8.size = value.toUTF8.data.toList.length := by simp
      rw [hLength]
      refine Parses.bind_nil (parses_take _) ?_
      have hArray : (⟨value.toUTF8.data.toList.toArray⟩ : ByteArray) = value.toUTF8 := by simp
      simp only [hArray, fromUTF8?_toUTF8]
      exact Parses.pure' _

theorem parses_within {parser : Parser α} {payload : List UInt8} {value : α}
    (h : Parses parser payload value) : Parses (within payload.length parser) payload value := by
  unfold within
  refine Parses.bind_nil (parses_take payload) ?_
  have hRun : parser.run payload = .ok (value, []) := by
    simpa using h []
  simp only [hRun]
  exact Parses.pure' _

end Wasm.Encoding.Decoder
