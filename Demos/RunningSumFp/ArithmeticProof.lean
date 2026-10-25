import Demos.RunningSumFp.Program
import Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem
import Library.Numerics.Decimal.PrintFloat.PrintFloatTheorem
import LeanExe.ProofKit.F64Bits

namespace Demos.RunningSumFp

open LeanExe
open Library.Numerics.Decimal
open Library.Numerics.Decimal.Shared.StrconvGrammar
open Library.Numerics.Decimal.Shared.StrconvRound
open Library.Numerics.Decimal.Shared.StrconvDecode

def trimCR (input : List UInt8) : List UInt8 :=
  if input.getLast? = some 13 then input.dropLast else input

def LineDenotes (input : List UInt8) (number : Num) : Prop := Derives true (trimCR input) number

noncomputable def lineBits (number : Num) : UInt64 := canon64 (round64 number)

noncomputable def lineMeaning (input : List UInt8) : Option UInt64 :=
  (decode true (trimCR input)).map lineBits

theorem lineDenotes_unique (input : List UInt8) (a b : Num)
    (ha : LineDenotes input a) (hb : LineDenotes input b) : a = b :=
  derives_unique ha hb

noncomputable def prefixBits (total : UInt64) : List Num → List UInt64
  | [] => []
  | number :: rest =>
      let next := Wasm.IEEE64.add total (lineBits number)
      next :: prefixBits next rest

noncomputable def prefixFloats (total : Float) : List Num → List Float
  | [] => []
  | number :: rest =>
      let next := total + Float.ofBits (round64 number)
      next :: prefixFloats next rest

theorem trimCR_length_le (input : List UInt8) : (trimCR input).length ≤ input.length := by
  unfold trimCR
  split <;> simp

theorem stripCR_words (input : List UInt8) (bound : input.length < 2 ^ 32) :
    stripCR (words input) = words (trimCR input) := by
  rcases List.eq_nil_or_concat input with empty | ⟨text, last, same⟩
  · subst input
    rfl
  · simp only [List.concat_eq_append] at same
    subst input
    have sizeNat : (words (text ++ [last])).size.toUInt64.toNat = text.length + 1 := by
      rw [ParseFloat.ParseFloatScan.words_size64 _ bound]
      simp
    have positive : (0 : UInt64) < (words (text ++ [last])).size.toUInt64 := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero, sizeNat]
      omega
    have previous : ((words (text ++ [last])).size.toUInt64 - 1).toNat = text.length := by
      rw [UInt64.toNat_sub_of_le]
      · simp [sizeNat]
      · simp only [UInt64.le_iff_toNat_le, sizeNat, UInt64.toNat_one]
        omega
    have lastByte : (words (text ++ [last]))[text.length]! = last.toUInt64 := by
      simp [words, getElem!_pos, List.getElem_append_right]
    have byteEq : last.toUInt64 = 13 ↔ last = 13 := by
      constructor
      · intro same
        apply UInt8.toNat.inj
        have bits := congrArg UInt64.toNat same
        simpa using bits
      · rintro rfl
        rfl
    simp only [stripCR, positive, decide_true, Bool.true_and, previous, lastByte,
      beq_iff_eq, byteEq, trimCR, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.some.injEq]
    by_cases cr : last = 13
    · have previousCR : ((words (text ++ [13])).size.toUInt64 - 1).toNat = text.length := by
        simpa only [cr] using previous
      simp only [cr, ↓reduceIte, List.dropLast_append, List.dropLast_singleton,
        List.append_nil, List.isEmpty_cons, Bool.false_eq_true]
      apply PrintFloat.PrintFloatLayout.build_words
      · exact previousCR.symm
      · intro i hi
        rw [previousCR] at hi
        have iNat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by
          change i < 18446744073709551616
          have length : text.length + 1 < 2 ^ 32 := by simpa using bound
          omega)
        rw [iNat, getElem!_pos (words (text ++ [13])) i (by simp [words]; omega)]
        simp only [words, List.getElem_toArray, List.getElem_map,
          List.getElem_append_left hi, ParseFloat.ParseFloatScan.byteAt_lt text i hi]
    · simp only [cr, ↓reduceIte]

theorem parse_accept (input : List UInt8) (number : Num) (bound : input.length < 2 ^ 32)
    (meaning : LineDenotes input number) :
    parse (words input) = (true, Float.ofBits (round64 number)) := by
  have trimmedBound : (trimCR input).length < 2 ^ 32 :=
    lt_of_le_of_lt (trimCR_length_le input) bound
  simp only [parse, stripCR_words input bound,
    ParseFloat.ParseFloatTheorem.parse64_accept true _ number trimmedBound meaning]

theorem parse_reject (input : List UInt8) (bound : input.length < 2 ^ 32)
    (invalid : ∀ number, ¬ LineDenotes input number) :
    parse (words input) = (false, Float.ofBits 0) := by
  have trimmedBound : (trimCR input).length < 2 ^ 32 :=
    lt_of_le_of_lt (trimCR_length_le input) bound
  simp only [parse, stripCR_words input bound,
    ParseFloat.ParseFloatTheorem.parse64_reject true _ trimmedBound invalid]

theorem parse_valid_iff (input : List UInt8) (bound : input.length < 2 ^ 32) :
    (parse (words input)).1 = true ↔ ∃ number, LineDenotes input number := by
  classical
  by_cases valid : ∃ number, LineDenotes input number
  · obtain ⟨number, meaning⟩ := valid
    constructor
    · intro _
      exact ⟨number, meaning⟩
    · intro _
      rw [parse_accept input number bound meaning]
  · have invalid : ∀ number, ¬ LineDenotes input number := by simpa using valid
    simp [parse_reject input bound invalid, valid]

theorem bits_of_reference (number : Num) : (Float.ofBits (round64 number)).toBits = lineBits number :=
  LeanExe.ProofKit.F64Bits.toBits_ofBits _

theorem parse_bits (input : List UInt8) (number : Num) (bound : input.length < 2 ^ 32)
    (meaning : LineDenotes input number) : (parse (words input)).2.toBits = lineBits number := by
  rw [parse_accept input number bound meaning]
  exact bits_of_reference number

theorem parse_meaning (input : List UInt8) (bound : input.length < 2 ^ 32) :
    (if (parse (words input)).1 then some (parse (words input)).2.toBits else none) =
      lineMeaning input := by
  have trimmedBound : (trimCR input).length < 2 ^ 32 :=
    lt_of_le_of_lt (trimCR_length_le input) bound
  simp only [parse, stripCR_words input bound,
    ParseFloat.ParseFloatTheorem.parse64_spec true _ trimmedBound]
  cases decoded : decode true (trimCR input) with
  | none => simp [ParseFloat.ParseFloatTheorem.res64, lineMeaning, decoded]
  | some number =>
      simp [ParseFloat.ParseFloatTheorem.res64, lineMeaning, decoded, bits_of_reference]

@[simp] theorem zero_bits : (0 : Float).toBits = 0 := rfl

theorem add_bits (total : Float) (number : Num) :
    (total + Float.ofBits (round64 number)).toBits = Wasm.IEEE64.add total.toBits (lineBits number) := by
  rw [LeanExe.ProofKit.F64Bits.toBits_add, bits_of_reference]

theorem prefixFloats_bits (total : Float) (numbers : List Num) :
    (prefixFloats total numbers).map Float.toBits = prefixBits total.toBits numbers := by
  induction numbers generalizing total with
  | nil => rfl
  | cons number rest ih =>
      simp only [prefixFloats, List.map_cons, ih, prefixBits, add_bits]

theorem print_size_bound (value : Float) : (PrintFloat.print64 value.toBits).size < 2 ^ 32 := by
  obtain ⟨text, number, printed, _, _, _, bound, _⟩ :=
    PrintFloat.PrintFloatTheorem.derives64 false value.toBits
  change (PrintFloat.print64With false value.toBits).size < 2 ^ 32
  rw [printed]
  simpa [words] using bound

theorem render_size (value : Float) :
    (render value).data.size = (PrintFloat.print64 value.toBits).size + 1 := by
  have bound := print_size_bound value
  have sizeNat : (PrintFloat.print64 value.toBits).size.toUInt64.toNat =
      (PrintFloat.print64 value.toBits).size := UInt64.toNat_ofNat_of_lt' (by
        change _ < 18446744073709551616
        omega)
  simp only [render, Bytes.data_size_build, UInt64.toNat_add, sizeNat, UInt64.toNat_one]
  omega

theorem render_nonempty (value : Float) : 0 < (render value).data.size := by
  rw [render_size]
  omega

theorem render_size_bound (value : Float) : (render value).data.size < UInt64.size := by
  have bound := print_size_bound value
  rw [render_size]
  change _ < 18446744073709551616
  omega

theorem packed_text (text : List UInt8) (bound : text.length < 2 ^ 32) :
    (Bytes.build ((words text).size.toUInt64 + 1) fun i =>
      if i == (words text).size.toUInt64 then 10 else (words text)[i.toNat]!).data.data.toList =
        text ++ [10] := by
  have sizeNat := ParseFloat.ParseFloatScan.words_size64 text bound
  have countNat : ((words text).size.toUInt64 + 1).toNat = text.length + 1 := by
    rw [UInt64.toNat_add, sizeNat, UInt64.toNat_one]
    omega
  apply List.ext_getElem
  · simp [Bytes.build, countNat]
  · intro i hi hj
    have inside : i < text.length + 1 := by simpa using hj
    have iNat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by
      change i < 18446744073709551616
      omega)
    have equal : UInt64.ofNat i = (words text).size.toUInt64 ↔ i = text.length := by
      constructor
      · intro same
        have := congrArg UInt64.toNat same
        simpa only [iNat, sizeNat] using this
      · intro same
        apply UInt64.toNat.inj
        rw [iNat, sizeNat, same]
    simp only [Bytes.build, Array.getElem_toList, Array.getElem_ofFn, beq_iff_eq, equal, iNat]
    by_cases last : i = text.length
    · subst i
      simp
    · have textInside : i < text.length := by omega
      simp only [last, ↓reduceIte, List.getElem_append_left textInside]
      rw [getElem!_pos (words text) i (by simpa [words] using textInside)]
      simp [words]

theorem render_of_printed (value : Float) (text : List UInt8)
    (printed : PrintFloat.print64 value.toBits = words text) :
    (render value).data.data.toList = text ++ [10] := by
  have bound : text.length < 2 ^ 32 := by
    have size := print_size_bound value
    rw [printed] at size
    simpa [words] using size
  simp only [render, printed]
  exact packed_text text bound

theorem canon_bits (value : Float) : canon64 value.toBits = value.toBits :=
  LeanExe.ProofKit.F64Bits.toBits_canonical value

theorem render_text (value : Float) :
    ∃ text number, PrintFloat.print64 value.toBits = words text ∧ Derives true text number ∧
      round64 number = value.toBits ∧ (render value).data.data.toList = text ++ [10] := by
  obtain ⟨text, number, printed, derives, rounded⟩ :=
    PrintFloat.PrintFloatTheorem.print64_derives value.toBits
  exact ⟨text, number, printed, derives, rounded.trans (canon_bits value),
    render_of_printed value text printed⟩

theorem render_roundtrip (value : Float) :
    ParseFloat.parse64 true (words (render value).data.data.toList.dropLast) = (true, value.toBits) := by
  obtain ⟨text, number, printed, _, _, output⟩ := render_text value
  simp only [output, List.dropLast_append, List.isEmpty_cons, Bool.false_eq_true,
    ↓reduceIte, List.dropLast_singleton, List.append_nil]
  rw [← printed, PrintFloat.PrintFloatTheorem.print64_roundtrip, canon_bits]

theorem render_shortest (value : Float) (finite : Wasm.IEEE64.isFinite value.toBits)
    (nonzero : Wasm.IEEE64.scaledMagnitude value.toBits ≠ 0) :
    ∃ text negative digits exponent, (render value).data.data.toList = text ++ [10] ∧
      Derives false text (.dec negative digits exponent) ∧
      Shortest64 value.toBits negative digits exponent := by
  obtain ⟨text, negative, digits, exponent, printed, derives, shortest⟩ :=
    PrintFloat.PrintFloatTheorem.print64_shortest value.toBits finite nonzero
  exact ⟨text, negative, digits, exponent, render_of_printed value text printed, derives, shortest⟩

end Demos.RunningSumFp
