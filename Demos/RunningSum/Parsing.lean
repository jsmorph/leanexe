import Demos.RunningSum.ParsingScan
import Demos.RunningSum.ParsingSlices

namespace Demos.RunningSum

def lineEnd (input : Array UInt64) : Nat :=
  if input.size > 0 && input[input.size - 1]! == 13 then input.size - 1 else input.size

def lineStart (input : Array UInt64) : Nat :=
  if lineEnd input > 0 && (input[0]! == 43 || input[0]! == 45) then 1 else 0

def ValidLine (input : Array UInt64) : Prop :=
  lineStart input < lineEnd input ∧
    ∀ i, lineStart input ≤ i → i < lineEnd input →
      48 ≤ input[i]!.toNat ∧ input[i]!.toNat ≤ 57

def lineInteger (input : Array UInt64) : Int :=
  let value := magnitude (input.extract (lineStart input) (lineEnd input))
  if input[0]! == 45 then -(value : Int) else value

structure LineSyntax (input : Array UInt64) (first last : Nat) : Prop where
  initial : first = 0 ∨ (first = 1 ∧ (input[0]! = 43 ∨ input[0]! = 45))
  final : last = input.size ∨ (last + 1 = input.size ∧ input[last]! = 13)
  nonempty : first < last
  digits : ∀ i, first ≤ i → i < last →
    48 ≤ input[i]!.toNat ∧ input[i]!.toNat ≤ 57

def DecimalLine (input : Array UInt64) (value : Int) : Prop :=
  ∃ first last, LineSyntax input first last ∧
    value = if input[0]! == 45 then -(magnitude (input.extract first last) : Int)
      else magnitude (input.extract first last)

theorem lineEnd_le (input : Array UInt64) : lineEnd input ≤ input.size := by
  unfold lineEnd
  split_ifs <;> omega

theorem lineStart_le (input : Array UInt64) : lineStart input ≤ lineEnd input := by
  unfold lineStart
  split_ifs with signed
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at signed
    omega
  · omega

theorem lineEnd_cases (input : Array UInt64) :
    lineEnd input = input.size ∨
      (lineEnd input + 1 = input.size ∧ input[lineEnd input]! = 13) := by
  unfold lineEnd
  split_ifs with trailing
  · right
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at trailing
    exact ⟨by omega, trailing.2⟩
  · exact Or.inl rfl

theorem lineStart_cases (input : Array UInt64) :
    lineStart input = 0 ∨
      (lineStart input = 1 ∧ (input[0]! = 43 ∨ input[0]! = 45)) := by
  unfold lineStart
  split_ifs with signed
  · right
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at signed
    exact ⟨rfl, signed.2⟩
  · exact Or.inl rfl

theorem validLine_nonempty (input : Array UInt64) (valid : ValidLine input) :
    0 < input.size := by
  have := lineEnd_le input
  have := valid.1
  omega

theorem validLine_noLF (input : Array UInt64) (valid : ValidLine input)
    (i : Nat) (hi : i < input.size) : input[i]! ≠ 10 := by
  intro newline
  by_cases before : i < lineStart input
  · obtain noSign | ⟨one, sign⟩ := lineStart_cases input
    · omega
    · have index : i = 0 := by omega
      rcases sign with plus | minus
      · rw [← index, newline] at plus
        contradiction
      · rw [← index, newline] at minus
        contradiction
  · by_cases inside : i < lineEnd input
    · have digit := valid.2 i (by omega) inside
      rw [newline] at digit
      simp only [UInt64.reduceToNat] at digit
      omega
    · obtain full | ⟨previous, cr⟩ := lineEnd_cases input
      · omega
      · have index : i = lineEnd input := by omega
        rw [← index, newline] at cr
        contradiction

theorem LineSyntax.last_eq {input : Array UInt64} {first last : Nat}
    (shape : LineSyntax input first last) : last = lineEnd input := by
  have nonempty := shape.nonempty
  rcases shape.final with full | ⟨trailing, cr⟩
  · have positive : 0 < input.size := by omega
    have bounds := shape.digits (input.size - 1) (by omega) (by omega)
    have notCR : input[input.size - 1]! ≠ 13 := by
      intro same
      rw [same] at bounds
      simp only [UInt64.reduceToNat] at bounds
      omega
    simp only [lineEnd, positive, decide_true, Bool.true_and, beq_iff_eq,
      notCR, ↓reduceIte, full]
  · have positive : 0 < input.size := by omega
    have previous : input.size - 1 = last := by omega
    simp [lineEnd, positive, previous, cr]

theorem LineSyntax.first_eq {input : Array UInt64} {first last : Nat}
    (shape : LineSyntax input first last) : first = lineStart input := by
  have lastEq := shape.last_eq
  have nonempty := shape.nonempty
  rcases shape.initial with noSign | ⟨one, sign⟩
  · have bounds := shape.digits 0 (by omega) (by omega)
    have noPlus : input[0]! ≠ 43 := by
      intro same
      rw [same] at bounds
      simp only [UInt64.reduceToNat] at bounds
      omega
    have noMinus : input[0]! ≠ 45 := by
      intro same
      rw [same] at bounds
      simp only [UInt64.reduceToNat] at bounds
      omega
    simp [lineStart, noSign, noPlus, noMinus]
  · have positive : 0 < lineEnd input := by omega
    rcases sign with plus | minus
    · simp [lineStart, positive, one, plus]
    · simp [lineStart, positive, one, minus]

theorem decimalLine_iff (input : Array UInt64) (value : Int) :
    DecimalLine input value ↔ ValidLine input ∧ value = lineInteger input := by
  constructor
  · rintro ⟨first, last, shape, meaning⟩
    have firstEq := shape.first_eq
    have lastEq := shape.last_eq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [← firstEq, ← lastEq] using shape.nonempty
    · simpa only [← firstEq, ← lastEq] using shape.digits
    · simpa only [firstEq, lastEq, lineInteger] using meaning
  · rintro ⟨valid, meaning⟩
    refine ⟨lineStart input, lineEnd input,
      ⟨lineStart_cases input, lineEnd_cases input, valid.1, valid.2⟩, ?_⟩
    exact meaning

theorem parse_eq (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    parse input =
      let start := (lineStart input).toUInt64
      let stop := (lineEnd input).toUInt64
      let scanned := parseScan input start stop
      ⟨start < stop && scanned.2,
        ⟨input[0]! == 45 && scanned.1 < stop,
          LeanExe.build (stop - scanned.1) fun i => input[(scanned.1 + i).toNat]!⟩⟩ := by
  have lengthNat : input.size.toUInt64.toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' sizeBound
  by_cases empty : input.size = 0
  · have arrayEmpty := Array.eq_empty_of_size_eq_zero empty
    subst input
    simp [parse, lineEnd, lineStart, parseScan, LeanExe.loop, LeanExe.build, parseScanStep]
    rfl
  · have lengthNonzero : input.size.toUInt64 ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      simp only [lengthNat, UInt64.reduceToNat] at this
      exact empty this
    have lengthPositive : (0 : UInt64) < input.size.toUInt64 := by
      simpa only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat, lengthNat] using
        (show 0 < input.size by omega)
    have previousNat : (input.size.toUInt64 - 1).toNat = input.size - 1 := by
      rw [UInt64.toNat_sub_of_le]
      · simp [lengthNat]
      · simp only [UInt64.le_iff_toNat_le, lengthNat, UInt64.reduceToNat]
        omega
    have stopEq :
        (if input.size.toUInt64 > 0 && input[(input.size.toUInt64 - 1).toNat]! == 13
         then input.size.toUInt64 - 1 else input.size.toUInt64) =
          (lineEnd input).toUInt64 := by
      simp only [lengthPositive, decide_true, Bool.true_and, previousNat, lineEnd,
        show 0 < input.size by omega, decide_true]
      split_ifs
      · apply UInt64.toNat.inj
        rw [previousNat, UInt64.toNat_ofNat_of_lt' (by omega)]
      · rfl
    have stopNat : (lineEnd input).toUInt64.toNat = lineEnd input :=
      UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (lineEnd_le input) sizeBound)
    have startEq :
        (if (lineEnd input).toUInt64 > 0 && (input[0]! == 43 || input[0]! == 45)
         then (1 : UInt64) else 0) = (lineStart input).toUInt64 := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat, stopNat, lineStart]
      split_ifs <;> rfl
    simp only [parse, beq_iff_eq, lengthNonzero, ↓reduceIte, UInt64.reduceToNat,
      stopEq, startEq, parseScan]
    rfl

theorem build_slice (input : Array UInt64) (start stop : UInt64)
    (ordered : start ≤ stop) (bounded : stop.toNat ≤ input.size) :
    (LeanExe.build (stop - start) fun i => input[(start + i).toNat]!) =
      input.extract start.toNat stop.toNat := by
  have subNat : (stop - start).toNat = stop.toNat - start.toNat :=
    UInt64.toNat_sub_of_le _ _ ordered
  apply Array.ext
  · simp [LeanExe.Dialect.build_size, subNat, Array.size_extract, Nat.min_eq_left bounded]
  · intro i hi hj
    have inside : i < (stop - start).toNat := by
      simpa only [LeanExe.Dialect.build_size] using hi
    have iNat : (UInt64.ofNat i).toNat = i :=
      UInt64.toNat_ofNat_of_lt' (lt_trans inside (UInt64.toNat_lt _))
    have sumNat : (start + UInt64.ofNat i).toNat = start.toNat + i := by
      rw [UInt64.toNat_add, iNat]
      have := UInt64.toNat_lt stop
      rw [subNat] at inside
      omega
    rw [← getElem!_pos
      (LeanExe.build (stop - start) fun j => input[(start + j).toNat]!) i hi,
      LeanExe.Dialect.build_get inside, sumNat,
      getElem!_pos input (start.toNat + i) (by
        rw [subNat] at inside
        omega), Array.getElem_extract]

def parseFirst (input : Array UInt64) : Nat :=
  (parseScan input (lineStart input).toUInt64 (lineEnd input).toUInt64).1.toNat

theorem parse_scan_spec (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    ScanInvariant input (lineStart input) (lineEnd input)
      (parseScan input (lineStart input).toUInt64 (lineEnd input).toUInt64) := by
  have stopNat : (lineEnd input).toUInt64.toNat = lineEnd input :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (lineEnd_le input) sizeBound)
  have startNat : (lineStart input).toUInt64.toNat = lineStart input :=
    UInt64.toNat_ofNat_of_lt'
      (lt_of_le_of_lt (le_trans (lineStart_le input) (lineEnd_le input)) sizeBound)
  simpa only [startNat, stopNat] using
    parseScan_invariant input (lineStart input).toUInt64 (lineEnd input).toUInt64

theorem parseFirst_bounds (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    lineStart input ≤ parseFirst input ∧ parseFirst input ≤ lineEnd input := by
  have scan := parse_scan_spec input sizeBound
  exact ⟨scan.start_le, by
    simpa only [parseFirst, Nat.max_eq_right (lineStart_le input)] using scan.first_le⟩

theorem parse_valid_iff (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    (parse input).valid = true ↔ ValidLine input := by
  have stopNat : (lineEnd input).toUInt64.toNat = lineEnd input :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (lineEnd_le input) sizeBound)
  have startNat : (lineStart input).toUInt64.toNat = lineStart input :=
    UInt64.toNat_ofNat_of_lt'
      (lt_of_le_of_lt (le_trans (lineStart_le input) (lineEnd_le input)) sizeBound)
  have scan := parse_scan_spec input sizeBound
  rw [parse_eq input sizeBound]
  simpa only [Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
    startNat, stopNat, ValidLine] using and_congr Iff.rfl scan.valid_iff

theorem parse_digits_eq (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    (parse input).value.digits = input.extract (parseFirst input) (lineEnd input) := by
  have stopNat : (lineEnd input).toUInt64.toNat = lineEnd input :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (lineEnd_le input) sizeBound)
  have bounds := parseFirst_bounds input sizeBound
  rw [parse_eq input sizeBound]
  simpa only [parseFirst, stopNat] using
    build_slice input
      (parseScan input (lineStart input).toUInt64 (lineEnd input).toUInt64).1
      (lineEnd input).toUInt64
      (by simpa only [UInt64.le_iff_toNat_le, stopNat, parseFirst] using bounds.2)
      (by simpa only [stopNat] using lineEnd_le input)

theorem parse_digits_size_le (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    (parse input).value.digits.size ≤ input.size := by
  rw [parse_digits_eq input sizeBound, Array.size_extract]
  have := lineEnd_le input
  omega

theorem parse_fits (input : Array UInt64) (sizeBound : input.size + 2 < UInt64.size) :
    (parse input).value.Fits := by
  have := parse_digits_size_le input (by omega)
  change (parse input).value.digits.size + 2 < UInt64.size
  omega

theorem parse_valid (input : Array UInt64) (sizeBound : input.size < UInt64.size)
    (accepted : (parse input).valid = true) : (parse input).value.Valid := by
  have valid := (parse_valid_iff input sizeBound).mp accepted
  have scan := parse_scan_spec input sizeBound
  have bounds := parseFirst_bounds input sizeBound
  change NormalDigits (parse input).value.digits
  rw [parse_digits_eq input sizeBound]
  refine ⟨extract_valid input _ _ (lineEnd_le input)
    (fun i hi hj => valid.2 i (by omega) hj), ?_⟩
  by_cases atEnd : parseFirst input = lineEnd input
  · left
    simp [atEnd, Array.size_extract]
  · right
    have inside : parseFirst input < lineEnd input := by omega
    rw [extract_byte input _ _ 0 (lineEnd_le input) (by omega), Nat.add_zero]
    exact fun same => scan.nonzero inside (UInt64.toNat.inj same)

theorem parse_negative (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    (parse input).value.negative =
      (input[0]! == 45 && decide (parseFirst input < lineEnd input)) := by
  have stopNat : (lineEnd input).toUInt64.toNat = lineEnd input :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (lineEnd_le input) sizeBound)
  rw [parse_eq input sizeBound]
  simp only [UInt64.lt_iff_toNat_lt, stopNat, parseFirst]
  rfl

theorem parse_zero_sign (input : Array UInt64) (sizeBound : input.size < UInt64.size)
    (empty : (parse input).value.digits.size = 0) : (parse input).value.negative = false := by
  rw [parse_digits_eq input sizeBound, Array.size_extract,
    Nat.min_eq_left (lineEnd_le input)] at empty
  have bounds := parseFirst_bounds input sizeBound
  have equal : parseFirst input = lineEnd input := by omega
  rw [parse_negative input sizeBound]
  simp [equal]

theorem parse_value (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    (parse input).value.value = lineInteger input := by
  have scan := parse_scan_spec input sizeBound
  have bounds := parseFirst_bounds input sizeBound
  have drop := drop_leading_zeros input (lineStart input) (parseFirst input) (lineEnd input)
    bounds.1 bounds.2 (lineEnd_le input) scan.zero_before
  unfold Decimal.value lineInteger
  rw [parse_negative input sizeBound, parse_digits_eq input sizeBound]
  by_cases inside : parseFirst input < lineEnd input
  · simp only [inside, decide_true, Bool.and_true, drop]
  · have equal : parseFirst input = lineEnd input := by omega
    have zero : magnitude (input.extract (parseFirst input) (lineEnd input)) = 0 := by
      simp [equal, magnitude, digitsValue]
    rw [← drop]
    simp [inside, zero]

theorem parse_correct (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    ((parse input).valid = true ↔ ValidLine input) ∧
      ((parse input).valid = true → (parse input).value.Valid) ∧
      (parse input).value.value = lineInteger input :=
  ⟨parse_valid_iff input sizeBound, parse_valid input sizeBound, parse_value input sizeBound⟩

theorem parse_decimalLine (input : Array UInt64) (sizeBound : input.size < UInt64.size) :
    (parse input).valid = true ↔ DecimalLine input (parse input).value.value := by
  rw [decimalLine_iff, parse_value input sizeBound]
  simp only [and_true]
  exact parse_valid_iff input sizeBound

end Demos.RunningSum
