import Init.Data.Nat.Lemmas
import Init.Omega
import Mathlib.Tactic.Ring
import Project.Artifact.Binary.Grammar
import Project.Artifact.Binary.Leb
import Project.Artifact.Binary.Proof.Cursor

namespace Wasm.Binary.Leb.Proof

open Parser

inductive UnsignedTrace (width : Nat) : Nat → Nat → Nat → List UInt8 → Nat → Prop
  | terminal (fuel : Nat) (byte : UInt8)
      (terminal : byte.toNat < 128)
      (shiftFits : shift < width)
      (fits : byte.toNat % 128 < 2 ^ (width - shift)) :
      UnsignedTrace width shift (fuel + 1) value [byte]
        (value + (byte.toNat % 128) * 2 ^ shift)
  | next (fuel : Nat) (byte : UInt8) (tail : List UInt8) (result : Nat)
      (continuation : 128 ≤ byte.toNat)
      (fuelPositive : 0 < fuel)
      (tailTrace : UnsignedTrace width (shift + 7) fuel
        (value + (byte.toNat % 128) * 2 ^ shift) tail result) :
      UnsignedTrace width shift (fuel + 1) value (byte :: tail) result

def UnsignedTerminalFitsFrom (width shift : Nat) (bytes : List UInt8) : Prop :=
  match bytes.getLast? with
  | none => False
  | some last =>
      let terminalShift := shift + 7 * (bytes.length - 1)
      terminalShift < width ∧
        last.toNat % 128 < 2 ^ (width - terminalShift)

theorem UnsignedTrace.nonempty
    (trace : UnsignedTrace width shift fuel value bytes result) :
    bytes ≠ [] := by
  cases trace <;> simp

theorem UnsignedTrace.length_le
    (trace : UnsignedTrace width shift fuel value bytes result) :
    bytes.length ≤ fuel := by
  induction trace with
  | terminal => simp
  | next _ _ _ _ _ _ _ ih =>
      simp
      omega

theorem UnsignedTrace.continuationForm
    (trace : UnsignedTrace width shift fuel value bytes result) :
    Grammar.continuationForm bytes := by
  induction trace with
  | terminal _ byte terminal =>
      simpa [Grammar.continuationForm] using terminal
  | next fuel byte tail result continuation fuelPositive tailTrace ih =>
      cases tail with
      | nil => exact (tailTrace.nonempty rfl).elim
      | cons head rest =>
          simpa [Grammar.continuationForm] using And.intro continuation ih

theorem UnsignedTrace.value_eq
    (trace : UnsignedTrace width shift fuel value bytes result) :
    result = value + 2 ^ shift * Grammar.unsignedValue bytes := by
  induction trace with
  | terminal =>
      simp [Grammar.unsignedValue]
      ring
  | next fuel byte tail result continuation fuelPositive tailTrace ih =>
      rw [ih]
      simp [Grammar.unsignedValue, pow_add]
      ring

theorem UnsignedTrace.terminalFitsFrom
    (trace : UnsignedTrace width shift fuel value bytes result) :
    UnsignedTerminalFitsFrom width shift bytes := by
  induction trace with
  | terminal fuel byte terminal shiftFits fits =>
      exact ⟨shiftFits, fits⟩
  | @next shift value fuel byte tail result continuation fuelPositive tailTrace ih =>
      cases tail with
      | nil => exact (tailTrace.nonempty rfl).elim
      | cons head rest =>
          simp [UnsignedTerminalFitsFrom] at ih ⊢
          have terminalShift : shift + 7 * (rest.length + 1) =
              shift + 7 + 7 * rest.length := by omega
          simpa [terminalShift] using ih

theorem UnsignedTrace.result_lt
    (trace : UnsignedTrace width shift fuel value bytes result)
    (valueFits : value < 2 ^ shift) :
    result < 2 ^ width := by
  induction trace with
  | @terminal shift value fuel byte terminal shiftFits fits =>
      calc
        value + (byte.toNat % 128) * 2 ^ shift <
            2 ^ shift + (byte.toNat % 128) * 2 ^ shift :=
          Nat.add_lt_add_right valueFits _
        _ = (byte.toNat % 128 + 1) * 2 ^ shift := by ring
        _ ≤ 2 ^ (width - shift) * 2 ^ shift :=
          Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr fits)
        _ = 2 ^ width := by
          rw [← pow_add]
          congr
          omega
  | @next shift value fuel byte tail result continuation fuelPositive tailTrace ih =>
      apply ih
      have payload : byte.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
      calc
        value + (byte.toNat % 128) * 2 ^ shift <
            2 ^ shift + (byte.toNat % 128) * 2 ^ shift :=
          Nat.add_lt_add_right valueFits _
        _ = (byte.toNat % 128 + 1) * 2 ^ shift := by ring
        _ ≤ 128 * 2 ^ shift :=
          Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr payload)
        _ = 2 ^ (shift + 7) := by
          rw [pow_add]
          ring

theorem terminalFitsFrom_zero
    (h : UnsignedTerminalFitsFrom width 0 bytes) :
    Grammar.unsignedTerminalFits width bytes := by
  unfold UnsignedTerminalFitsFrom at h
  unfold Grammar.unsignedTerminalFits
  cases hlast : bytes.getLast? <;> simp [hlast] at h ⊢
  exact h

theorem unsignedLoop_sound
    (width shift fuel value : Nat)
    (room : shift + 7 * (fuel - 1) < width) :
    Sound (Internal.unsignedLoop width shift fuel value)
      (UnsignedTrace width shift fuel value) := by
  induction fuel generalizing shift value with
  | zero =>
      intro start result finish hstart hrun
      unfold Internal.unsignedLoop at hrun
      contradiction
  | succ fuel ih =>
      intro start result finish hstart hrun
      unfold Internal.unsignedLoop at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hread
        rcases pair with ⟨byte, middle⟩
        dsimp only at hrun
        rcases readByte_sound start byte middle hstart hread with
          ⟨firstBytes, hfirstConsumed, hfirstBytes⟩
        split at hrun
        · contradiction
        · rename_i noOverflow
          split at hrun
          · rename_i terminal
            cases hrun
            have fits : byte.toNat % 128 < 2 ^ (width - shift) := by
              by_cases fuelZero : fuel = 0
              · simp [fuelZero] at noOverflow
                exact noOverflow
              · have fuelPositive : 0 < fuel := Nat.pos_of_ne_zero fuelZero
                have exponent : 7 ≤ width - shift := by
                  omega
                have power : 128 ≤ 2 ^ (width - shift) :=
                  Nat.pow_le_pow_right Nat.zero_lt_two exponent
                have payload : byte.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
                exact Nat.lt_of_lt_of_le payload power
            rw [hfirstBytes] at hfirstConsumed
            exact ⟨[byte], hfirstConsumed,
              UnsignedTrace.terminal fuel byte terminal (by omega) fits⟩
          · rename_i notTerminal
            split at hrun
            · contradiction
            · rename_i fuelNonzero
              have fuelPositive : 0 < fuel := Nat.pos_of_ne_zero fuelNonzero
              have nextRoom : shift + 7 + 7 * (fuel - 1) < width := by
                omega
              rcases ih (shift + 7)
                  (value + (byte.toNat % 128) * 2 ^ shift) nextRoom
                  middle result finish
                  (hfirstConsumed.finish_wellFormed hstart) hrun with
                ⟨tailBytes, htailConsumed, htailTrace⟩
              have continuation : 128 ≤ byte.toNat := by omega
              rw [hfirstBytes] at hfirstConsumed
              exact ⟨byte :: tailBytes, hfirstConsumed.trans htailConsumed,
                UnsignedTrace.next fuel byte tailBytes result continuation
                  fuelPositive htailTrace⟩

def Unsigned32 (bytes : List UInt8) (value : Nat) : Prop :=
  Grammar.U32 bytes value ∧ value < 2 ^ 32

def Unsigned64 (bytes : List UInt8) (value : Nat) : Prop :=
  Grammar.U64 bytes value ∧ value < 2 ^ 64

theorem unsignedLoop32_sound :
    Sound (Internal.unsignedLoop 32 0 5 0) Unsigned32 := by
  intro start value finish hstart hrun
  rcases unsignedLoop_sound 32 0 5 0 (by decide)
      start value finish hstart hrun with
    ⟨bytes, hconsumed, htrace⟩
  refine ⟨bytes, hconsumed, ?_⟩
  constructor
  · refine ⟨htrace.length_le, htrace.continuationForm, ?_, ?_⟩
    · exact terminalFitsFrom_zero htrace.terminalFitsFrom
    · simpa using htrace.value_eq.symm
  · exact htrace.result_lt (by decide)

theorem unsignedLoop64_sound :
    Sound (Internal.unsignedLoop 64 0 10 0) Unsigned64 := by
  intro start value finish hstart hrun
  rcases unsignedLoop_sound 64 0 10 0 (by decide)
      start value finish hstart hrun with
    ⟨bytes, hconsumed, htrace⟩
  refine ⟨bytes, hconsumed, ?_⟩
  constructor
  · refine ⟨htrace.length_le, htrace.continuationForm, ?_, ?_⟩
    · exact terminalFitsFrom_zero htrace.terminalFitsFrom
    · simpa using htrace.value_eq.symm
  · exact htrace.result_lt (by decide)

theorem u32_sound :
    Sound u32 (fun bytes value => Grammar.U32 bytes value.toNat) := by
  intro start value finish hstart hrun
  unfold u32 at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hloop
    rcases pair with ⟨natural, middle⟩
    cases hrun
    rcases unsignedLoop32_sound start natural middle hstart hloop with
      ⟨bytes, hconsumed, hgrammar, hfits⟩
    refine ⟨bytes, hconsumed, ?_⟩
    change Grammar.U32 bytes (UInt32.ofNat natural).toNat
    rw [UInt32.toNat_ofNat_of_lt' hfits]
    exact hgrammar

theorem u64_sound :
    Sound u64 (fun bytes value => Grammar.U64 bytes value.toNat) := by
  intro start value finish hstart hrun
  unfold u64 at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hloop
    rcases pair with ⟨natural, middle⟩
    cases hrun
    rcases unsignedLoop64_sound start natural middle hstart hloop with
      ⟨bytes, hconsumed, hgrammar, hfits⟩
    refine ⟨bytes, hconsumed, ?_⟩
    change Grammar.U64 bytes (UInt64.ofNat natural).toNat
    rw [UInt64.toNat_ofNat_of_lt' hfits]
    exact hgrammar

inductive SignedTrace (width : Nat) : Nat → Nat → Nat → List UInt8 → Int → Prop
  | terminal (fuel : Nat) (byte : UInt8)
      (terminal : byte.toNat < 128)
      (shiftFits : shift < width)
      (fits : Internal.signedTerminalFits width shift (byte.toNat % 128) = true) :
      SignedTrace width shift (fuel + 1) value [byte]
        (Internal.signedValue shift (byte.toNat % 128) value)
  | next (fuel : Nat) (byte : UInt8) (tail : List UInt8) (result : Int)
      (continuation : 128 ≤ byte.toNat)
      (fuelPositive : 0 < fuel)
      (tailTrace : SignedTrace width (shift + 7) fuel
        (value + (byte.toNat % 128) * 2 ^ shift) tail result) :
      SignedTrace width shift (fuel + 1) value (byte :: tail) result

def SignedTerminalFitsFrom (width shift : Nat) (bytes : List UInt8) : Prop :=
  match bytes.getLast? with
  | none => False
  | some last =>
      let terminalShift := shift + 7 * (bytes.length - 1)
      let used := width - terminalShift
      terminalShift < width ∧
        (terminalShift + 7 ≤ width ∨
          last.toNat % 128 < 2 ^ (used - 1) ∨
          128 - 2 ^ (used - 1) ≤ last.toNat % 128)

def SignedValueFrom (shift value : Nat) (bytes : List UInt8) : Int :=
  let natural := value + 2 ^ shift * Grammar.unsignedValue bytes
  match bytes.getLast? with
  | some last =>
      if last.toNat % 128 < 64 then
        Int.ofNat natural
      else
        Int.ofNat natural - Int.ofNat (2 ^ (shift + 7 * bytes.length))
  | none => Int.ofNat value

theorem SignedTrace.nonempty
    (trace : SignedTrace width shift fuel value bytes result) :
    bytes ≠ [] := by
  cases trace <;> simp

theorem SignedTrace.length_le
    (trace : SignedTrace width shift fuel value bytes result) :
    bytes.length ≤ fuel := by
  induction trace with
  | terminal => simp
  | next _ _ _ _ _ _ _ ih =>
      simp
      omega

theorem SignedTrace.continuationForm
    (trace : SignedTrace width shift fuel value bytes result) :
    Grammar.continuationForm bytes := by
  induction trace with
  | terminal _ byte terminal =>
      simpa [Grammar.continuationForm] using terminal
  | next fuel byte tail result continuation fuelPositive tailTrace ih =>
      cases tail with
      | nil => exact (tailTrace.nonempty rfl).elim
      | cons head rest =>
          simpa [Grammar.continuationForm] using And.intro continuation ih

theorem SignedTrace.terminalFitsFrom
    (trace : SignedTrace width shift fuel value bytes result) :
    SignedTerminalFitsFrom width shift bytes := by
  induction trace with
  | @terminal shift value fuel byte terminal shiftFits fits =>
      refine ⟨shiftFits, ?_⟩
      unfold Internal.signedTerminalFits at fits
      split at fits
      · rename_i fullWidth
        exact Or.inl fullWidth
      · rename_i partialWidth
        simp only [Bool.or_eq_true, decide_eq_true_eq] at fits
        change shift + 7 ≤ width ∨
          byte.toNat % 128 < 2 ^ (width - shift - 1) ∨
          128 - 2 ^ (width - shift - 1) ≤ byte.toNat % 128
        exact Or.inr fits
  | @next shift value fuel byte tail result continuation fuelPositive tailTrace ih =>
      cases tail with
      | nil => exact (tailTrace.nonempty rfl).elim
      | cons head rest =>
          simp [SignedTerminalFitsFrom] at ih ⊢
          have terminalShift : shift + 7 * (rest.length + 1) =
              shift + 7 + 7 * rest.length := by omega
          simpa [terminalShift] using ih

theorem SignedTrace.valueFrom
    (trace : SignedTrace width shift fuel value bytes result) :
    result = SignedValueFrom shift value bytes := by
  induction trace with
  | @terminal shift value fuel byte terminal shiftFits fits =>
      simp [SignedValueFrom, Internal.signedValue, Grammar.unsignedValue]
      ring_nf
  | @next shift value fuel byte tail result continuation fuelPositive tailTrace ih =>
      cases tail with
      | nil => exact (tailTrace.nonempty rfl).elim
      | cons head rest =>
          have natural :
              value + 2 ^ shift * Grammar.unsignedValue (byte :: head :: rest) =
                value + (byte.toNat % 128) * 2 ^ shift +
                  2 ^ (shift + 7) * Grammar.unsignedValue (head :: rest) := by
            simp [Grammar.unsignedValue, pow_add]
            ring
          have exponent : shift + 7 * (byte :: head :: rest).length =
              shift + 7 + 7 * (head :: rest).length := by
            simp
            omega
          unfold SignedValueFrom at ih ⊢
          simp only [List.getLast?_cons_cons]
          rw [natural, exponent]
          exact ih

theorem signedValueFrom_zero (bytes : List UInt8) :
    SignedValueFrom 0 0 bytes = Grammar.signedValue bytes := by
  unfold SignedValueFrom Grammar.signedValue
  simp
  rfl

theorem signedTerminalFitsFrom_zero
    (h : SignedTerminalFitsFrom width 0 bytes) :
    Grammar.signedTerminalFits width bytes := by
  unfold SignedTerminalFitsFrom at h
  unfold Grammar.signedTerminalFits
  cases hlast : bytes.getLast? <;> simp [hlast] at h ⊢
  exact h

theorem signedLoop_sound
    (width shift fuel value : Nat)
    (room : shift + 7 * (fuel - 1) < width) :
    Sound (Internal.signedLoop width shift fuel value)
      (SignedTrace width shift fuel value) := by
  induction fuel generalizing shift value with
  | zero =>
      intro start result finish hstart hrun
      unfold Internal.signedLoop at hrun
      contradiction
  | succ fuel ih =>
      intro start result finish hstart hrun
      unfold Internal.signedLoop at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsed pair hread
        rcases pair with ⟨byte, middle⟩
        dsimp only at hrun
        rcases readByte_sound start byte middle hstart hread with
          ⟨firstBytes, hfirstConsumed, hfirstBytes⟩
        split at hrun
        · contradiction
        · rename_i noOverflow
          split at hrun
          · rename_i terminal
            cases hrun
            have fits :
                Internal.signedTerminalFits width shift (byte.toNat % 128) = true := by
              by_cases fuelZero : fuel = 0
              · simp [fuelZero] at noOverflow
                exact noOverflow
              · have fuelPositive : 0 < fuel := Nat.pos_of_ne_zero fuelZero
                have fullWidth : shift + 7 ≤ width := by omega
                simp [Internal.signedTerminalFits, fullWidth]
            rw [hfirstBytes] at hfirstConsumed
            exact ⟨[byte], hfirstConsumed,
              SignedTrace.terminal fuel byte terminal (by omega) fits⟩
          · rename_i notTerminal
            split at hrun
            · contradiction
            · rename_i fuelNonzero
              have fuelPositive : 0 < fuel := Nat.pos_of_ne_zero fuelNonzero
              have nextRoom : shift + 7 + 7 * (fuel - 1) < width := by omega
              rcases ih (shift + 7)
                  (value + (byte.toNat % 128) * 2 ^ shift) nextRoom
                  middle result finish
                  (hfirstConsumed.finish_wellFormed hstart) hrun with
                ⟨tailBytes, htailConsumed, htailTrace⟩
              have continuation : 128 ≤ byte.toNat := by omega
              rw [hfirstBytes] at hfirstConsumed
              exact ⟨byte :: tailBytes, hfirstConsumed.trans htailConsumed,
                SignedTrace.next fuel byte tailBytes result continuation
                  fuelPositive htailTrace⟩

theorem s32_sound :
    Sound s32 Grammar.S32 := by
  intro start value finish hstart hrun
  rcases signedLoop_sound 32 0 5 0 (by decide)
      start value finish hstart hrun with
    ⟨bytes, hconsumed, htrace⟩
  refine ⟨bytes, hconsumed, htrace.length_le, htrace.continuationForm, ?_, ?_⟩
  · exact signedTerminalFitsFrom_zero htrace.terminalFitsFrom
  · rw [← signedValueFrom_zero bytes]
    exact htrace.valueFrom.symm

theorem s64_sound :
    Sound s64 Grammar.S64 := by
  intro start value finish hstart hrun
  rcases signedLoop_sound 64 0 10 0 (by decide)
      start value finish hstart hrun with
    ⟨bytes, hconsumed, htrace⟩
  refine ⟨bytes, hconsumed, htrace.length_le, htrace.continuationForm, ?_, ?_⟩
  · exact signedTerminalFitsFrom_zero htrace.terminalFitsFrom
  · rw [← signedValueFrom_zero bytes]
    exact htrace.valueFrom.symm

end Wasm.Binary.Leb.Proof
