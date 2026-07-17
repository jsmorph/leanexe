import Project.Validate.Program
import Project.Common
import LeanExe.Examples.AsciiDigits
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `validateGeneric`

The generated export takes a byte-array pointer and length, scans the input
bytes in linear memory, and returns `1` when every byte is an ASCII digit and
`0` otherwise.  The theorem quantifies over the store, the pointer, and the
byte list; the `BytesAt` hypothesis states what the host wrote into memory.
-/

namespace Project.Validate.Spec

open Wasm
open Project.Common
open LeanExe.Examples.AsciiDigits

set_option maxHeartbeats 64000000

private def digitFlag (b : UInt64) : UInt64 :=
  if 48 ≤ b ∧ b ≤ 57 then 1 else 0

private theorem digitFlag_toUInt64 (b : UInt8) :
    digitFlag b.toUInt64 = if isAsciiDigit b then 1 else 0 := by
  unfold digitFlag isAsciiDigit
  by_cases h48 : 48 ≤ b.toNat
  · by_cases h57 : b.toNat ≤ 57
    · simp [h48, h57, UInt64.le_iff_toNat_le]
    · simp [h48, h57, UInt64.le_iff_toNat_le]
  · simp [h48, UInt64.le_iff_toNat_le]

/-- `func0` decides whether a byte value is an ASCII digit. -/
private theorem func0_terminates (env : HostEnv Unit) (st : Store Unit) (b : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env) [.i64 b]
      (fun st' vs => st' = st ∧ vs = [.i64 (digitFlag b)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 b], locals := [.i64 0], values := [] } env
    unfold func0
    wp_run
    refine wp_iff_cons rfl ?_
    by_cases h48 : (48 : UInt64) ≤ b
    · rw [if_pos (by simp [h48])]
      wp_run
      refine wp_iff_cons rfl ?_
      by_cases h57 : b ≤ (57 : UInt64)
      · rw [if_pos (by simp [h57])]
        wp_run
        simp [func0Def, digitFlag, h48, h57]
      · rw [if_neg (by simp [h57])]
        wp_run
        simp [func0Def, digitFlag, h48, h57]
    · rw [if_neg (by simp [h48])]
      wp_run
      simp [func0Def, digitFlag, h48]

/-- `func1` reads one input byte from linear memory. -/
private theorem func1_terminates (env : HostEnv Unit) (st : Store Unit)
    (owner ptr len index : UInt64) (bytes : List UInt8)
    (hLen : len = UInt64.ofNat bytes.length)
    (hSize : bytes.length < UInt64.size)
    (hBytes : BytesAt st ptr bytes)
    (hIndex : index.toNat < bytes.length) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      [.i64 index, .i64 len, .i64 ptr, .i64 owner]
      (fun st' vs => st' = st ∧ vs = [.i64 (bytes[index.toNat]!.toUInt64)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def)
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [.i64 owner, .i64 ptr, .i64 len, .i64 index],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
    unfold func1
    obtain ⟨hRead, hBound⟩ := hBytes index.toNat hIndex
    rw [UInt64.ofNat_toNat] at hRead hBound
    have hLt : index < len := by
      rw [hLen, UInt64.lt_iff_toNat_lt, toNat_ofNat_lt hSize]
      exact hIndex
    have hNoTrap : ¬ ((ptr + index).toUInt32.toNat + 1 > st.mem.pages * 65536) := by
      omega
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hLt])]
    wp_run
    simp_all [func1Def]
    have haddr : UInt32.ofNat ((ptr.toNat + index.toNat) % 4294967296) =
        ptr.toUInt32 + index.toUInt32 := by
      apply UInt32.toNat.inj
      simp
    rw [haddr, hRead]

private def vFrame
    (fuel owner ptr len index l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15
      l16 l17 l18 l19 l20 l21 l22 l23 : UInt64) : Locals :=
  { params := [.i64 fuel, .i64 owner, .i64 ptr, .i64 len, .i64 index],
    locals := [.i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 l9, .i64 l10, .i64 l11,
      .i64 l12, .i64 l13, .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18,
      .i64 l19, .i64 l20, .i64 l21, .i64 l22, .i64 l23],
    values := [] }

/-- Loop invariant: either the scan is still running at position `i` with every
byte below `i` a digit, or the done flag is set and the result local holds the
final answer. -/
private def vInv (st0 : Store Unit) (owner ptr : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    ∃ (fuel index l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19
        l20 l21 l22 l23 : UInt64),
      s = vFrame fuel owner ptr (UInt64.ofNat bytes.length) index l5 l6 l7 l8 l9
        l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 ∧
      ((l6 = 0 ∧ ∃ i : Nat, i ≤ bytes.length ∧ index = UInt64.ofNat i ∧
          fuel = UInt64.ofNat (bytes.length + 1 - i) ∧
          ∀ j : Nat, j < i → isAsciiDigit bytes[j]! = true) ∨
        (l6 = 1 ∧ l5 = validateExpected bytes))

private def vMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params, s.locals with
  | .i64 fuel :: _, _ :: .i64 l6 :: _ =>
      2 * fuel.toNat + (if l6 = 0 then 1 else 0)
  | _, _ => 0

private theorem all_of_prefix {bytes : List UInt8}
    (h : ∀ j : Nat, j < bytes.length → isAsciiDigit bytes[j]! = true) :
    bytes.all isAsciiDigit = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have := h j hj
  rwa [getBang_eq hj] at this

private theorem not_all_of_witness {bytes : List UInt8} {i : Nat}
    (hi : i < bytes.length) (h : isAsciiDigit bytes[i]! = false) :
    bytes.all isAsciiDigit = false := by
  rw [getBang_eq hi] at h
  cases hval : bytes.all isAsciiDigit
  · rfl
  · have := List.all_eq_true.mp hval (bytes[i]'hi) (List.getElem_mem hi)
    rw [h] at this
    exact Bool.noConfusion this

/-- `func2` runs the fuel loop and computes the final answer. -/
private theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
    (owner ptr : UInt64) (bytes : List UInt8)
    (hLen : bytes.length + 1 < UInt64.size)
    (hBytes : BytesAt st ptr bytes) :
    TerminatesWith (m := «module») (id := 2) (initial := st) (env := env)
      [.i64 0, .i64 (UInt64.ofNat bytes.length), .i64 ptr, .i64 owner,
        .i64 (UInt64.ofNat (bytes.length + 1))]
      (fun st' vs => st' = st ∧ vs = [.i64 (validateExpected bytes)]) := by
  have hSize : bytes.length < UInt64.size := by omega
  apply TerminatesWith.of_wp_entry_for (f := func2Def)
  · simp [«module»]
  · change wp «module» func2 _ st
      { params := [.i64 (UInt64.ofNat (bytes.length + 1)), .i64 owner, .i64 ptr,
          .i64 (UInt64.ofNat bytes.length), .i64 0],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func2
    wp_run
    apply wp_block_cons
    apply wp_loop_cons (Inv := vInv st owner ptr bytes) (μ := vMeasure)
    · exact ⟨rfl, UInt64.ofNat (bytes.length + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl,
        Or.inl ⟨rfl, 0, Nat.zero_le _, rfl, rfl,
          fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
    · rintro st2 s ⟨hst, fuel, index, l5, l6, l7, l8, l9, l10, l11, l12, l13,
        l14, l15, l16, l17, l18, l19, l20, l21, l22, l23, rfl, harm⟩
      subst hst
      rcases harm with ⟨rfl, i, hile, rfl, rfl, hpref⟩ | ⟨rfl, hres⟩
      · -- scanning arm: fuel is positive, done flag is zero
        have hfuel_ne : UInt64.ofNat (bytes.length + 1 - i) ≠ 0 := by
          intro h
          have := congrArg UInt64.toNat h
          rw [toNat_ofNat_lt (by omega)] at this
          have h0 : (0 : UInt64).toNat = 0 := rfl
          rw [h0] at this
          omega
        simp only [vFrame]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hfuel_ne])]
        wp_run
        refine wp_iff_cons rfl ?_
        by_cases hi : i = bytes.length
        · -- cursor at the end: set the result to 1 and the done flag
          rw [if_pos (by simp [hi])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hi])]
          wp_run
          refine ⟨⟨rfl, UInt64.ofNat (bytes.length + 1 - i), UInt64.ofNat i, 1, 1,
            l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
            l21, l22, l23, ?_, Or.inr ⟨rfl, ?_⟩⟩, ?_⟩
          · simp [vFrame]
          · unfold validateExpected
            rw [all_of_prefix (hi ▸ hpref)]
            simp
          · simp [vMeasure]
            try omega
        · have hilt : i < bytes.length := Nat.lt_of_le_of_ne hile hi
          have hne : UInt64.ofNat i ≠ UInt64.ofNat bytes.length := by
            intro h
            exact hi (ofNat_inj (by omega) (by omega) h)
          rw [if_neg (by simp [hne])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          have hidx : (UInt64.ofNat i).toNat < bytes.length := by
            rw [toNat_ofNat_lt (by omega)]
            exact hilt
          apply wp_call_tw
            (func1_terminates env st2 owner ptr (UInt64.ofNat bytes.length)
              (UInt64.ofNat i) bytes rfl hSize hBytes hidx)
          rintro st3 vs ⟨rfl, rfl⟩
          wp_run
          apply wp_call_tw
            (func0_terminates env st3 (bytes[(UInt64.ofNat i).toNat]!).toUInt64)
          rintro st3 vs ⟨rfl, rfl⟩
          rw [digitFlag_toUInt64]
          have hgetnat : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
          rw [hgetnat]
          have hadd1 : (UInt64.ofNat i + 1).toNat = i + 1 := by
            rw [toNat_add_one]
            · rw [toNat_ofNat_lt (by omega)]
            · rw [toNat_ofNat_lt (by omega)]
              omega
          have hnext : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
            apply UInt64.toNat.inj
            rw [hadd1, toNat_ofNat_lt (by omega)]
          have hsucc_no_wrap : ¬ (UInt64.ofNat i + 1 < UInt64.ofNat i) := by
            rw [UInt64.lt_iff_toNat_lt, hadd1, toNat_ofNat_lt (by omega)]
            omega
          have hfuel_next :
              UInt64.ofNat (bytes.length + 1 - i) - 1 =
                UInt64.ofNat (bytes.length + 1 - (i + 1)) := by
            have hstep : UInt64.ofNat (bytes.length + 1 - i) =
                UInt64.ofNat (bytes.length + 1 - (i + 1)) + 1 := by
              apply UInt64.toNat.inj
              rw [toNat_ofNat_lt (by omega), toNat_add_one, toNat_ofNat_lt (by omega)]
              · omega
              · rw [toNat_ofNat_lt (by omega)]
                omega
            rw [hstep]
            simp
          by_cases hd : isAsciiDigit bytes[i]! = true
          · -- digit: advance the cursor and burn one unit of fuel
            rw [hd]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp [hsucc_no_wrap])]
            wp_run
            refine ⟨⟨rfl, UInt64.ofNat (bytes.length + 1 - i) - 1,
              UInt64.ofNat i + 1, l5, 0, owner, ptr, UInt64.ofNat bytes.length,
              UInt64.ofNat i, bytes[i]!.toUInt64, bytes[i]!.toUInt64, owner, ptr,
              UInt64.ofNat bytes.length, UInt64.ofNat i + 1, owner, ptr,
              UInt64.ofNat bytes.length, UInt64.ofNat i + 1, UInt64.ofNat i, 1,
              UInt64.ofNat i + 1, ?_, Or.inl ⟨rfl, i + 1, hilt, hnext, ?_, ?_⟩⟩, ?_⟩
            · simp [vFrame]
            · rw [hfuel_next]
            · intro j hj
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
              · exact hpref j hj'
              · exact hd
            · simp [vMeasure, vFrame]
              have hLen' : bytes.length + 1 < 18446744073709551616 := by
                rw [size_eq] at hLen
                exact hLen
              rw [hfuel_next, toNat_ofNat_lt (by omega)]
              omega
          · -- non-digit byte: set the result to 0 and the done flag
            have hd0 : isAsciiDigit bytes[i]! = false := by
              cases hval : isAsciiDigit bytes[i]!
              · rfl
              · exact absurd hval hd
            rw [hd0]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp [hne])]
            wp_run
            refine ⟨⟨rfl, UInt64.ofNat (bytes.length + 1 - i), UInt64.ofNat i,
              0, 1, owner, ptr, UInt64.ofNat bytes.length, UInt64.ofNat i,
              bytes[i]!.toUInt64, bytes[i]!.toUInt64, l13, l14, l15, l16, l17,
              l18, l19, l20, l21, l22, l23, ?_, Or.inr ⟨rfl, ?_⟩⟩, ?_⟩
            · simp [vFrame]
            · unfold validateExpected
              rw [not_all_of_witness hilt hd0]
              simp
            · simp [vMeasure, vFrame]
              try omega
      · -- done arm: the loop exits and the answer is already in the result local
        simp only [vFrame]
        wp_run
        refine wp_iff_cons rfl ?_
        by_cases hfz : fuel = 0
        · rw [if_neg (by simp [hfz])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp [func2Def, hres]
        · rw [if_pos (by simp [hfz])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp [func2Def, hres]

/-- The generated export `validateGeneric` returns `1` exactly when every input
byte is an ASCII digit. -/
def wasmRunsTo (bytes : List UInt8) (output : UInt64) : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64),
    bytes.length + 1 < UInt64.size →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun _ vs => vs = [.i64 output])

@[spec_of "lean" "LeanExe.Examples.AsciiDigits.validateGeneric"]
def ValidateGenericSpec : Prop :=
  ValidateSpec wasmRunsTo

@[proves Project.Validate.Spec.ValidateGenericSpec]
theorem validateGeneric_correct : ValidateGenericSpec := by
  unfold ValidateGenericSpec ValidateSpec wasmRunsTo
  intro bytes env st ptr hLen hBytes
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func3
    have hadd1 : (UInt64.ofNat bytes.length + 1).toNat = bytes.length + 1 := by
      rw [toNat_add_one]
      · rw [toNat_ofNat_lt (by omega)]
      · rw [toNat_ofNat_lt (by omega)]
        omega
    have hsucc_no_wrap :
        ¬ (UInt64.ofNat bytes.length + 1 < UInt64.ofNat bytes.length) := by
      rw [UInt64.lt_iff_toNat_lt, hadd1, toNat_ofNat_lt (by omega)]
      omega
    have hplus : UInt64.ofNat bytes.length + 1 = UInt64.ofNat (bytes.length + 1) := by
      apply UInt64.toNat.inj
      rw [hadd1, toNat_ofNat_lt (by omega)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hsucc_no_wrap])]
    wp_run
    rw [hplus]
    apply wp_call_tw (func2_terminates env st 0 ptr bytes hLen hBytes)
    rintro st2 vs ⟨rfl, rfl⟩
    wp_run
    simp [func3Def]

end Project.Validate.Spec
