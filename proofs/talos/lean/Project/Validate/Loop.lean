import Project.Validate.Digit
import Project.Validate.Read
import Project.Validate.Invariant
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call

/-!
# Fuel loop for `validateGeneric`

`func2` runs the fuel loop over the input bytes and computes the final
answer through `func1` reads and `func0` classifications.
-/

namespace Project.Validate.Spec

open Wasm
open Project.Common
open LeanExe.Examples.AsciiDigits

set_option maxHeartbeats 64000000

/-- `func2` runs the fuel loop and computes the final answer. -/
theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
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
            · simp [vMeasure]
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
            · simp [vMeasure]
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

end Project.Validate.Spec
