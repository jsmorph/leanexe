import Library.Hashing.Sha3.Program
import Library.Hashing.Sha3.Spec
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! The lane program's permutation computes KECCAK-p[1600, 24] of the transcription.  `toState`
reads the lanes as a state array: `A[x, y, z]` is bit `z` of lane `x + 5y`.  Each step function
of the program gives the step mapping of its algorithm on that view, `round_spec` gives `Rnd`,
and `keccakF_spec` gives the 24 rounds of Algorithm 7. -/

namespace Library.Hashing.Sha3.RoundProof

open Library.Hashing.Sha3 Library.Hashing.Sha3.Spec

/-- Bit `z` of a word, least significant first. -/
def bit (w : UInt64) (z : Nat) : Bool := w.toNat.testBit z

theorem bit_xor (a b : UInt64) (z : Nat) : bit (a ^^^ b) z = (bit a z ^^ bit b z) := by
  simp [bit, UInt64.toNat_xor, Nat.testBit_xor]

theorem bit_zero (z : Nat) : bit 0 z = false := by
  simp [bit]

theorem bit_or (a b : UInt64) (z : Nat) : bit (a ||| b) z = (bit a z || bit b z) := by
  simp [bit, UInt64.toNat_or, Nat.testBit_or]

theorem bit_and (a b : UInt64) (z : Nat) : bit (a &&& b) z = (bit a z && bit b z) := by
  simp [bit, UInt64.toNat_and, Nat.testBit_and]

theorem bit_complement (a : UInt64) {z : Nat} (hz : z < 64) : bit (complement a) z = !bit a z := by
  have h : bit 0xFFFFFFFFFFFFFFFF z = true := by
    simp only [bit, show (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.testBit_two_pow_sub_one, hz, decide_true]
  rw [complement, bit_xor, h, Bool.xor_true]

/-- A rotation by `k` moves bit `(z - k) mod 64` to bit `z`. -/
theorem bit_rotl (a k : UInt64) (hk0 : 0 < k.toNat) (hk : k.toNat < 64) {z : Nat}
    (hz : z < 64) : bit (rotl a k) z = bit a (modW 6 (z - k.toNat : Int)).val := by
  have h64 : (64 - k).toNat = 64 - k.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; rfl
  have hidx : (modW 6 (z - k.toNat : Int)).val = (z + 64 - k.toNat) % 64 := by
    simp only [modW, modFin, laneSize]
    omega
  rw [hidx]
  simp only [bit, rotl, UInt64.toNat_or, Nat.testBit_or, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, h64, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (by omega : 64 - k.toNat < 64),
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hzk : k.toNat ≤ z
  · have h1 : (z + 64 - k.toNat) % 64 = z - k.toNat := by omega
    have h2 : a.toNat.testBit (64 - k.toNat + z) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt a)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h2, hz, hzk]
  · have h1 : (z + 64 - k.toNat) % 64 = 64 - k.toNat + z := by omega
    have h3 : ¬ k.toNat ≤ z := hzk
    simp [h1, hz, h3]

/-- The 25 lanes in the order of their fields. -/
def laneList (s : Lanes) : List UInt64 :=
  [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14,
    s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

/-- Lane `(x, y)` of the state, the field `a(x + 5y)`. -/
def laneWord (s : Lanes) (x y : Fin 5) : UInt64 := (laneList s).getD (x.val + 5 * y.val) 0

/-- The state array of the lanes: `A[x, y, z]` is bit `z` of lane `x + 5y`. -/
def toState (s : Lanes) : StateArray 6 := fun x y z => bit (laneWord s x y) z.val

set_option maxHeartbeats 1000000 in
theorem thetaL_spec (s : Lanes) : toState (thetaL s) = theta (toState s) := by
  funext x y z
  have hz : z.val < 64 := z.isLt
  fin_cases x <;> fin_cases y <;>
    simp [toState, laneWord, laneList, thetaL, theta, bit_xor, bit_rotl, hz, mod5, modFin]

/-- The offsets of Table 2 modulo 64, by `x` and then `y`. -/
def rhoOffset (x y : Fin 5) : Nat :=
  ([[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14]].getD x.val []).getD y.val 0

theorem modW6_coe (z : Fin (laneSize 6)) : modW 6 (z.val : Int) = z := by
  apply Fin.ext
  have := z.isLt
  simp only [modW, modFin, laneSize] at *
  omega

set_option maxHeartbeats 1000000 in
/-- ρ on the lanes of width 64 rotates lane `(x, y)` by its offset of Table 2 modulo 64. -/
theorem rho_lane (A : StateArray 6) (x y : Fin 5) (z : Fin (laneSize 6)) :
    rho A x y z = A x y (modW 6 (z.val - rhoOffset x y : Int)) := by
  have hz := z.isLt
  fin_cases x <;> fin_cases y <;>
    simp (config := { decide := true }) only [rho, rhoSteps_table2, rhoOffset, List.foldl_cons,
      List.foldl_nil, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ] <;>
    congr 1 <;> apply Fin.ext <;> simp only [modW, modFin, laneSize] at hz ⊢ <;> omega

set_option maxHeartbeats 1000000 in
theorem rhoPiL_spec (s : Lanes) : toState (rhoPiL s) = pi (rho (toState s)) := by
  funext x y z
  have hz : z.val < 64 := z.isLt
  fin_cases x <;> fin_cases y <;>
    simp [toState, laneWord, laneList, rhoPiL, pi, rho_lane, rhoOffset, bit_rotl, hz, mod5,
      modFin, modW6_coe]

set_option maxHeartbeats 1000000 in
theorem chiL_spec (s : Lanes) : toState (chiL s) = chi (toState s) := by
  funext x y z
  have hz : z.val < 64 := z.isLt
  fin_cases x <;> fin_cases y <;>
    simp [toState, laneWord, laneList, chiL, chi, bit_xor, bit_and, bit_complement, hz, mod5,
      modFin]

set_option maxHeartbeats 1000000 in
theorem iotaL_spec (s : Lanes) (rc : UInt64) (ir : Int)
    (h : ∀ z : Fin (laneSize 6), bit rc z.val = (roundConstant 6 ir).getD z.val false) :
    toState (iotaL s rc) = iota (toState s) ir := by
  funext x y z
  fin_cases x <;> fin_cases y <;>
    simp [toState, laneWord, laneList, iotaL, iota, addRoundConstant, bit_xor, h]

theorem round_spec (s : Lanes) (rc : UInt64) (ir : Int)
    (h : ∀ z : Fin (laneSize 6), bit rc z.val = (roundConstant 6 ir).getD z.val false) :
    toState (round s rc) = rnd (toState s) ir := by
  rw [round, rnd, iotaL_spec _ _ _ h, chiL_spec, rhoPiL_spec, thetaL_spec]

theorem getD_map_bit (c : UInt64) (z : Fin (laneSize 6)) :
    ((List.range 64).map (bit c)).getD z.val false = bit c z.val := by
  have : z.val < 64 := z.isLt
  simp [List.getD_eq_getElem?_getD, this]

theorem round_0 (s : Lanes) :
    toState (round s 0x0000000000000001) = rnd (toState s) ((0 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((0 : Nat) : Int) = (List.range 64).map (bit 0x0000000000000001) by
      decide +kernel, getD_map_bit]

theorem round_1 (s : Lanes) :
    toState (round s 0x0000000000008082) = rnd (toState s) ((1 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((1 : Nat) : Int) = (List.range 64).map (bit 0x0000000000008082) by
      decide +kernel, getD_map_bit]

theorem round_2 (s : Lanes) :
    toState (round s 0x800000000000808A) = rnd (toState s) ((2 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((2 : Nat) : Int) = (List.range 64).map (bit 0x800000000000808A) by
      decide +kernel, getD_map_bit]

theorem round_3 (s : Lanes) :
    toState (round s 0x8000000080008000) = rnd (toState s) ((3 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((3 : Nat) : Int) = (List.range 64).map (bit 0x8000000080008000) by
      decide +kernel, getD_map_bit]

theorem round_4 (s : Lanes) :
    toState (round s 0x000000000000808B) = rnd (toState s) ((4 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((4 : Nat) : Int) = (List.range 64).map (bit 0x000000000000808B) by
      decide +kernel, getD_map_bit]

theorem round_5 (s : Lanes) :
    toState (round s 0x0000000080000001) = rnd (toState s) ((5 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((5 : Nat) : Int) = (List.range 64).map (bit 0x0000000080000001) by
      decide +kernel, getD_map_bit]

theorem round_6 (s : Lanes) :
    toState (round s 0x8000000080008081) = rnd (toState s) ((6 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((6 : Nat) : Int) = (List.range 64).map (bit 0x8000000080008081) by
      decide +kernel, getD_map_bit]

theorem round_7 (s : Lanes) :
    toState (round s 0x8000000000008009) = rnd (toState s) ((7 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((7 : Nat) : Int) = (List.range 64).map (bit 0x8000000000008009) by
      decide +kernel, getD_map_bit]

theorem round_8 (s : Lanes) :
    toState (round s 0x000000000000008A) = rnd (toState s) ((8 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((8 : Nat) : Int) = (List.range 64).map (bit 0x000000000000008A) by
      decide +kernel, getD_map_bit]

theorem round_9 (s : Lanes) :
    toState (round s 0x0000000000000088) = rnd (toState s) ((9 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((9 : Nat) : Int) = (List.range 64).map (bit 0x0000000000000088) by
      decide +kernel, getD_map_bit]

theorem round_10 (s : Lanes) :
    toState (round s 0x0000000080008009) = rnd (toState s) ((10 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((10 : Nat) : Int) = (List.range 64).map (bit 0x0000000080008009) by
      decide +kernel, getD_map_bit]

theorem round_11 (s : Lanes) :
    toState (round s 0x000000008000000A) = rnd (toState s) ((11 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((11 : Nat) : Int) = (List.range 64).map (bit 0x000000008000000A) by
      decide +kernel, getD_map_bit]

theorem round_12 (s : Lanes) :
    toState (round s 0x000000008000808B) = rnd (toState s) ((12 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((12 : Nat) : Int) = (List.range 64).map (bit 0x000000008000808B) by
      decide +kernel, getD_map_bit]

theorem round_13 (s : Lanes) :
    toState (round s 0x800000000000008B) = rnd (toState s) ((13 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((13 : Nat) : Int) = (List.range 64).map (bit 0x800000000000008B) by
      decide +kernel, getD_map_bit]

theorem round_14 (s : Lanes) :
    toState (round s 0x8000000000008089) = rnd (toState s) ((14 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((14 : Nat) : Int) = (List.range 64).map (bit 0x8000000000008089) by
      decide +kernel, getD_map_bit]

theorem round_15 (s : Lanes) :
    toState (round s 0x8000000000008003) = rnd (toState s) ((15 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((15 : Nat) : Int) = (List.range 64).map (bit 0x8000000000008003) by
      decide +kernel, getD_map_bit]

theorem round_16 (s : Lanes) :
    toState (round s 0x8000000000008002) = rnd (toState s) ((16 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((16 : Nat) : Int) = (List.range 64).map (bit 0x8000000000008002) by
      decide +kernel, getD_map_bit]

theorem round_17 (s : Lanes) :
    toState (round s 0x8000000000000080) = rnd (toState s) ((17 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((17 : Nat) : Int) = (List.range 64).map (bit 0x8000000000000080) by
      decide +kernel, getD_map_bit]

theorem round_18 (s : Lanes) :
    toState (round s 0x000000000000800A) = rnd (toState s) ((18 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((18 : Nat) : Int) = (List.range 64).map (bit 0x000000000000800A) by
      decide +kernel, getD_map_bit]

theorem round_19 (s : Lanes) :
    toState (round s 0x800000008000000A) = rnd (toState s) ((19 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((19 : Nat) : Int) = (List.range 64).map (bit 0x800000008000000A) by
      decide +kernel, getD_map_bit]

theorem round_20 (s : Lanes) :
    toState (round s 0x8000000080008081) = rnd (toState s) ((20 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((20 : Nat) : Int) = (List.range 64).map (bit 0x8000000080008081) by
      decide +kernel, getD_map_bit]

theorem round_21 (s : Lanes) :
    toState (round s 0x8000000000008080) = rnd (toState s) ((21 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((21 : Nat) : Int) = (List.range 64).map (bit 0x8000000000008080) by
      decide +kernel, getD_map_bit]

theorem round_22 (s : Lanes) :
    toState (round s 0x0000000080000001) = rnd (toState s) ((22 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((22 : Nat) : Int) = (List.range 64).map (bit 0x0000000080000001) by
      decide +kernel, getD_map_bit]

theorem round_23 (s : Lanes) :
    toState (round s 0x8000000080008008) = rnd (toState s) ((23 : Nat) : Int) :=
  round_spec s _ _ fun z => by
    rw [show roundConstant 6 ((23 : Nat) : Int) = (List.range 64).map (bit 0x8000000080008008) by
      decide +kernel, getD_map_bit]

/-- The 24 rounds of the program are the 24 rounds of Algorithm 7.  Rounds 5 and 22 share a
constant, as do rounds 6 and 20, so the rewrites run from the last round inward. -/
theorem keccakF_spec (s : Lanes) :
    toState (keccakF s) = (List.range 24).foldl (fun A (k : Nat) => rnd A k) (toState s) := by
  simp only [keccakF, show List.range 24 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23] from rfl, List.foldl_cons, List.foldl_nil]
  rw [round_23, round_22, round_21, round_20, round_19, round_18, round_17, round_16,
    round_15, round_14, round_13, round_12, round_11, round_10, round_9, round_8,
    round_7, round_6, round_5, round_4, round_3, round_2, round_1, round_0]

end Library.Hashing.Sha3.RoundProof
