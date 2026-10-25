import Library.Regex.Program
import Library.Regex.Bits
import LeanExe.IR.Combinators
import Library.Regex.Automaton
import Library.Bytes.Packed

/-! The sets that the matcher's tables hold.  `bit_loop` gives the bits of a loop whose step adds
bits to its state, `steps_bit` the union of follow sets that each entry of `steps` holds, and
`advance_bit` the states after one byte: the positions that may follow a state of `s` and whose
set holds the byte. -/

namespace Library.Regex.RunProof

open Library.Regex Library.Regex.Bits Library.Regex.Spec Library.Regex.Glushkov

/-- The bits of a loop whose step adds the bits of `P i` at index `i`. -/
theorem bit_loop {n : UInt64} {init : UInt64} {f : UInt64 → UInt64 → UInt64} {q : Nat}
    {P : Nat → Prop}
    (hf : ∀ i acc, i < n.toNat →
      (bit (f (UInt64.ofNat i) acc) q = true ↔ bit acc q = true ∨ P i)) :
    bit (LeanExe.loop n init f) q = true ↔ bit init q = true ∨ ∃ i, i < n.toNat ∧ P i := by
  refine LeanExe.IR.loop_induction
    (P := fun k s => bit s q = true ↔ bit init q = true ∨ ∃ i, i < k ∧ P i) ?_ ?_
  · simp
  · intro k s hk ih
    rw [hf k s hk, ih]
    constructor
    · rintro ((h | ⟨i, hi, hp⟩) | hp)
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, hp⟩
      · exact Or.inr ⟨k, by omega, hp⟩
    · rintro (h | ⟨i, hi, hp⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl (Or.inr ⟨i, hi, hp⟩)
        · exact Or.inr hp

theorem toNat_ofNat_lt {i n : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) : (UInt64.ofNat i).toNat = i := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- The bits of a byte of a word: bit `j` of byte `k` is bit `8 k + j` of the word. -/
theorem bit_byte {s : UInt64} {k j : Nat} (hk : k < 8) :
    bit ((s >>> (UInt64.ofNat (8 * k))) &&& 255) j = (decide (j < 8) && bit s (8 * k + j)) := by
  have hk' : (UInt64.ofNat (8 * k)).toNat = 8 * k :=
    toNat_ofNat_lt (by omega : 8 * k < 64) (by decide)
  simp only [bit, UInt64.toNat_and, UInt64.toNat_shiftRight, hk',
    Nat.mod_eq_of_lt (by omega : 8 * k < 64)]
  rw [show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  exact Bool.and_comm _ _

/-- Entry `256 k + v` of `steps follow` holds the union of the follow sets of the positions
`8 k + j` for the bits `j` of `v`. -/
theorem steps_bit (follow : Array UInt64) {k v : Nat} (hk : k < 8) (hv : v < 256) (q : Nat) :
    bit (steps follow)[256 * k + v]! q = true ↔
      ∃ j, j < 8 ∧ v.testBit j = true ∧ bit follow[8 * k + j]! q = true := by
  rw [steps, LeanExe.IR.build_get (by show 256 * k + v < (2048 : UInt64).toNat; simp; omega)]
  dsimp only
  have hidx : (UInt64.ofNat (256 * k + v)).toNat = 256 * k + v :=
    toNat_ofNat_lt (by omega : 256 * k + v < 2048) (by decide)
  have hk8 : (UInt64.ofNat (256 * k + v) >>> 8).toNat = k := by
    rw [UInt64.toNat_shiftRight, hidx, Nat.shiftRight_eq_div_pow,
      show (8 : UInt64).toNat = 8 from rfl]
    norm_num
    omega
  have hv8 : (UInt64.ofNat (256 * k + v) &&& 255).toNat = v := by
    rw [UInt64.toNat_and, hidx, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [bit_loop (P := fun j => v.testBit j = true ∧ bit follow[8 * k + j]! q = true)]
  · simp [bit_zero]
  · intro j acc hj
    have hj8 : j < 8 := by simpa using hj
    have hjt : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj8 (by decide)
    have htest := shiftRight_and_one (s := UInt64.ofNat (256 * k + v) &&& 255)
      (q := UInt64.ofNat j) (by omega)
    rw [hjt, bit, hv8] at htest
    have hnat : ((8 : UInt64) * (UInt64.ofNat (256 * k + v) >>> 8) + UInt64.ofNat j).toNat =
        8 * k + j := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hk8, hjt, show (8 : UInt64).toNat = 8 from rfl]
      omega
    rw [htest, hnat]
    by_cases hb : v.testBit j = true
    · simp only [hb, ite_true, bit_or, Bool.or_eq_true, true_and]
    · simp only [hb, Bool.false_eq_true, ite_false, false_and, or_false]

/-- The states after one byte: the positions that may follow a state of `s`, by the follow
table, and whose set holds the byte, by the mask. -/
theorem advance_bit (follow ms : Array UInt64) (s b : UInt64) (q : Nat) :
    bit (advance (steps follow) ms s b) q = true ↔
      (∃ p, p < 64 ∧ bit s p = true ∧ bit follow[p]! q = true) ∧ bit ms[b.toNat]! q = true := by
  rw [advance, bit_and, Bool.and_eq_true]
  apply and_congr_left'
  rw [bit_loop (P := fun k => ∃ j, j < 8 ∧ bit s (8 * k + j) = true ∧
    bit follow[8 * k + j]! q = true)]
  · simp only [bit_zero, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨k, hk, j, hj, hs, hf⟩
      exact ⟨8 * k + j, by simp at hk; omega, hs, hf⟩
    · rintro ⟨p, hp, hs, hf⟩
      refine ⟨p / 8, by simp; omega, p % 8, by omega, ?_, ?_⟩
      · rwa [show 8 * (p / 8) + p % 8 = p by omega]
      · rwa [show 8 * (p / 8) + p % 8 = p by omega]
  · intro k acc hk
    have hk8 : k < 8 := by simpa using hk
    have hkt : (UInt64.ofNat k).toNat = k := toNat_ofNat_lt hk8 (by decide)
    have hshift : (8 : UInt64) * UInt64.ofNat k = UInt64.ofNat (8 * k) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul, hkt, toNat_ofNat_lt (by omega : 8 * k < 64) (by decide)]
      show 8 * k % 2 ^ 64 = 8 * k
      omega
    have hbyte : ((s >>> UInt64.ofNat (8 * k)) &&& 255).toNat < 256 := by
      rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    have hidx : ((256 : UInt64) * UInt64.ofNat k + ((s >>> UInt64.ofNat (8 * k)) &&& 255)).toNat =
        256 * k + ((s >>> UInt64.ofNat (8 * k)) &&& 255).toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hkt, show (256 : UInt64).toNat = 256 from rfl]
      omega
    rw [hshift, bit_or, Bool.or_eq_true, hidx, steps_bit follow hk8 hbyte]
    apply or_congr_right
    constructor
    · rintro ⟨j, hj, hv, hf⟩
      refine ⟨j, hj, ?_, hf⟩
      have := bit_byte (s := s) (j := j) hk8
      rw [bit, hv] at this
      simpa [hj] using this.symm
    · rintro ⟨j, hj, hs, hf⟩
      refine ⟨j, hj, ?_, hf⟩
      have := bit_byte (s := s) (j := j) hk8
      rw [bit] at this
      rw [this]
      simp [hj, hs]

/-- Whether byte `b` is in the set of position `p`, as `sets` holds it: bit `b % 64` of word
`4 p + b / 64`. -/
def inSet (sets : Array UInt64) (p b : Nat) : Bool := bit sets[4 * p + b / 64]! (b % 64)

/-- Entry `b` of `masks sets count` holds the positions `1` to `count` whose set holds `b`. -/
theorem masks_bit (sets : Array UInt64) {count : UInt64} (hc : count.toNat ≤ 63) {b : Nat}
    (hb : b < 256) (q : Nat) :
    bit (masks sets count)[b]! q = true ↔
      ∃ i, i < count.toNat ∧ q = i + 1 ∧ inSet sets (i + 1) b = true := by
  rw [masks, LeanExe.IR.build_get (by show b < (256 : UInt64).toNat; simpa using hb)]
  have hbt : (UInt64.ofNat b).toNat = b := toNat_ofNat_lt hb (by decide)
  rw [bit_loop (P := fun i => q = i + 1 ∧ inSet sets (i + 1) b = true)]
  · simp [bit_zero]
  · intro i acc hi
    have hit : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt hi (by omega)
    have hp : (UInt64.ofNat i + (1 : UInt64)).toNat = i + 1 := by
      rw [UInt64.toNat_add, hit, UInt64.toNat_one]; omega
    have hidx : ((4 : UInt64) * (UInt64.ofNat i + (1 : UInt64)) + (UInt64.ofNat b >>> 6)).toNat =
        4 * (i + 1) + b / 64 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hp, UInt64.toNat_shiftRight, hbt,
        show (4 : UInt64).toNat = 4 from rfl, show (6 : UInt64).toNat = 6 from rfl,
        Nat.shiftRight_eq_div_pow]
      norm_num
      omega
    have hlow : (UInt64.ofNat b &&& 63).toNat = b % 64 := by
      rw [UInt64.toNat_and, hbt, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have htest := shiftRight_and_one (s := sets[((4 : UInt64) * (UInt64.ofNat i + (1 : UInt64)) +
      (UInt64.ofNat b >>> 6)).toNat]!) (q := UInt64.ofNat b &&& 63) (by omega)
    rw [hlow, hidx] at htest
    dsimp only
    rw [hidx, htest]
    by_cases hs : inSet sets (i + 1) b = true
    · rw [inSet] at hs
      simp only [hs, ↓reduceIte, bit_or, Bool.or_eq_true]
      rw [bit_one_shiftLeft (by omega), hp]
      simp [inSet, hs]
    · rw [inSet] at hs
      simp only [Bool.not_eq_true] at hs
      rw [hs]
      simp [inSet, hs]

/-- The steps of the automaton over a word that ends with `c`. -/
theorem steps_append (r : Re) : ∀ (S : Nat → Prop) (u : List UInt8) (c : UInt8),
    Automaton.steps r S (u ++ [c]) = Automaton.step r (Automaton.steps r S u) c
  | _, [], _ => rfl
  | S, d :: u, c => steps_append r (Automaton.step r S d) u c

/-- From states below 64, the automaton reaches only states below 64 when every state that may
follow another is below 64. -/
theorem steps_lt (r : Re) (h : ∀ p q, Automaton.Next r p q → q < 64) :
    ∀ (w : List UInt8) (S : Nat → Prop), (∀ q, S q → q < 64) →
      ∀ q, Automaton.steps r S w q → q < 64
  | [], _, hS, q, hq => hS q hq
  | _ :: w, _, _, q, hq =>
    steps_lt r h w _ (fun _ ⟨p, _, hn, _⟩ => h p _ hn) q hq

/-- The byte that `runInput` reads at index `i`. -/
theorem input_byte (msg : Array UInt64) {i : Nat} (hi : i < 2 ^ 64) :
    ((msg[(UInt64.ofNat i >>> 3).toNat]! >>> ((UInt64.ofNat i &&& 7) <<< 3)) &&& 255) =
      (Library.Bytes.byteAt msg i).toUInt64 := by
  have hit : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (Nat.lt_succ_of_lt hi |> fun _ => hi)
    (le_refl _)
  have hword : (UInt64.ofNat i >>> 3).toNat = i / 8 := by
    rw [UInt64.toNat_shiftRight, hit, show (3 : UInt64).toNat = 3 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hshift : ((UInt64.ofNat i &&& 7) <<< 3).toNat = 8 * (i % 8) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, hit, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (3 : UInt64).toNat = 3 from rfl, Nat.shiftLeft_eq]
    have : i % 2 ^ 3 < 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt (by omega : 3 < 64), Nat.mod_eq_of_lt (by omega)]
    norm_num
    ring
  have hs8 : (8 * (i % 8)).toUInt64.toNat = 8 * (i % 8) := by
    have : i % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  apply UInt64.toNat_inj.mp
  rw [Library.Bytes.byteAt, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, hword, UInt64.toNat_and,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, hshift, hs8,
    show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The states after the first `n` bytes of `msg` are the states that the automaton reaches from
the start, when the follow table holds `Next` and the masks hold `Class`. -/
theorem runInput_bit (r : Re) (F M msg : Array UInt64) (n : UInt64)
    (hF : ∀ p, p < 64 → ∀ q, bit F[p]! q = true ↔ Automaton.Next r p q)
    (hM : ∀ (c : UInt8) q, bit M[c.toNat]! q = true ↔ Class r 0 q c)
    (hstates : ∀ p q, Automaton.Next r p q → q < 64) (q : Nat) :
    bit (runInput (steps F) M msg n) q = true ↔
      Automaton.steps r (· = 0) ((List.range n.toNat).map (Library.Bytes.byteAt msg)) q := by
  revert q
  refine LeanExe.IR.loop_induction (P := fun k s => ∀ q, bit s q = true ↔
    Automaton.steps r (· = 0) ((List.range k).map (Library.Bytes.byteAt msg)) q) ?_ ?_
  · intro q
    have := bit_one_shiftLeft (p := 0) (by decide) q
    rw [show (1 : UInt64) <<< (0 : UInt64) = 1 from rfl] at this
    simp [this, Automaton.steps]
  · intro k s hk ih q
    have hk64 : k < 2 ^ 64 := lt_of_lt_of_le hk (UInt64.toNat_lt n).le
    rw [input_byte msg hk64, advance_bit, UInt8.toNat_toUInt64, hM, List.range_succ,
      List.map_append, List.map_singleton, steps_append]
    constructor
    · rintro ⟨⟨p, _, hs, hf⟩, hc⟩
      refine ⟨p, (ih p).1 hs, ?_, hc⟩
      exact (hF p (by assumption) q).1 hf
    · rintro ⟨p, hs, hn, hc⟩
      have hp : p < 64 := steps_lt r hstates _ (· = 0) (fun q hq => by omega) p hs
      exact ⟨⟨p, hp, (ih p).2 hs, (hF p hp q).2 hn⟩, hc⟩

#print axioms steps_bit
#print axioms runInput_bit
#print axioms masks_bit
#print axioms advance_bit

end Library.Regex.RunProof
