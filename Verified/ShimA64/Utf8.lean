import Verified.Shim.Utf8
import LeanExe.A64.WasiFiles

/-!
The stub of `path_open` in `LeanExe/A64/WasiFiles.lean` checks that the path is UTF-8 with
`utf8Check`, whose decision on the path's bytes is `LeanExe.A64.utf8Scan`.  `utf8Scan_validate`
proves that `utf8Scan` of a byte array's bytes equals core's `ByteArray.validateUTF8`, and
`utf8Scan_iff` that it is `true` exactly when the array satisfies `ByteArray.IsValidUTF8`, the
condition that `Verified.Shim.openCheck` tests.  The stub classifies a first byte by the thresholds
`0x80`, `0xC2`, `0xE0`, `0xF0`, and `0xF5`, while core's
`ByteArray.utf8DecodeChar?.parseFirstByte` classifies it by bit masks and rejects `0xC0`, `0xC1`,
and `0xF5` to `0xF7` only through the range checks of `verify₂` and `verify₄`.

`utf8Scan_go` follows core's loop `ByteArray.validateUTF8.go` from each position, by induction on
the cases of `utf8Scan`.  In each case the stub's tests of the first byte fix the byte's class
under `parseFirstByte` and its length under `UInt8.utf8ByteSize`, through statements about every
byte that `decide` checks.  `Verified.Shim.verify₂_iff`,
`Verified.Shim.verify₃_iff`, and `Verified.Shim.verify₄_iff` then turn core's checks of the later
bytes into the stub's tests.
-/

namespace Verified.ShimA64

open LeanExe.A64 Verified.Shim ByteArray.utf8DecodeChar?

/-- Core declares `FirstByte` without `DecidableEq`, so this instance compares constructor indices
for `decide` to check equations of `parseFirstByte`. -/
local instance : DecidableEq FirstByte := fun a b =>
  decidable_of_iff (a.ctorIdx = b.ctorIdx)
    ⟨fun h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide), congrArg _⟩

private theorem utf8ByteSize_eq (w : UInt8) (h : w.IsUTF8FirstByte) :
    w.utf8ByteSize h = if w < 0x80 then 1 else if w < 0xE0 then 2 else if w < 0xF0 then 3 else 4 := by
  revert w
  refine forall_uint8 ?_
  decide +kernel

private theorem parse_done : ∀ w : UInt8, w < 0x80 → parseFirstByte w = .done :=
  forall_uint8 (by decide +kernel)

private theorem parse_low : ∀ w : UInt8, ¬ w < 0x80 → w < 0xC2 →
    parseFirstByte w = .invalid ∨ parseFirstByte w = .oneMore ∧ 0xC0 ≤ w ∧ w < 0xE0 :=
  forall_uint8 (by decide +kernel)

private theorem parse_two : ∀ w : UInt8, ¬ w < 0xC2 → w < 0xE0 → parseFirstByte w = .oneMore :=
  forall_uint8 (by decide +kernel)

private theorem parse_three : ∀ w : UInt8, ¬ w < 0xE0 → w < 0xF0 → parseFirstByte w = .twoMore :=
  forall_uint8 (by decide +kernel)

private theorem parse_four : ∀ w : UInt8, ¬ w < 0xF0 → w < 0xF5 → parseFirstByte w = .threeMore :=
  forall_uint8 (by decide +kernel)

private theorem parse_high : ∀ w : UInt8, ¬ w < 0xF5 →
    parseFirstByte w = .invalid ∨ parseFirstByte w = .threeMore ∧ 0xF0 ≤ w ∧ w < 0xF8 :=
  forall_uint8 (by decide +kernel)

/-- This form of `ByteArray.validateUTF8At` matches on `parseFirstByte` without binding the match's
equation, so `simp` reduces it once the class of the first byte is known. -/
private theorem validateUTF8At_eq {b : ByteArray} {i : Nat} (h : i < b.size) :
    b.validateUTF8At i = match parseFirstByte b[i] with
      | .invalid => false
      | .done => true
      | .oneMore => if h : i + 1 < b.size then verify₂ b[i] b[i + 1] else false
      | .twoMore => if h : i + 2 < b.size then verify₃ b[i] b[i + 1] b[i + 2] else false
      | .threeMore =>
        if h : i + 3 < b.size then verify₄ b[i] b[i + 1] b[i + 2] b[i + 3] else false := by
  unfold ByteArray.validateUTF8At
  simp only [h, ↓reduceDIte]
  split <;> simp_all [verify₁]

private theorem drop_cons {b : ByteArray} {i : Nat} {w : UInt8} {rest : List UInt8}
    (hl : b.data.toList.drop i = w :: rest) :
    ∃ h : i < b.size, b[i] = w ∧ i + rest.length + 1 = b.size := by
  have hn := congrArg List.length hl
  simp only [List.length_drop, Array.length_toList, ByteArray.size_data, List.length_cons] at hn
  have h : i < b.size := by omega
  rw [List.drop_eq_getElem_cons (by simpa using h)] at hl
  obtain ⟨hw, -⟩ := List.cons.inj hl
  exact ⟨h, by simpa [ByteArray.getElem_eq_getElem_data] using hw, by omega⟩

private theorem drop_shift {b : ByteArray} {i : Nat} {L : List UInt8}
    (hl : b.data.toList.drop i = L) (k : Nat) : b.data.toList.drop (i + k) = L.drop k := by
  rw [← List.drop_drop, hl]

private theorem go_step {b : ByteArray} {i k : Nat} {hi : i ≤ b.size} (h : i < b.size)
    (hk : ∀ h' : b[i].IsUTF8FirstByte, b[i].utf8ByteSize h' = k) (hik : i + k ≤ b.size) :
    ByteArray.validateUTF8.go b i hi =
      (b.validateUTF8At i && ByteArray.validateUTF8.go b (i + k) hik) := by
  rw [ByteArray.validateUTF8.go]
  simp only [h, ↓reduceDIte]
  split <;> simp_all

private theorem go_false {b : ByteArray} {i : Nat} {hi : i ≤ b.size} (h : i < b.size)
    (hv : b.validateUTF8At i = false) : ByteArray.validateUTF8.go b i hi = false := by
  rw [ByteArray.validateUTF8.go]
  simp only [h, ↓reduceDIte]
  split <;> simp_all

private theorem verify₂_eq {w x : UInt8} (h₀ : ¬ w < 0xC2) (h₁ : w < 0xE0) :
    verify₂ w x = contByte x := by
  have h₂ : 0xC2 ≤ w := UInt8.not_lt.1 h₀
  rw [Bool.eq_iff_iff, verify₂_iff (UInt8.le_trans (by decide) h₂) h₁]
  simp [contByte, h₂]

private theorem verify₃_eq {w x y : UInt8} (h₀ : ¬ w < 0xE0) (h₁ : w < 0xF0) :
    verify₃ w x y = (contByte x && contByte y && (w != 0xE0 || 0xA0 ≤ x) &&
      (w != 0xED || x < 0xA0)) := by
  rw [Bool.eq_iff_iff, verify₃_iff (UInt8.not_lt.1 h₀) h₁]
  simp [contByte, Decidable.imp_iff_not_or, and_assoc]

private theorem verify₄_eq {w x y z : UInt8} (h₀ : ¬ w < 0xF0) (h₁ : w < 0xF5) :
    verify₄ w x y z = (contByte x && contByte y && contByte z && (w != 0xF0 || 0x90 ≤ x) &&
      (w != 0xF4 || x < 0x90)) := by
  have h₂ : w < 0xF8 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at h₁ ⊢
    omega
  rw [Bool.eq_iff_iff, verify₄_iff (UInt8.not_lt.1 h₀) h₂]
  simp [contByte, h₁, Decidable.imp_iff_not_or, and_assoc]

private theorem utf8Scan_go (b : ByteArray) (L : List UInt8) :
    ∀ i (hi : i ≤ b.size), b.data.toList.drop i = L →
      utf8Scan L = ByteArray.validateUTF8.go b i hi := by
  fun_induction utf8Scan L with
  | case1 =>
    intro i hi hl
    have hn := congrArg List.length hl
    simp only [List.length_drop, Array.length_toList, ByteArray.size_data, List.length_nil] at hn
    rw [ByteArray.validateUTF8.go]
    simp only [show ¬ i < b.size by omega, ↓reduceDIte]
  | case2 w rest h₁ ih =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    rw [go_step h (k := 1) (fun _ => by simp [utf8ByteSize_eq, hw, h₁]) (by omega)]
    simp only [validateUTF8At_eq h, hw, parse_done _ h₁, Bool.true_and]
    exact ih _ _ (drop_shift hl 1)
  | case3 w rest h₁ h₂ =>
    intro i hi hl
    obtain ⟨h, hw, -⟩ := drop_cons hl
    have hv : b.validateUTF8At i = false := by
      rw [validateUTF8At_eq h, hw]
      rcases parse_low _ h₁ h₂ with hp | ⟨hp, h₃, h₄⟩
      · simp only [hp]
      · simp only [hp]
        split
        · exact Bool.eq_false_iff.2 fun hv => UInt8.not_le.2 h₂ ((verify₂_iff h₃ h₄).1 hv).1
        · rfl
    rw [go_false h hv]
  | case4 w h₁ h₂ h₃ x rest ih =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    obtain ⟨_, hx, -⟩ := drop_cons (drop_shift hl 1)
    simp only [List.length_cons] at hn
    rw [go_step h (k := 2) (fun _ => by simp [utf8ByteSize_eq, hw, h₁, h₃]) (by omega)]
    simp only [validateUTF8At_eq h, hw, parse_two _ h₂ h₃, show i + 1 < b.size by omega,
      ↓reduceDIte, hx, verify₂_eq h₂ h₃]
    congr 1
    exact ih _ _ (drop_shift hl 2)
  | case5 w h₁ h₂ h₃ =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    simp only [List.length_nil] at hn
    rw [go_false h (by simp only [validateUTF8At_eq h, hw, parse_two _ h₂ h₃,
      show ¬ i + 1 < b.size by omega, ↓reduceDIte])]
  | case6 w h₁ h₂ h₃ h₄ x y rest ih =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    obtain ⟨_, hx, -⟩ := drop_cons (drop_shift hl 1)
    obtain ⟨_, hy, -⟩ := drop_cons (drop_shift hl 2)
    simp only [List.length_cons] at hn
    rw [go_step h (k := 3) (fun _ => by simp [utf8ByteSize_eq, hw, h₁, h₃, h₄]) (by omega)]
    simp only [validateUTF8At_eq h, hw, parse_three _ h₃ h₄, show i + 2 < b.size by omega,
      ↓reduceDIte, hx, hy, verify₃_eq h₃ h₄]
    congr 1
    exact ih _ _ (drop_shift hl 3)
  | case7 w rest h₁ h₂ h₃ h₄ hs =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    have : rest.length < 2 := by
      rcases rest with _ | ⟨_, _ | ⟨_, _⟩⟩
      · simp
      · simp
      · exact (hs _ _ _ rfl).elim
    rw [go_false h (by simp only [validateUTF8At_eq h, hw, parse_three _ h₃ h₄,
      show ¬ i + 2 < b.size by omega, ↓reduceDIte])]
  | case8 w h₁ h₂ h₃ h₄ h₅ x y z rest ih =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    obtain ⟨_, hx, -⟩ := drop_cons (drop_shift hl 1)
    obtain ⟨_, hy, -⟩ := drop_cons (drop_shift hl 2)
    obtain ⟨_, hz, -⟩ := drop_cons (drop_shift hl 3)
    simp only [List.length_cons] at hn
    rw [go_step h (k := 4) (fun _ => by simp [utf8ByteSize_eq, hw, h₁, h₃, h₄]) (by omega)]
    simp only [validateUTF8At_eq h, hw, parse_four _ h₄ h₅, show i + 3 < b.size by omega,
      ↓reduceDIte, hx, hy, hz, verify₄_eq h₄ h₅]
    congr 1
    exact ih _ _ (drop_shift hl 4)
  | case9 w rest h₁ h₂ h₃ h₄ h₅ hs =>
    intro i hi hl
    obtain ⟨h, hw, hn⟩ := drop_cons hl
    have : rest.length < 3 := by
      rcases rest with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
      · simp
      · simp
      · simp
      · exact (hs _ _ _ _ rfl).elim
    rw [go_false h (by simp only [validateUTF8At_eq h, hw, parse_four _ h₄ h₅,
      show ¬ i + 3 < b.size by omega, ↓reduceDIte])]
  | case10 w rest h₁ h₂ h₃ h₄ h₅ =>
    intro i hi hl
    obtain ⟨h, hw, -⟩ := drop_cons hl
    have hv : b.validateUTF8At i = false := by
      rw [validateUTF8At_eq h, hw]
      rcases parse_high _ h₅ with hp | ⟨hp, h₆, h₇⟩
      · simp only [hp]
      · simp only [hp]
        split
        · exact Bool.eq_false_iff.2 fun hv => h₅ ((verify₄_iff h₆ h₇).1 hv).1
        · rfl
    rw [go_false h hv]

theorem utf8Scan_validate (b : ByteArray) : utf8Scan b.data.toList = b.validateUTF8 :=
  utf8Scan_go b _ 0 (Nat.zero_le _) rfl

theorem utf8Scan_iff (b : ByteArray) : utf8Scan b.data.toList = true ↔ b.IsValidUTF8 := by
  rw [utf8Scan_validate, ByteArray.validateUTF8_eq_true_iff]

end Verified.ShimA64
