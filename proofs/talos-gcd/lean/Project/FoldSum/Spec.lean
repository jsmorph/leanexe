import Project.FoldSum.Program
import Project.Common
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Specification for `foldSum`

The export folds byte addition over its input array.  The theorem is
input-generic: for every input byte list, the compiled function returns the
value of the source fold and leaves the store untouched.  The loop invariant
carries the fold over the consumed prefix; the source-level overflow guard
discharges against the prefix-sum bound.
-/

namespace Project.FoldSum.Spec

open Wasm Project.Common Project.FoldSum

/-- The byte sum of a prefix of the input. -/
def sumTake (bytes : List UInt8) (k : Nat) : Nat :=
  (bytes.take k).foldl (fun acc b => acc + b.toNat) 0

theorem sumTake_succ (bytes : List UInt8) (k : Nat) (h : k < bytes.length) :
    sumTake bytes (k + 1) = sumTake bytes k + bytes[k]!.toNat := by
  unfold sumTake
  rw [List.take_succ, List.getElem?_eq_getElem h]
  rw [List.foldl_append]
  simp [List.getElem?_eq_getElem h]

theorem sumTake_le (bytes : List UInt8) (k : Nat) :
    sumTake bytes k ≤ 255 * k := by
  induction k with
  | zero => simp [sumTake]
  | succ n ih =>
      by_cases h : n < bytes.length
      · rw [sumTake_succ bytes n h]
        have h256 : UInt8.size = 256 := rfl
        have hb : bytes[n]!.toNat < UInt8.size := bytes[n]!.toNat_lt_size
        omega
      · have h1 : bytes.take (n + 1) = bytes :=
          List.take_of_length_le (by omega)
        have h2 : bytes.take n = bytes :=
          List.take_of_length_le (by omega)
        unfold sumTake at ih ⊢
        rw [h1]
        rw [h2] at ih
        omega

private def fFrame (ptr len acc idx l3 l4 l11 l12 l13 l15 l16 : UInt64) :
    Locals :=
  { params := [.i64 ptr, .i64 len],
    locals := [.i64 acc, .i64 l3, .i64 l4, .i64 0, .i64 ptr, .i64 len,
      .i64 idx, .i64 len, .i64 len, .i64 l11, .i64 l12, .i64 l13, .i64 0,
      .i64 l15, .i64 l16],
    values := [] }

private def fInv (st0 : Store Unit) (ptr : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    ∃ k : Nat, k ≤ bytes.length ∧
    ∃ l3 l4 l11 l12 l13 l15 l16 : UInt64,
      s = fFrame ptr (UInt64.ofNat bytes.length)
        (UInt64.ofNat (sumTake bytes k)) (UInt64.ofNat k)
        l3 l4 l11 l12 l13 l15 l16

private def fMeasure (bytes : List UInt8) (_ : Store Unit) (s : Locals) :
    Nat :=
  match s.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: .i64 idx :: _ => bytes.length - idx.toNat
  | _ => 0

/-- The export returns the byte sum of its input and leaves the store
unchanged. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.foldSum"]
def FoldSumSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (bytes : List UInt8),
    bytes.length < 4294967296 →
    ptr.toNat + bytes.length < 4294967296 →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat
          (bytes.foldl (fun acc b => acc + b.toNat) 0))] ∧
        st' = st)

@[proves Project.FoldSum.Spec.FoldSumSpec]
theorem foldSum_correct : FoldSumSpec := by
  intro env st ptr bytes hlen hfit hInput
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func0
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    apply wp_block_cons
    apply wp_loop_cons (Inv := fInv st ptr bytes) (μ := fMeasure bytes)
    · exact ⟨rfl, 0, Nat.zero_le _, 0, 0, 0, 0, 0, 0, 0,
        by simp [fFrame, sumTake]⟩
    · rintro st2 s2 ⟨rfl, k, hk, l3, l4, l11, l12, l13, l15, l16, rfl⟩
      have hkU : (UInt64.ofNat k).toNat = k :=
        toNat_ofNat_lt (by rw [size_eq]; omega)
      simp only [fFrame]
      wp_run
      try simp
      by_cases hkend : k = bytes.length
      · have hge : UInt64.ofNat k ≥ UInt64.ofNat bytes.length := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
          omega
        rw [if_pos hge]
        try wp_run
        try simp
        subst hkend
        have hfull : sumTake bytes bytes.length =
            List.foldl (fun acc b => acc + b.toNat) 0 bytes := by
          unfold sumTake
          rw [List.take_length]
        simp [func0Def, hfull]
      · have hklt : k < bytes.length := Nat.lt_of_le_of_ne hk hkend
        have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat bytes.length) := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
          omega
        rw [if_neg hnge]
        wp_run
        try simp
        obtain ⟨hread, hbound⟩ := hInput k hklt
        have hb2 : (ptr + UInt64.ofNat k).toUInt32.toNat =
            (ptr.toNat + k) % 4294967296 := by
          rw [toUInt32_toNat, UInt64.toNat_add, hkU]
          omega
        rw [hb2] at hbound
        refine ⟨by omega, ?_⟩
        have hsrcN : (ptr + UInt64.ofNat k).toNat = ptr.toNat + k := by
          rw [UInt64.toNat_add, hkU]
          have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
          omega
        have hread' : st2.mem.read8
            (UInt32.ofNat ((ptr.toNat + k) % 4294967296)) = bytes[k]! := by
          rw [← hsrcN, ← toUInt32_eq_ofNat]
          exact hread
        rw [hread']
        have hsle := sumTake_le bytes k
        have h256 : UInt8.size = 256 := rfl
        have hbyte : bytes[k]!.toNat < UInt8.size := bytes[k]!.toNat_lt_size
        have hnowrap : ¬ (UInt64.ofNat (sumTake bytes k) +
            bytes[k]!.toUInt64 < UInt64.ofNat (sumTake bytes k)) := by
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
          have hsu : (UInt64.ofNat (sumTake bytes k)).toNat = sumTake bytes k :=
            toNat_ofNat_lt (by rw [size_eq]; omega)
          have hbu : (bytes[k]!.toUInt64).toNat = bytes[k]!.toNat := by
            rw [UInt8.toNat_toUInt64]
          rw [hsu, hbu]
          have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simpa using hnowrap)]
        try wp_run
        try simp
        have hsu : (UInt64.ofNat (sumTake bytes k)).toNat = sumTake bytes k :=
          toNat_ofNat_lt (by rw [size_eq]; omega)
        have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one, hkU, toNat_ofNat_lt (by rw [size_eq]; omega)]
          rw [hkU, size_eq]
          omega
        have hacc : UInt64.ofNat (sumTake bytes k) + bytes[k]!.toUInt64 =
            UInt64.ofNat (sumTake bytes (k + 1)) := by
          apply UInt64.toNat.inj
          rw [UInt64.toNat_add, hsu, UInt8.toNat_toUInt64,
            toNat_ofNat_lt (by rw [size_eq]; exact
              Nat.lt_of_le_of_lt (sumTake_le bytes (k + 1)) (by omega))]
          rw [sumTake_succ bytes k hklt]
          have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
          rw [Nat.mod_eq_of_lt (by omega)]
        refine ⟨⟨rfl, k + 1, by omega,
          bytes[k]!.toUInt64,
          UInt64.ofNat (sumTake bytes k) + bytes[k]!.toUInt64,
          UInt64.ofNat (sumTake bytes k),
          bytes[k]!.toUInt64,
          UInt64.ofNat (sumTake bytes k) + bytes[k]!.toUInt64,
          UInt64.ofNat (sumTake bytes k) + bytes[k]!.toUInt64,
          1, ?_⟩, ?_⟩
        · simp only [fFrame, ← hacc, ← hkadd]
          simp
        · have hk1 : (UInt64.ofNat k + 1).toNat = k + 1 := by
            rw [hkadd]
            exact toNat_ofNat_lt (by rw [size_eq]; omega)
          simp only [fMeasure, hk1, hkU]
          omega
end Project.FoldSum.Spec
