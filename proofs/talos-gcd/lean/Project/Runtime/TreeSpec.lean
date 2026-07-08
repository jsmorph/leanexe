import Project.Runtime.Tree
import Project.Runtime.Spec

/-!
# The generic teardown theorem's walk preamble

Facts the walk proof consumes at each loop iteration: the stored mask
word's shift-and-test agrees with the slot's kind, a slot list indexes to
its read fact and child shape, and a child is smaller than its tree for
the fuel induction.
-/

namespace Project.Runtime

open Wasm Project.Common

theorem slotsMask_cons (slot : RelSlot) (rest : List RelSlot) :
    slotsMask (slot :: rest) =
    2 * slotsMask rest + (if slot.masked then 1 else 0) := by
  cases slot <;> rfl

theorem slotsMask_eq (slots : List RelSlot) :
    slotsMask slots = UInt64.ofNat (natMask slots) := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      rw [slotsMask_cons, natMask_cons, ih]
      cases slot <;> simp [RelSlot.masked] <;> push_cast <;> ring

theorem slotsMask_shift_and (slots : List RelSlot) (k : Nat)
    (hk : k < slots.length) (h32 : slots.length ≤ 32) :
    ((slotsMask slots >>> UInt64.ofNat k) &&& 1) =
    (if (slots[k]!).masked then 1 else 0) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, slotsMask_eq]
  have hm32 : natMask slots < 4294967296 := by
    have h := Nat.lt_of_lt_of_le (natMask_lt slots)
      (Nat.pow_le_pow_right (by omega) h32)
    rw [show (2 : Nat) ^ 32 = 4294967296 from by norm_num] at h
    exact h
  have hk64 : (UInt64.ofNat k).toNat % 64 = k := by
    rw [toNat_ofNat_lt (by rw [size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hk64, toNat_ofNat_lt (by rw [size_eq]; omega)]
  have htb := natMask_testBit slots k hk
  rw [Nat.testBit_eq_decide_div_mod_eq] at htb
  rw [show (1 : UInt64).toNat = 1 from rfl]
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  cases hmask : (slots[k]!).masked <;> rw [hmask] at htb
  · simp only [decide_eq_false_iff_not] at htb
    have : natMask slots / 2 ^ k % 2 = 0 := by omega
    rw [this]
    rfl
  · simp only [decide_eq_true_eq] at htb
    rw [htb]
    rfl

theorem SlotsAt_get {m : Mem} {p : UInt64} {i : Nat} {slots : List RelSlot}
    (h : SlotsAt m p i slots) (k : Nat) (hk : k < slots.length) :
    m.read64 ((p + UInt64.ofNat (8 * (i + k))).toUInt32) =
      (slots[k]!).stored ∧
    (∀ t : RelTree, slots[k]! = .child t → TreeAt m t) := by
  induction slots generalizing i k with
  | nil => simp at hk
  | cons slot rest ih =>
      cases k with
      | zero =>
          cases h with
          | scalar hword hrest =>
              exact ⟨by simpa [RelSlot.stored] using hword,
                fun t ht => by simp at ht⟩
          | null hword hrest =>
              exact ⟨by simpa [RelSlot.stored] using hword,
                fun t ht => by simp at ht⟩
          | child hword hchild hrest =>
              refine ⟨by simpa [RelSlot.stored] using hword, ?_⟩
              intro t ht
              simp at ht
              subst ht
              exact hchild
      | succ k =>
          have hrest : SlotsAt m p (i + 1) rest := by
            cases h with
            | scalar _ hrest => exact hrest
            | null _ hrest => exact hrest
            | child _ _ hrest => exact hrest
          have := ih hrest k (by simpa using hk)
          rw [show i + 1 + k = i + (k + 1) from by omega] at this
          simpa using this

theorem sizeOf_child_lt {t : RelTree} {slots : List RelSlot}
    (h : RelSlot.child t ∈ slots) : sizeOf t < sizeOf slots := by
  induction slots with
  | nil => simp at h
  | cons slot rest ih =>
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        simp
        omega
      · have := ih hin
        simp
        omega

end Project.Runtime
