import Verified.TreeFieldsCode
import Verified.LocalFrame
import LeanExe.Pipeline.Records

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

def recordLoadLocals (store : Store Unit) (p : UInt64) : Nat → List Nat → Locals → Locals
  | _, [], s => s
  | i, dst :: rest, s => recordLoadLocals store p (i + 1) rest
      (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i))))

theorem wp_recordLoadCode {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {ptr : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit} :
    ∀ (i : Nat) (dsts : List Nat) (s : Locals),
      s.get ptr = some (.i64 p) →
      (∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr) →
      p.toNat + 8 * (i + dsts.length) < 4294967296 →
      p.toNat + 8 * (i + dsts.length) ≤ store.mem.pages * 65536 →
      wp m rest Q store (recordLoadLocals store p i dsts s) host →
      wp m (recordLoadCode ptr i dsts ++ rest) Q store s host
  | _, [], _, _, _, _, _, hNext => hNext
  | i, dst :: dsts, s, hPtr, hDsts, hAddress, hMemory, hNext => by
    obtain ⟨hLow, hHigh, hNe⟩ := hDsts dst List.mem_cons_self
    let s1 := setLocal s dst (.i64 (store.mem.read64 (slotAddress p i)))
    have hFrame : Frame dst s s1 := Frame.set hLow (Nat.le_refl _) hHigh
    have hPtr1 : s1.get ptr = some (.i64 p) := by
      rw [Locals.get_setLocal_ne hLow hNe.symm]
      exact hPtr
    have hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      simp only [List.length_cons] at hMemory
      omega
    change (p + UInt64.ofNat (8 * i)).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 at hRoom
    have hRest := wp_recordLoadCode (i + 1) dsts s1 hPtr1
      (fun next hn => by
        rw [hFrame.params, hFrame.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn))
      (by simp only [List.length_cons] at hAddress; omega)
      (by simp only [List.length_cons] at hMemory; omega) hNext
    have hSet := wp_localSet_local (m := m) (env := host) (rest := recordLoadCode ptr (i + 1) dsts ++ rest)
      hLow (Locals.lt_total hHigh) hRest
    simpa only [recordLoadCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Locals.get_values, hPtr, wp_constI64_cons, wp_addI64_cons,
      wp_wrapI64_cons, wrap_toUInt32, slotAddress, wp_load64_cons, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, ite_eq_right (Nat.not_lt.mpr hRoom)] using hSet

theorem recordLoadLocals_frame (store : Store Unit) (p : UInt64) (base : Nat) :
    ∀ (i : Nat) (dsts : List Nat) (s : Locals), s.params.length ≤ base →
      (∀ dst ∈ dsts, base ≤ dst ∧ dst < s.positions) →
      Frame base s (recordLoadLocals store p i dsts s)
  | _, [], s, _, _ => Frame.refl base s
  | i, dst :: dsts, s, hLow, hDsts => by
    obtain ⟨hBase, hHigh⟩ := hDsts dst List.mem_cons_self
    have hHead : Frame base s (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i)))) :=
      Frame.set (by omega) hBase hHigh
    exact hHead.trans (recordLoadLocals_frame store p base (i + 1) dsts _
      (by rw [hHead.params]; exact hLow) fun next hn => by
        rw [hHead.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn))

theorem recordLoadLocals_get_other (store : Store Unit) (p : UInt64) :
    ∀ (i : Nat) (dsts : List Nat) (s : Locals) (k : Nat),
      (∀ dst ∈ dsts, s.params.length ≤ dst) → k ∉ dsts →
      (recordLoadLocals store p i dsts s).get k = s.get k
  | _, [], _, _, _, _ => rfl
  | i, dst :: dsts, s, k, hLow, hNot => by
    have hLow0 := hLow dst List.mem_cons_self
    have hNe : k ≠ dst := fun he => hNot (by rw [he]; exact List.mem_cons_self)
    have hNotTail : k ∉ dsts := fun hk => hNot (List.mem_cons_of_mem _ hk)
    rw [recordLoadLocals, recordLoadLocals_get_other store p (i + 1) dsts
      (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i)))) k
      (fun next hn => hLow next (List.mem_cons_of_mem _ hn)) hNotTail,
      Locals.get_setLocal_ne hLow0 hNe]

theorem recordLoadLocals_get (store : Store Unit) (p : UInt64) :
    ∀ (i : Nat) (dsts : List Nat) (s : Locals), dsts.Nodup →
      (∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions) →
      ∀ j (hj : j < dsts.length),
        (recordLoadLocals store p i dsts s).get dsts[j] =
          some (.i64 (store.mem.read64 (slotAddress p (i + j))))
  | _, [], _, _, _, j, hj => by simp at hj
  | i, dst :: dsts, s, hUnique, hDsts, 0, _ => by
    obtain ⟨hLow, hHigh⟩ := hDsts dst List.mem_cons_self
    obtain ⟨hNot, _⟩ := List.nodup_cons.mp hUnique
    change (recordLoadLocals store p (i + 1) dsts
      (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i))))).get dst = _
    rw [recordLoadLocals_get_other store p (i + 1) dsts
      (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i)))) dst
      (fun next hn => (hDsts next (List.mem_cons_of_mem _ hn)).1) hNot,
      Locals.get_setLocal_same hLow (Locals.lt_total hHigh)]
    rfl
  | i, dst :: dsts, s, hUnique, hDsts, j + 1, hj => by
    obtain ⟨hLow, hHigh⟩ := hDsts dst List.mem_cons_self
    have hFrame : Frame dst s (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i)))) :=
      Frame.set hLow (Nat.le_refl _) hHigh
    have hRest := recordLoadLocals_get store p (i + 1) dsts
      (setLocal s dst (.i64 (store.mem.read64 (slotAddress p i)))) (List.nodup_cons.mp hUnique).2
      (fun next hn => by
        rw [hFrame.params, hFrame.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn)) j
      (by simp only [List.length_cons] at hj; omega)
    simpa only [recordLoadLocals, List.getElem_cons_succ, Nat.add_assoc,
      Nat.add_comm 1 j] using hRest

end Verified
