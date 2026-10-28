import Verified.TreeFieldsCode
import Verified.LocalFrame
import Verified.WordCode
import LeanExe.Pipeline.Records

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- The locals after the loads of `recordLoadCode`: the local of position `dst` and type `ty` holds
the value of that type whose word is the slot's. -/
def recordLoadLocals (store : Store Unit) (p : UInt64) (h : Nat) :
    Nat → List Nat → List ValueType → Locals → Locals
  | _, [], _, s => s
  | i, dst :: rest, tys, s => recordLoadLocals store p h (i + 1) rest tys.tail
      (setLocal s (slotIndex h dst (tys.headD .i64))
        (typedValue (tys.headD .i64) (store.mem.read64 (slotAddress p i))))

theorem recordLoadLocals_values (store : Store Unit) (p : UInt64) (h : Nat) :
    ∀ i dsts tys s, (recordLoadLocals store p h i dsts tys s).values = s.values
  | _, [], _, _ => rfl
  | i, dst :: dsts, tys, s => recordLoadLocals_values store p h (i + 1) dsts tys.tail _

theorem recordLoadLocals_positions (store : Store Unit) (p : UInt64) (h : Nat) :
    ∀ i dsts tys s, (recordLoadLocals store p h i dsts tys s).positions = s.positions
  | _, [], _, _ => rfl
  | i, dst :: dsts, tys, s => by
    rw [recordLoadLocals, recordLoadLocals_positions store p h (i + 1) dsts tys.tail,
      Locals.positions_setLocal]

theorem wp_recordLoadCode {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {ptr : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit} :
    ∀ (i : Nat) (dsts : List Nat) (tys : List ValueType) (s : Locals),
      s.get ptr = some (.i64 p) → ptr < s.positions →
      (∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr) →
      p.toNat + 8 * (i + dsts.length) < 4294967296 →
      p.toNat + 8 * (i + dsts.length) ≤ store.mem.pages * 65536 →
      wp m rest Q store (recordLoadLocals store p s.positions i dsts tys s) host →
      wp m (recordLoadCode s.positions ptr i dsts tys ++ rest) Q store s host
  | _, [], _, _, _, _, _, _, _, hNext => hNext
  | i, dst :: dsts, tys, s, hPtr, hPtrLow, hDsts, hAddress, hMemory, hNext => by
    obtain ⟨hLow, hHigh, hNe⟩ := hDsts dst List.mem_cons_self
    let ty := tys.headD .i64
    let s1 := setLocal s (slotIndex s.positions dst ty)
      (typedValue ty (store.mem.read64 (slotAddress p i)))
    obtain ⟨hSlotLow, hSlotHigh⟩ := slotIndex_bounds (s := s) ty hLow hHigh
    have hFrame : Frame dst s s1 := Frame.setSlot ty hSlotLow (Nat.le_refl _) hHigh
    have hSlotNe : slotIndex s.positions dst ty ≠ ptr := by
      cases hty : ty <;> simp only [slotIndex] <;> omega
    have hPtr1 : s1.get ptr = some (.i64 p) := by
      rw [Locals.get_setLocal_ne hSlotLow hSlotNe.symm]
      exact hPtr
    have hPositions : s1.positions = s.positions := Locals.positions_setLocal _ _ _
    have hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      simp only [List.length_cons] at hMemory
      omega
    change (p + UInt64.ofNat (8 * i)).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 at hRoom
    have hRest := wp_recordLoadCode (m := m) (host := host) (store := store) (ptr := ptr) (p := p)
      (rest := rest) (Q := Q) (i + 1) dsts tys.tail s1 hPtr1 (by rw [hPositions]; exact hPtrLow)
      (fun next hn => by
        rw [hFrame.params, hFrame.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn))
      (by simp only [List.length_cons] at hAddress; omega)
      (by simp only [List.length_cons] at hMemory; omega)
      (by rw [hPositions]; exact hNext)
    rw [hPositions] at hRest
    have hSet := wp_localSet_local (m := m) (env := host)
      (rest := recordLoadCode s.positions ptr (i + 1) dsts tys.tail ++ rest)
      hSlotLow hSlotHigh hRest
    have hOf := (wp_ofWordCode (m := m) (st := store) (env' := host) (s := s) (vs := s.values)
      (rest := [.localSet (slotIndex s.positions dst ty)] ++
        (recordLoadCode s.positions ptr (i + 1) dsts tys.tail ++ rest)) (Q := Q) ty
      (store.mem.read64 (slotAddress p i))).mpr (by simpa only [List.cons_append,
        List.nil_append] using hSet)
    simpa only [recordLoadCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Locals.get_values, hPtr, wp_constI64_cons, wp_addI64_cons,
      wp_wrapI64_cons, wrap_toUInt32, slotAddress, wp_load64_cons, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, ite_eq_right (Nat.not_lt.mpr hRoom)] using hOf

theorem recordLoadLocals_frame (store : Store Unit) (p : UInt64) (base : Nat) :
    ∀ (i : Nat) (dsts : List Nat) (tys : List ValueType) (s : Locals), s.params.length ≤ base →
      (∀ dst ∈ dsts, base ≤ dst ∧ dst < s.positions) →
      Frame base s (recordLoadLocals store p s.positions i dsts tys s)
  | _, [], _, s, _, _ => Frame.refl base s
  | i, dst :: dsts, tys, s, hLow, hDsts => by
    obtain ⟨hBase, hHigh⟩ := hDsts dst List.mem_cons_self
    let ty := tys.headD .i64
    obtain ⟨hSlotLow, -⟩ := slotIndex_bounds (s := s) ty (by omega) hHigh
    have hHead : Frame base s (setLocal s (slotIndex s.positions dst ty)
        (typedValue ty (store.mem.read64 (slotAddress p i)))) :=
      Frame.setSlot ty hSlotLow hBase hHigh
    have hRest := recordLoadLocals_frame store p base (i + 1) dsts tys.tail _
      (by rw [hHead.params]; exact hLow) fun next hn => by
        rw [hHead.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn)
    rw [Locals.positions_setLocal] at hRest
    exact hHead.trans hRest

theorem recordLoadLocals_get_other (store : Store Unit) (p : UInt64) (h : Nat) :
    ∀ (i : Nat) (dsts : List Nat) (tys : List ValueType) (s : Locals) (k : Nat),
      (∀ dst ∈ dsts, ∀ ty, s.params.length ≤ slotIndex h dst ty ∧ k ≠ slotIndex h dst ty) →
      (recordLoadLocals store p h i dsts tys s).get k = s.get k
  | _, [], _, _, _, _ => rfl
  | i, dst :: dsts, tys, s, k, hOther => by
    obtain ⟨hLow0, hNe⟩ := hOther dst List.mem_cons_self (tys.headD .i64)
    rw [recordLoadLocals, recordLoadLocals_get_other store p h (i + 1) dsts tys.tail _ k
      (fun next hn ty => by
        have := hOther next (List.mem_cons_of_mem _ hn) ty
        simpa only [setLocal] using this),
      Locals.get_setLocal_ne hLow0 hNe]

/-- The local of the position `dsts[j]` holds slot `i + j` as a value of its type, when the
positions are distinct and below the position bound `h`. -/
theorem recordLoadLocals_get (store : Store Unit) (p : UInt64) :
    ∀ (i : Nat) (dsts : List Nat) (tys : List ValueType) (s : Locals), dsts.Nodup →
      (∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions) →
      ∀ j (hj : j < dsts.length),
        (recordLoadLocals store p s.positions i dsts tys s).get
            (slotIndex s.positions dsts[j] (tys.getD j .i64)) =
          some (typedValue (tys.getD j .i64) (store.mem.read64 (slotAddress p (i + j))))
  | _, [], _, _, _, _, j, hj => by simp at hj
  | i, dst :: dsts, tys, s, hUnique, hDsts, 0, _ => by
    obtain ⟨hLow, hHigh⟩ := hDsts dst List.mem_cons_self
    obtain ⟨hNot, _⟩ := List.nodup_cons.mp hUnique
    let ty := tys.headD .i64
    obtain ⟨hSlotLow, hSlotHigh⟩ := slotIndex_bounds (s := s) ty hLow hHigh
    have hTy : tys.getD 0 .i64 = ty := by cases tys <;> rfl
    rw [hTy]
    change (recordLoadLocals store p s.positions (i + 1) dsts tys.tail
      (setLocal s (slotIndex s.positions dst ty)
        (typedValue ty (store.mem.read64 (slotAddress p i))))).get
          (slotIndex s.positions dst ty) = _
    rw [recordLoadLocals_get_other store p s.positions (i + 1) dsts tys.tail _ _
      (fun next hn ty' => by
        obtain ⟨hl, hh⟩ := hDsts next (List.mem_cons_of_mem _ hn)
        have hne : next ≠ dst := fun he => hNot (he ▸ hn)
        refine ⟨by simp only [setLocal]; exact (slotIndex_bounds (s := s) ty' hl hh).1, ?_⟩
        cases ty <;> cases ty' <;> simp only [slotIndex] <;> omega),
      Locals.get_setLocal_same hSlotLow hSlotHigh]
    rfl
  | i, dst :: dsts, tys, s, hUnique, hDsts, j + 1, hj => by
    obtain ⟨hLow, hHigh⟩ := hDsts dst List.mem_cons_self
    let ty := tys.headD .i64
    obtain ⟨hSlotLow, -⟩ := slotIndex_bounds (s := s) ty hLow hHigh
    let s1 := setLocal s (slotIndex s.positions dst ty)
      (typedValue ty (store.mem.read64 (slotAddress p i)))
    have hFrame : Frame dst s s1 := Frame.setSlot ty hSlotLow (Nat.le_refl _) hHigh
    have hRest := recordLoadLocals_get store p (i + 1) dsts tys.tail s1
      (List.nodup_cons.mp hUnique).2
      (fun next hn => by
        rw [hFrame.params, hFrame.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn)) j
      (by simp only [List.length_cons] at hj; omega)
    rw [hFrame.positions] at hRest
    have hTy : tys.getD (j + 1) .i64 = tys.tail.getD j .i64 := by cases tys <;> simp
    simpa only [recordLoadLocals, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j, hTy]
      using hRest

end Verified
