import LeanExe.ProofKit.FixedArraySearchFrame
import LeanExe.ProofKit.FixedArrayHeaderExec
import LeanExe.ProofKit.FreeListMemory
import Interpreter.Wasm.Wp.Block

namespace LeanExe.ProofKit.FixedArrayReuse
open Wasm LeanExe.Runtime
  LeanExe.ProofKit.Memory FixedArraySearch

def unlinkStore (store : Store Unit) (choice : FreeChoice) : Store Unit :=
  { store with
    globals := if choice.previous = 0 then
      { globals := store.globals.globals.set 1 (.i64 choice.next) } else store.globals
    mem := unlinkFreeChoice store.mem choice }

theorem unlinkStore_pages (store : Store Unit) (choice : FreeChoice) :
    (unlinkStore store choice).mem.pages = store.mem.pages := by
  unfold unlinkStore unlinkFreeChoice
  split <;> rfl

theorem fitStore_header (store : Store Unit) (choice : FreeChoice) (stride : UInt64)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat ≤ 4294967296) :
    fixedArrayAllocFitStore store choice stride =
      { unlinkStore store choice with
        mem := fixedArrayHeaderMem (unlinkStore store choice).mem
          (choice.node.root - 48) choice.node.capacity stride } := by
  simp only [unlinkStore, fixedArrayAllocFitStore, fixedArrayAllocFitMem,
    FixedArrayHeader.from_root _ _ _ _ hRoot hRoot32]

def unlinkProgram (start : Nat) : Wasm.Program :=
  [.localGet (start + 1), .constI64 0, .eqI64,
    .iff 0 0 [.localGet (start + 4), .globalSet 1]
      [.localGet (start + 1), .constI64 8, .subI64, .wrapI64,
        .localGet (start + 4), .store64 0]]

/-- Reuses the whole block: unlinks it and writes the header at its start. -/
def wholeProgram (start : Nat) (stride : UInt64) : Wasm.Program :=
  unlinkProgram start ++ FixedArrayHeader.program (start + 2) (start + 3) stride ++
    [.localGet (start + 2), .localSet (start + 5)]

/-- Splits the block: lowers its size word by `need + 48` and writes the new
object's header at the upper end. -/
def splitProgram (start : Nat) (stride : UInt64) : Wasm.Program :=
  [.localGet (start + 2), .constI64 32, .subI64, .wrapI64,
    .localGet (start + 3), .localGet start, .subI64, .constI64 48, .subI64, .store64 0,
   .localGet (start + 2), .localGet (start + 3), .addI64, .localGet start, .subI64,
    .localSet (start + 5)] ++
  FixedArrayHeader.program (start + 5) start stride

/-- Splits the block when at least 56 bytes would remain, and otherwise reuses it
whole. -/
def program (start : Nat) (stride : UInt64) : Wasm.Program :=
  [.localGet (start + 3), .localGet start, .subI64, .constI64 56, .geUI64,
    .iff 0 0 (splitProgram start stride) (wholeProgram start stride)]

theorem unlinkProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hBound : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (unlinkStore store choice)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env) :
    wp module_ (unlinkProgram start ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  unfold unlinkProgram
  simp [wp_simp, frame, Nat.add_assoc]
  refine wp_iff_cons rfl ?_
  by_cases hPrevious : choice.previous = 0
  · simpa [wp_simp, frame, Nat.add_assoc, hPrevious,
      unlinkStore, unlinkFreeChoice, hGlobalLength, hGlobalRead] using hNext
  · have hWriteBound : (choice.previous.toUInt32 - 8).toNat + 8 ≤
        store.mem.pages * 65536 := by simpa using hBound hPrevious
    simpa [wp_simp, frame, Nat.add_assoc, hPrevious,
      unlinkStore, unlinkFreeChoice, Nat.reducePow, ← toUInt32_eq_ofNat,
      Nat.not_lt.mpr hWriteBound] using hNext

theorem wholeProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head stride : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hPrevious : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat ≤ 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (fixedArrayAllocFitStore store choice stride)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp module_ (wholeProgram start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le choice.node.root 48 hRoot
  simp only [wholeProgram, List.append_assoc]
  apply unlinkProgram_spec module_ env store params saved tail _ rfl need result head choice
    hGlobal hPrevious
  refine FixedArrayHeader.program_spec module_ env _ _ _ _
    (choice.node.root - 48) choice.node.capacity stride rfl ?_ ?_ ?_ ?_ _ _ ?_
  · simp [frame, Locals.get, Nat.add_assoc]
  · simp [frame, Locals.get, Nat.add_assoc]
  · rw [hBase]
    omega
  · rw [hBase, unlinkStore_pages]
    omega
  · rw [← fitStore_header store choice stride hRoot (by omega)]
    simpa [wp_simp, frame, Nat.add_assoc] using hNext

theorem splitProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result stride : UInt64)
    (choice : FreeChoice) (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat < 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (hNeed : need ≤ choice.node.capacity) (hSplit : splitsFit need choice = true)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q { store with mem := fixedArraySplitMem store.mem choice need stride }
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next (choice.node.root + choice.node.capacity - need)) env) :
    wp module_ (splitProgram start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  have hNeedNat := UInt64.le_iff_toNat_le.mp hNeed
  have hSplitNat := hSplit
  simp only [splitsFit, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.toNat_sub_of_le _ _ hNeed] at hSplitNat
  simp only [UInt64.reduceToNat] at hSplitNat
  have h32 : (choice.node.root - 32).toUInt32.toNat = choice.node.root.toNat - 32 := by
    rw [toUInt32_toNat, toNat_sub_of_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
    rfl
  have hSum : (choice.node.root + choice.node.capacity).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat := by
    rw [UInt64.toNat_add]
    omega
  have hTop : (choice.node.root + choice.node.capacity - need).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat - need.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hSum]; omega), hSum]
  have hBase : (splitBase need choice).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat - need.toNat - 48 := by
    unfold splitBase
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hTop]; simp; omega), hTop]
    rfl
  have hs : (choice.node.root - 32).toNat = choice.node.root.toNat - 32 :=
    toNat_sub_of_le _ _ (by simp; omega)
  have hBound : ¬ store.mem.pages * 65536 < (choice.node.root - 32).toNat % 4294967296 + 8 := by
    rw [hs, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [splitProgram, List.cons_append, List.append_assoc]
  simp [wp_simp, frame, Nat.add_assoc]
  rw [if_neg hBound, ← toUInt32_eq_ofNat]
  refine FixedArrayHeader.program_spec module_ env _ _ _ _ (splitBase need choice) need stride
    rfl ?_ ?_ (by omega) (by simp only [Wasm.Mem.write64_pages]; omega) _ _ ?_
  · simp [frame, Locals.get, Nat.add_assoc, splitBase]
  · simp [frame, Locals.get, Nat.add_assoc]
  · simpa [fixedArraySplitMem, frame, Nat.add_assoc] using hNext

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head stride : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hPrevious : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat < 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (hNeed : need ≤ choice.node.capacity)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (fixedArrayReuseStore store choice need stride)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next (reuseRoot choice need)) env) :
    wp module_ (program start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  simp only [program, List.cons_append, List.nil_append]
  simp [wp_simp, frame, Nat.add_assoc]
  refine wp_iff_cons rfl ?_
  by_cases hSplit : splitsFit need choice = true
  · have hGe : 56 ≤ choice.node.capacity - need := by simpa [splitsFit] using hSplit
    simp only [fixedArrayReuseStore, reuseRoot, hSplit, ite_true] at hNext
    simp only [hGe, ite_true, ne_eq, one_ne_zero, not_false_eq_true]
    rw [← List.append_nil (splitProgram _ stride)]
    apply splitProgram_spec module_ env store params saved tail _ rfl need result stride choice
      hRoot hRoot32 hFit hNeed hSplit
    simpa [wp_simp, frame] using hNext
  · have hLt : ¬ 56 ≤ choice.node.capacity - need := by simpa [splitsFit] using hSplit
    simp only [fixedArrayReuseStore, reuseRoot, hSplit, Bool.false_eq_true, ite_false] at hNext
    simp only [hLt, ite_false, ne_eq, not_true_eq_false]
    rw [← List.append_nil (wholeProgram _ stride)]
    apply wholeProgram_spec module_ env store params saved tail _ rfl need result head stride
      choice hGlobal hPrevious hRoot (by omega) hFit
    simpa [wp_simp, frame] using hNext

#print axioms unlinkStore_pages
#print axioms fitStore_header
#print axioms unlinkProgram_spec
#print axioms wholeProgram_spec
#print axioms splitProgram_spec
#print axioms program_spec

end LeanExe.ProofKit.FixedArrayReuse
