import Project.ProofKit.FixedArraySearchFrame
import Project.ProofKit.FixedArrayHeaderExec
import Project.ClobMatchFuel.BookAllocFitState
import Interpreter.Wasm.Wp.Block

namespace Project.ProofKit.FixedArrayReuse
open Wasm Project.Runtime Project.Clob Project.ClobMatchFuel.BookAllocFit
  Project.ProofKit.Memory FixedArraySearch

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

def program (start : Nat) (stride : UInt64) : Wasm.Program :=
  unlinkProgram start ++ FixedArrayHeader.program (start + 2) (start + 3) stride ++
    [.localGet (start + 2), .localSet (start + 5)]

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

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
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
    wp module_ (program start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le choice.node.root 48 hRoot
  simp only [program, List.append_assoc]
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

#print axioms unlinkStore_pages
#print axioms fitStore_header
#print axioms unlinkProgram_spec
#print axioms program_spec

end Project.ProofKit.FixedArrayReuse
