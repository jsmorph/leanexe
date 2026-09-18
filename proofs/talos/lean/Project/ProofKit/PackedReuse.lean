import Project.ProofKit.FixedArraySearchFit
import Project.ProofKit.PackedHeader

namespace Project.ProofKit.PackedReuse
open Wasm Project.Runtime Project.ProofKit.Memory FixedArraySearch FixedArrayReuse

def reused (store : Store Unit) (choice : FreeChoice) : Store Unit :=
  let unlinked := unlinkStore store choice
  { unlinked with mem := PackedHeader.headerMem unlinked.mem (choice.node.root - 48) choice.node.capacity }

def program (start : Nat) : Wasm.Program :=
  unlinkProgram start ++ PackedHeader.program (start + 2) (start + 3) ++
    [.localGet (start + 2), .localSet (start + 5)]

theorem reused_pages (store : Store Unit) (choice : FreeChoice) :
    (reused store choice).mem.pages = store.mem.pages := unlinkStore_pages store choice

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hPrevious : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat ≤ 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (reused store choice)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp module_ (program start ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le choice.node.root 48 hRoot
  have hPointer : choice.node.root - 48 + 48 = choice.node.root := UInt64.sub_add_cancel ..
  simp only [program, List.append_assoc]
  apply unlinkProgram_spec module_ env store params saved tail _ rfl need result head choice
    hGlobal hPrevious
  refine PackedHeader.program_spec module_ env _ _ _ _
    (choice.node.root - 48) choice.node.capacity rfl ?_ ?_ ?_ ?_ _ _ ?_
  · simp [frame, Locals.get, Nat.add_assoc, hPointer]
  · simp [frame, Locals.get, Nat.add_assoc]
  · rw [hBase]
    omega
  · rw [hBase, unlinkStore_pages]
    omega
  · simpa [wp_simp, frame, Nat.add_assoc, reused] using hNext

theorem search_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need capacity next : UInt64) (nodes : List FreeNode)
    (choice : FreeChoice) (hGlobal : initial.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt initial.mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (reused initial choice)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp module_ (FixedArraySearch.program start (program start) ++ rest) Q initial
      (frame params saved tail need 0 (freeHead nodes) capacity next 0) env := by
  apply fitProgram_spec_of module_ env initial _ params saved tail start hStart need capacity next
    nodes choice (program start) hList hTake _ Q rest hNext
  intro post continuation hContinuation
  obtain ⟨hRoot, hRoot32, hFit⟩ := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
  exact program_spec module_ env initial params saved tail start hStart need 0
    (freeHead nodes) choice hGlobal (choice_previous_bound hList hTake) hRoot
    (by omega) hFit post continuation hContinuation

#print axioms program_spec
#print axioms search_spec

end Project.ProofKit.PackedReuse
