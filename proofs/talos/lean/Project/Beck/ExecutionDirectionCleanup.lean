import Project.Beck.ExecutionDirectionAssembly
import Project.Beck.ExecutionReleasePlan

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem ownedRoots_ne {heap : Heap} {store : Store Unit} {left right : FreeNode} {leftWords rightWords : Array UInt64}
    (leftOwned : heap.OwnsWords store left leftWords) (rightOwned : heap.OwnsWords store right rightWords)
    (separated : regionsDisjoint left.region right.region) : left.root ≠ right.root := by
  intro equal
  have root := leftOwned.buffer.rootBound
  have rightRoot := rightOwned.buffer.rootBound
  have capacity := leftOwned.buffer.capacity
  have rightCapacity := rightOwned.buffer.capacity
  simp only [regionsDisjoint, FreeNode.region, equal] at separated
  rw [equal] at root
  omega

def directionCleanupEntries (matrix ro rp co cp : FreeNode) (words : Array UInt64) : List ReleaseEntry :=
  [⟨31, [96], cp, #[]⟩, ⟨30, [31, 96], co, #[]⟩, ⟨29, [30, 31, 96], rp, #[]⟩,
    ⟨28, [29, 30, 31, 96], ro, #[]⟩, ⟨18, [96], matrix, words⟩]

set_option maxRecDepth 4096 in
theorem direction_cleanup_shape (matrix ro rp co cp : FreeNode) (words : Array UInt64) :
    func30.drop 289 = releasePlanProgram (directionCleanupEntries matrix ro rp co cp words) ++ [.localGet 96, .localGet 97] := rfl

theorem directionCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (params locals : List Value) (matrixNode sro srp sco scp resultNode : FreeNode) (matrix resultWords : Array UInt64)
    (basis : Basis) (ro rp co cp : UInt64)
    (paramsSize : params.length = 9)
    (state : DirectionSearchLocals locals matrixNode.root sro.root srp.root sco.root scp.root basis ro rp co cp)
    (resultRead : locals[87]? = some (.i64 resultNode.root)) (pointerRead : locals[88]? = some (.i64 resultNode.root))
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (matrixOwned : heap.OwnsWords middle matrixNode matrix) (resultOwned : heap.OwnsWords middle resultNode resultWords)
    (seed : DirectionSeed original heap middle sro srp sco scp)
    (preserved : original.Frame initial heap middle) (matrixFresh : FreshFor original matrixNode)
    (matrixRO : regionsDisjoint matrixNode.region sro.region) (matrixRP : regionsDisjoint matrixNode.region srp.region)
    (matrixCO : regionsDisjoint matrixNode.region sco.region) (matrixCP : regionsDisjoint matrixNode.region scp.region)
    (resultSeparated : ∀ entry ∈ directionCleanupEntries matrixNode sro srp sco scp matrix, regionsDisjoint entry.node.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final { params := params, locals := locals, values := [.i64 resultNode.root, .i64 resultNode.root] })) :
    wp Project.Beck.«module» (func30.drop 289) Q middle { params := params, locals := locals } env := by
  let frame : Locals := { params := params, locals := locals }
  have r18 : frame.get 18 = some (.i64 matrixNode.root) := by
    simpa only [frame, Locals.get, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.matrixOriginal
  have r28 : frame.get 28 = some (.i64 sro.root) := by
    simpa only [frame, Locals.get, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.seedRowOwner
  have r29 : frame.get 29 = some (.i64 srp.root) := by
    simpa only [frame, Locals.get, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.seedRowPointer
  have r30 : frame.get 30 = some (.i64 sco.root) := by
    simpa only [frame, Locals.get, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.seedColumnOwner
  have r31 : frame.get 31 = some (.i64 scp.root) := by
    simpa only [frame, Locals.get, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.seedColumnPointer
  have r96 : frame.get 96 = some (.i64 resultNode.root) := by
    simpa only [frame, Locals.get, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using resultRead
  have allOwned : ∀ entry ∈ directionCleanupEntries matrixNode sro srp sco scp matrix, heap.OwnsWords middle entry.node entry.words := by
    intro entry member
    simp only [directionCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact seed.columnPointer
    · exact seed.columnOwner
    · exact seed.rowPointer
    · exact seed.rowOwner
    · exact matrixOwned
  have resultDifferent : ∀ entry ∈ directionCleanupEntries matrixNode sro srp sco scp matrix, entry.node.root ≠ resultNode.root :=
    fun entry member => ownedRoots_ne (allOwned entry member) resultOwned (resultSeparated entry member)
  rw [direction_cleanup_shape matrixNode sro srp sco scp matrix]
  refine Sequence.wp_append (P := fun store after => wp Project.Beck.«module» [.localGet 96, .localGet 97] Q store after env) ?_ (fun _ _ h => h)
  apply releasePlan_exact env initial middle original heap frame (directionCleanupEntries matrixNode sro srp sco scp matrix)
    resultNode resultWords remaining pageLimit valid allOwned resultOwned preserved
  · intro entry member
    simp only [directionCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact seed.columnPointerFresh
    · exact seed.columnOwnerFresh
    · exact seed.rowPointerFresh
    · exact seed.rowOwnerFresh
    · exact matrixFresh
  · simp [directionCleanupEntries, List.pairwise_cons,
      regionsDisjoint_symm seed.co_cp, regionsDisjoint_symm seed.rp_cp, regionsDisjoint_symm seed.ro_cp,
      regionsDisjoint_symm seed.rp_co, regionsDisjoint_symm seed.ro_co, regionsDisjoint_symm seed.ro_rp,
      regionsDisjoint_symm matrixRO, regionsDisjoint_symm matrixRP, regionsDisjoint_symm matrixCO, regionsDisjoint_symm matrixCP]
  · exact resultSeparated
  · exact budget
  · rfl
  · intro entry member
    simp only [directionCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact r31
    · exact r30
    · exact r29
    · exact r28
    · exact r18
  · intro entry member other avoided
    have resultNe := resultDifferent entry member
    simp only [directionCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp only [List.mem_singleton] at avoided
      subst other
      exact ⟨_, r96, resultNe⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at avoided
      rcases avoided with rfl | rfl
      · exact ⟨_, r31, ownedRoots_ne seed.columnOwner seed.columnPointer seed.co_cp⟩
      · exact ⟨_, r96, resultNe⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at avoided
      rcases avoided with rfl | rfl | rfl
      · exact ⟨_, r30, ownedRoots_ne seed.rowPointer seed.columnOwner seed.rp_co⟩
      · exact ⟨_, r31, ownedRoots_ne seed.rowPointer seed.columnPointer seed.rp_cp⟩
      · exact ⟨_, r96, resultNe⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at avoided
      rcases avoided with rfl | rfl | rfl | rfl
      · exact ⟨_, r29, ownedRoots_ne seed.rowOwner seed.rowPointer seed.ro_rp⟩
      · exact ⟨_, r30, ownedRoots_ne seed.rowOwner seed.columnOwner seed.ro_co⟩
      · exact ⟨_, r31, ownedRoots_ne seed.rowOwner seed.columnPointer seed.ro_cp⟩
      · exact ⟨_, r96, resultNe⟩
    · simp only [List.mem_singleton] at avoided
      subst other
      exact ⟨_, r96, resultNe⟩
  · intro final finalHeap finalValid finalOwned finalFrame finalBudget
    dsimp only [Sequence.Fallthrough]
    wp_run [frame, paramsSize, state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, resultRead, pointerRead, reduceIte]
    exact next final finalHeap finalValid finalOwned finalFrame finalBudget

#print axioms directionCleanup_exact

end Project.Beck.Execution
