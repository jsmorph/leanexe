import Project.Beck.ExecutionDirectionEmpty

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem FreshFor.separated {heap : Heap} {store : Store Unit} {old node : FreeNode} {words : Array UInt64}
    (fresh : FreshFor heap node) (owned : heap.OwnsWords store old words) (root : 48 ≤ node.root.toNat) :
    regionsDisjoint old.region node.region := by
  have separation := fresh _ _ owned.protects
  have oldRoot := owned.buffer.rootBound
  simp only [regionsDisjoint, FreeNode.region]
  omega

theorem FreshFor.original {original current : Heap} {initial middle : Store Unit} {node : FreeNode}
    (fresh : FreshFor current node) (preserved : original.Frame initial current middle) : FreshFor original node :=
  fun lower upper protectedRegion => fresh lower upper (preserved.protects lower upper protectedRegion)

structure DirectionSeed (original heap : Heap) (store : Store Unit) (ro rp co cp : FreeNode) : Prop where
  rowOwner : heap.OwnsWords store ro #[]
  rowPointer : heap.OwnsWords store rp #[]
  columnOwner : heap.OwnsWords store co #[]
  columnPointer : heap.OwnsWords store cp #[]
  rowOwnerFresh : FreshFor original ro
  rowPointerFresh : FreshFor original rp
  columnOwnerFresh : FreshFor original co
  columnPointerFresh : FreshFor original cp
  ro_rp : regionsDisjoint ro.region rp.region
  ro_co : regionsDisjoint ro.region co.region
  ro_cp : regionsDisjoint ro.region cp.region
  rp_co : regionsDisjoint rp.region co.region
  rp_cp : regionsDisjoint rp.region cp.region
  co_cp : regionsDisjoint co.region cp.region

def directionSeedSaved (saved : List Value) (ro rp co cp : UInt64) : List Value :=
  directionEmptySaved (directionEmptySaved (directionEmptySaved (directionEmptySaved saved 17 19 ro) 17 20 rp) 18 21 co) 18 22 cp

set_option maxRecDepth 4096 in
theorem direction_seed_shape : (func30.drop 42).take 172 =
    directionEmptyProgram 17 19 ++ (directionEmptyProgram 17 20 ++
      (directionEmptyProgram 18 21 ++ directionEmptyProgram 18 22)) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionSeed_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (paramsSize : params.length = 9) (savedSize : saved.length = 93)
    (tailSize : tail.length = 13) (need previous current capacity afterNode result : UInt64)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (budget : OutputBudget initial heap (224 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final finalHeap ro rp co cp, finalHeap.At final → heap.Frame initial finalHeap final →
      DirectionSeed heap finalHeap final ro rp co cp → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      wp Project.Beck.«module» rest Q final
        (FixedArraySearch.frame params (directionSeedSaved saved ro.root rp.root co.root cp.root) tail
          8 previous current capacity afterNode cp.root) env) :
    wp Project.Beck.«module» ((func30.drop 42).take 172 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail need previous current capacity afterNode result) env := by
  rw [direction_seed_shape]
  simp only [List.append_assoc]
  apply directionEmpty_exact env initial heap params saved tail paramsSize savedSize tailSize need previous current capacity afterNode result
    17 19 (by decide) (by decide) (168 + remaining) pageLimit valid (by simpa only [← Nat.add_assoc] using budget)
  dsimp only
  intro valid1 owned1 frame1 fresh1 budget1 previous1 current1 capacity1 after1
  apply directionEmpty_exact env _ _ params _ tail paramsSize (by simp [directionEmptySaved, savedSize]) tailSize 8 previous1 current1 capacity1 after1 _
    17 20 (by decide) (by decide) (112 + remaining) pageLimit valid1 (by simpa only [← Nat.add_assoc] using budget1)
  dsimp only
  intro valid2 owned2 frame2 fresh2 budget2 previous2 current2 capacity2 after2
  apply directionEmpty_exact env _ _ params _ tail paramsSize (by simp [directionEmptySaved, savedSize]) tailSize 8 previous2 current2 capacity2 after2 _
    18 21 (by decide) (by decide) (56 + remaining) pageLimit valid2 (by simpa only [← Nat.add_assoc] using budget2)
  dsimp only
  intro valid3 owned3 frame3 fresh3 budget3 previous3 current3 capacity3 after3
  apply directionEmpty_exact env _ _ params _ tail paramsSize (by simp [directionEmptySaved, savedSize]) tailSize 8 previous3 current3 capacity3 after3 _
    18 22 (by decide) (by decide) remaining pageLimit valid3 budget3
  dsimp only
  intro valid4 owned4 frame4 fresh4 budget4 previous4 current4 capacity4 after4
  apply finish _ _ _ _ _ _ valid4 (frame1.trans (frame2.trans (frame3.trans frame4))) _ budget4 previous4 current4 capacity4 after4
  exact ⟨(frame2.trans (frame3.trans frame4)).ownsWords valid4 owned1,
    (frame3.trans frame4).ownsWords valid4 owned2, frame4.ownsWords valid4 owned3, owned4,
    fresh1, fresh2.original frame1, fresh3.original (frame1.trans frame2), fresh4.original (frame1.trans (frame2.trans frame3)),
    fresh2.separated owned1 owned2.buffer.rootBound,
    fresh3.separated (frame2.ownsWords valid2 owned1) owned3.buffer.rootBound,
    fresh4.separated ((frame2.trans frame3).ownsWords valid3 owned1) owned4.buffer.rootBound,
    fresh3.separated owned2 owned3.buffer.rootBound,
    fresh4.separated (frame3.ownsWords valid3 owned2) owned4.buffer.rootBound,
    fresh4.separated owned3 owned4.buffer.rootBound⟩

#print axioms directionSeed_exact

end Project.Beck.Execution
