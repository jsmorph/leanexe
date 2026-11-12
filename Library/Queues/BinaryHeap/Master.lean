import Library.Queues.BinaryHeap.Compiled
import Verified.Master

namespace Library.Queues.BinaryHeap

/-- The export `heapQueue`, called on an array of words read as pairs of an operation code and a
value, returns the outputs of `runOps`, a queue kept as a list, on those operations from the empty
queue: code 0 inserts the value, and any other code removes and outputs the largest word of a
nonempty queue. -/
theorem heapQueue_master :
    Verified.Master compiled.module compiled.tables "heapQueue" compiled.heapQueue.bound
      (fun _ => True)
      (fun (xs : Array UInt64) ys => ys = (runOps
        ((List.range (xs.size / 2)).map fun i => (xs[2 * i]!, xs[2 * i + 1]!)) [] []).toArray) :=
  .of_trapFree (.ofA compiled.heapQueue.trapFree) nofun heapQueue_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => heapQueue_eq xs hxs.values.size_lt

#print axioms heapQueue_master

end Library.Queues.BinaryHeap
