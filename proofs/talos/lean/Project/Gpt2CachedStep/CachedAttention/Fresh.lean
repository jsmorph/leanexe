import Project.Gpt2CachedStep.CachedAttention.Resources
import Project.ProofKit.PackedFresh

namespace Project.Gpt2CachedStep.CachedAttention
open Project.EulerRiemann.Execution

theorem outputNode_fresh {heap : Heap} {position pageCapacity : Nat}
    (h : Resources heap position pageCapacity) : heap.FreshNode (outputNode heap position) := by
  intro lower upper hProtected
  have hScores := hProtected.allocated (scoresNeed position) (fun fit => (h.scores fit).1.le)
  have hMaxima := hScores.allocated maximaNeed (fun fit => (h.maxima fit).1.le)
  have hExponentials := hMaxima.allocated (scoresNeed position) (fun fit => (h.exponentials fit).1.le)
  have hSums := hExponentials.allocated maximaNeed (fun fit => (h.sums fit).1.le)
  have hProbabilities := hSums.allocated (scoresNeed position) (fun fit => (h.probabilities fit).1.le)
  exact hProbabilities.allocated_disjoint mixedNeed (fun fit => (h.output fit).1.le)

#print axioms outputNode_fresh

end Project.Gpt2CachedStep.CachedAttention
