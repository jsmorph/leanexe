import Project.ClobLimit.InternalInitialization
import Project.ClobLimit.RunMatchResult

/-!
# Historical matcher instruction proofs

These checked, explicit instruction fragments retain the earlier 64-local,
bump-only matcher as worked examples. They include its branch allocations,
copy loops, source progress, decreasing loop invariant, and result extraction.
They are not a decomposition or correctness claim for the current generated
function 17. The current function is proved by `HeapCorrect.spec`, transported
from the shared release-aware matcher. `HeapRunMatch.func18_correct` proves its
wrapper, and `LimitCorrect.func21_correct` proves the public limit operation.
-/
