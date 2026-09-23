import Project.Gpt2QuantizedCached.Entry.OutputGuard
import Project.Gpt2QuantizedCached.Entry.Release
import Project.Gpt2QuantizedCached.CachedHidden.FinishGuard

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit

def hiddenFailureCode : Program := failureResultCode (.localGet 31) ++ releaseCode 28

def normalizedFailureCode : Program := failureResultCode (.constI64 4) ++ releaseCode 28

def outputFailureCode : Program := failureResultCode (.constI64 4) ++
  releaseCode 73 ++ releaseCode 28 [73, 90, 93]

theorem emitted_entry : func59 = headerCode ++
    [.iff 0 0 (failureResultCode (.constI64 1)) inputBody] ++ returnCode := rfl

theorem emitted_input : inputBody = inputTestCode ++ ReadOnlyDisjunction.canonicalProgram ++
    [.iff 0 0 (failureResultCode (.constI64 3)) cacheBody] := rfl

theorem emitted_cache : cacheBody = cacheTestCode ++
    [.iff 0 0 (failureResultCode (.constI64 3)) acceptedBody] := rfl

theorem emitted_accepted : acceptedBody = hiddenCode ++ CachedHidden.failureTestCode 31 ++
    [.iff 0 0 hiddenFailureCode hiddenBody] ++ releaseCode 25 := rfl

theorem emitted_hiddenBody : hiddenBody = normalizedCode ++ finiteTestCode 42 45 768 ++
    ReadOnlyDisjunction.negateProgram ++ ReadOnlyDisjunction.canonicalProgram ++
    [.iff 0 0 normalizedFailureCode normalizedBody] ++ releaseCode 47 := rfl

theorem emitted_normalizedBody : normalizedBody = logitsCode ++ outputTestCode ++
    [.iff 0 0 outputFailureCode successResultCode] := rfl

end Project.Gpt2QuantizedCached.Entry
