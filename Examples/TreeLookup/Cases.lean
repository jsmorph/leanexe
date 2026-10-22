import Examples.TreeLookup.Spec
import Examples.TreeLookup.Samples
import TestSupport.Host

/-! The module cases of `treeLookup`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.TreeLookup

open TestSupport.Host

def cases : IO Unit := do
  for l in TestSupport.Host.lines "treeLookup" "compute" Examples.TreeLookup.expected
      Examples.TreeLookup.samples do
    IO.println l

end Examples.TreeLookup
