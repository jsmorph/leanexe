import Examples.TreeLookup.Spec
import Examples.TreeLookup.Samples
import Examples.Host

/-! The module cases of `treeLookup`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.TreeLookup

open Examples.Host

def cases : IO Unit := do
  for l in Examples.Host.lines "treeLookup" "compute" Examples.TreeLookup.expected
      Examples.TreeLookup.samples do
    IO.println l

end Examples.TreeLookup
