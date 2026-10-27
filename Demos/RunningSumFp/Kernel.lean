import Demos.RunningSumFp.ArithmeticProof
import Demos.RunningSumFp.StreamView

namespace Demos.RunningSumFp

def kernelSpec : StreamFold.KernelSpec lineKernel where
  Good := fun _ => True
  Room := fun _ line => line.size < 2 ^ 32
  lineFits := fun room => lt_trans room (by decide)
  accepted := fun _ _ _ => ⟨True.intro, render_nonempty _⟩
  outputBound := fun _ _ _ => render_size_bound _

end Demos.RunningSumFp
