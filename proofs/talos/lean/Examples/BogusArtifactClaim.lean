import Examples.KernelUnsoundness
import Project.LebU32.Program
import Project.Common

/-!
# A false claim about a compiled artifact, accepted by the proof gate

`Project.LebU32.Spec` proves that the compiled LEB128 encoder returns
exactly the bytes of `lebList 10 n`.  For `n = 300` those bytes are
`0xac 0x02`, and the export returns length `2`.

The theorem below claims length `1`, in the shape of the real one, and
the kernel accepts it because its proof consumes the `False` derived in
`Examples.KernelUnsoundness`.  Running the artifact refutes it:
`test/kernel_unsoundness_exhibit.js` executes the same WASM the theorem
describes and prints length `2` with bytes `0xac 0x02`.

That contrast is the exhibit.  A proof gate alone accepts this file; the
proof gate together with an execution gate does not.  The protection has
a limit worth stating: a false theorem about behavior no test exercises
survives both gates.
-/

namespace Examples.BogusArtifactClaim

open Wasm Project.LebU32

/-- False: the artifact returns length `2` and bytes `0xac 0x02` for `300`. -/
theorem u32lebU64_bogus (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      [.i64 300]
      (fun st' vs =>
        vs = [.i64 1, .i64 0] ∧
        st'.mem.bytes 0 = 0) :=
  False.elim Examples.KernelUnsoundness.derived_false

#print axioms u32lebU64_bogus

end Examples.BogusArtifactClaim
