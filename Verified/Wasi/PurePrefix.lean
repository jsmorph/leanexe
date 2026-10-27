import Verified.Wasi.PureTransportSpecs
import LeanExe.ProofKit.Sequencing

namespace Verified.Wasi.PureTransport

open Wasm

theorem wp_prefix {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {code : Program} (hForm : Encoding.ProgramForm code)
    (hClosed : Relocation.programClosed source.funcs.length code = true)
    {initial : Store Unit} {locals : Locals} {P : Assertion Unit} {Q : Assertion World}
    {rest : Program} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    (world : World) (h : wp source code P initial locals sourceHost)
    (hPost : ∀ continuation, P continuation →
      Then targetHost target rest Q (liftContinuation world continuation)) :
    wp target (Relocation.program code ++ rest) Q
      (restore world initial) locals targetHost :=
  wp_append (wp_transport layout profile hForm hClosed world h hPost)

end Verified.Wasi.PureTransport
