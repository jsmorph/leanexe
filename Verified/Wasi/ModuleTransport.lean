import Verified.Wasi.Module
import Verified.Wasi.PureTransportSpecs

namespace Verified.Wasi.Module

open Wasm

theorem run_pure {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    (fuel : Nat) (initial : Store World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    run fuel (assemble source extra) (pureIndex index) initial args targetHost =
      PureTransport.liftResult initial.host
        (run fuel source index (PureTransport.erase initial) args sourceHost) := by
  simpa only [pureIndex, PureTransport.restore_erase] using
    PureTransport.entry_transport (layout source extra hImports) profile hIndex fuel
      (PureTransport.erase initial) initial.host args sourceHost targetHost

theorem runs_pure {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {aborts : Bool} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : Runs aborts sourceHost source index (PureTransport.erase initial) args P) :
    Runs aborts targetHost (assemble source extra) (pureIndex index) initial args
      (fun final values => P (PureTransport.erase final) values ∧ final.host = initial.host) := by
  simpa only [pureIndex, PureTransport.restore_erase] using
    PureTransport.runs_transport (layout source extra hImports) profile hIndex h initial.host

theorem terminatesWith_pure {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith sourceHost source index (PureTransport.erase initial) args P) :
    TerminatesWith targetHost (assemble source extra) (pureIndex index) initial args
      (fun final values => P (PureTransport.erase final) values ∧ final.host = initial.host) := by
  simpa only [pureIndex, PureTransport.restore_erase] using
    PureTransport.terminatesWith_transport (layout source extra hImports) profile hIndex h initial.host

end Verified.Wasi.Module
