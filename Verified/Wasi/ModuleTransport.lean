import Verified.Wasi.Module
import Verified.Wasi.PureTransportSpecs

namespace Verified.Wasi.Module

open Wasm

theorem run_pure_with {calls : List LeanExe.Wasi.Call}
    {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    (fuel : Nat) (initial : Store World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    run fuel (assembleWith calls source extra) (pureIndexWith calls index) initial args targetHost =
      PureTransport.liftResult initial.host
        (run fuel source index (PureTransport.erase initial) args sourceHost) := by
  simpa only [pureIndexWith, PureTransport.restore_erase] using
    PureTransport.entry_transport_with (layout_with source extra hImports) profile hIndex fuel
      (PureTransport.erase initial) initial.host args sourceHost targetHost

theorem run_pure {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    (fuel : Nat) (initial : Store World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    run fuel (assemble source extra) (pureIndex index) initial args targetHost =
      PureTransport.liftResult initial.host
        (run fuel source index (PureTransport.erase initial) args sourceHost) := by
  layout_instance run_pure_with

theorem runs_pure_with {calls : List LeanExe.Wasi.Call}
    {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {aborts : Bool} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : Runs aborts sourceHost source index (PureTransport.erase initial) args P) :
    Runs aborts targetHost (assembleWith calls source extra) (pureIndexWith calls index) initial args
      (fun final values => P (PureTransport.erase final) values ∧ final.host = initial.host) := by
  simpa only [pureIndexWith, PureTransport.restore_erase] using
    PureTransport.runs_transport_with (layout_with source extra hImports) profile hIndex h initial.host

theorem runs_pure {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {aborts : Bool} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : Runs aborts sourceHost source index (PureTransport.erase initial) args P) :
    Runs aborts targetHost (assemble source extra) (pureIndex index) initial args
      (fun final values => P (PureTransport.erase final) values ∧ final.host = initial.host) := by
  layout_instance runs_pure_with

theorem terminatesWith_pure_with {calls : List LeanExe.Wasi.Call}
    {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith sourceHost source index (PureTransport.erase initial) args P) :
    TerminatesWith targetHost (assembleWith calls source extra) (pureIndexWith calls index) initial args
      (fun final values => P (PureTransport.erase final) values ∧ final.host = initial.host) := by
  simpa only [pureIndexWith, PureTransport.restore_erase] using
    PureTransport.terminatesWith_transport_with (layout_with source extra hImports) profile hIndex h initial.host

theorem terminatesWith_pure {World : Type} (source : Wasm.Module) (extra : Extension)
    (hImports : source.imports = []) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith sourceHost source index (PureTransport.erase initial) args P) :
    TerminatesWith targetHost (assemble source extra) (pureIndex index) initial args
      (fun final values => P (PureTransport.erase final) values ∧ final.host = initial.host) := by
  layout_instance terminatesWith_pure_with

end Verified.Wasi.Module
