module

public import Verified.Wasi.CostCodeSpec
public import Verified.Wasi.CompilerFacts
public import Verified.Wasi.WriteCommand

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem cost_command_write_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit)
    (output : Output) (buffer : Var context .bytes) (start count : Var context .word) :
    CostCommandCodeSpecWith calls source target pure program pool
      (.write output buffer start count) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ _ _ vars at_ _ scratch _ _ _ ready _ _ _
  have fragment := ready.1 _ (List.mem_singleton_self _)
  obtain ⟨typeIndex, lookup⟩ := facts.write_function output
  exact wp_write_command_with (sourceHost := sourceHost) facts.runtime facts.layout facts.profile
    facts.imports lookup valid at_ vars scratch fragment.1 fragment.2
    (fun result finalHeap final trace execution after topEq =>
      CostCommandResult.returned (result := .value (.elem (.prod .word .word)))
        (result.errno, result.count) finalHeap final locals
        [.i64 result.errno, .i64 result.count] trace 0 true (.write execution) after
        (fun _ => by rw [topEq]; exact Nat.le_add_right _ _))
    (fun final message trace execution =>
      .trapped final message (.terminal final trace (.trapped message) message execution rfl))

theorem cost_command_write_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit)
    (output : Output) (buffer : Var context .bytes) (start count : Var context .word) :
    CostCommandCodeSpec source target pure program pool (.write output buffer start count) := by
  layout_instance cost_command_write_spec_with

end Verified.Wasi
