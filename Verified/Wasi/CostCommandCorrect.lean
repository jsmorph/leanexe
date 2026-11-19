import Verified.Wasi.CostLeaves
import Verified.Wasi.ReadAllCommand
import Verified.Wasi.CostCallSpec
import Verified.Wasi.CostBindUnit
import Verified.Wasi.CostBindValue
import Verified.Wasi.CostConditionalSpec
import Verified.Wasi.CostLoopSpec
import Verified.Wasi.SysCommand
import Verified.Wasi.ReadCommand
import Verified.Wasi.CommandLetPair

namespace Verified.Wasi

open Wasm

theorem Command.cost_code_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (effectCalls : CostEffectCallsWith calls source target pure program pool) (sourceHost : HostEnv Unit)
    (command : Command pureSigs effectSigs context result) :
    CostCommandCodeSpecWith calls source target pure program pool command := by
  induction command with
  | unit => exact cost_command_unit_spec_with
  | ret value => exact cost_command_ret_spec_with facts sourceHost value
  | @bind context intermediate result first next firstSpec nextSpec =>
      cases intermediate with
      | unit => exact cost_command_bind_unit_spec_with facts first next firstSpec nextSpec
      | value type => exact cost_command_bind_value_spec_with facts sourceHost first next firstSpec nextSpec
  | ite condition yes no yesSpec noSpec =>
      exact cost_command_ite_spec_with facts sourceHost yesSpec noSpec
  | call callee args => exact cost_command_call_spec_with facts effectCalls sourceHost callee args
  | read buffer start count => exact cost_command_read_spec_with facts sourceHost buffer start count
  | readAll limit => exact cost_command_readAll_spec_with facts sourceHost limit
  | write output buffer start count =>
    exact cost_command_write_spec_with facts sourceHost output buffer start count
  | exit status => exact cost_command_exit_spec_with facts sourceHost status
  | loop count initial test step stepSpec => exact cost_command_loop_spec_with facts sourceHost stepSpec
  | sys operation form args inputs buffers =>
    exact cost_command_sys_spec_with facts sourceHost operation form args inputs buffers
  | letPair pair body bodySpec =>
    exact cost_command_letPair_spec_with facts sourceHost pair body bodySpec

theorem Command.cost_code_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (calls : CostEffectCalls source target pure program pool) (sourceHost : HostEnv Unit)
    (command : Command pureSigs effectSigs context result) :
    CostCommandCodeSpec source target pure program pool command := by
  layout_instance Command.cost_code_spec_with

end Verified.Wasi
