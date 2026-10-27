import Verified.Wasi.CostLeaves
import Verified.Wasi.CostCallSpec
import Verified.Wasi.CostBindUnit
import Verified.Wasi.CostBindValue
import Verified.Wasi.CostConditionalSpec
import Verified.Wasi.CostLoopSpec

namespace Verified.Wasi

open Wasm

theorem Command.cost_code_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (calls : CostEffectCalls source target pure program pool) (sourceHost : HostEnv Unit)
    (command : Command pureSigs effectSigs context result) :
    CostCommandCodeSpec source target pure program pool command := by
  induction command with
  | unit => exact cost_command_unit_spec
  | ret value => exact cost_command_ret_spec facts sourceHost value
  | @bind context intermediate result first next firstSpec nextSpec =>
      cases intermediate with
      | unit => exact cost_command_bind_unit_spec facts first next firstSpec nextSpec
      | value type => exact cost_command_bind_value_spec facts sourceHost first next firstSpec nextSpec
  | ite condition yes no yesSpec noSpec =>
      exact cost_command_ite_spec facts sourceHost yesSpec noSpec
  | call callee args => exact cost_command_call_spec facts calls sourceHost callee args
  | read capacity => exact cost_command_read_spec facts sourceHost capacity
  | write output bytes => exact cost_command_write_spec facts sourceHost output bytes
  | exit status => exact cost_command_exit_spec facts sourceHost status
  | loop count initial test step stepSpec => exact cost_command_loop_spec facts sourceHost stepSpec

end Verified.Wasi
