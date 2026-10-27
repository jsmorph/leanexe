import Verified.Wasi.CommandLeaves
import Verified.Wasi.CommandCallSpec
import Verified.Wasi.CommandBindSpec
import Verified.Wasi.CommandBindValueSpec
import Verified.Wasi.CommandConditionalSpec
import Verified.Wasi.CommandLoopSpec

namespace Verified.Wasi

open Wasm

theorem Command.code_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFacts source target pure effects pool)
    (sourceHost : HostEnv Unit) (command : Command pureSigs effectSigs context result) :
    CommandCodeSpec source target pure effects pool command := by
  induction command with
  | unit => exact command_unit_spec
  | ret value => exact command_ret_spec facts sourceHost value
  | @bind context intermediate result first next firstSpec nextSpec =>
      cases intermediate with
      | unit => exact command_bind_unit_spec facts first next firstSpec nextSpec
      | value type => exact command_bind_value_spec facts sourceHost first next firstSpec nextSpec
  | ite condition yes no yesSpec noSpec =>
      exact command_ite_spec facts sourceHost yesSpec noSpec
  | call callee args => exact command_call_spec facts sourceHost callee args
  | read capacity => exact command_read_spec facts sourceHost capacity
  | write output bytes => exact command_write_spec facts sourceHost output bytes
  | exit status => exact command_exit_spec facts sourceHost status
  | loop count initial test step stepSpec =>
      exact command_loop_spec facts sourceHost stepSpec

end Verified.Wasi
