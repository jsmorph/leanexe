import Verified.Wasi.CommandLeaves
import Verified.Wasi.ReadAllCommand
import Verified.Wasi.CommandCallSpec
import Verified.Wasi.CommandBindSpec
import Verified.Wasi.CommandBindValueSpec
import Verified.Wasi.CommandConditionalSpec
import Verified.Wasi.CommandLoopSpec
import Verified.Wasi.SysCommand

namespace Verified.Wasi

open Wasm

theorem Command.code_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFactsWith calls source target pure effects pool)
    (sourceHost : HostEnv Unit) (command : Command pureSigs effectSigs context result) :
    CommandCodeSpecWith calls source target pure effects pool command := by
  induction command with
  | unit => exact command_unit_spec_with
  | ret value => exact command_ret_spec_with facts sourceHost value
  | @bind context intermediate result first next firstSpec nextSpec =>
      cases intermediate with
      | unit => exact command_bind_unit_spec_with facts first next firstSpec nextSpec
      | value type => exact command_bind_value_spec_with facts sourceHost first next firstSpec nextSpec
  | ite condition yes no yesSpec noSpec =>
      exact command_ite_spec_with facts sourceHost yesSpec noSpec
  | call callee args => exact command_call_spec_with facts sourceHost callee args
  | read capacity => exact command_read_spec_with facts sourceHost capacity
  | readAll limit => exact command_readAll_spec_with facts sourceHost limit
  | write output bytes => exact command_write_spec_with facts sourceHost output bytes
  | exit status => exact command_exit_spec_with facts sourceHost status
  | loop count initial test step stepSpec =>
      exact command_loop_spec_with facts sourceHost stepSpec
  | sys operation form args inputs =>
    exact command_sys_spec_with facts sourceHost operation form args inputs

theorem Command.code_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFacts source target pure effects pool)
    (sourceHost : HostEnv Unit) (command : Command pureSigs effectSigs context result) :
    CommandCodeSpec source target pure effects pool command := by
  layout_instance Command.code_spec_with

end Verified.Wasi
