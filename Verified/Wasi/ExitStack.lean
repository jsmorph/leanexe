import Verified.Wasi.Relocation
import Verified.Wasi.HostSpec
import Verified.Wasi.WrapperCode
import LeanExe.TalosCompat
import Verified.LocalFrame
import Interpreter.Wasm.Wp.Call

namespace Verified.Wasi

open Wasm LeanExe.Wasi

theorem wp_exit_stack_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {target : Wasm.Module} {host : Host World}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {locals : Locals}
    {code : UInt64} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    (imports : target.imports = ABI.importsWith calls)
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (accepted : ∀ final,
      (observedHost host).exit initial.host (exitStatus code) final.host →
      GuestFrame initial final [] → Q (.Trap final exitTrap))
    (trapped : ∀ final message,
      (observedHost host).exitTrap initial.host (exitStatus code) message final.host →
      GuestFrame initial final [] → Q (.Trap final message)) :
    wp target (.wrapI64 :: .call 2 :: .unreachable :: rest) Q initial
      { locals with values := .i64 code :: values } targetHost := by
  simp only [wp_wrapI64_cons, wrap_toUInt32]
  refine wp_call_host_contract (id := 2) (imp := ABI.imports[2]!) (c := exitContract host)
    (by rw [imports]; exact ABI.importsWith_get calls (by decide)) valid (by rw [imports, ABI.importsWith_length]; omega)
    (hostSpecWith_exit host calls) ?_ ?_ ?_
  · intro returnedValues final contract
    exact False.elim (contract code.toUInt32 (by simp [ABI.importsWith_getElem?, ABI.importsWith_length, ABI.imports, ABI.exitType] <;> omega))
  · intro final message contract
    simp [ABI.importsWith_getElem?, ABI.importsWith_length, ABI.imports, ABI.exitType] at contract
    obtain ⟨frame, reply⟩ := contract code.toUInt32 rfl
    rcases reply with ⟨rfl, acceptedStep⟩ | rejectedStep
    · exact accepted final acceptedStep frame
    · exact trapped final message rejectedStep frame
  · intro final tag arguments contract
    exact False.elim (contract code.toUInt32 (by simp [ABI.importsWith_getElem?, ABI.importsWith_length, ABI.imports, ABI.exitType] <;> omega))

theorem wp_exit_stack {World : Type} {target : Wasm.Module} {host : Host World}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {locals : Locals}
    {code : UInt64} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (accepted : ∀ final,
      (observedHost host).exit initial.host (exitStatus code) final.host →
      GuestFrame initial final [] → Q (.Trap final exitTrap))
    (trapped : ∀ final message,
      (observedHost host).exitTrap initial.host (exitStatus code) message final.host →
      GuestFrame initial final [] → Q (.Trap final message)) :
    wp target (.wrapI64 :: .call 2 :: .unreachable :: rest) Q initial
      { locals with values := .i64 code :: values } targetHost := by
  layout_instance wp_exit_stack_with

end Verified.Wasi
