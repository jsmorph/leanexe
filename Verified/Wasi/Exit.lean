import Verified.Wasi.HostSpec
import Verified.Wasi.WrapperCode
import LeanExe.TalosCompat
import Verified.LocalFrame
import Interpreter.Wasm.Wp.Call

namespace Verified.Wasi

open Wasm LeanExe.Wasi

theorem wp_exit {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {store : Store (Observed World)} {s : Locals}
    {code : UInt64} {codeSlot : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.imports) (hHost : env.Satisfies m (hostSpec host))
    (hCode : s.get codeSlot = some (.i64 code))
    (hExit : ∀ final,
      (observedHost host).exit store.host (exitStatus code) final.host →
      GuestFrame store final [] → Q (.Trap final exitTrap)) :
    wp m (exitCode codeSlot ++ rest) Q store s env := by
  simp only [exitCode, List.cons_append, List.nil_append, wp_localGet_cons, hCode,
    wp_wrapI64_cons, wrap_toUInt32]
  refine wp_call_host_contract (id := 2) (imp := ABI.imports[2]!) (c := exitContract host)
    (by simp [hImports, ABI.imports]) hHost (by simp [hImports, ABI.imports])
    (hostSpec_exit host) ?_ ?_ ?_
  · intro values final hContract
    obtain ⟨after, hEq, _, _⟩ := hContract code.toUInt32 (by simp [ABI.imports, ABI.exitType])
    cases hEq
  · intro final message hContract
    obtain ⟨after, hEq, hStep, hFrame⟩ :=
      hContract code.toUInt32 (by simp [ABI.imports, ABI.exitType])
    cases hEq
    exact hExit final hStep hFrame
  · intro final tag arguments hContract
    obtain ⟨after, hEq, _, _⟩ := hContract code.toUInt32 (by simp [ABI.imports, ABI.exitType])
    cases hEq

end Verified.Wasi
