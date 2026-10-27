import Verified.Wasi.ExitStack

namespace Verified.Wasi

open Wasm LeanExe.Wasi

theorem wp_exit {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {store : Store (Observed World)} {s : Locals}
    {code : UInt64} {codeSlot : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.imports) (hHost : env.Satisfies m (hostSpec host))
    (hCode : s.get codeSlot = some (.i64 code))
    (hExit : ∀ final,
      (observedHost host).exit store.host (exitStatus code) final.host →
      GuestFrame store final [] → Q (.Trap final exitTrap))
    (hTrap : ∀ final message,
      (observedHost host).exitTrap store.host (exitStatus code) message final.host →
      GuestFrame store final [] → Q (.Trap final message)) :
    wp m (exitCode codeSlot ++ rest) Q store s env := by
  simp only [exitCode, List.cons_append, List.nil_append, wp_localGet_cons, hCode]
  exact wp_exit_stack (target := m) (targetHost := env) hImports hHost hExit hTrap

end Verified.Wasi
