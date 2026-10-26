import Verified.Wasi.ScriptHostABI

namespace Verified.Wasi.ScriptHost

open Wasm

def env (target : Wasm.Module) : HostEnv (Observed World) :=
  OracleHost.env oracle sourceHost oracle_sound target

theorem env_satisfies (target : Wasm.Module) (imports : target.imports = ABI.imports) :
    (env target).Satisfies target (hostSpec sourceHost) :=
  OracleHost.env_satisfies oracle sourceHost oracle_sound target imports

end Verified.Wasi.ScriptHost
