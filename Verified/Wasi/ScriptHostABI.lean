import Verified.Wasi.ScriptHostModel
import Verified.Wasi.OracleHost

namespace Verified.Wasi.ScriptHost

open LeanExe.Wasi

/-- The scripted world's replies: its queues, links, and policies decide every request. -/
def oracle : OracleHost.Oracle World := ⟨readStep, writeStep, exitStep⟩

theorem oracle_sound : oracle.Sound sourceHost where
  read _ _ := rfl
  write _ _ _ := rfl
  exit _ _ _ step := step
  exitTrap _ _ _ _ step := step

end Verified.Wasi.ScriptHost
