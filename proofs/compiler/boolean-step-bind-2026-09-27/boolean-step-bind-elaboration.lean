import LeanExe.Extract.ScalarFunc
namespace BooleanStepBindElaboration

def joinedWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← if flag then pure (i.toUInt64 + seed) else pure (seed + 1)
    flag := n % 3 == 0
    if flag then break
  return flag

end BooleanStepBindElaboration
set_option pp.explicit true in
run_elab do
  let env ← Lean.getEnv
  let some info := env.find? `BooleanStepBindElaboration.joinedWord | throwError "missing"
  let some value := info.value? | throwError "missing"
  Lean.logInfo m!"{value}"
