import Project.WGSL.Precision

def main (args : List String) : IO Unit := do
  let mode :: inputs := args | throw (IO.userError "expected promote or demote and decimal words")
  unless mode == "promote" || mode == "demote" do throw (IO.userError "unknown conversion")
  for input in inputs do
    let some n := input.toNat? | throw (IO.userError "invalid decimal word")
    if mode == "promote" then
      if n ≥ 2^32 then throw (IO.userError "binary32 word out of range")
      let word := UInt32.ofNat n
      unless Wasm.IEEE32.isFinite word do throw (IO.userError "nonfinite binary32 input")
      IO.println (Project.WGSL.Precision.promote word).toNat
    else
      if n ≥ 2^64 then throw (IO.userError "binary64 word out of range")
      let word := UInt64.ofNat n
      unless Wasm.IEEE64.isFinite word do throw (IO.userError "nonfinite binary64 input")
      IO.println (Project.WGSL.Precision.demote word).toNat
