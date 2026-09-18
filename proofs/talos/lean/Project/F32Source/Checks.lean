import Project.ProofKit.F32Source

namespace Project.F32Source.Checks
open Project.ProofKit

def edgeWords : Array UInt32 := #[
  0, 0x80000000, 1, 0x80000001, 0x007FFFFF, 0x807FFFFF,
  0x00800000, 0x80800000, 0x00800001, 0x80800001,
  0x3EFFFFFF, 0x3F000000, 0x3F000001, 0x3F7FFFFF, 0x3F800000, 0x3F800001,
  0xBF800000, 0x7F7FFFFF, 0xFF7FFFFF, 0x7F800000, 0xFF800000,
  0x7FC00000, 0x7F800001, 0xFFC01234]

def checkPair (left right : UInt32) : IO Unit := do
  for (name, source, talos) in [
      ("add", F32Source.add left right, Wasm.IEEE32.add left right),
      ("sub", F32Source.sub left right, Wasm.IEEE32.sub left right),
      ("mul", F32Source.mul left right, Wasm.IEEE32.mul left right),
      ("div", F32Source.div left right, Wasm.IEEE32.div left right),
      ("sqrt", F32Source.sqrt left, Wasm.IEEE32.sqrt left)] do
    unless source == talos do
      throw <| IO.userError s!"{name} differs for {left}, {right}: source {source}, Talos {talos}"

def check : IO Unit := do
  for left in edgeWords do
    for right in edgeWords do
      checkPair left right
  let mut state : UInt32 := 0xC0DEC0DE
  for _ in [:1024] do
    state := 1664525 * state + 1013904223
    let left := state
    state := 1664525 * state + 1013904223
    checkPair left state
  IO.println s!"FP32 logical-model comparison passed: {5 * (edgeWords.size ^ 2 + 1024)} results"

#eval check

end Project.F32Source.Checks
