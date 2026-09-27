import LeanExe.Wasm.Binary

open LeanExe.Wasm.Binary.CoreWasm

private def pairCallee : Func :=
  { sourceName := `pair, exportName := none, params := 0, locals := 0,
    body := .skip, results := [.u64 1, .u64 2] }

-- Calls at the end of a function or branch leave their results on the stack.
#guard directCallResults #[pairCallee] [.call 0] 0 0 == (1, #[], "stack")

-- A partial suffix is not a complete two-result local assignment.
#guard directCallResults #[pairCallee] [.call 0, .localSet 4] 0 0 == (1, #[], "stack")

-- A complete suffix records local destinations in source result order.
#guard directCallResults #[pairCallee] [.call 0, .localSet 4, .localSet 3] 0 0 ==
  (3, #[3, 4], "locals")
