import LeanExe.WGSL.Compile

open LeanExe.WGSL LeanExe.WGSL.Source

def main : IO Unit := do
  let shader ← IO.FS.readFile "build/wgsl/review-add.wgsl"
  let .ok tokens := tokenize shader | throw (IO.userError "tokenization failed")
  let .ok parsed := Source.parse shader | throw (IO.userError "parse failed")
  let header := "import LeanExe.WGSL.Compile\nset_option maxRecDepth 16384\nopen LeanExe.WGSL LeanExe.WGSL.Source\n"
  IO.FS.writeFile "ReviewLex.lean" (header ++
    s!"def reviewTokens : List String := {reprStr tokens}\ntheorem reviewLex : tokenize {reprStr shader} = Except.ok reviewTokens := Source.ok_of_toOption _ _ (by decide +kernel)\n#print axioms reviewLex\n")
  IO.FS.writeFile "ReviewParse.lean" (header ++
    s!"def reviewTokens : List String := {reprStr tokens}\ndef reviewCode : Statement.Code := {parsed.code.lean}\ntheorem reviewParse : Source.parseTokens reviewTokens = Except.ok (Source.Parsed.mk 2 3 reviewCode) := Source.ok_of_toOption _ _ (by decide +kernel)\n#print axioms reviewParse\n")
