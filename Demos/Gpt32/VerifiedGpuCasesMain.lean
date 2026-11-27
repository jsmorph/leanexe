module

public import Demos.Gpt32.VerifiedCases
public meta import Demos.Gpt32.VerifiedCases

@[expose] public section

def main : IO Unit := Demos.Gpt32.VerifiedCases.runCases .wgsl
