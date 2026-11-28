module

public import Verified.Examples.WgslCases

@[expose] public section

def main : IO Unit := Verified.Examples.WgslCases.runCases false
