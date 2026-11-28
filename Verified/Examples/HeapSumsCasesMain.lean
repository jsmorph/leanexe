module

public import Verified.Examples.HeapSumsCases

@[expose] public section

def main : IO Unit := Verified.Examples.HeapSums.cases
