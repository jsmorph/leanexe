import TestSupport.OrderBook.Cases

/-! The cases of the module `orderbook` alone, for `tests/verified/run.sh --cases orderbook`. -/

def main : IO Unit := TestSupport.OrderBook.Cases.cases
