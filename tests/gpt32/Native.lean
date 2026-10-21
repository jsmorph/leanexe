import Examples.Gpt32.NativeCases

def main : List String → IO Unit
  | [host, dir] => Examples.Gpt32.NativeCases.run host dir
  | _ => throw <| IO.userError "usage: Native.lean HOST DIR"
