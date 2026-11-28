module

public import Library.Regex.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Regex

verified_compile compiled := [addFollow, scan, masks, steps, advance, runInput, matchWith]

#print axioms compiled.matchWith.implements

end Library.Regex
