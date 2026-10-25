import Library.Regex.Program
import Verified.Reflect.Command

namespace Library.Regex

verified_compile compiled := [addFollow, scan, masks, steps, advance, runInput, matchWith]

#print axioms compiled.matchWith.implements

end Library.Regex
