module

public import Library.Lists.Word.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Lists.Word

verified_compile compiled := [listSum, range, sum, reverse, increment]

end Library.Lists.Word
