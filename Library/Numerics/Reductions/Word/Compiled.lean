module

public import Library.Numerics.Reductions.Word.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Reductions.Word

verified_compile compiled := [sumArray, productArray, xorArray]

end Library.Numerics.Reductions.Word
