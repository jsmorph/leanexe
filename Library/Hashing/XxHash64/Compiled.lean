module

public import Library.Hashing.XxHash64.Encoding
public import Library.Hashing.XxHash64.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Hashing.XxHash64

verified_compile compiled := [stripeAt, converge, avalanche, xxh64]

end Library.Hashing.XxHash64
