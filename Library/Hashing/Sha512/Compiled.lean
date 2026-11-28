module

public import Library.Hashing.Sha512.Program
public import Library.Hashing.Words.Encoding
public import Verified.Reflect.Command
public meta import Library.Hashing.Sha512.Program
public meta import Library.Hashing.Words.Encoding

@[expose] public section

namespace Library.Hashing.Sha512

open Library.Hashing.Words

verified_compile compiled := [bswap, paddedWord, loadBlock, roundStep, advance, compress,
  hashFrom, sha512With, sha384With, sha512_256With, sha512_224With, sha512, sha384, sha512_256,
  sha512_224]

end Library.Hashing.Sha512
