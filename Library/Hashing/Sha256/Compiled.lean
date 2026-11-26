module

public import Library.Hashing.Sha256.Program
public import Library.Hashing.Words.Encoding
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Hashing.Sha256

open Library.Hashing.Words

set_option verified_compile.alignedNative true in
verified_compile compiled := [bswap, paddedWord, loadBlock, roundStep, advance, compress,
  hashFrom, sha256With, sha224With, sha256, sha224]

end Library.Hashing.Sha256
