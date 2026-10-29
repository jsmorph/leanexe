import Library.Hashing.Sha256.Program
import Library.Hashing.Words.Encoding
import Verified.Reflect.Command

namespace Library.Hashing.Sha256

open Library.Hashing.Words

set_option verified_compile.alignedNative true in
verified_compile compiled := [bswap, paddedWord, loadBlock, roundStep, advance, compress,
  hashFrom, sha256With, sha224With, sha256, sha224]

end Library.Hashing.Sha256
