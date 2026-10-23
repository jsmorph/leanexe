import Library.Hashing.Sha512.Program
import Library.Hashing.Words.Encoding
import Verified.Reflect.Command

namespace Library.Hashing.Sha512

open Library.Hashing.Words

verified_compile compiled := [bswap, paddedWord, loadBlock, roundStep, advance, compress,
  hashWith, sha512With, sha384With, sha512_256With, sha512_224With, sha512, sha384, sha512_256,
  sha512_224]

end Library.Hashing.Sha512
