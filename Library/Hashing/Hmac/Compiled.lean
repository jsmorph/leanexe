import Library.Hashing.Hmac.Program
import Library.Hashing.Words.Encoding
import Verified.Reflect.Command

/-! The modules `hmac_sha256` and `hmac_sha512`.  Each holds the compression and the block loop of
its hash function, since the two families name their functions alike and a module's exports take
the last component of each name. -/

namespace Library.Hashing.Hmac

open Library.Hashing.Words

verified_compile compiled256 := [bswap, Sha256.paddedWord, Sha256.loadBlock, Sha256.roundStep,
  Sha256.advance, Sha256.compress, Sha256.hashFrom, keyWord256, keyBlock256, xorBlock,
  hmacSha256With, hmacSha256]

verified_compile compiled512 := [bswap, Sha512.paddedWord, Sha512.loadBlock, Sha512.roundStep,
  Sha512.advance, Sha512.compress, Sha512.hashFrom, keyWord512, keyBlock512, xorBlock,
  hmacSha512With, hmacSha512]

end Library.Hashing.Hmac
