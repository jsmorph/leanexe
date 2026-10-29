import Library.Hashing.Sha3.Encoding
import Library.Hashing.Words.Encoding
import Verified.Reflect.Command

namespace Library.Hashing.Sha3

set_option verified_compile.alignedNative true in
verified_compile compiled := [thetaL, rhoPiL, chiL, iotaL, round, keccakF, messageWord,
  paddedWord, xorBlock, absorb, sha3_224, sha3_256, sha3_384, sha3_512, laneAt, squeezeBlock,
  shakeWith, shake128, shake256]

#print axioms compiled.sha3_256.implements
#print axioms compiled.shake128.implements

end Library.Hashing.Sha3
