import Library.Hashing.Crc.Program
import Verified.Reflect.Command

namespace Library.Hashing.Crc

set_option verified_compile.alignedNative true in
verified_compile compiled := [updateWith, crcWith, crc32, crc32c, crc32Update, crc32cUpdate]

end Library.Hashing.Crc
