import Library.Hashing.Crc.Program
import Verified.Reflect.Command

/-!
The CRC programs of `Library/Hashing/Crc/Compiled.lean` compiled with
`verified_compile.alignedNative`, so that `compiled.f.nativeAligned` covers each function and
wrapper of the translation without the test of alignment.  `tests/native/aligned.sh` builds this
module with `native-verified build --aligned`, which refuses `Library.Hashing.Crc.Compiled`
itself.
-/

namespace TestSupport.Native.AlignedCrc

open Library.Hashing.Crc

set_option verified_compile.alignedNative true in
verified_compile compiled := [updateWith, crcWith, crc32, crc32c, crc32Update, crc32cUpdate]

end TestSupport.Native.AlignedCrc
