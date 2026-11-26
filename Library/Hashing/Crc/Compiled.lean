module

public import Library.Hashing.Crc.Program
public import Verified.Reflect.Command
public meta import Library.Hashing.Crc.Program

@[expose] public section

namespace Library.Hashing.Crc

set_option verified_compile.alignedNative true in
verified_compile compiled := [updateWith, crcWith, crc32, crc32c, crc32Update, crc32cUpdate]

end Library.Hashing.Crc
