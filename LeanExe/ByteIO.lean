namespace LeanExe

abbrev ByteIO (α : Type) := BaseIO α

namespace ByteIO

@[extern "leanexe_byte_io_read"]
opaque read (maxBytes : Nat) (timeoutNs : UInt64) : ByteIO (Except UInt32 ByteArray)

@[extern "leanexe_byte_io_write"]
opaque write (bytes : ByteArray) (timeoutNs : UInt64) : ByteIO UInt32

end ByteIO
end LeanExe
