import LeanExe.Wasi.CallTable
import LeanExe.Wasi.Sys

/-!
Typed functions of the flat Preview 1 functions, which `tools/wasi-calls.py` generates from the
pinned witx with the descriptions of `LeanExe/Wasi/CallTable.lean`.  A record result holds the
errno and the record's fields as words.  A descriptor parameter takes a `Handle`.  `path_open`,
`fd_close`, and `fd_renumber` have no typed function: only `withOpen` opens and closes descriptors.
Its check fails when this file differs from its output.
-/

namespace LeanExe.Wasi

structure FdstatResult where
  errno : UInt64
  fsFiletype : UInt64
  fsFlags : UInt64
  fsRightsBase : UInt64
  fsRightsInheriting : UInt64

structure FilestatResult where
  errno : UInt64
  dev : UInt64
  ino : UInt64
  filetype : UInt64
  nlink : UInt64
  size : UInt64
  atim : UInt64
  mtim : UInt64
  ctim : UInt64

structure PrestatResult where
  errno : UInt64
  tag : UInt64
  prNameLen : UInt64

def environSizesGet : Action ArgsSizes :=
  .sys .environSizesGet [] fun reply =>
    .pure ⟨reply.errno, reply.word 0, reply.word 1⟩

def clockResGet (id : UInt64) : Action WordResult :=
  .sys .clockResGet [.word id] fun reply =>
    .pure ⟨reply.errno, reply.word 0⟩

def fdAdvise (fd : Handle) (offset : UInt64) (len : UInt64) (advice : UInt64) : Action UInt64 :=
  .sys .fdAdvise [.word fd.fd, .word offset, .word len, .word advice] fun reply =>
    .pure reply.errno

def fdAllocate (fd : Handle) (offset : UInt64) (len : UInt64) : Action UInt64 :=
  .sys .fdAllocate [.word fd.fd, .word offset, .word len] fun reply =>
    .pure reply.errno

def fdDatasync (fd : Handle) : Action UInt64 :=
  .sys .fdDatasync [.word fd.fd] fun reply =>
    .pure reply.errno

def fdFdstatGet (fd : Handle) : Action FdstatResult :=
  .sys .fdFdstatGet [.word fd.fd] fun reply =>
    .pure ⟨reply.errno, reply.field 0 0 1, reply.field 0 2 2, reply.field 0 8 8, reply.field 0 16 8⟩

def fdFdstatSetFlags (fd : Handle) (flags : UInt64) : Action UInt64 :=
  .sys .fdFdstatSetFlags [.word fd.fd, .word flags] fun reply =>
    .pure reply.errno

def fdFdstatSetRights (fd : Handle) (fsRightsBase : UInt64)
    (fsRightsInheriting : UInt64) : Action UInt64 :=
  .sys .fdFdstatSetRights [.word fd.fd, .word fsRightsBase, .word fsRightsInheriting] fun reply =>
    .pure reply.errno

def fdFilestatGet (fd : Handle) : Action FilestatResult :=
  .sys .fdFilestatGet [.word fd.fd] fun reply =>
    .pure ⟨reply.errno, reply.field 0 0 8, reply.field 0 8 8, reply.field 0 16 1,
      reply.field 0 24 8, reply.field 0 32 8, reply.field 0 40 8, reply.field 0 48 8,
      reply.field 0 56 8⟩

def fdFilestatSetSize (fd : Handle) (size : UInt64) : Action UInt64 :=
  .sys .fdFilestatSetSize [.word fd.fd, .word size] fun reply =>
    .pure reply.errno

def fdFilestatSetTimes (fd : Handle) (atim : UInt64) (mtim : UInt64)
    (fstFlags : UInt64) : Action UInt64 :=
  .sys .fdFilestatSetTimes [.word fd.fd, .word atim, .word mtim, .word fstFlags] fun reply =>
    .pure reply.errno

def fdPrestatGet (fd : Handle) : Action PrestatResult :=
  .sys .fdPrestatGet [.word fd.fd] fun reply =>
    .pure ⟨reply.errno, reply.field 0 0 1, reply.field 0 4 4⟩

def fdPrestatDirName (fd : Handle) (pathLen : UInt64) : Action BytesResult :=
  .sys .fdPrestatDirName [.word fd.fd, .space pathLen] fun reply =>
    .pure ⟨reply.errno, reply.bytes 0⟩

def fdReaddir (fd : Handle) (bufLen : UInt64) (cookie : UInt64) : Action BytesCountResult :=
  .sys .fdReaddir [.word fd.fd, .space bufLen, .word cookie] fun reply =>
    .pure ⟨reply.errno, reply.bytes 0, reply.word 1⟩

def fdSeek (fd : Handle) (offset : UInt64) (whence : UInt64) : Action WordResult :=
  .sys .fdSeek [.word fd.fd, .word offset, .word whence] fun reply =>
    .pure ⟨reply.errno, reply.word 0⟩

def fdSync (fd : Handle) : Action UInt64 :=
  .sys .fdSync [.word fd.fd] fun reply =>
    .pure reply.errno

def fdTell (fd : Handle) : Action WordResult :=
  .sys .fdTell [.word fd.fd] fun reply =>
    .pure ⟨reply.errno, reply.word 0⟩

def pathCreateDirectory (fd : Handle) (path : Bytes) : Action UInt64 :=
  .sys .pathCreateDirectory [.word fd.fd, .bytes path] fun reply =>
    .pure reply.errno

def pathFilestatGet (fd : Handle) (flags : UInt64) (path : Bytes) : Action FilestatResult :=
  .sys .pathFilestatGet [.word fd.fd, .word flags, .bytes path] fun reply =>
    .pure ⟨reply.errno, reply.field 0 0 8, reply.field 0 8 8, reply.field 0 16 1,
      reply.field 0 24 8, reply.field 0 32 8, reply.field 0 40 8, reply.field 0 48 8,
      reply.field 0 56 8⟩

def pathFilestatSetTimes (fd : Handle) (flags : UInt64) (path : Bytes) (atim : UInt64)
    (mtim : UInt64) (fstFlags : UInt64) : Action UInt64 :=
  .sys .pathFilestatSetTimes [.word fd.fd, .word flags, .bytes path, .word atim, .word mtim,
    .word fstFlags] fun reply =>
    .pure reply.errno

def pathLink (oldFd : Handle) (oldFlags : UInt64) (oldPath : Bytes) (newFd : Handle)
    (newPath : Bytes) : Action UInt64 :=
  .sys .pathLink [.word oldFd.fd, .word oldFlags, .bytes oldPath, .word newFd.fd,
    .bytes newPath] fun reply =>
    .pure reply.errno

def pathReadlink (fd : Handle) (path : Bytes) (bufLen : UInt64) : Action BytesCountResult :=
  .sys .pathReadlink [.word fd.fd, .bytes path, .space bufLen] fun reply =>
    .pure ⟨reply.errno, reply.bytes 0, reply.word 1⟩

def pathRemoveDirectory (fd : Handle) (path : Bytes) : Action UInt64 :=
  .sys .pathRemoveDirectory [.word fd.fd, .bytes path] fun reply =>
    .pure reply.errno

def pathRename (fd : Handle) (oldPath : Bytes) (newFd : Handle) (newPath : Bytes) : Action UInt64 :=
  .sys .pathRename [.word fd.fd, .bytes oldPath, .word newFd.fd, .bytes newPath] fun reply =>
    .pure reply.errno

def pathSymlink (oldPath : Bytes) (fd : Handle) (newPath : Bytes) : Action UInt64 :=
  .sys .pathSymlink [.bytes oldPath, .word fd.fd, .bytes newPath] fun reply =>
    .pure reply.errno

def pathUnlinkFile (fd : Handle) (path : Bytes) : Action UInt64 :=
  .sys .pathUnlinkFile [.word fd.fd, .bytes path] fun reply =>
    .pure reply.errno

def procRaise (sig : UInt64) : Action UInt64 :=
  .sys .procRaise [.word sig] fun reply =>
    .pure reply.errno

def schedYield : Action UInt64 :=
  .sys .schedYield [] fun reply =>
    .pure reply.errno

def sockAccept (fd : Handle) (flags : UInt64) : Action WordResult :=
  .sys .sockAccept [.word fd.fd, .word flags] fun reply =>
    .pure ⟨reply.errno, reply.word 0⟩

def sockShutdown (fd : Handle) (how : UInt64) : Action UInt64 :=
  .sys .sockShutdown [.word fd.fd, .word how] fun reply =>
    .pure reply.errno

end LeanExe.Wasi
