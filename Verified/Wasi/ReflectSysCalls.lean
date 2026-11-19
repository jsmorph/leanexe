import Verified.Wasi.ReflectLemmas
import Verified.Wasi.ReflectSysOperation
import LeanExe.Wasi.SysCalls

/-!
The `Flat` instances of the record result types, the reflection equations of the generated typed
functions, and the table of the equations that `reflect` reads, which `tools/wasi-calls.py`
generates from the pinned witx.  Each equation states that the `sys` command of the call denotes
the typed function followed by the `Flat` form of its result.  Its check fails when this file
differs from its output.
-/

namespace LeanExe.Wasi

open LeanExe.Pipeline

instance : Flat FdstatResult (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun result => (result.errno, result.fsFiletype, result.fsFlags, result.fsRightsBase,
    result.fsRightsInheriting)⟩

instance : Flat FilestatResult
    (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun result => (result.errno, result.dev, result.ino, result.filetype, result.nlink, result.size,
    result.atim, result.mtim, result.ctim)⟩

instance : Flat PrestatResult (UInt64 × UInt64 × UInt64) :=
  ⟨fun result => (result.errno, result.tag, result.prNameLen)⟩

instance : Flat PollResult (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun result => (result.errno, result.count, result.userdata, result.error, result.type,
    result.nbytes, result.flags)⟩

end LeanExe.Wasi

namespace Verified.Wasi.Reflect

open LeanExe.Wasi LeanExe.Pipeline

variable {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty}

-- With `Reply.field` folded, `rfl` unfolds the command's side of a record equation to the
-- typed function's fields instead of unfolding the fields' byte readers.
attribute [local irreducible] Reply.field

theorem environSizesGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) (context := context)
      Call.environSizesGet (.flat 2 false) [] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : ArgsSizes → UInt64 × UInt64 × UInt64) environSizesGet := rfl

theorem clockResGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (id : Var context .word) (idValue : UInt64) (hId : env.get id = idValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.clockResGet (.flat 1 false)
      [id] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (clockResGet idValue) := by
  subst hId
  rfl

theorem fdAdvise_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (offset : Var context .word)
    (len : Var context .word) (advice : Var context .word) (fdValue : Handle) (offsetValue : UInt64)
    (lenValue : UInt64) (adviceValue : UInt64) (hFd : env.get fd = fdValue.fd)
    (hOffset : env.get offset = offsetValue) (hLen : env.get len = lenValue)
    (hAdvice : env.get advice = adviceValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdAdvise (.flat 0 false)
      [fd, offset, len, advice] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdAdvise fdValue offsetValue lenValue
        adviceValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hOffset hLen hAdvice
  rfl

theorem fdAllocate_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (offset : Var context .word)
    (len : Var context .word) (fdValue : Handle) (offsetValue : UInt64) (lenValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hOffset : env.get offset = offsetValue)
    (hLen : env.get len = lenValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdAllocate (.flat 0 false)
      [fd, offset, len] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdAllocate fdValue offsetValue lenValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hOffset hLen
  rfl

theorem fdDatasync_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : Handle)
    (hFd : env.get fd = fdValue.fd) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdDatasync (.flat 0 false)
      [fd] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdDatasync fdValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd
  rfl

theorem fdFdstatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : Handle)
    (hFd : env.get fd = fdValue.fd) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFdstatGet (.record 4) [fd]
      [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FdstatResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64)
        (fdFdstatGet fdValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd
  rfl

theorem fdFdstatSetFlags_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word) (fdValue : Handle)
    (flagsValue : UInt64) (hFd : env.get fd = fdValue.fd) (hFlags : env.get flags = flagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFdstatSetFlags
      (.flat 0 false) [fd, flags] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFdstatSetFlags fdValue flagsValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hFlags
  rfl

theorem fdFdstatSetRights_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fsRightsBase : Var context .word)
    (fsRightsInheriting : Var context .word) (fdValue : Handle) (fsRightsBaseValue : UInt64)
    (fsRightsInheritingValue : UInt64) (hFd : env.get fd = fdValue.fd)
    (hFsRightsBase : env.get fsRightsBase = fsRightsBaseValue)
    (hFsRightsInheriting : env.get fsRightsInheriting = fsRightsInheritingValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFdstatSetRights
      (.flat 0 false) [fd, fsRightsBase, fsRightsInheriting] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFdstatSetRights fdValue fsRightsBaseValue
        fsRightsInheritingValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hFsRightsBase hFsRightsInheriting
  rfl

theorem fdFilestatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : Handle)
    (hFd : env.get fd = fdValue.fd) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFilestatGet (.record 8)
      [fd] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FilestatResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 × UInt64) (fdFilestatGet fdValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd
  rfl

theorem fdFilestatSetSize_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (size : Var context .word) (fdValue : Handle)
    (sizeValue : UInt64) (hFd : env.get fd = fdValue.fd) (hSize : env.get size = sizeValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFilestatSetSize
      (.flat 0 false) [fd, size] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFilestatSetSize fdValue sizeValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hSize
  rfl

theorem fdFilestatSetTimes_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (atim : Var context .word)
    (mtim : Var context .word) (fstFlags : Var context .word) (fdValue : Handle)
    (atimValue : UInt64) (mtimValue : UInt64) (fstFlagsValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hAtim : env.get atim = atimValue)
    (hMtim : env.get mtim = mtimValue) (hFstFlags : env.get fstFlags = fstFlagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFilestatSetTimes
      (.flat 0 false) [fd, atim, mtim, fstFlags] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFilestatSetTimes fdValue atimValue mtimValue
        fstFlagsValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hAtim hMtim hFstFlags
  rfl

theorem fdPread_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (buffer : Var context .bytes)
    (start : Var context .word) (count : Var context .word) (offset : Var context .word)
    (fdValue : Handle) (bufferValue : LeanExe.Bytes) (startValue : UInt64) (countValue : UInt64)
    (offsetValue : UInt64) (hFd : env.get fd = fdValue.fd) (hBuffer : env.get buffer = bufferValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue)
    (hOffset : env.get offset = offsetValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdPread .iovecRead
      [fd, start, count, offset] [] [buffer]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FillResult → UInt64 × UInt64 × LeanExe.Bytes) (fdPread fdValue
        bufferValue startValue countValue offsetValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hBuffer hStart hCount hOffset
  rfl

theorem fdPrestatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : Handle)
    (hFd : env.get fd = fdValue.fd) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdPrestatGet (.record 2)
      [fd] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : PrestatResult → UInt64 × UInt64 × UInt64) (fdPrestatGet fdValue)
        := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd
  rfl

theorem fdPrestatDirName_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (buffer : Var context .bytes)
    (start : Var context .word) (count : Var context .word) (fdValue : Handle)
    (bufferValue : LeanExe.Bytes) (startValue : UInt64) (countValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hBuffer : env.get buffer = bufferValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdPrestatDirName
      (.flat 0 true) [fd, start, count] [] [buffer]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FillResult → UInt64 × UInt64 × LeanExe.Bytes) (fdPrestatDirName
        fdValue bufferValue startValue countValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hBuffer hStart hCount
  rfl

theorem fdPwrite_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (bytes : Var context .bytes)
    (start : Var context .word) (count : Var context .word) (offset : Var context .word)
    (fdValue : Handle) (bytesValue : LeanExe.Bytes) (startValue : UInt64) (countValue : UInt64)
    (offsetValue : UInt64) (hFd : env.get fd = fdValue.fd) (hBytes : env.get bytes = bytesValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue)
    (hOffset : env.get offset = offsetValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdPwrite .iovecWrite
      [fd, start, count, offset] [bytes] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (fdPwrite fdValue bytesValue
        startValue countValue offsetValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hBytes hStart hCount hOffset
  rfl

theorem fdRead_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (buffer : Var context .bytes)
    (start : Var context .word) (count : Var context .word) (fdValue : Handle)
    (bufferValue : LeanExe.Bytes) (startValue : UInt64) (countValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hBuffer : env.get buffer = bufferValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdRead .iovecRead
      [fd, start, count] [] [buffer]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FillResult → UInt64 × UInt64 × LeanExe.Bytes) (fdRead fdValue
        bufferValue startValue countValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hBuffer hStart hCount
  rfl

theorem fdReaddir_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (buffer : Var context .bytes)
    (start : Var context .word) (count : Var context .word) (cookie : Var context .word)
    (fdValue : Handle) (bufferValue : LeanExe.Bytes) (startValue : UInt64) (countValue : UInt64)
    (cookieValue : UInt64) (hFd : env.get fd = fdValue.fd) (hBuffer : env.get buffer = bufferValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue)
    (hCookie : env.get cookie = cookieValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdReaddir (.flat 1 true)
      [fd, start, count, cookie] [] [buffer]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FillResult → UInt64 × UInt64 × LeanExe.Bytes) (fdReaddir fdValue
        bufferValue startValue countValue cookieValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hBuffer hStart hCount hCookie
  rfl

theorem fdSeek_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (offset : Var context .word)
    (whence : Var context .word) (fdValue : Handle) (offsetValue : UInt64) (whenceValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hOffset : env.get offset = offsetValue)
    (hWhence : env.get whence = whenceValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdSeek (.flat 1 false)
      [fd, offset, whence] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (fdSeek fdValue offsetValue
        whenceValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hOffset hWhence
  rfl

theorem fdSync_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : Handle)
    (hFd : env.get fd = fdValue.fd) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdSync (.flat 0 false) [fd]
      [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdSync fdValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd
  rfl

theorem fdTell_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : Handle)
    (hFd : env.get fd = fdValue.fd) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdTell (.flat 1 false) [fd]
      [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (fdTell fdValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd
  rfl

theorem fdWrite_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (bytes : Var context .bytes)
    (start : Var context .word) (count : Var context .word) (fdValue : Handle)
    (bytesValue : LeanExe.Bytes) (startValue : UInt64) (countValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hBytes : env.get bytes = bytesValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdWrite .iovecWrite
      [fd, start, count] [bytes] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (fdWrite fdValue bytesValue
        startValue countValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hBytes hStart hCount
  rfl

theorem pathCreateDirectory_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes) (fdValue : Handle)
    (pathValue : LeanExe.Bytes) (hFd : env.get fd = fdValue.fd) (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathCreateDirectory
      (.flat 0 false) [fd] [path] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathCreateDirectory fdValue pathValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hPath
  rfl

theorem pathFilestatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word)
    (path : Var context .bytes) (fdValue : Handle) (flagsValue : UInt64) (pathValue : LeanExe.Bytes)
    (hFd : env.get fd = fdValue.fd) (hFlags : env.get flags = flagsValue)
    (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathFilestatGet (.record 8)
      [fd, flags] [path] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FilestatResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 × UInt64) (pathFilestatGet fdValue flagsValue pathValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hFlags hPath
  rfl

theorem pathFilestatSetTimes_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word)
    (path : Var context .bytes) (atim : Var context .word) (mtim : Var context .word)
    (fstFlags : Var context .word) (fdValue : Handle) (flagsValue : UInt64)
    (pathValue : LeanExe.Bytes) (atimValue : UInt64) (mtimValue : UInt64) (fstFlagsValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hFlags : env.get flags = flagsValue)
    (hPath : env.get path = pathValue) (hAtim : env.get atim = atimValue)
    (hMtim : env.get mtim = mtimValue) (hFstFlags : env.get fstFlags = fstFlagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathFilestatSetTimes
      (.flat 0 false) [fd, flags, atim, mtim, fstFlags] [path] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathFilestatSetTimes fdValue flagsValue pathValue
        atimValue mtimValue fstFlagsValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hFlags hPath hAtim hMtim hFstFlags
  rfl

theorem pathLink_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (oldFd : Var context .word) (oldFlags : Var context .word)
    (oldPath : Var context .bytes) (newFd : Var context .word) (newPath : Var context .bytes)
    (oldFdValue : Handle) (oldFlagsValue : UInt64) (oldPathValue : LeanExe.Bytes)
    (newFdValue : Handle) (newPathValue : LeanExe.Bytes) (hOldFd : env.get oldFd = oldFdValue.fd)
    (hOldFlags : env.get oldFlags = oldFlagsValue) (hOldPath : env.get oldPath = oldPathValue)
    (hNewFd : env.get newFd = newFdValue.fd) (hNewPath : env.get newPath = newPathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathLink (.flat 0 false)
      [oldFd, oldFlags, newFd] [oldPath, newPath] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathLink oldFdValue oldFlagsValue oldPathValue
        newFdValue newPathValue) := by
  obtain ⟨oldFdValue⟩ := oldFdValue
  change env.get oldFd = oldFdValue at hOldFd
  obtain ⟨newFdValue⟩ := newFdValue
  change env.get newFd = newFdValue at hNewFd
  subst hOldFd hOldFlags hOldPath hNewFd hNewPath
  rfl

theorem pathReadlink_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes)
    (buffer : Var context .bytes) (start : Var context .word) (count : Var context .word)
    (fdValue : Handle) (pathValue : LeanExe.Bytes) (bufferValue : LeanExe.Bytes)
    (startValue : UInt64) (countValue : UInt64) (hFd : env.get fd = fdValue.fd)
    (hPath : env.get path = pathValue) (hBuffer : env.get buffer = bufferValue)
    (hStart : env.get start = startValue) (hCount : env.get count = countValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathReadlink (.flat 1 true)
      [fd, start, count] [path] [buffer]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FillResult → UInt64 × UInt64 × LeanExe.Bytes) (pathReadlink fdValue
        pathValue bufferValue startValue countValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hPath hBuffer hStart hCount
  rfl

theorem pathRemoveDirectory_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes) (fdValue : Handle)
    (pathValue : LeanExe.Bytes) (hFd : env.get fd = fdValue.fd) (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathRemoveDirectory
      (.flat 0 false) [fd] [path] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathRemoveDirectory fdValue pathValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hPath
  rfl

theorem pathRename_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (oldPath : Var context .bytes)
    (newFd : Var context .word) (newPath : Var context .bytes) (fdValue : Handle)
    (oldPathValue : LeanExe.Bytes) (newFdValue : Handle) (newPathValue : LeanExe.Bytes)
    (hFd : env.get fd = fdValue.fd) (hOldPath : env.get oldPath = oldPathValue)
    (hNewFd : env.get newFd = newFdValue.fd) (hNewPath : env.get newPath = newPathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathRename (.flat 0 false)
      [fd, newFd] [oldPath, newPath] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathRename fdValue oldPathValue newFdValue
        newPathValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  obtain ⟨newFdValue⟩ := newFdValue
  change env.get newFd = newFdValue at hNewFd
  subst hFd hOldPath hNewFd hNewPath
  rfl

theorem pathSymlink_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (oldPath : Var context .bytes) (fd : Var context .word)
    (newPath : Var context .bytes) (oldPathValue : LeanExe.Bytes) (fdValue : Handle)
    (newPathValue : LeanExe.Bytes) (hOldPath : env.get oldPath = oldPathValue)
    (hFd : env.get fd = fdValue.fd) (hNewPath : env.get newPath = newPathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathSymlink (.flat 0 false)
      [fd] [oldPath, newPath] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathSymlink oldPathValue fdValue newPathValue)
        := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hOldPath hFd hNewPath
  rfl

theorem pathUnlinkFile_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes) (fdValue : Handle)
    (pathValue : LeanExe.Bytes) (hFd : env.get fd = fdValue.fd) (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathUnlinkFile
      (.flat 0 false) [fd] [path] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathUnlinkFile fdValue pathValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hPath
  rfl

theorem pollClock_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (clock : Var context .word) (timeout : Var context .word)
    (precision : Var context .word) (flags : Var context .word) (clockValue : UInt64)
    (timeoutValue : UInt64) (precisionValue : UInt64) (flagsValue : UInt64)
    (hClock : env.get clock = clockValue) (hTimeout : env.get timeout = timeoutValue)
    (hPrecision : env.get precision = precisionValue) (hFlags : env.get flags = flagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pollOneoffClock .poll
      [clock, timeout, precision, flags] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : PollResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64) (pollClock clockValue timeoutValue precisionValue flagsValue) := by
  subst hClock hTimeout hPrecision hFlags
  rfl

theorem pollRead_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (clock : Var context .word)
    (timeout : Var context .word) (fdValue : Handle) (clockValue : UInt64) (timeoutValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hClock : env.get clock = clockValue)
    (hTimeout : env.get timeout = timeoutValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pollOneoffRead .poll
      [fd, clock, timeout] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : PollResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64) (pollRead fdValue clockValue timeoutValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hClock hTimeout
  rfl

theorem pollWrite_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (clock : Var context .word)
    (timeout : Var context .word) (fdValue : Handle) (clockValue : UInt64) (timeoutValue : UInt64)
    (hFd : env.get fd = fdValue.fd) (hClock : env.get clock = clockValue)
    (hTimeout : env.get timeout = timeoutValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pollOneoffWrite .poll
      [fd, clock, timeout] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : PollResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64) (pollWrite fdValue clockValue timeoutValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hClock hTimeout
  rfl

theorem procRaise_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (sig : Var context .word) (sigValue : UInt64)
    (hSig : env.get sig = sigValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.procRaise (.flat 0 false)
      [sig] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (procRaise sigValue) := by
  subst hSig
  rfl

theorem schedYield_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) (context := context)
      Call.schedYield (.flat 0 false) [] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) schedYield := rfl

theorem sockAccept_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word) (fdValue : Handle)
    (flagsValue : UInt64) (hFd : env.get fd = fdValue.fd) (hFlags : env.get flags = flagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.sockAccept (.flat 1 false)
      [fd, flags] [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (sockAccept fdValue flagsValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hFlags
  rfl

theorem sockShutdown_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (how : Var context .word) (fdValue : Handle)
    (howValue : UInt64) (hFd : env.get fd = fdValue.fd) (hHow : env.get how = howValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.sockShutdown (.flat 0 false)
      [fd, how] [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (sockShutdown fdValue howValue) := by
  obtain ⟨fdValue⟩ := fdValue
  change env.get fd = fdValue at hFd
  subst hFd hHow
  rfl

/-- The generated typed functions that `reflect` maps to one `sys` command. -/
def generatedSysOperations : List (Lean.Name × SysOperation) := [
  (``LeanExe.Wasi.environSizesGet, ⟨``LeanExe.Wasi.Call.environSizesGet,
    flatForm 2 false, [], ``environSizesGet_eq⟩),
  (``LeanExe.Wasi.clockResGet, ⟨``LeanExe.Wasi.Call.clockResGet,
    flatForm 1 false, [.word], ``clockResGet_eq⟩),
  (``LeanExe.Wasi.fdAdvise, ⟨``LeanExe.Wasi.Call.fdAdvise,
    flatForm 0 false, [.word, .word, .word, .word], ``fdAdvise_eq⟩),
  (``LeanExe.Wasi.fdAllocate, ⟨``LeanExe.Wasi.Call.fdAllocate,
    flatForm 0 false, [.word, .word, .word], ``fdAllocate_eq⟩),
  (``LeanExe.Wasi.fdDatasync, ⟨``LeanExe.Wasi.Call.fdDatasync,
    flatForm 0 false, [.word], ``fdDatasync_eq⟩),
  (``LeanExe.Wasi.fdFdstatGet, ⟨``LeanExe.Wasi.Call.fdFdstatGet,
    recordForm 4, [.word], ``fdFdstatGet_eq⟩),
  (``LeanExe.Wasi.fdFdstatSetFlags, ⟨``LeanExe.Wasi.Call.fdFdstatSetFlags,
    flatForm 0 false, [.word, .word], ``fdFdstatSetFlags_eq⟩),
  (``LeanExe.Wasi.fdFdstatSetRights, ⟨``LeanExe.Wasi.Call.fdFdstatSetRights,
    flatForm 0 false, [.word, .word, .word], ``fdFdstatSetRights_eq⟩),
  (``LeanExe.Wasi.fdFilestatGet, ⟨``LeanExe.Wasi.Call.fdFilestatGet,
    recordForm 8, [.word], ``fdFilestatGet_eq⟩),
  (``LeanExe.Wasi.fdFilestatSetSize, ⟨``LeanExe.Wasi.Call.fdFilestatSetSize,
    flatForm 0 false, [.word, .word], ``fdFilestatSetSize_eq⟩),
  (``LeanExe.Wasi.fdFilestatSetTimes, ⟨``LeanExe.Wasi.Call.fdFilestatSetTimes,
    flatForm 0 false, [.word, .word, .word, .word], ``fdFilestatSetTimes_eq⟩),
  (``LeanExe.Wasi.fdPread, ⟨``LeanExe.Wasi.Call.fdPread,
    iovecReadForm, [.word, .buffer, .word, .word, .word], ``fdPread_eq⟩),
  (``LeanExe.Wasi.fdPrestatGet, ⟨``LeanExe.Wasi.Call.fdPrestatGet,
    recordForm 2, [.word], ``fdPrestatGet_eq⟩),
  (``LeanExe.Wasi.fdPrestatDirName, ⟨``LeanExe.Wasi.Call.fdPrestatDirName,
    flatForm 0 true, [.word, .buffer, .word, .word], ``fdPrestatDirName_eq⟩),
  (``LeanExe.Wasi.fdPwrite, ⟨``LeanExe.Wasi.Call.fdPwrite,
    iovecWriteForm, [.word, .input, .word, .word, .word], ``fdPwrite_eq⟩),
  (``LeanExe.Wasi.fdRead, ⟨``LeanExe.Wasi.Call.fdRead,
    iovecReadForm, [.word, .buffer, .word, .word], ``fdRead_eq⟩),
  (``LeanExe.Wasi.fdReaddir, ⟨``LeanExe.Wasi.Call.fdReaddir,
    flatForm 1 true, [.word, .buffer, .word, .word, .word], ``fdReaddir_eq⟩),
  (``LeanExe.Wasi.fdSeek, ⟨``LeanExe.Wasi.Call.fdSeek,
    flatForm 1 false, [.word, .word, .word], ``fdSeek_eq⟩),
  (``LeanExe.Wasi.fdSync, ⟨``LeanExe.Wasi.Call.fdSync,
    flatForm 0 false, [.word], ``fdSync_eq⟩),
  (``LeanExe.Wasi.fdTell, ⟨``LeanExe.Wasi.Call.fdTell,
    flatForm 1 false, [.word], ``fdTell_eq⟩),
  (``LeanExe.Wasi.fdWrite, ⟨``LeanExe.Wasi.Call.fdWrite,
    iovecWriteForm, [.word, .input, .word, .word], ``fdWrite_eq⟩),
  (``LeanExe.Wasi.pathCreateDirectory, ⟨``LeanExe.Wasi.Call.pathCreateDirectory,
    flatForm 0 false, [.word, .input], ``pathCreateDirectory_eq⟩),
  (``LeanExe.Wasi.pathFilestatGet, ⟨``LeanExe.Wasi.Call.pathFilestatGet,
    recordForm 8, [.word, .word, .input], ``pathFilestatGet_eq⟩),
  (``LeanExe.Wasi.pathFilestatSetTimes, ⟨``LeanExe.Wasi.Call.pathFilestatSetTimes,
    flatForm 0 false, [.word, .word, .input, .word, .word, .word], ``pathFilestatSetTimes_eq⟩),
  (``LeanExe.Wasi.pathLink, ⟨``LeanExe.Wasi.Call.pathLink,
    flatForm 0 false, [.word, .word, .input, .word, .input], ``pathLink_eq⟩),
  (``LeanExe.Wasi.pathReadlink, ⟨``LeanExe.Wasi.Call.pathReadlink,
    flatForm 1 true, [.word, .input, .buffer, .word, .word], ``pathReadlink_eq⟩),
  (``LeanExe.Wasi.pathRemoveDirectory, ⟨``LeanExe.Wasi.Call.pathRemoveDirectory,
    flatForm 0 false, [.word, .input], ``pathRemoveDirectory_eq⟩),
  (``LeanExe.Wasi.pathRename, ⟨``LeanExe.Wasi.Call.pathRename,
    flatForm 0 false, [.word, .input, .word, .input], ``pathRename_eq⟩),
  (``LeanExe.Wasi.pathSymlink, ⟨``LeanExe.Wasi.Call.pathSymlink,
    flatForm 0 false, [.input, .word, .input], ``pathSymlink_eq⟩),
  (``LeanExe.Wasi.pathUnlinkFile, ⟨``LeanExe.Wasi.Call.pathUnlinkFile,
    flatForm 0 false, [.word, .input], ``pathUnlinkFile_eq⟩),
  (``LeanExe.Wasi.pollClock, ⟨``LeanExe.Wasi.Call.pollOneoffClock,
    pollForm, [.word, .word, .word, .word], ``pollClock_eq⟩),
  (``LeanExe.Wasi.pollRead, ⟨``LeanExe.Wasi.Call.pollOneoffRead,
    pollForm, [.word, .word, .word], ``pollRead_eq⟩),
  (``LeanExe.Wasi.pollWrite, ⟨``LeanExe.Wasi.Call.pollOneoffWrite,
    pollForm, [.word, .word, .word], ``pollWrite_eq⟩),
  (``LeanExe.Wasi.procRaise, ⟨``LeanExe.Wasi.Call.procRaise,
    flatForm 0 false, [.word], ``procRaise_eq⟩),
  (``LeanExe.Wasi.schedYield, ⟨``LeanExe.Wasi.Call.schedYield,
    flatForm 0 false, [], ``schedYield_eq⟩),
  (``LeanExe.Wasi.sockAccept, ⟨``LeanExe.Wasi.Call.sockAccept,
    flatForm 1 false, [.word, .word], ``sockAccept_eq⟩),
  (``LeanExe.Wasi.sockShutdown, ⟨``LeanExe.Wasi.Call.sockShutdown,
    flatForm 0 false, [.word, .word], ``sockShutdown_eq⟩)]

end Verified.Wasi.Reflect
