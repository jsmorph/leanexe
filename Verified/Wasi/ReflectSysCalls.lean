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
      Call.environSizesGet (.flat 2 false) [] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : ArgsSizes → UInt64 × UInt64 × UInt64) environSizesGet := rfl

theorem clockResGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (id : Var context .word) (idValue : UInt64) (hId : env.get id = idValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.clockResGet (.flat 1 false)
      [id] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (clockResGet idValue) := by
  subst hId
  rfl

theorem fdAdvise_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (offset : Var context .word)
    (len : Var context .word) (advice : Var context .word) (fdValue : UInt64) (offsetValue : UInt64)
    (lenValue : UInt64) (adviceValue : UInt64) (hFd : env.get fd = fdValue)
    (hOffset : env.get offset = offsetValue) (hLen : env.get len = lenValue)
    (hAdvice : env.get advice = adviceValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdAdvise (.flat 0 false)
      [fd, offset, len, advice] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdAdvise fdValue offsetValue lenValue
        adviceValue) := by
  subst hFd hOffset hLen hAdvice
  rfl

theorem fdAllocate_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (offset : Var context .word)
    (len : Var context .word) (fdValue : UInt64) (offsetValue : UInt64) (lenValue : UInt64)
    (hFd : env.get fd = fdValue) (hOffset : env.get offset = offsetValue)
    (hLen : env.get len = lenValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdAllocate (.flat 0 false)
      [fd, offset, len] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdAllocate fdValue offsetValue lenValue) := by
  subst hFd hOffset hLen
  rfl

theorem fdClose_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdClose (.flat 0 false) [fd]
      []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdClose fdValue) := by
  subst hFd
  rfl

theorem fdDatasync_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdDatasync (.flat 0 false)
      [fd] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdDatasync fdValue) := by
  subst hFd
  rfl

theorem fdFdstatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFdstatGet (.record 4) [fd]
      []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FdstatResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64)
        (fdFdstatGet fdValue) := by
  subst hFd
  rfl

theorem fdFdstatSetFlags_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word) (fdValue : UInt64)
    (flagsValue : UInt64) (hFd : env.get fd = fdValue) (hFlags : env.get flags = flagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFdstatSetFlags
      (.flat 0 false) [fd, flags] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFdstatSetFlags fdValue flagsValue) := by
  subst hFd hFlags
  rfl

theorem fdFdstatSetRights_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fsRightsBase : Var context .word)
    (fsRightsInheriting : Var context .word) (fdValue : UInt64) (fsRightsBaseValue : UInt64)
    (fsRightsInheritingValue : UInt64) (hFd : env.get fd = fdValue)
    (hFsRightsBase : env.get fsRightsBase = fsRightsBaseValue)
    (hFsRightsInheriting : env.get fsRightsInheriting = fsRightsInheritingValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFdstatSetRights
      (.flat 0 false) [fd, fsRightsBase, fsRightsInheriting] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFdstatSetRights fdValue fsRightsBaseValue
        fsRightsInheritingValue) := by
  subst hFd hFsRightsBase hFsRightsInheriting
  rfl

theorem fdFilestatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFilestatGet (.record 8)
      [fd] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FilestatResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 × UInt64) (fdFilestatGet fdValue) := by
  subst hFd
  rfl

theorem fdFilestatSetSize_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (size : Var context .word) (fdValue : UInt64)
    (sizeValue : UInt64) (hFd : env.get fd = fdValue) (hSize : env.get size = sizeValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFilestatSetSize
      (.flat 0 false) [fd, size] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFilestatSetSize fdValue sizeValue) := by
  subst hFd hSize
  rfl

theorem fdFilestatSetTimes_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (atim : Var context .word)
    (mtim : Var context .word) (fstFlags : Var context .word) (fdValue : UInt64)
    (atimValue : UInt64) (mtimValue : UInt64) (fstFlagsValue : UInt64) (hFd : env.get fd = fdValue)
    (hAtim : env.get atim = atimValue) (hMtim : env.get mtim = mtimValue)
    (hFstFlags : env.get fstFlags = fstFlagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdFilestatSetTimes
      (.flat 0 false) [fd, atim, mtim, fstFlags] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdFilestatSetTimes fdValue atimValue mtimValue
        fstFlagsValue) := by
  subst hFd hAtim hMtim hFstFlags
  rfl

theorem fdPrestatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdPrestatGet (.record 2)
      [fd] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : PrestatResult → UInt64 × UInt64 × UInt64) (fdPrestatGet fdValue)
        := by
  subst hFd
  rfl

theorem fdPrestatDirName_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (pathLen : Var context .word) (fdValue : UInt64)
    (pathLenValue : UInt64) (hFd : env.get fd = fdValue)
    (hPathLen : env.get pathLen = pathLenValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdPrestatDirName
      (.flat 0 true) [fd, pathLen] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : BytesResult → UInt64 × LeanExe.Bytes) (fdPrestatDirName fdValue
        pathLenValue) := by
  subst hFd hPathLen
  rfl

theorem fdReaddir_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (bufLen : Var context .word)
    (cookie : Var context .word) (fdValue : UInt64) (bufLenValue : UInt64) (cookieValue : UInt64)
    (hFd : env.get fd = fdValue) (hBufLen : env.get bufLen = bufLenValue)
    (hCookie : env.get cookie = cookieValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdReaddir (.flat 1 true)
      [fd, bufLen, cookie] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : BytesCountResult → UInt64 × UInt64 × LeanExe.Bytes) (fdReaddir
        fdValue bufLenValue cookieValue) := by
  subst hFd hBufLen hCookie
  rfl

theorem fdRenumber_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) («to» : Var context .word) (fdValue : UInt64)
    (toValue : UInt64) (hFd : env.get fd = fdValue) (hTo : env.get «to» = toValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdRenumber (.flat 0 false)
      [fd, «to»] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdRenumber fdValue toValue) := by
  subst hFd hTo
  rfl

theorem fdSeek_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (offset : Var context .word)
    (whence : Var context .word) (fdValue : UInt64) (offsetValue : UInt64) (whenceValue : UInt64)
    (hFd : env.get fd = fdValue) (hOffset : env.get offset = offsetValue)
    (hWhence : env.get whence = whenceValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdSeek (.flat 1 false)
      [fd, offset, whence] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (fdSeek fdValue offsetValue
        whenceValue) := by
  subst hFd hOffset hWhence
  rfl

theorem fdSync_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdSync (.flat 0 false) [fd]
      []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (fdSync fdValue) := by
  subst hFd
  rfl

theorem fdTell_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (fdValue : UInt64) (hFd : env.get fd = fdValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.fdTell (.flat 1 false) [fd]
      []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (fdTell fdValue) := by
  subst hFd
  rfl

theorem pathCreateDirectory_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes) (fdValue : UInt64)
    (pathValue : LeanExe.Bytes) (hFd : env.get fd = fdValue) (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathCreateDirectory
      (.flat 0 false) [fd] [path]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathCreateDirectory fdValue pathValue) := by
  subst hFd hPath
  rfl

theorem pathFilestatGet_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word)
    (path : Var context .bytes) (fdValue : UInt64) (flagsValue : UInt64) (pathValue : LeanExe.Bytes)
    (hFd : env.get fd = fdValue) (hFlags : env.get flags = flagsValue)
    (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathFilestatGet (.record 8)
      [fd, flags] [path]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : FilestatResult → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 × UInt64) (pathFilestatGet fdValue flagsValue pathValue) := by
  subst hFd hFlags hPath
  rfl

theorem pathFilestatSetTimes_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word)
    (path : Var context .bytes) (atim : Var context .word) (mtim : Var context .word)
    (fstFlags : Var context .word) (fdValue : UInt64) (flagsValue : UInt64)
    (pathValue : LeanExe.Bytes) (atimValue : UInt64) (mtimValue : UInt64) (fstFlagsValue : UInt64)
    (hFd : env.get fd = fdValue) (hFlags : env.get flags = flagsValue)
    (hPath : env.get path = pathValue) (hAtim : env.get atim = atimValue)
    (hMtim : env.get mtim = mtimValue) (hFstFlags : env.get fstFlags = fstFlagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathFilestatSetTimes
      (.flat 0 false) [fd, flags, atim, mtim, fstFlags] [path]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathFilestatSetTimes fdValue flagsValue pathValue
        atimValue mtimValue fstFlagsValue) := by
  subst hFd hFlags hPath hAtim hMtim hFstFlags
  rfl

theorem pathLink_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (oldFd : Var context .word) (oldFlags : Var context .word)
    (oldPath : Var context .bytes) (newFd : Var context .word) (newPath : Var context .bytes)
    (oldFdValue : UInt64) (oldFlagsValue : UInt64) (oldPathValue : LeanExe.Bytes)
    (newFdValue : UInt64) (newPathValue : LeanExe.Bytes) (hOldFd : env.get oldFd = oldFdValue)
    (hOldFlags : env.get oldFlags = oldFlagsValue) (hOldPath : env.get oldPath = oldPathValue)
    (hNewFd : env.get newFd = newFdValue) (hNewPath : env.get newPath = newPathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathLink (.flat 0 false)
      [oldFd, oldFlags, newFd] [oldPath, newPath]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathLink oldFdValue oldFlagsValue oldPathValue
        newFdValue newPathValue) := by
  subst hOldFd hOldFlags hOldPath hNewFd hNewPath
  rfl

theorem pathOpen_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (dirflags : Var context .word)
    (path : Var context .bytes) (oflags : Var context .word) (fsRightsBase : Var context .word)
    (fsRightsInheriting : Var context .word) (fdflags : Var context .word) (fdValue : UInt64)
    (dirflagsValue : UInt64) (pathValue : LeanExe.Bytes) (oflagsValue : UInt64)
    (fsRightsBaseValue : UInt64) (fsRightsInheritingValue : UInt64) (fdflagsValue : UInt64)
    (hFd : env.get fd = fdValue) (hDirflags : env.get dirflags = dirflagsValue)
    (hPath : env.get path = pathValue) (hOflags : env.get oflags = oflagsValue)
    (hFsRightsBase : env.get fsRightsBase = fsRightsBaseValue)
    (hFsRightsInheriting : env.get fsRightsInheriting = fsRightsInheritingValue)
    (hFdflags : env.get fdflags = fdflagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathOpen (.flat 1 false)
      [fd, dirflags, oflags, fsRightsBase, fsRightsInheriting, fdflags] [path]).denote pureFuns
      effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (pathOpen fdValue dirflagsValue
        pathValue oflagsValue fsRightsBaseValue fsRightsInheritingValue fdflagsValue) := by
  subst hFd hDirflags hPath hOflags hFsRightsBase hFsRightsInheriting hFdflags
  rfl

theorem pathReadlink_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes)
    (bufLen : Var context .word) (fdValue : UInt64) (pathValue : LeanExe.Bytes)
    (bufLenValue : UInt64) (hFd : env.get fd = fdValue) (hPath : env.get path = pathValue)
    (hBufLen : env.get bufLen = bufLenValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathReadlink (.flat 1 true)
      [fd, bufLen] [path]).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : BytesCountResult → UInt64 × UInt64 × LeanExe.Bytes) (pathReadlink
        fdValue pathValue bufLenValue) := by
  subst hFd hPath hBufLen
  rfl

theorem pathRemoveDirectory_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes) (fdValue : UInt64)
    (pathValue : LeanExe.Bytes) (hFd : env.get fd = fdValue) (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathRemoveDirectory
      (.flat 0 false) [fd] [path]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathRemoveDirectory fdValue pathValue) := by
  subst hFd hPath
  rfl

theorem pathRename_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (oldPath : Var context .bytes)
    (newFd : Var context .word) (newPath : Var context .bytes) (fdValue : UInt64)
    (oldPathValue : LeanExe.Bytes) (newFdValue : UInt64) (newPathValue : LeanExe.Bytes)
    (hFd : env.get fd = fdValue) (hOldPath : env.get oldPath = oldPathValue)
    (hNewFd : env.get newFd = newFdValue) (hNewPath : env.get newPath = newPathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathRename (.flat 0 false)
      [fd, newFd] [oldPath, newPath]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathRename fdValue oldPathValue newFdValue
        newPathValue) := by
  subst hFd hOldPath hNewFd hNewPath
  rfl

theorem pathSymlink_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (oldPath : Var context .bytes) (fd : Var context .word)
    (newPath : Var context .bytes) (oldPathValue : LeanExe.Bytes) (fdValue : UInt64)
    (newPathValue : LeanExe.Bytes) (hOldPath : env.get oldPath = oldPathValue)
    (hFd : env.get fd = fdValue) (hNewPath : env.get newPath = newPathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathSymlink (.flat 0 false)
      [fd] [oldPath, newPath]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathSymlink oldPathValue fdValue newPathValue)
        := by
  subst hOldPath hFd hNewPath
  rfl

theorem pathUnlinkFile_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (path : Var context .bytes) (fdValue : UInt64)
    (pathValue : LeanExe.Bytes) (hFd : env.get fd = fdValue) (hPath : env.get path = pathValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.pathUnlinkFile
      (.flat 0 false) [fd] [path]).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (pathUnlinkFile fdValue pathValue) := by
  subst hFd hPath
  rfl

theorem procRaise_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (sig : Var context .word) (sigValue : UInt64)
    (hSig : env.get sig = sigValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.procRaise (.flat 0 false)
      [sig] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (procRaise sigValue) := by
  subst hSig
  rfl

theorem schedYield_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) (context := context)
      Call.schedYield (.flat 0 false) [] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) schedYield := rfl

theorem sockAccept_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (flags : Var context .word) (fdValue : UInt64)
    (flagsValue : UInt64) (hFd : env.get fd = fdValue) (hFlags : env.get flags = flagsValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.sockAccept (.flat 1 false)
      [fd, flags] []).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WordResult → UInt64 × UInt64) (sockAccept fdValue flagsValue) := by
  subst hFd hFlags
  rfl

theorem sockShutdown_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (fd : Var context .word) (how : Var context .word) (fdValue : UInt64)
    (howValue : UInt64) (hFd : env.get fd = fdValue) (hHow : env.get how = howValue) :
    (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) Call.sockShutdown (.flat 0 false)
      [fd, how] []).denote pureFuns effectFuns env =
      flattenAction (fun value : UInt64 => value) (sockShutdown fdValue howValue) := by
  subst hFd hHow
  rfl

/-- The generated typed functions that `reflect` maps to one `sys` command. -/
def generatedSysOperations : List (Lean.Name × SysOperation) := [
  (``LeanExe.Wasi.environSizesGet, ⟨``LeanExe.Wasi.Call.environSizesGet,
    flatForm 2 false, [], ``environSizesGet_eq⟩),
  (``LeanExe.Wasi.clockResGet, ⟨``LeanExe.Wasi.Call.clockResGet,
    flatForm 1 false, [false], ``clockResGet_eq⟩),
  (``LeanExe.Wasi.fdAdvise, ⟨``LeanExe.Wasi.Call.fdAdvise,
    flatForm 0 false, [false, false, false, false], ``fdAdvise_eq⟩),
  (``LeanExe.Wasi.fdAllocate, ⟨``LeanExe.Wasi.Call.fdAllocate,
    flatForm 0 false, [false, false, false], ``fdAllocate_eq⟩),
  (``LeanExe.Wasi.fdClose, ⟨``LeanExe.Wasi.Call.fdClose,
    flatForm 0 false, [false], ``fdClose_eq⟩),
  (``LeanExe.Wasi.fdDatasync, ⟨``LeanExe.Wasi.Call.fdDatasync,
    flatForm 0 false, [false], ``fdDatasync_eq⟩),
  (``LeanExe.Wasi.fdFdstatGet, ⟨``LeanExe.Wasi.Call.fdFdstatGet,
    recordForm 4, [false], ``fdFdstatGet_eq⟩),
  (``LeanExe.Wasi.fdFdstatSetFlags, ⟨``LeanExe.Wasi.Call.fdFdstatSetFlags,
    flatForm 0 false, [false, false], ``fdFdstatSetFlags_eq⟩),
  (``LeanExe.Wasi.fdFdstatSetRights, ⟨``LeanExe.Wasi.Call.fdFdstatSetRights,
    flatForm 0 false, [false, false, false], ``fdFdstatSetRights_eq⟩),
  (``LeanExe.Wasi.fdFilestatGet, ⟨``LeanExe.Wasi.Call.fdFilestatGet,
    recordForm 8, [false], ``fdFilestatGet_eq⟩),
  (``LeanExe.Wasi.fdFilestatSetSize, ⟨``LeanExe.Wasi.Call.fdFilestatSetSize,
    flatForm 0 false, [false, false], ``fdFilestatSetSize_eq⟩),
  (``LeanExe.Wasi.fdFilestatSetTimes, ⟨``LeanExe.Wasi.Call.fdFilestatSetTimes,
    flatForm 0 false, [false, false, false, false], ``fdFilestatSetTimes_eq⟩),
  (``LeanExe.Wasi.fdPrestatGet, ⟨``LeanExe.Wasi.Call.fdPrestatGet,
    recordForm 2, [false], ``fdPrestatGet_eq⟩),
  (``LeanExe.Wasi.fdPrestatDirName, ⟨``LeanExe.Wasi.Call.fdPrestatDirName,
    flatForm 0 true, [false, false], ``fdPrestatDirName_eq⟩),
  (``LeanExe.Wasi.fdReaddir, ⟨``LeanExe.Wasi.Call.fdReaddir,
    flatForm 1 true, [false, false, false], ``fdReaddir_eq⟩),
  (``LeanExe.Wasi.fdRenumber, ⟨``LeanExe.Wasi.Call.fdRenumber,
    flatForm 0 false, [false, false], ``fdRenumber_eq⟩),
  (``LeanExe.Wasi.fdSeek, ⟨``LeanExe.Wasi.Call.fdSeek,
    flatForm 1 false, [false, false, false], ``fdSeek_eq⟩),
  (``LeanExe.Wasi.fdSync, ⟨``LeanExe.Wasi.Call.fdSync,
    flatForm 0 false, [false], ``fdSync_eq⟩),
  (``LeanExe.Wasi.fdTell, ⟨``LeanExe.Wasi.Call.fdTell,
    flatForm 1 false, [false], ``fdTell_eq⟩),
  (``LeanExe.Wasi.pathCreateDirectory, ⟨``LeanExe.Wasi.Call.pathCreateDirectory,
    flatForm 0 false, [false, true], ``pathCreateDirectory_eq⟩),
  (``LeanExe.Wasi.pathFilestatGet, ⟨``LeanExe.Wasi.Call.pathFilestatGet,
    recordForm 8, [false, false, true], ``pathFilestatGet_eq⟩),
  (``LeanExe.Wasi.pathFilestatSetTimes, ⟨``LeanExe.Wasi.Call.pathFilestatSetTimes,
    flatForm 0 false, [false, false, true, false, false, false], ``pathFilestatSetTimes_eq⟩),
  (``LeanExe.Wasi.pathLink, ⟨``LeanExe.Wasi.Call.pathLink,
    flatForm 0 false, [false, false, true, false, true], ``pathLink_eq⟩),
  (``LeanExe.Wasi.pathOpen, ⟨``LeanExe.Wasi.Call.pathOpen,
    flatForm 1 false, [false, false, true, false, false, false, false], ``pathOpen_eq⟩),
  (``LeanExe.Wasi.pathReadlink, ⟨``LeanExe.Wasi.Call.pathReadlink,
    flatForm 1 true, [false, true, false], ``pathReadlink_eq⟩),
  (``LeanExe.Wasi.pathRemoveDirectory, ⟨``LeanExe.Wasi.Call.pathRemoveDirectory,
    flatForm 0 false, [false, true], ``pathRemoveDirectory_eq⟩),
  (``LeanExe.Wasi.pathRename, ⟨``LeanExe.Wasi.Call.pathRename,
    flatForm 0 false, [false, true, false, true], ``pathRename_eq⟩),
  (``LeanExe.Wasi.pathSymlink, ⟨``LeanExe.Wasi.Call.pathSymlink,
    flatForm 0 false, [true, false, true], ``pathSymlink_eq⟩),
  (``LeanExe.Wasi.pathUnlinkFile, ⟨``LeanExe.Wasi.Call.pathUnlinkFile,
    flatForm 0 false, [false, true], ``pathUnlinkFile_eq⟩),
  (``LeanExe.Wasi.procRaise, ⟨``LeanExe.Wasi.Call.procRaise,
    flatForm 0 false, [false], ``procRaise_eq⟩),
  (``LeanExe.Wasi.schedYield, ⟨``LeanExe.Wasi.Call.schedYield,
    flatForm 0 false, [], ``schedYield_eq⟩),
  (``LeanExe.Wasi.sockAccept, ⟨``LeanExe.Wasi.Call.sockAccept,
    flatForm 1 false, [false, false], ``sockAccept_eq⟩),
  (``LeanExe.Wasi.sockShutdown, ⟨``LeanExe.Wasi.Call.sockShutdown,
    flatForm 0 false, [false, false], ``sockShutdown_eq⟩)]

end Verified.Wasi.Reflect
