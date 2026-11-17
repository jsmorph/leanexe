import Verified.Shim.Clocks
import Verified.Shim.Strings
import Verified.Shim.Files

/-!
The shim's host environment.  `sysInvoke F L I replies call` is the function of the flat call
`call` among `shimCalls` and traps on every other call.  `linuxEnv F L I replies calls` places the
stream functions first and then one function for each call of `calls`, in the order of
`ABI.importsWith calls`, and `linuxEnv_satisfies` proves that it satisfies
`hostSpecWith (linuxHost F L I replies) calls` for every module with at most those imports, when
the shim implements every call of `calls`.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

variable (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)

/-- The shim's function for the flat call `call`. -/
def sysInvoke (call : Call) :
    Store (Observed LinuxWorld) → List Value → HostResult (Observed LinuxWorld) :=
  if call = Call.clockTimeGet then clockInvoke L replies
  else if call = Call.randomGet then randomInvoke L replies
  else if call = Call.argsSizesGet then sizesInvoke I.args Call.argsSizesGet
  else if call = Call.argsGet then stringsInvoke I.args Call.argsGet
  else if call = Call.environSizesGet then sizesInvoke I.environ Call.environSizesGet
  else if call = Call.environGet then stringsInvoke I.environ Call.environGet
  else if call = Call.pathOpen then openInvoke F L I replies
  else if call = Call.fdClose then closeInvoke I replies
  else if call = Call.fdRead then handleReadInvoke L I replies
  else if call = Call.fdWrite then handleWriteInvoke L I replies
  else if call = Call.fdPrestatGet then prestatInvoke I
  else if call = Call.fdPrestatDirName then dirNameInvoke I
  else fun before _ => .Trap before shimTrap

def sysFn (call : Call) : HostFn (Observed LinuxWorld) where
  params := (ABI.callImport call).params
  results := (ABI.callImport call).results
  invoke := sysInvoke F L I replies call

/-- The shim's host environment for the three stream imports followed by the flat calls `calls`,
in the order of `ABI.importsWith calls`. -/
def linuxEnv (calls : List Call) : HostEnv (Observed LinuxWorld) :=
  { funcs := [readFn L replies, writeFn L replies, exitFn] ++ calls.map (sysFn F L I replies) }

theorem sys_contract {call : Call} (member : call ∈ shimCalls) (before : Store (Observed LinuxWorld))
    (args : List Value) :
    sysContract (linuxHost F L I replies) call before args
      (sysInvoke F L I replies call before args) := by
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [sysInvoke, ↓reduceIte]
  · exact clock_contract F L I replies before args
  · exact random_contract F L I replies before args
  · exact sizes_contract F L I replies rfl
      (fun _ => by rw [sysImage_argsSizes]; exact ⟨rfl, rfl, rfl⟩) before args
  · exact strings_contract F L I replies rfl (shimReported_args I)
      (fun _ => by rw [sysImage_args]; exact ⟨rfl, rfl, rfl⟩) before args
  · exact sizes_contract F L I replies rfl
      (fun _ => by rw [sysImage_environSizes]; exact ⟨rfl, rfl, rfl⟩) before args
  · exact strings_contract F L I replies rfl (shimReported_environ I)
      (fun _ => by rw [sysImage_environ]; exact ⟨rfl, rfl, rfl⟩) before args
  · exact open_contract F L I replies before args
  · exact close_contract F L I replies before args
  · exact handleRead_contract F L I replies before args
  · exact handleWrite_contract F L I replies before args
  · exact prestat_contract F L I replies before args
  · exact dirName_contract F L I replies before args

/-- The shim's environment satisfies the contracts of `linuxHost F L I replies` for every module
with at most the three stream imports and the flat calls `calls`, all of which the shim
implements. -/
theorem linuxEnv_satisfies (calls : List Call) (supported : ∀ call ∈ calls, call ∈ shimCalls)
    (m : Wasm.Module) (imports : m.imports.length ≤ 3 + calls.length) :
    (linuxEnv F L I replies calls).Satisfies m (hostSpecWith (linuxHost F L I replies) calls) := by
  intro index bound
  match index, bound with
  | 0, _ =>
    exact ⟨readFn L replies, _, rfl, hostSpecWith_read _ calls, read_contract F L I replies⟩
  | 1, _ =>
    exact ⟨writeFn L replies, _, rfl, hostSpecWith_write _ calls, write_contract F L I replies⟩
  | 2, _ => exact ⟨exitFn, _, rfl, hostSpecWith_exit _ calls, exit_contract F L I replies⟩
  | position + 3, bound =>
    have inCalls : position < calls.length := by omega
    refine ⟨sysFn F L I replies calls[position], sysContract (linuxHost F L I replies)
      calls[position], ?_, ?_, sys_contract F L I replies (supported _ (List.getElem_mem inCalls))⟩
    · simp [linuxEnv, inCalls]
    · rw [Nat.add_comm]
      exact hostSpecWith_sys _ (List.getElem?_eq_getElem inCalls)

end Verified.Shim
