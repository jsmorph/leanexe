module

public import Verified.Shim.Host
public import Verified.Wasi.SysRule
public import LeanExe.Wasi.Sys

@[expose] public section

/-!
The block that a command's `args` asks for under the shim's host.  A successful `args_sizes_get`
reply under `linuxHost` holds the count and the size of the launch's arguments (`linux_sizes`), so
the block that it asks for, with a pointer of four bytes for each argument and three bytes of
alignment, fits every limit from 3 below `2^32` that the strings and eight-byte pointers of the
arguments fit (`reportedSize_le`).  A budget that bounds the block of `args` by such a limit
therefore holds under the shim's host for every launch whose arguments fit it, such as the 6 MiB
that Linux lets the strings and pointers of `argv` and `envp` take.  For such a launch, a run of
`args` under the shim's host that returns gives errno 0 and the launch's arguments, each followed
by a zero byte, and its events have no layer event as their image (`linux_args`).
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- Under the shim's host, a successful `args_sizes_get` reply holds the count and the size of the
launch's arguments. -/
theorem linux_sizes {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world after : LinuxWorld} {outputs : List Bytes}
    (step : (linuxHost F L I R).sys world Call.argsSizesGet [] (.returned 0 outputs) after) :
    outputs = sizesOutputs I.args := by
  obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
  rw [sysImage_argsSizes] at image
  obtain ⟨-, -, reply⟩ := image
  unfold sizesReply at reply
  split at reply
  · exact (Transfer.returned.inj reply).2
  · exact absurd (Transfer.returned.inj reply).1 (by decide)

theorem length_le_stringsSize (strings : List (List UInt8)) :
    strings.length ≤ stringsSize strings := by
  induction strings with
  | nil => simp [stringsSize]
  | cons s rest ih =>
    simp only [stringsSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- The block that the arguments ask for, with a pointer of four bytes for each and three bytes of
alignment, fits a limit from 3 below `2^32` when the strings and eight-byte pointers of the
arguments do. -/
theorem reportedSize_le {strings : List (List UInt8)} {limit : Nat} (low : 3 ≤ limit)
    (high : limit < 2 ^ 32) (small : stringsSize strings + 8 * strings.length ≤ limit) :
    Resource.reportedSize (sizesOutputs strings) ≤ limit := by
  have least := length_le_stringsSize strings
  have size : stringsSize strings < 2 ^ (8 * 4) := by omega
  have count : strings.length < 2 ^ (8 * 4) := by omega
  simp only [Resource.reportedSize, sizesOutputs, Reply.word, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some,
    littleEndian_leBytes (by decide) size, littleEndian_leBytes (by decide) count]
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat]
  rcases strings with _ | ⟨s, rest⟩
  · simp only [stringsSize, List.map_nil, List.sum_nil, List.length_nil] at small ⊢
    omega
  · simp only [List.length_cons] at small least count size ⊢
    omega

theorem stringsFit_of_le {strings : List (List UInt8)} {limit : Nat} (high : limit < 2 ^ 32)
    (small : stringsSize strings + 8 * strings.length ≤ limit) : stringsFit strings = true := by
  unfold stringsFit
  simp only [decide_eq_true_eq]
  omega

/-- Under the shim's host, an `args_sizes_get` reply for arguments that fit is errno 0 with their
count and size. -/
theorem linux_sizes_fit {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world after : LinuxWorld} {errno : UInt64} {outputs : List Bytes}
    (step : (linuxHost F L I R).sys world Call.argsSizesGet [] (.returned errno outputs) after)
    (fit : stringsFit I.args = true) :
    errno = 0 ∧ outputs = sizesOutputs I.args := by
  obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
  rw [sysImage_argsSizes] at image
  obtain ⟨-, -, reply⟩ := image
  unfold sizesReply at reply
  rw [if_pos fit] at reply
  exact ⟨(Transfer.returned.inj reply).1, (Transfer.returned.inj reply).2⟩

/-- Under the shim's host, a returned `args_get` reply is errno 0 with the arguments, each followed
by a zero byte. -/
theorem linux_strings_any {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world after : LinuxWorld} {errno : UInt64} {got : List Bytes}
    (step : (linuxHost F L I R).sys world Call.argsGet [] (.returned errno got) after) :
    errno = 0 ∧ got = [bytesOfList (stringsBytes I.args)] := by
  obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
  rw [sysImage_args] at image
  obtain ⟨-, -, reply⟩ := image
  unfold stringsReply at reply
  split at reply
  · exact ⟨(Transfer.returned.inj reply).1, (Transfer.returned.inj reply).2⟩
  · cases reply

/-- Under the shim's host, a returned run of `args` for arguments whose strings and eight-byte
pointers take at most a limit from 3 below `2^32` holds errno 0 and the arguments, each followed by
a zero byte, and the images of its events hold no layer event. -/
theorem linux_args {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {trace : List Event} {a : ArgsResult} {limit : Nat}
    (low : 3 ≤ limit) (high : limit < 2 ^ 32)
    (small : stringsSize I.args + 8 * I.args.length ≤ limit)
    (run : Exec (linuxHost F L I R) args world trace (.returned a) final) :
    a.errno = 0 ∧ a.bytes = bytesOfList (stringsBytes I.args) ∧
      ∀ events ls, Images F L I events trace ls → ls = [] := by
  have fit := stringsFit_of_le high small
  have reported := reportedSize_le low high small
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | @sys_return _ _ _ _ _ _ _ _ _ errno sizes _ reporter next =>
    obtain ⟨rfl, rfl⟩ := linux_sizes_fit reporter fit
    beta_reduce at next
    rw [if_neg (by simp [sysReply])] at next
    have below : ¬4294967296 ≤ (sysReply 0 (sizesOutputs I.args)).word 1 +
        4 * (sysReply 0 (sizesOutputs I.args)).word 0 + 3 := by
      rw [UInt64.le_iff_toNat_le]
      simp only [Resource.reportedSize, sysReply, ↓reduceIte] at reported ⊢
      simp only [UInt64.reduceToNat]
      omega
    rw [if_neg below] at next
    cases next with
    | sys_reject fits => exact absurd (by decide) fits
    | @sys_return _ _ _ _ _ _ _ _ _ gotErrno got _ getter next =>
      obtain ⟨rfl, rfl⟩ := linux_strings_any getter
      beta_reduce at next
      rw [if_neg (by simp [sysReply])] at next
      cases next
      refine ⟨rfl, rfl, fun events ls images => ?_⟩
      cases images with
      | cons first images =>
        cases images with
        | cons second images =>
          cases images
          obtain ⟨-, first⟩ := first
          rw [sysImage_argsSizes] at first
          obtain ⟨-, rfl, -⟩ := first
          obtain ⟨-, second⟩ := second
          rw [sysImage_args] at second
          obtain ⟨-, rfl, -⟩ := second
          rfl

end Verified.Shim
