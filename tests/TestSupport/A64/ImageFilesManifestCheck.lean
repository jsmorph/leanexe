import TestSupport.A64.WasiElf
import TestSupport.A64.ElfWitness
import Demos.ManifestCheck.Native
import Demos.ManifestCheck.NativeMeets
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi wasm` writes for the manifest checker's command
of `Demos/ManifestCheck/Command.lean`, which checks the SHA-256 digests of a manifest's files
under the preopened directory as `sha256sum -c` does.  `tests/linux/a64-wasi.sh` elaborates this
file in the directory of the executable, so `file_nat%` and `file_size%` read manifest.elf, and no
build target includes it.  The kernel evaluates `genWasiElf` on the command's module, the index of
`_start`, the stack's room, and the cap, and checks that the executable's bytes are the file's
(`manifest_elf_file`).  `manifest_elf_segments` states the two program headers that `elfSegments`
reads from the file, `manifest_elf_layout` that they are those of the generator's layout,
`manifest_elf_entry` that the file's entry is the prefix `wasiEntry`, and `manifest_elf_room` that
the stack's room holds the module's stack bound.

The command imports `path_open`, `fd_close`, `fd_read` on a handle, and `fd_filestat_get`, so the
executable starts with the check of descriptor 3, whose events and outcome `preopenRun` gives for
the path buffer of the scratch and the replies from the first on.  `manifest_elf` holds for every
reply sequence.  From a process whose memory holds the file as Linux's loader places it, with the
arguments `args` and the environment `environ` on Linux's initial stack at SP, the program counter
at the entry, and no event in the trace, the process reaches `SVC #0` with X8 at 94, `exit_group`,
with the UART's state as it was.  When the check ends the run, the trace holds its events and X0
holds 67.  Otherwise the launch grants descriptor 3 as the check found it, and the trace holds the
check's events and then the layer events `ls`, the images of the WASI events `T` of a run of the
command's action under `linuxHost` with the replies after the check's.  Each event of `ls` holds
its reply and writes within the cap's linear memory or into the `statx` record, the events of
`ls` name only standard streams and the descriptor numbers that the shim holds open (`NamesHeld`),
and the writes of descriptor 1 in `ls` took the bytes that the `fd_write` events of `T` to
standard output committed.  The run is an accepted exit, whose status X0 holds, an exit that the
shim rejects, with X0 at 1, a trap of the shim, with X0 at 2, or a trap of the guest after a
prefix of the action, with X0 at 2.

`manifest_elf_meets` is the corollary for the file, from arguments whose strings, each with its
zero byte, and eight-byte pointers take at most `argsLimit` bytes, as Linux requires of every
process, and for replies that meet `StatxAfterCheck`: after the check, the reply to the `statx` of
the manifest's `fd_filestat_get`, when the shim reads errno 0 from it, reports at most
`manifestLimit` bytes, whose budget fits the executable's 4,096 pages (`budget_fits`), or `2^32`
bytes or more.  The premise bounds no other reply.  When the check does
not end the run and the results of the layer events `ls` lie in Linux's range (`InRange`), X0 and
`ls` meet `NMeets` for the check's grant of descriptor 3.
`manifest_elf_runs` gives the run from `linux_footprint_bounded`, the footprint without a guest
trap, through `wasiElf_footprint_with`, and `linux_exec_meets` gives the status and `NMeets` from
the `Exec` run that the footprint names.

`manifest_elf_witness` shows that the corollary's premises and `InRange` hold together.  The
process holds the file in memory as `ElfLoaded` states and, at SP `2^32`, the initial stack of the
arguments `witnessArgs`, `h` and `1`, with no environment.  Under the replies `witnessReplies`, the
check's `openat` returns descriptor 4 and its `close` 0, so the check grants descriptor 3, and
every later call returns `-ENOENT`, from which `filestatReply` reads errno 44, so the replies meet
`StatxAfterCheck`.  The process reaches `exit_group` after layer events whose results lie in
Linux's range and that meet `NMeets` with X0.  The manifest's `openat2` returns `-ENOENT`, so the
run ends before any `statx`, and the bound of `StatxAfterCheck` applies to no reply of that run.
-/

namespace TestSupport.A64.ImageFilesManifestCheck

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Demos.ManifestCheck TestSupport.A64.WasiElf TestSupport.A64.ElfWitness

def manifestElfBytes : Nat := file_nat% "manifest.elf"
def manifestElfSize : Nat := file_size% "manifest.elf"

/-- The executable's layout. -/
def manifestLayout : ElfLayout := wasiLayout command.module startIndex wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def manifestShimLayout : ShimLayout := wasiShimLayout command.module startIndex wasiRoom wasiCap

/-- The shim's scratch of the executable. -/
def manifestScratch : Scratch := wasiScratch command.module startIndex wasiRoom wasiCap

set_option maxRecDepth 100000

theorem manifest_elf_file : bytesOk (genWasiElf command.module startIndex wasiRoom wasiCap)
    manifestElfBytes manifestElfSize = true := by decide +kernel

theorem manifest_elf_segments : elfSegments (byteAt manifestElfBytes) =
    [⟨1, 5, 0, 0x400000, 61680, 61680⟩, ⟨1, 6, 0x10000, 0x410000, 8712, 268510288⟩] := by
  decide +kernel

theorem manifest_elf_layout : elfSegmentsOf manifestLayout =
    [⟨1, 5, 0, 0x400000, 61680, 61680⟩, ⟨1, 6, 0x10000, 0x410000, 8712, 268510288⟩] := by
  decide +kernel

theorem manifest_elf_entry : elfEntryOf (byteAt manifestElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem manifest_elf_room : wasiStackBound command.module startIndex ≤ wasiRoom.toNat := by
  decide +kernel

theorem manifest_startup (R : Linux.Replies) :
    startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module startIndex wasiRoom wasiCap) R =
      preopenRun manifestScratch.path R 0 := by
  rw [command.module, compile_imports_with]
  rfl

theorem manifest_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt manifestElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform manifestLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords manifestLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords manifestLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      match preopenRun manifestScratch.path R 0 with
      | (l₀, none) => q.trace = l₀.map A64.Event.sys ∧ q.core.x 0 = 67
      | (l₀, some granted) =>
        ∃ T ls w, q.trace = (l₀ ++ ls).map A64.Event.sys ∧
          Images arm64Flags manifestShimLayout ⟨args, environ, granted⟩ [] T ls ∧
          Carried R l₀.length ls ∧
          (∀ e ∈ ls, WritesNative manifestShimLayout (wasiCap * 65536) e) ∧
          NamesHeld ⟨args, environ, granted⟩ [] ls ∧
          Linux.writeData 1 ls = committedWrites 1 T ∧
          ((∃ c, Exec (linuxHost arm64Flags manifestShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.exited c) w ∧ q.core.x 0 = c) ∨
            (Exec (linuxHost arm64Flags manifestShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
            (Exec (linuxHost arm64Flags manifestShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
            ((∃ residual, Prefix (linuxHost arm64Flags manifestShimLayout
                ⟨args, environ, granted⟩ (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              residual w) ∧ q.core.x 0 = 2)) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint (calls := command.sysCalls) manifest_elf_file
      (manifest_elf_segments.trans manifest_elf_layout.symm) himp calls_supported (by decide)
      manifest_elf_room
      (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, ?_⟩
  rw [manifest_startup] at hq
  generalize preopenRun manifestScratch.path R 0 = pr at hq ⊢
  rcases pr with ⟨l₀, _ | granted⟩
  · exact hq
  · obtain ⟨T, ls, w, trq, himg, hcar, hwq, hend⟩ := hq
    refine ⟨T, ls, w, trq, himg, hcar, hwq, images_namesHeld himg, himg.writeData 1, ?_⟩
    rcases hend with h | h | h | ⟨-, h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))

/-- The replies `R` meet `StatxBounded manifestLimit` after the check of descriptor 3 when the
check does not end the run: under the shim's host for the launch of `args` and `environ` with the
check's grant, with the replies after the check's.  The premise bounds only the reply to the
`statx` of the manifest's `fd_filestat_get`. -/
def StatxAfterCheck (args environ : List (List UInt8)) (R : Linux.Replies) : Prop :=
  ∀ l₀ granted, preopenRun manifestScratch.path R 0 = (l₀, some granted) →
    StatxBounded arm64Flags manifestShimLayout ⟨args, environ, granted⟩ manifestLimit
      (fun j => R (l₀.length + j))

/-- The runs of the file from arguments and replies within the limits of the corollary: when the
check does not end the run, the process reaches `exit_group` after the check's events and the
layer events `ls`, which hold their replies, and `ls` are the images of the WASI events `T` of an
`Exec` run of the command's action that ends at an accepted exit, whose status X0 holds, at an
exit that the shim rejects, or at a trap of the shim. -/
theorem manifest_elf_runs (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ argsLimit)
    (bounded : StatxAfterCheck args environ R)
    (hl : ElfLoaded (byteAt manifestElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform manifestLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords manifestLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords manifestLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      match preopenRun manifestScratch.path R 0 with
      | (l₀, none) => q.trace = l₀.map A64.Event.sys ∧ q.core.x 0 = 67
      | (l₀, some granted) =>
        ∃ T ls w, q.trace = (l₀ ++ ls).map A64.Event.sys ∧
          Images arm64Flags manifestShimLayout ⟨args, environ, granted⟩ [] T ls ∧
          Carried R l₀.length ls ∧
          ((∃ c, Exec (linuxHost arm64Flags manifestShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.exited c) w ∧ q.core.x 0 = c) ∨
            Exec (linuxHost arm64Flags manifestShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.trapped exitRejected) w ∨
            Exec (linuxHost arm64Flags manifestShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.trapped shimTrap) w) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint_with manifest_elf_file
      (manifest_elf_segments.trans manifest_elf_layout.symm) himp calls_supported (by decide)
      manifest_elf_room R p
      (fun l₀ granted h => linux_footprint_bounded arm64Flags _ ⟨args, environ, granted⟩ _ small
        (bounded l₀ granted h) (by decide) budget_fits)
      hl hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, ?_⟩
  rw [manifest_startup] at hq
  generalize preopenRun manifestScratch.path R 0 = pr at hq ⊢
  rcases pr with ⟨l₀, _ | granted⟩
  · exact hq
  · obtain ⟨T, ls, w, trq, himg, hcar, -, hend⟩ := hq
    refine ⟨T, ls, w, trq, himg, hcar, ?_⟩
    rcases hend with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨impossible, -⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · cases impossible

/-- The manifest checker's corollary for `manifest.elf`.  For every reply sequence `R` that meets
`StatxAfterCheck`, a process started as for `manifest_elf` with arguments whose strings,
each with its zero byte, and eight-byte pointers take at most `argsLimit` bytes, 6 MiB, reaches
`SVC #0` with X8 at 94, `exit_group`, and the UART's state as it was.  When the check of
descriptor 3 ends the run, the trace holds its events and X0 is 67.  Otherwise the trace holds the
check's events and then the layer events `ls`, each of which holds its reply of `R`, and when the
results of `ls` lie in Linux's range (`InRange`), X0 and `ls` meet `NMeets` for the check's grant
of descriptor 3: the manifest that the reads of the opened manifest returned, the verdicts that the
writes of descriptor 1 offered and took, the status, the confinement of every `openat2` to
descriptor 3 with RESOLVE_BENEATH, and the handles of the `read`, `statx`, and `close` calls. -/
theorem manifest_elf_meets (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ argsLimit)
    (bounded : StatxAfterCheck args environ R)
    (hl : ElfLoaded (byteAt manifestElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform manifestLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords manifestLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords manifestLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      match preopenRun manifestScratch.path R 0 with
      | (l₀, none) => q.trace = l₀.map A64.Event.sys ∧ q.core.x 0 = 67
      | (l₀, some granted) =>
        ∃ ls, q.trace = (l₀ ++ ls).map A64.Event.sys ∧ Carried R l₀.length ls ∧
          (InRange ls → NMeets granted args ls (q.core.x 0)) := by
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ := manifest_elf_runs R p small bounded hl hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, ?_⟩
  generalize preopenRun manifestScratch.path R 0 = pr at hq ⊢
  rcases pr with ⟨l₀, _ | granted⟩
  · exact hq
  · obtain ⟨T, ls, w, trq, himg, hcar, hend⟩ := hq
    refine ⟨ls, trq, hcar, fun range => ?_⟩
    have noZero : ∀ s ∈ args, (0 : UInt8) ∉ s := fun s m => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem m
      exact (hstack.argv i hi).2.2.1
    rcases hend with ⟨c, h, hx⟩ | h | h
    · obtain ⟨c', exited, meets⟩ :=
        linux_exec_meets rfl noZero small h himg range (Carried.sized hcar)
      cases exited
      rw [hx]
      exact meets
    · obtain ⟨_, exited, -⟩ := linux_exec_meets rfl noZero small h himg range (Carried.sized hcar)
      cases exited
    · obtain ⟨_, exited, -⟩ := linux_exec_meets rfl noZero small h himg range (Carried.sized hcar)
      cases exited

/-! ## The premises hold together -/

/-- The replies of the witness: descriptor 4 for the check's `openat`, 0 for its `close`, and
`-ENOENT` for every later call, each with zero bytes. -/
def witnessReplies : Linux.Replies := fun k =>
  if k = 0 then ⟨4, fun _ => 0⟩ else if k = 1 then ⟨0, fun _ => 0⟩ else ⟨0 - 2, fun _ => 0⟩

theorem witness_startup : preopenRun manifestScratch.path witnessReplies 0 =
    ([preopenOpenEvent manifestScratch.path ⟨4, fun _ => 0⟩,
      preopenCloseEvent 4 ⟨0, fun _ => 0⟩], some true) := by
  rfl

/-- The witness's replies after the check's two give errno 44 (`noent`) to every `statx`, so they
meet `StatxAfterCheck` for every argument list and environment. -/
theorem witness_bounded {args environ : List (List UInt8)} :
    StatxAfterCheck args environ witnessReplies := by
  intro l₀ granted h
  rw [witness_startup] at h
  cases h
  intro trace residual world _
  cases residual with
  | sys call args next =>
    intro _ fd _ _ outputs reply _
    have later : witnessReplies (2 + world.events.length) = ⟨0 - 2, fun _ => 0⟩ := by
      unfold witnessReplies
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have error : filestatReply (witnessReplies (2 + world.events.length)).ret
        ((List.range 256).map (witnessReplies (2 + world.events.length)).bytes) =
          .returned 44 [zeros 64] := by
      rw [later]
      rfl
    exact absurd (Transfer.returned.inj (error.symm.trans reply)).1 (by decide)
  | _ => trivial

theorem carried_errors : ∀ {k : Nat} {ls : List Linux.Event}, 2 ≤ k →
    Carried witnessReplies k ls → ∀ e ∈ ls, e.ret = 0 - 2
  | _, [], _, _ => fun _ m => nomatch m
  | k, e :: ls, low, ⟨carries, rest⟩ => fun x m => by
    rcases List.mem_cons.mp m with rfl | m
    · rw [carries.1]
      unfold witnessReplies
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · exact carried_errors (by omega) rest x m

theorem witness_inRange {ls : List Linux.Event} (carried : Carried witnessReplies 2 ls) :
    InRange ls := fun e m => by
  have error : Linux.isError e.ret = true := by
    rw [carried_errors (Nat.le_refl 2) carried e m]
    decide
  exact ⟨fun _ => .inl error, fun _ => .inl error, fun _ => .inr error, fun _ => .inl error⟩

/-- The premises of `manifest_elf_meets` and `InRange` hold together.  For the replies
`witnessReplies`, the process with the memory `loadedMem` of the file and `witnessStack`, the
arguments `witnessArgs`, no environment, and the stack's top `witnessTop`, every premise of the
corollary holds, the check grants descriptor 3, and the process reaches `exit_group` after the
check's events and layer events that hold their replies, whose results lie in Linux's range, and
that meet `NMeets` with X0. -/
theorem manifest_elf_witness :
    ∃ (R : Linux.Replies) (p : Proc) (args environ : List (List UInt8)) (top : UInt64),
      stringsSize args + 8 * args.length ≤ argsLimit ∧ StatxAfterCheck args environ R ∧
      ElfLoaded (byteAt manifestElfBytes) p.core.mem ∧
      InitialStack args environ p.core.sp top p.core.mem ∧ p.core.pc = wasiEntry ∧
      p.trace = [] ∧
      ∃ q, ProcReachWith Linux.table R (wasiPlatform manifestLayout p.core.sp top)
          (fetchFrom p.core.mem elfEntry (elfWords manifestLayout)) p q ∧
        fetchFrom p.core.mem elfEntry (elfWords manifestLayout) q.core.pc = some svcWord ∧
        q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
        ∃ l₀ ls, preopenRun manifestScratch.path R 0 = (l₀, some true) ∧
          q.trace = (l₀ ++ ls).map A64.Event.sys ∧ Carried R l₀.length ls ∧ InRange ls ∧
          NMeets true args ls (q.core.x 0) := by
  have small : stringsSize witnessArgs + 8 * witnessArgs.length ≤ argsLimit := by decide
  have loaded : ElfLoaded (byteAt manifestElfBytes)
      (loadedMem (byteAt manifestElfBytes) 61680 8712 witnessStack) :=
    loadedMem_loaded manifest_elf_segments (by decide) (by decide)
  have stack := loadedMem_stack (byteAt manifestElfBytes) 61680 8712
  refine ⟨witnessReplies, witnessProc (loadedMem (byteAt manifestElfBytes) 61680 8712 witnessStack),
    witnessArgs, [], witnessTop, small, witness_bounded, loaded, stack, rfl, rfl, ?_⟩
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    manifest_elf_meets witnessReplies
      (witnessProc (loadedMem (byteAt manifestElfBytes) 61680 8712 witnessStack)) small
      witness_bounded loaded stack rfl rfl
  refine ⟨q, rq, cq, x8q, ioq, ?_⟩
  rw [witness_startup] at hq
  obtain ⟨ls, trq, hcar, meets⟩ := hq
  have range := witness_inRange hcar
  exact ⟨_, ls, witness_startup, trq, hcar, range, meets range⟩

#print axioms manifest_elf_file
#print axioms manifest_elf_segments
#print axioms manifest_elf_layout
#print axioms manifest_elf_entry
#print axioms manifest_elf_room
#print axioms manifest_elf
#print axioms manifest_elf_runs
#print axioms manifest_elf_meets
#print axioms manifest_elf_witness

end TestSupport.A64.ImageFilesManifestCheck
