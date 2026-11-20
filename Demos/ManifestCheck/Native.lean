import Demos.ManifestCheck.Budget
import Verified.Shim
import Verified.Shim.Args
import Verified.ShimA64.Elf

/-! The footprint theorems of the manifest checker's command at the memory cap of a native
executable.  The shim implements every flat call that the command imports (`calls_supported`).  A
native executable reserves a smaller linear memory than the module's declared cap of 65,535 pages,
and `nativeStore` holds the module's initial store with the executable's cap and the world
`nativeWorld`.  `main` takes the table of SHA-256's round constants, which the store holds as it
holds it in `initialStore` (`native_table_rep`, `native_table_low`).  `linux_footprint_native`
states that every Talos run of `_start` from that store under the shim's environment with enough
fuel has the footprint of `Footprint`: the layer events are images of the run's WASI trace, which
ends at an accepted exit, a rejected exit, a trap of the shim, or a trap of the guest after a
prefix of `main`.

`linux_footprint_bounded` states the footprint without a guest trap at a cap of at most 65,535
pages that hold `budget M` above the static heap's top, for a launch whose arguments' strings, each
with its zero
byte, and eight-byte pointers take at most `argsLimit` bytes, and for replies `R` that meet
`StatxBounded F L I M R`.  `StatxBounded` states the premise of `body_bounded` on
`fd_filestat_get` in terms of the replies, as `LeanExe.Wasi.Host.Along`: at each prefix of
`main` under `linuxHost F L I R` whose next request is `fd_filestat_get` of a descriptor that the
shim holds, the reply `R k` of the `statx` that the shim then makes after the
world's `k` layer events, when the shim's `filestatReply` reads errno 0 from it, reports a size of
at most `M` bytes or of `2^32` bytes or more.  `main` makes at most one such request, of the
manifest's descriptor, so the premise bounds the reply to the run's `statx` and no other reply of
`R`.  The earlier replies decide whether that `statx` happens and its index.
`statx_along` gives `StatAlong` of `main` from it, since the image of `fd_filestat_get` of a held
descriptor is one `statx` that holds the reply `R k`.  `budget_fits` states that the budget of a
manifest of `manifestLimit` bytes, 1 MiB, fits the 4,096 pages of the native executable. -/

namespace Demos.ManifestCheck

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim Verified.ShimA64

theorem calls_supported : ∀ call ∈ command.sysCalls, call ∈ shimCalls := by decide +kernel

/-- The native store, erased to the pure store, is the command's initial store with the cap
`cap`. -/
theorem erase_native (cap : Nat) :
    PureTransport.erase (nativeStore command.module cap nativeWorld) =
      { PureTransport.erase (initialStore nativeWorld) with memoryCaps := [cap] } := by
  have same : PureTransport.erase (initialStore nativeWorld) =
      (command.module.initialStore : Store Unit) := by
    unfold initialStore compileInitialStoreWith
    rw [PureTransport.erase_restore, command.module]
  rw [same]
  unfold nativeStore initStore PureTransport.erase
  generalize (command.module.initialStore : Store Unit) = X
  cases X
  rfl

theorem borrowed_caps {heap : Heap} {s : Store Unit} {ptr : UInt64} {words : Array UInt64}
    (c : List Nat) (h : heap.Borrowed s ptr words) :
    heap.Borrowed { s with memoryCaps := c } ptr words := ⟨h.values, h.below, h.separate⟩

theorem at_caps {heap : Heap} {s : Store Unit} (c : List Nat) (h : heap.At s) :
    heap.At { s with memoryCaps := c } :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

theorem static_caps {pool : Verified.Bytes.LiteralPool} {heap : Heap} {s : Store Unit}
    (c : List Nat) (h : pool.Static heap s) : pool.Static heap { s with memoryCaps := c } := h

/-- The table's address represents `mainArgs` in the native store, borrowed. -/
theorem native_table_rep {cap : Nat} {modes : Nat → Verified.Mode}
    (borrowed : modes 0 = .borrowed) :
    Verified.Env.Rep modes (Verified.initialStaticHeap command.literalPool)
      (PureTransport.erase (nativeStore command.module cap nativeWorld))
      [Value.i64 (Verified.tableAddr command.pure.tables 0)] mainArgs := by
  have initialized := command.initial nativeWorld
  rw [erase_native]
  exact Verified.Env.withTables_rep (tables := command.pure.tables) [⟨0, by decide⟩]
    (fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this
      exact borrowed)
    (fun k hk => by
      rw [List.mem_singleton.mp hk]
      exact borrowed_caps _ (initialized.2.2.1 0 (by decide))) rfl

/-- The table lies apart from the low memory in the native store. -/
theorem native_table_low {cap : Nat} {modes : Nat → Verified.Mode}
    (borrowed : modes 0 = .borrowed) :
    ∀ region ∈ Verified.Env.reads (PureTransport.erase (nativeStore command.module cap nativeWorld))
      modes [Value.i64 (Verified.tableAddr command.pure.tables 0)] mainArgs,
      LeanExe.Runtime.regionsDisjoint ABI.low region := by
  rw [erase_native]
  intro region hregion
  have reads := Verified.Env.withTables_reads
    (store := { PureTransport.erase (initialStore nativeWorld) with memoryCaps := [cap] })
    (tables := command.pure.tables) [⟨0, by decide⟩] (modes := modes)
    (fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this
      exact borrowed) (ws := []) (env := Verified.Env.nil)
  have member : region ∈ Verified.Env.reads
      { PureTransport.erase (initialStore nativeWorld) with memoryCaps := [cap] } modes
      (([⟨0, by decide⟩] : List (Fin command.pure.tables.length)).map
        (fun k => Value.i64 (Verified.tableAddr command.pure.tables k.val)) ++ [])
      (Verified.Env.withTables command.pure.tables [⟨0, by decide⟩] Verified.Env.nil) := hregion
  rw [reads] at member
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons]
    at member
  rcases member with rfl | member
  · unfold LeanExe.Runtime.regionsDisjoint ABI.low
    left
    decide
  · nomatch member

/-- The static heap's facts in the native store. -/
theorem native_at {cap : Nat} :
    (Verified.initialStaticHeap command.literalPool).At
      (PureTransport.erase (nativeStore command.module cap nativeWorld)) := by
  rw [erase_native]
  exact at_caps _ (command.initial nativeWorld).1

/-- The static data of the literal pool in the native store. -/
theorem native_static {cap : Nat} :
    command.literalPool.Static (Verified.initialStaticHeap command.literalPool)
      (PureTransport.erase (nativeStore command.module cap nativeWorld)) := by
  rw [erase_native]
  exact static_caps _ (command.initial nativeWorld).2.2.2

theorem linux_footprint_native (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (replies : Linux.Replies) {cap : Nat} (hcap : cap ≤ 65535) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) nativeWorld true
        (run fuel command.module startIndex (nativeStore command.module cap nativeWorld) []
          (linuxEnv F L I replies command.sysCalls)) := by
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := true)
    (initial := nativeStore command.module cap nativeWorld) (budget := 0)
    (linuxEnv_satisfies F L I replies _ calls_supported _
      (by simp [compile_imports_with, ABI.importsWith_length]))
    native_at (native_table_rep rfl) Separate.nil ⟨native_static, fun _ _ => Apart.nil⟩
    (native_table_low rfl) hcap (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

/-- The reply `r` answers the `statx` that the shim makes for a request of `fd_filestat_get` of a
descriptor of `opened` that `action` makes first: when `filestatReply` reads errno 0 from it, the
record reports a size of at most `M` bytes or of `2^32` bytes or more. -/
def StatxAt (opened : List UInt64) (M : Nat) (r : Linux.Reply) : Action α → Prop
  | .sys call args _ => call = Call.fdFilestatGet → ∀ fd, args = [.word fd] → fd ∈ opened →
      ∀ outputs, filestatReply r.ret ((List.range 256).map r.bytes) = .returned 0 outputs →
        (statSize outputs).toNat < 2 ^ 32 → (statSize outputs).toNat ≤ M
  | _ => True

/-- The replies `R` answer as `StatxAt` states every `statx` that the shim makes for a request of
`fd_filestat_get` of a prefix of `main` under `linuxHost F L I R` from `nativeWorld`: the shim
makes it for a descriptor that it holds, as the call after the world's `k` layer events, which
takes the reply `R k`.  `main` makes at most one such request, of the manifest's descriptor, and
the premise bounds no other reply of `R`. -/
def StatxBounded (F : OpenFlags) (L : ShimLayout) (I : Launch) (M : Nat) (R : Linux.Replies) :
    Prop :=
  (linuxHost F L I R).Along
    (fun residual world => StatxAt (openNumbers I world.events) M (R world.events.length) residual)
    main nativeWorld.world

/-- Under the shim's host with replies that meet `StatxBounded M`, every reply with errno 0 to a
request of `fd_filestat_get` that a prefix of `main` makes reports a size of at most `M` bytes or
of `2^32` bytes or more. -/
theorem statx_along {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {M : Nat} (bounded : StatxBounded F L I M R) :
    StatAlong (linuxHost F L I R) M main nativeWorld.world := by
  intro trace residual world progress
  have answered := bounded _ _ _ progress
  cases residual with
  | sys call args next =>
    intro named outputs after step small
    subst named
    obtain ⟨l, ⟨-, image⟩, carried, -, -⟩ := step
    rw [sysImage_filestat] at image
    unfold FilestatImage at image
    split at image
    · rename_i fd
      split at image
      · rename_i held
        obtain ⟨ret, output, rfl, reply⟩ := image
        obtain ⟨⟨hret, hout⟩, -⟩ := carried
        dsimp only at hret hout
        simp only [Linux.outputRegions, Linux.statxCall, Linux.arg, Linux.Param.words] at hout
        rw [hret, hout] at reply
        exact answered rfl fd rfl held _ reply.symm small
      · obtain ⟨-, same⟩ := image
        exact absurd (Transfer.returned.inj same).1 (by decide)
    · exact image.elim
  | _ => trivial

/-- The budget of `main` holds under the shim's host for a launch whose arguments' strings and
eight-byte pointers take at most `argsLimit` bytes and for replies that meet `StatxBounded M`. -/
theorem call_prefix_bound (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies)
    {M : Nat} (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (bounded : StatxBounded F L I M R) :
    Resource.CallPrefixBound (observedHost (linuxHost F L I R))
      (.ofProg command.pure.program command.pure.funs) command.program .here 0 mainArgs nativeWorld
      (budget M) :=
  prefix_bound (fun _ _ _ step => by
      rw [linux_sizes step]
      exact reportedSize_le (by decide) (by decide) small)
    (statx_along bounded)

/-- The footprint of `linux_footprint_native` without a guest trap, at a cap of at most 65,535 pages
that hold `budget M` above the static heap's top, for a launch whose arguments meet the premise of
`call_prefix_bound` and replies that meet `StatxBounded M`. -/
theorem linux_footprint_bounded (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (R : Linux.Replies) {M : Nat} (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (bounded : StatxBounded F L I M R) {cap : Nat} (hcap : cap ≤ 65535)
    (room : (Verified.initialStaticHeap command.literalPool).top.toNat + budget M ≤ 65536 * cap) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I R (main.bind fun status => Action.exit status) nativeWorld false
        (run fuel command.module startIndex (nativeStore command.module cap nativeWorld) []
          (linuxEnv F L I R command.sysCalls)) := by
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I R) (aborts := false)
    (initial := nativeStore command.module cap nativeWorld) (budget := budget M)
    (linuxEnv_satisfies F L I R _ calls_supported _
      (by simp [compile_imports_with, ABI.importsWith_length]))
    native_at (native_table_rep rfl) Separate.nil ⟨native_static, fun _ _ => Apart.nil⟩
    (native_table_low rfl) hcap
    (fun _ => ⟨by change _ + budget M ≤ 65536 * cap; exact room,
      call_prefix_bound F L I R small bounded⟩)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I R (results fuel enough)⟩

/-- The bound on the manifest's size of the native executable's corollary: 1 MiB, whose budget
fits above the static heap's top in the executable's 4,096 pages. -/
def manifestLimit : Nat := 1048576

theorem budget_fits :
    (Verified.initialStaticHeap command.literalPool).top.toNat + budget manifestLimit ≤
      65536 * 4096 := by
  have bound : budget manifestLimit ≤ 181 * 1048576 + 12649115 := budget_le manifestLimit
  have top : (Verified.initialStaticHeap command.literalPool).top.toNat ≤ 65536 := by decide
  omega

#print axioms calls_supported
#print axioms linux_footprint_native
#print axioms statx_along
#print axioms call_prefix_bound
#print axioms linux_footprint_bounded
#print axioms budget_fits

end Demos.ManifestCheck
