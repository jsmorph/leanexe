import Verified.ShimA64.Flat
import LeanExe.A64.Proof.WasiProgram

/-!
The executable of `genWasiElf` from its entry to `exit_group`.  Linux enters the executable at the
prefix `wasiEntry` with SP at the initial stack (`InitialStack`), and the prefix keeps that SP in
X2 and branches to the runtime of `genElfEntry`, which reaches `main` (`elfEntry_main`) with X2
and the memory unchanged.  `main` stores X2 in the scratch's first word, calls the startup
routine, which returns at once, and calls `_start` (`run_wasiFront`, `run_wasiStart`) with the
module's initial store at the native cap in the area, `nativeStore`.  There the shim's machine
holds the store: the loader's zeros give the scratch's preopen flag and held bytes for a launch
without a preopened directory, and the initial stack lies from `2^32` up, where no instruction
before `_start` stores.
The simulation of `_start` over `shimMachine`, whose code map `wasiCode` holds the routine
`SVC #0; RET` and the program after `main`, none of whose instructions writes X17 or X18, follows
Talos's run of `_start` under the shim's environment.  When
that run traps at an accepted exit or a rejected one, the process stands at the exit word with
the status in X0, and when it traps in the shim or the guest, the process stands at the trap stub,
which sets status 2 and branches to the exit word.  From there the runtime makes `exit_group`.
`wasiElf_run` states this for every reply sequence and every fuel at which Talos's run of `_start`
traps: the process's trace holds the layer events of the final world, each of which writes within
the native cap's linear memory or is a `clock_gettime` into the timespec, and X0 holds the status.
`wasiElf_footprint_with` takes the trap from a footprint premise for one reply sequence and the
launch of the initial stack, which excludes a return of `_start` and every run that does not
finish, and `wasiElf_footprint` takes it from a premise for every reply sequence and launch.
The module's flat imports are those of calls of `shimCalls` whose stubs `flatStubs` lists, and
`flatStub_sim` gives the simulation of each.  The startup
routine makes no check of descriptor 3, so the launch grants no preopened directory.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-- The layout of the executable of `genWasiElf`, and an empty layout when the generator fails. -/
def wasiLayout (m : Module) (k : Nat) (room : UInt64) (cap : Nat) : ElfLayout :=
  match genWasiElf m k room cap with
  | .ok (_, L) => L
  | .error _ => ⟨0, 0, 0, 0, 0, 0⟩

/-- The scratch of the executable of `genWasiElf`, from the area's end. -/
def wasiScratch (m : Module) (k : Nat) (room : UInt64) (cap : Nat) : Scratch :=
  ⟨(wasiLayout m k room cap).area + UInt64.ofNat (areaSize cap)⟩

/-- The shim's layout of the executable of `genWasiElf`. -/
def wasiShimLayout (m : Module) (k : Nat) (room : UInt64) (cap : Nat) : ShimLayout :=
  shimLayout (wasiLayout m k room cap).area (wasiScratch m k room cap)

/-- The world in which a native run starts: no layer event, no exit, no recorded outputs, and no
WASI event. -/
def nativeWorld : Observed LinuxWorld := ⟨⟨[], none, fun _ => []⟩, []⟩

/-- The store in which `_start` starts natively: the module's initial store with the memory's cap
at `cap` pages and the world `w`. -/
def nativeStore (m : Module) (cap : Nat) (w : Observed LinuxWorld) :
    Store (Observed LinuxWorld) :=
  (initStore m cap).mapHost fun _ => w

theorem StoreRel.mapHost {P : Platform} {cap : Nat} {gts : List ValueType} {α β : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) (f : α → β) :
    StoreRel P cap gts (st.mapHost f) s :=
  ⟨h.caps, h.cap_lt, h.glen, h.pages, h.size, h.types, h.globals, h.bytes, h.mapped, h.below⟩

theorem trapStub_ok {a base : UInt64} {is : List Instr} (hg : trapStub a base = .ok is) :
    ∃ g, bField (after a 1) base = .ok g ∧ is = [.movz 0 2 0, .b g] := by
  unfold trapStub at hg
  cases h1 : bField (after a 1) base with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g =>
  simp only [h1, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g, rfl, hg.symm⟩

theorem wasiPrefix_ok {a : UInt64} {is : List Instr} (hg : wasiPrefix a = .ok is) :
    ∃ g, bField (after a 1) elfEntry = .ok g ∧ is = [.addImm 2 31 0, .b g] := by
  unfold wasiPrefix at hg
  cases h1 : bField (after a 1) elfEntry with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g =>
  simp only [h1, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g, rfl, hg.symm⟩

theorem readStub_length {a svc tr en : UInt64} {is : List Instr}
    (hg : readStub a svc tr en = .ok is) : is.length = 46 := by
  obtain ⟨_, _, _, _, _, _, checks, call, tail, _, _, _, _, hc, _, _, hcall, ht, rfl⟩ :=
    readStub_ok hg
  obtain ⟨_, _, _, _, rfl⟩ := bufferChecks_ok hc
  obtain ⟨_, _, rfl⟩ := bufferCall_ok hcall
  obtain ⟨_, _, _, _, _, _, rfl⟩ := resultTail_ok ht
  rfl

theorem writeStub_length {a svc tr en : UInt64} {is : List Instr}
    (hg : writeStub a svc tr en = .ok is) : is.length = 44 := by
  obtain ⟨_, _, _, _, checks, call, tail, _, _, _, _, hc, hcall, ht, rfl⟩ := writeStub_ok hg
  obtain ⟨_, _, _, _, rfl⟩ := bufferChecks_ok hc
  obtain ⟨_, _, rfl⟩ := bufferCall_ok hcall
  obtain ⟨_, _, _, _, _, _, rfl⟩ := resultTail_ok ht
  rfl

theorem wasiMain_length {a st e room : UInt64} {cap : Nat} {is : List Instr}
    (hg : wasiMain a st e room cap = .ok is) : is.length = 20 := by
  unfold wasiMain at hg
  cases hb1 : bField (after a 14) st with
  | error err => simp [hb1, bind, Except.bind] at hg
  | ok g1 =>
  cases hb2 : bField (after a 15) e with
  | error err => simp [hb1, hb2, bind, Except.bind] at hg
  | ok g2 =>
  simp only [hb1, hb2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  rfl

/-- The loader fills the data segment past the file's bytes with zeros. -/
theorem elf_zero {nb : Nat} {L : ElfLayout} {mem : UInt64 → UInt8}
    (hl : ElfLoaded (byteAt nb) mem) (hseg : elfSegments (byteAt nb) = elfSegmentsOf L) {j : Nat}
    (h1 : L.dataFile ≤ j) (h2 : j < L.dataMem) (hlt : L.area.toNat + j < 2 ^ 64) :
    mem (L.area + UInt64.ofNat j) = 0 := by
  have := hl ⟨1, 6, L.dataOff, L.area.toNat, L.dataFile, L.dataMem⟩
    (by rw [hseg]; simp [elfSegmentsOf]) rfl j h2
  dsimp only at this
  rw [if_neg (by omega)] at this
  have e : L.area + UInt64.ofNat j = UInt64.ofNat (L.area.toNat + j) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hlt ⊢
    omega
  rw [e, this]

/-- The executable of `genWasiElf` from its entry to `exit_group`, for every reply sequence `R` and
every fuel at which Talos's run of `_start` from `nativeStore` under the shim's environment traps
with the store `final` and the message `msg`: the run of `ProcReachWith` over
`LeanExe.Linux.table` on the platform of the data segment and the initial stack reaches `SVC #0`
with X8 at 94, its trace holds the layer events of the final world, each of which writes within
the `cap` pages of linear memory or is a `clock_gettime` into the timespec, and X0 holds the
accepted exit's status, 1 for a rejected exit, or 2 for a trap of the shim or of the guest.  The
premises are the kernel's check of the file, its program headers, the module's imports, whose flat
calls `calls` lie in `shimCalls`, a stack's room that is a multiple of 16 and holds
`wasiStackBound`, the loader's placement of the file, Linux's initial stack of the arguments
`args` and the environment `environ` at SP, the program counter at the entry, and an empty
trace. -/
theorem wasiElf_run {m : Module} {k : Nat} {room : UInt64} {cap : Nat} {nb len : Nat}
    {calls : List LeanExe.Wasi.Call} (hk : bytesOk (genWasiElf m k room cap) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (wasiLayout m k room cap))
    (himp : m.imports = ABI.importsWith calls) (hsup : ∀ c ∈ calls, c ∈ shimCalls)
    (hroom16 : room.toNat % 16 = 0) (hroom : wasiStackBound m k ≤ room.toNat)
    (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)} {top : UInt64}
    (hl : ElfLoaded (byteAt nb) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = [])
    {fuel : Nat} {final : Store (Observed LinuxWorld)} {msg : String}
    (hres : Wasm.run fuel m k (nativeStore m cap nativeWorld) []
      (linuxEnv arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R calls) =
        .Trap final msg) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform (wasiLayout m k room cap) p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap))) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap)) q.core.pc =
        some svcWord ∧ q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      q.trace = final.host.world.events.map A64.Event.sys ∧
      (∀ e ∈ final.host.world.events,
        WritesNative (wasiShimLayout m k room cap) (cap * 65536) e) ∧
      ((msg = exitTrap ∧ ∃ c, final.host.world.exited = some c ∧ q.core.x 0 = c) ∨
        (msg = exitRejected ∧ q.core.x 0 = 1) ∨
        ((msg = shimTrap ∨ msg = "unreachable" ∨ msg = "out of bounds memory access" ∨
          msg = "integer divide by zero") ∧ q.core.x 0 = 2)) := by
  obtain ⟨bytes, L, hg, -, hbyte⟩ := of_bytesOk hk
  have hL : wasiLayout m k room cap = L := by simp only [wasiLayout, hg]
  have hLS : wasiShimLayout m k room cap =
      shimLayout L.area ⟨L.area + UInt64.ofNat (areaSize cap)⟩ := by
    simp only [wasiShimLayout, wasiScratch, hL]
  rw [hL] at hseg ⊢
  rw [hLS] at hres ⊢
  generalize hG : (⟨L.area + UInt64.ofNat (areaSize cap)⟩ : Scratch) = G at hres ⊢
  obtain ⟨prog, -, hprog, hLeq, hbound, hpre, -, -⟩ := gen_elfEntry hg
  obtain ⟨stubs, gts, e, main, pre, rd, wr, ex, tr, sts, fns, himp', hmem, hroom32, hok, hgt, hgl,
    hen, hmg, hpg, hrdg, hwrg, hexg, htrg, hstsg, hfg, his, hall18, hall⟩ :=
    gen_wasiProgram hprog
  -- the flat imports: one stub of `flatStubs` for each call of `calls`
  have hcallsEq : calls.map ABI.callImport = stubs.map (·.decl) := by
    have h := himp.symm.trans himp'
    rw [ABI.importsWith_eq] at h
    exact List.append_cancel_left h
  have hlenCS : calls.length = stubs.length := by
    simpa using congrArg List.length hcallsEq
  -- the layout
  have hroomS : (room + UInt64.ofNat scratchSize).toNat = room.toNat + 5184 := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', scratchSize, Nat.reducePow]
    omega
  have hcodeEnd : L.codeEnd = 176 + 4 * (18 + prog.length) := by rw [hLeq]; rfl
  have hdataOff : L.codeEnd ≤ L.dataOff := by rw [hLeq]; simp only [elfLayoutOf, roundUp]; omega
  have hdm : L.dataMem = areaSize cap + room.toNat + 5184 + 16 := by
    rw [hLeq]
    show areaSize cap + (room + UInt64.ofNat scratchSize).toNat + 16 = _
    rw [hroomS]
    omega
  have hdf : L.dataFile = areaPrefix m := by rw [hLeq]; rfl
  have harea : L.area.toNat = 4194304 + L.dataOff := by
    have : L.area = elfBase + UInt64.ofNat L.dataOff := by rw [hLeq]; rfl
    rw [this, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [elfBase, UInt64.reduceToNat, Nat.reducePow] at hbound ⊢
    omega
  have hLL : L.area.toNat + L.dataMem ≤ 2 ^ 32 := by
    simp only [elfBase, UInt64.reduceToNat] at hbound
    omega
  have hLL' : L.area.toNat + areaSize cap + room.toNat + 5184 + 16 ≤ 2 ^ 32 := by
    have h := hLL
    rw [hdm, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc] at h
    exact h
  have hareaSz : areaSize cap < 2 ^ 32 := by
    rw [hdm] at hLL
    omega
  have hGbase : G.base.toNat = L.area.toNat + areaSize cap := by
    rw [← hG]
    show (L.area + UInt64.ofNat (areaSize cap)).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at hLL hareaSz ⊢
    omega
  have hGG : G.base.toNat + scratchSize < 2 ^ 64 := by
    rw [hGbase]
    unfold scratchSize
    rw [hdm] at hLL
    omega
  -- the prefix, from the entry to the runtime
  let c1 : State := { p.core.setXsp 2 (p.core.xsp 31 + UInt64.ofNat 0) with pc := p.core.pc + 4 }
  let p1 : Proc := { p with core := { c1 with pc := elfEntry } }
  have hm1 : p1.core.mem = p.core.mem := State.setXsp_mem
  have hx21 : p1.core.x 2 = p.core.sp := by
    show (p.core.setXsp 2 (p.core.xsp 31 + UInt64.ofNat 0)).x 2 = _
    rw [State.setXsp_eq_setX (by decide), State.x_setX_same (by decide), add_ofNat_zero]
    rfl
  obtain ⟨is, p0, hgp, hprogC, hrdC, -, hdom', hbase', hp0, pc0, f0, tr0, h30, hal, htop, hstk,
    h17, hdata, hamap, habove, hU, hio0, hx20, hmem0, hsp0, hexit⟩ :=
    elfEntry_main hg hbyte hseg (by rw [hroomS]; omega) p1 (by rw [hm1]; exact hl) rfl htr
      (code' := fetchFrom p.core.mem elfEntry (elfWords L)) (by rw [hm1])
  have hprogeq : prog = is := Except.ok.inj (hprog.symm.trans hgp)
  subst hprogeq
  have hsp : p0.core.sp.toNat = L.area.toNat + areaSize cap + room.toNat + 5184 + 16 := by
    have : L.stackTop = elfBase + UInt64.ofNat (L.dataOff + L.dataMem) := by rw [hLeq]; rfl
    rw [hsp0, this, UInt64.toNat_add, UInt64.toNat_ofNat', harea]
    simp only [elfBase, UInt64.reduceToNat, Nat.reducePow] at hbound ⊢
    rw [hdm] at hbound ⊢
    omega
  -- the machine's code: the routine `SVC #0; RET` and the program after `main`
  have lm := wasiMain_length hmg
  rw [his] at hprogC hall
  have cm := CodeAt.split _ hprogC (n := 20) (by simp [lm])
  have hall17 : (pre ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ sts ++ wasiStartup ++ fns).all
      Instr.keepsX17 = true := by
    rw [List.all_append, Bool.and_eq_true] at hall
    exact hall.2
  have hplen : prog.length = 20 +
      (pre ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ sts ++ wasiStartup ++ fns).length := by
    rw [his, List.length_append, lm]
  generalize hb :
    pre ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ sts ++ wasiStartup ++ fns = body
    at cm hall17 hall18 hplen
  have hA : (after (after elfExitWord 1) 20).toNat + 4 * body.length < 2 ^ 55 := by
    have : (after (after elfExitWord 1) 20).toNat = elfBase.toNat + 176 + 72 + 80 := by decide
    rw [this]
    simp only [elfBase, UInt64.reduceToNat] at hbound ⊢
    omega
  have hsvcA : svcRetAddr.toNat + 8 ≤ (after (after elfExitWord 1) 20).toNat := by decide
  have hdomW := wasiCode_dom (svc := svcRetAddr) (is := body) (a := after (after elfExitWord 1) 20)
    (by decide) hA
  have hkW := wasiCode_keeps (svc := svcRetAddr) (a := after (after elfExitWord 1) 20) hall17
  have hk18W := wasiCode_all (svc := svcRetAddr) (a := after (after elfExitWord 1) 20)
    (f := Instr.keepsX18) rfl hall18
  have hWsub : ∀ a w, wasiCode svcRetAddr (after (after elfExitWord 1) 20) body a = some w →
      fetchFrom p.core.mem elfEntry (elfWords L) a = some w :=
    wasiCode_sub (OpsAt.drop (l1 := [.ins (.movz 8 63 0)]) hrdC) cm.2
  have cAll : CodeAt (wasiCode svcRetAddr (after (after elfExitWord 1) 20) body)
      (after (after elfExitWord 1) 20) body :=
    wasiCode_prog hsvcA (by omega)
  generalize hW : wasiCode svcRetAddr (after (after elfExitWord 1) 20) body = W
    at hdomW hkW hk18W hWsub cAll
  have hsvcW : OpsAt W svcRetAddr [.svc, .ins (.ret 30)] := by rw [← hW]; exact wasiCode_svc
  have hwasiEntry : wasiEntry = wasiPrefixAt (after elfExitWord 1) := rfl
  generalize hA' : after elfExitWord 1 = A at *
  -- the parts of the program after `main`, from `after A 20`
  have lr := readStub_length hrdg
  have lw := writeStub_length hwrg
  obtain ⟨gp, hgp1, rfl⟩ := wasiPrefix_ok hpg
  obtain ⟨fx1, gx3, hfx1, hgx3, rfl⟩ := exitStub_ok hexg
  obtain ⟨gt, hgt1, rfl⟩ := trapStub_ok htrg
  rw [← hb] at cAll
  have c7 := CodeAt.split W cAll (n := 205 + sts.length)
    (by simp [lr, lw, errnoRoutine, errnoTable, wasiStartup] <;> omega)
  have c6 := CodeAt.split W c7.1 (n := 204 + sts.length)
    (by simp [lr, lw, errnoRoutine, errnoTable] <;> omega)
  have c6s := CodeAt.split W c6.1 (n := 204) (by simp [lr, lw, errnoRoutine, errnoTable])
  have c5 := CodeAt.split W c6s.1 (n := 98) (by simp [lr, lw])
  have c4 := CodeAt.split W c5.1 (n := 96) (by simp [lr, lw])
  have c3 := CodeAt.split W c4.1 (n := 92) (by simp [lr, lw])
  have c2 := CodeAt.split W c3.1 (n := 48) (by simp [lr])
  have c1' := CodeAt.split W c2.1 (n := 2) rfl
  simp only [after_after] at c7 c6 c6s c5 c4 c3 c2 c1'
  have csts : CodeAt W (wasiFlatAt A) sts := by
    rw [wasiFlatAt, show 224 = 20 + 204 from rfl]
    exact c6s.2
  have lsts := (genStubs_code (j := 3) hstsg csts).1
  have hsend : stubsEnd (wasiFlatAt A) stubs = after A (20 + (204 + sts.length)) := by
    rw [stubsEnd_eq, wasiFlatAt, after_after, lsts, ← Nat.add_assoc]
  have cfns : CodeAt W (after (stubsEnd (wasiFlatAt A) stubs) wasiStartup.length) fns := by
    rw [hsend, after_after, show 20 + (204 + sts.length) + wasiStartup.length =
      20 + (205 + sts.length) by simp [wasiStartup] <;> omega]
    exact c7.2
  -- the run of the prefix
  have cpre0 := hWsub _ _ (CodeAt.cons.mp c1'.1).1
  have cpre1 := hWsub _ _ (CodeAt.cons.mp (CodeAt.cons.mp c1'.1).2).1
  rw [after_after] at cpre1
  have hpc1 : c1.pc = after A 21 := by
    show p.core.pc + 4 = _
    rw [hpc, hwasiEntry, wasiPrefixAt, ← after_succ]
  have hpre1 : IReach (elfPlatform L) (fetchFrom p.core.mem elfEntry (elfWords L)) p p1 := by
    have s1 := istep_at (P := elfPlatform L) (code := fetchFrom p.core.mem elfEntry (elfWords L))
      (p := p) (c := c1) (by rw [hpc, hwasiEntry]; exact cpre0) (.inl rfl) rfl
      (by rw [hpc1]; exact hdom' _ _ cpre1)
    have hjump : after A 21 + sext 26 gp.val * 4 = elfEntry := by
      rw [show after A 21 = after (wasiPrefixAt A) 1 by rw [wasiPrefixAt, after_after]]
      exact bField_target hgp1
    have s2 := istep_at (P := elfPlatform L) (code := fetchFrom p.core.mem elfEntry (elfWords L))
      (p := { p with core := c1 }) (c := { c1 with pc := elfEntry }) (by rw [hpc1]; exact cpre1)
      (.inl rfl) (by
        show some { c1 with pc := c1.pc + sext 26 gp.val * 4 } = _
        rw [hpc1, hjump]) (show elfEntry.toNat < 2 ^ 55 by decide)
    exact .next s1 (.next s2 (.refl _))
  have hPe := elfPlatform_le_wasi L p.core.sp top
  -- the machine and its calls
  let I : Launch := ⟨args, environ, false⟩
  let S : Shared :=
    { trapUnreachable := wasiTrapAt A, trapBounds := wasiTrapAt A, trapDiv := wasiTrapAt A,
      trapStack := wasiTrapAt A, cap, globalTypes := gts, byteStores := true }
  have hRl : (fun j => R (([] : List Linux.Event).length + j)) = R :=
    funext fun j => by simp
  rw [← hRl] at hres
  let M := shimMachine R L G I p.core.sp top [] calls W hdomW hkW hk18W hLL hGG elfExitWord
    (cap * 65536)
  let need := wasiStackNeed m (m.funcs.length + 1)
  have h64 : m.memIs64 = false := memIs64_of_areaOk hok
  have hUm : (modulePlatform L G).normal (modulePlatform L G).uart = false := by
    simp only [modulePlatform, Bool.and_eq_false_iff]
    exact .inl hU
  have hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap) := by rw [← hG]
  have hdataW : areaSize S.cap + scratchSize ≤ L.dataMem := by
    show areaSize cap + 5184 ≤ L.dataMem
    rw [hdm]
    omega
  have hflat : ∀ c ∈ stubEntries (wasiFlatAt A) 3 stubs, ∃ imp hf,
      m.imports[c.1]? = some imp ∧ M.env.funcs[c.1]? = some hf ∧
      c.2.2 = (imp.params, imp.results) ∧
      M.StubSim S (need c.1) imp.params imp.results hf c.2.1 := by
    intro c hc
    obtain ⟨i, hi, is', b, rfl, hgi, hci⟩ := (genStubs_code hstsg csts).2 c hc
    have hic : i < calls.length := by omega
    have himpi : m.imports[3 + i]? = some stubs[i].decl := by
      rw [himp', List.getElem?_append_right (by simp [streamImports])]
      simp [streamImports, hi]
    have henvi : M.env.funcs[3 + i]? = some (sysFn arm64Flags (shimLayout L.area G) I
        (fun j => R (([] : List Linux.Event).length + j)) calls[i]) := by
      show (linuxEnv arm64Flags (shimLayout L.area G) I
        (fun j => R (([] : List Linux.Event).length + j)) calls).funcs[3 + i]? = _
      simp [linuxEnv, hic, Nat.add_comm]
    have hdi : ABI.callImport calls[i] = stubs[i].decl := by
      have := congrArg (fun l => l[i]?) hcallsEq
      simpa [hic, hi] using this
    refine ⟨stubs[i].decl, _, himpi, henvi, rfl, ?_⟩
    exact flatStub_sim (hmem _ (List.getElem_mem hi)) (hsup _ (List.getElem_mem hic)) hdi S
      (need (3 + i)) hgi hci hsvcW c5.2 hGb hdataW hUm (Nat.le_refl _)
  have hcalls := wasi_calls_ok M (need := need) (flat := stubEntries (wasiFlatAt A) 3 stubs)
    (by rw [himp']; rfl) h64
    (fun _ => hUm) rfl
    (readStub_sim (R := R) (L := L) (G := G) (I := I) (sp₀ := p.core.sp) (top := top) (l₀ := [])
      (calls := calls) (code := W) (hdom := hdomW) (hk := hkW) (hL := hLL) (hG := hGG)
      (base := elfExitWord) (size := cap * 65536) S (need 0) hrdg c1'.2 hsvcW c5.2 hUm
      (Nat.le_refl _))
    (writeStub_sim (R := R) (L := L) (G := G) (I := I) (sp₀ := p.core.sp) (top := top) (l₀ := [])
      (calls := calls) (code := W) (hdom := hdomW) (hk := hkW) (hL := hLL) (hG := hGG)
      (base := elfExitWord) (size := cap * 65536) S (need 1) hwrg c2.2 hsvcW c5.2 hUm)
    (exitStub_sim (R := R) (L := L) (G := G) (I := I) (sp₀ := p.core.sp) (top := top) (l₀ := [])
      (calls := calls) (code := W) (hdom := hdomW) (hk := hkW) (hL := hLL) (hG := hGG)
      (base := elfExitWord) (size := cap * 65536) S (need 2)
      (is := [.subsImm 31 0 126, .bcond 3 fx1, .movz 0 1 0, .b gx3]) hexg c3.2)
    hflat hfg cfns
    (fun k f hle hf => wasiStackNeed_ok (definedFunc_of hle hf) _)
  -- the end of a run: the exit word, or the trap stub and then the exit word
  have hp0w : ProcReachWith Linux.table R (wasiPlatform L p.core.sp top)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p p0 :=
    ((hpre1.le hPe).toWith Linux.table R).trans ((hp0.le hPe).toWith Linux.table R)
  have exitAt : ∀ q : Proc, ProcRunWith Linux.table R (wasiPlatform L p.core.sp top)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q → q.core.pc = elfExitWord →
      ∃ z, ProcReachWith Linux.table R (wasiPlatform L p.core.sp top)
          (fetchFrom p.core.mem elfEntry (elfWords L)) p z ∧
        fetchFrom p.core.mem elfEntry (elfWords L) z.core.pc = some svcWord ∧ z.core.x 8 = 94 ∧
        z.core.io = q.core.io ∧ z.trace = q.trace ∧ z.core.x 0 = q.core.x 0 := by
    intro q hq hpcq
    obtain ⟨z, rz, cz, x8z, x0z, trz, ioz⟩ := hexit q (.inr hpcq)
    exact ⟨z, hp0w.trans (hq.thenWith hdom' (by rw [hpcq]; exact hbase')
      ((rz.le hPe).toWith _ _)), cz, x8z, ioz, trz, x0z⟩
  have trapAt : ∀ q : Proc, q.fpcr = fpcrValue → ProcRunWith Linux.table R
      (wasiPlatform L p.core.sp top) (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q →
      q.core.pc = wasiTrapAt A →
      ∃ z, ProcReachWith Linux.table R (wasiPlatform L p.core.sp top)
          (fetchFrom p.core.mem elfEntry (elfWords L)) p z ∧
        fetchFrom p.core.mem elfEntry (elfWords L) z.core.pc = some svcWord ∧ z.core.x 8 = 94 ∧
        z.core.io = q.core.io ∧ z.trace = q.trace ∧ z.core.x 0 = 2 := by
    intro q hf hq hpcq
    have ct := CodeAt.cons.mp c4.2
    obtain ⟨s1, r1, p1', x01, -, -, -, io1⟩ := step_movz (wasiPlatform L p.core.sp top) W
      (s := q.core) (d := 0) (imm := 2) (hw := 0) (by decide) (by rw [hpcq]; exact ct.1)
    obtain ⟨s2, r2, p2, x2, -, -, io2⟩ := step_b (wasiPlatform L p.core.sp top) W (s := s1)
      (g := gt) (target := elfExitWord)
      (by rw [p1', hpcq, ← after_one]; exact (CodeAt.cons.mp ct.2).1)
      (by rw [p1', hpcq, ← after_one]; exact bField_target hgt1)
    have hs := ProcRunWith.mono hWsub (ProcRunWith.ofReach (T := Linux.table) (R := R) hf
      (r1.trans r2))
    obtain ⟨z, rz, cz, x8z, iz, tz, x0z⟩ :=
      exitAt _ (ProcRunWith.trans hdom' hq hs) p2
    refine ⟨z, rz, cz, x8z, ?_, tz, ?_⟩
    · rw [iz]
      show s2.io = _
      rw [io2, io1]
    · rw [x0z]
      show s2.x 0 = 2
      rw [x2, x01]
      decide
  -- `main` up to the entry of `_start`
  have hsp16 : (p0.core.sp - 16).toNat = p0.core.sp.toNat - 16 := by
    rw [toNat_sub_le (by show 16 ≤ _; omega)]
    rfl
  have hnormal : ∀ a : UInt64, L.area.toNat ≤ a.toNat → a.toNat < L.area.toNat + L.dataMem →
      (elfPlatform L).normal a = true := fun a h1 h2 => by
    simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le]
    exact ⟨h1, h2⟩
  have hscrE : ∀ k < 8, (elfPlatform L).normal
      (p0.core.x 17 + UInt64.ofNat (areaSize cap) + UInt64.ofNat k) = true := by
    intro k hk
    rw [h17, add_ofNat_add]
    have e : (L.area + UInt64.ofNat (areaSize cap + k)).toNat =
        L.area.toNat + areaSize cap + k := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
      omega
    apply hnormal
    · rw [e]
      omega
    · rw [e, hdm]
      omega
  obtain ⟨t0, rt0, pt0, x30t0, spt0, x18t0, x17t0, iot0, memt0⟩ :=
    run_wasiFront (elfPlatform L) (fetchFrom p.core.mem elfEntry (elfWords L)) hmg cm.1 pc0 hal
      (fun j hj => by
      rw [stack_main p0.core.sp (room + UInt64.ofNat scratchSize) j]
      exact hstk _ (by omega)) hscrE
  have cst := hWsub _ _ (CodeAt.cons.mp c6.2).1
  obtain ⟨t1, rt1, pt1, kt1, spt1, memt1, iot1⟩ :=
    step_ret (elfPlatform L) (fetchFrom p.core.mem elfEntry (elfWords L)) (s := t0) (n := 30)
    (by rw [pt0, hsend]; exact cst)
  rw [x30t0] at pt1
  obtain ⟨t, rt, pt, x30t, kt, spt, memt, iot⟩ :=
    run_wasiStart (elfPlatform L) (fetchFrom p.core.mem elfEntry (elfWords L)) hmg cm.1 pt1
  let q1 : Proc := { p0 with core := t }
  have hq1 : ProcRunWith Linux.table R (wasiPlatform L p.core.sp top)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q1 :=
    ProcRunWith.ofReach f0 ((rt0.trans (rt1.trans rt)).le hPe)
  have tx17 : t.x 17 = L.area := by rw [kt 17 (by decide), kt1, x17t0, h17]
  have tx18 : t.x 18 = p0.core.sp - 16 - room := by rw [kt 18 (by decide), kt1, x18t0]
  have tsp : t.sp = p0.core.sp - 16 := by rw [spt, spt1, spt0]
  have tmem : t.mem = store64 (store64 p.core.mem (slotAddr (p0.core.sp - 16) 0) (p0.core.x 30))
      G.base p.core.sp := by
    rw [memt, memt1, memt0, hmem0, hm1, h17, hx20, hx21, ← hG]
  have tio : t.io = p.core.io := by rw [iot, iot1, iot0, hio0]; rfl
  have hlim : (p0.core.sp - 16 - room).toNat = p0.core.sp.toNat - 16 - room.toNat := by
    rw [toNat_sub_le (by rw [hsp16]; omega), hsp16]
  have hd1 : (t.sp - t.x 18).toNat = room.toNat := by
    rw [tsp, tx18, toNat_sub_le (by rw [hlim, hsp16]; omega), hlim, hsp16]
    omega
  have hareaG : G.base.toNat = L.area.toNat + areaSize cap := hGbase
  have hstk1 : StackOk (modulePlatform L G) t := by
    refine ⟨by rw [tsp]; exact sub_aligned (k := 16) hal (by decide), ?_, ?_⟩
    · rw [tsp, tx18, hlim, hsp16]
      unfold areaSize at hsp
      omega
    · intro j hj
      rw [hd1] at hj
      have e : (t.x 18 + UInt64.ofNat j).toNat = p0.core.sp.toNat - 16 - room.toNat + j := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat', tx18, hlim]
        simp only [Nat.reducePow]
        omega
      refine modulePlatform_normal (hnormal _ (by rw [e]; omega) (by rw [e, hdm]; omega))
        (.inr (by rw [e, hareaG]; unfold scratchSize; omega))
  -- the store at the entry of `_start`
  have hslot : slotAddr (p0.core.sp - 16) 0 = p0.core.sp - 16 := by simp [slotAddr]
  rw [hslot] at tmem
  have hGtop : G.base.toNat + 5184 + 16 + room.toNat ≤ p0.core.sp.toNat := by
    rw [hareaG, hsp]
    omega
  have hsp32 : p0.core.sp.toNat ≤ 2 ^ 32 := by
    rw [hsp]
    exact hLL'
  have hbelowG : ∀ a : UInt64, a.toNat < G.base.toNat → t.mem a = p.core.mem a := by
    intro a ha
    rw [tmem, store64_other _ _ _ _ (not_within8 (.inl ha) (by omega)),
      store64_other _ _ _ _ (not_within8 (.inl (by rw [hsp16]; omega)) (by rw [hsp16]; omega))]
  have habove32 : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → t.mem a = p.core.mem a := by
    intro a ha
    rw [tmem, store64_other _ _ _ _ (not_within8 (.inr (by omega)) (by omega)),
      store64_other _ _ _ _ (not_within8 (.inr (by rw [hsp16]; omega)) (by rw [hsp16]; omega))]
  have hzero : ∀ j, 8 ≤ j → j < 1040 → t.mem (G.base + UInt64.ofNat j) = 0 := by
    intro j h1 h2
    have e : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [tmem, store64_other _ _ _ _ (not_within8 (.inr (by rw [e]; omega)) (by omega)),
      store64_other _ _ _ _ (not_within8 (.inl (by rw [e, hsp16]; omega))
        (by rw [hsp16]; omega)), ← hG]
    show p.core.mem (L.area + UInt64.ofNat (areaSize cap) + UInt64.ofNat j) = 0
    rw [add_ofNat_add]
    exact elf_zero hl hseg (by rw [hdf]; omega) (by rw [hdm]; omega) (by omega)
  have hsr1 : M.SR S.cap S.globalTypes (nativeStore m cap nativeWorld) q1 := by
    refine ⟨StoreRel.mapHost (storeRel_init (modulePlatform L G) hok hgt hgl (fun j hj => ?_)
      (fun j hj => ?_) ?_) _, f0, tx17,
      ?_, ⟨by show p0.trace = _; rw [tr0]; rfl, fun e he => nomatch he⟩, ?_⟩
    · show t.mem (t.x 17 + UInt64.ofNat j) = _
      have hlt : (L.area + UInt64.ofNat j).toNat < G.base.toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat', hareaG]
        simp only [Nat.reducePow]
        omega
      rw [tx17, hbelowG _ hlt, ← hm1, ← hmem0]
      exact hdata j hj
    · show (modulePlatform L G).normal (t.x 17 + UInt64.ofNat j) = true
      rw [tx17]
      refine modulePlatform_normal (hamap j hj) (.inl ?_)
      rw [UInt64.toNat_add, UInt64.toNat_ofNat', hareaG]
      simp only [Nat.reducePow]
      omega
    · show (t.x 17).toNat + areaSize cap ≤ (t.x 18).toNat
      rw [tx17, tx18, hlim, ← hareaG]
      omega
    · show L.area.toNat + areaSize cap + scratchSize ≤ (t.x 18).toNat
      rw [tx18, hlim, hsp]
      unfold scratchSize
      omega
    · show ScratchHolds G I p.core.sp top [] t.mem
      refine ⟨?_, hstack.congr habove32, ?_, fun d hd => ?_⟩
      · show load64 t.mem G.base = p.core.sp
        rw [tmem]
        exact load64_store64_same _ _ _
      · exact hzero 8 (by decide) (by decide)
      · have hn : UInt64.ofNat d ∉ openNumbers I [] := by simp [openNumbers, Linux.openAfter, I]
        rw [if_neg hn]
        exact hzero (16 + d) (by omega) (by unfold descriptorLimit at hd; omega)
  -- the call of `_start`
  obtain ⟨f, fis, hmemf, hpr, hgen, hcd⟩ := gen_functions W (sigOf_wasiTable _ _ _ _ _ _) hfg
    cfns _ (entryIn_mem hen)
  obtain ⟨hle, hf⟩ := mem_wasiFuncs hmemf
  simp only [Prod.mk.injEq] at hpr
  obtain ⟨hpar, hrsl⟩ := hpr
  have hout := Machine.run_outcome M hle h64 hf hgen hcd (hcalls fuel)
    (wasiStackNeed_ok (definedFunc_of hle hf) _) (nativeStore m cap nativeWorld) [] q1
    (by rw [← hpar]; exact Nat.le_refl _) (by rw [← hpar]; exact trivial) pt hstk1 hsr1
    (by rw [← hpar]; exact ⟨by simp, fun i hi => by simp at hi⟩)
  rw [← hpar, ← hrsl] at hout
  have hres' : Wasm.run fuel m (k, e, ([] : List ValueType), ([] : List ValueType)).1
      (nativeStore m cap nativeWorld) [] M.env = .Trap final msg := hres
  unfold Machine.CallOutcome at hout
  rw [hres'] at hout
  rcases hout with ⟨hov, -⟩ | hro
  · change (t.sp - t.x 18).toNat < wasiStackBound m k at hov
    omega
  obtain ⟨q', rq', ioq', hend, hfq', htr'⟩ := hro
  have hrun' : ProcRunWith Linux.table R (wasiPlatform L p.core.sp top)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q' :=
    ProcRunWith.trans hdom' hq1 (ProcRunWith.mono hWsub rq')
  have hio' : q'.core.io = p.core.io := by
    change q'.core.io = t.io at ioq'
    rw [ioq', tio]
  obtain ⟨htrq, hwq⟩ := htr'
  rw [List.nil_append] at htrq
  rcases hend with hta | hse
  · obtain ⟨z, rz, cz, x8z, iz, tz, x0z⟩ := trapAt q' hfq' hrun' (by
      rcases hta with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact h)
    refine ⟨z, rz, cz, x8z, by rw [iz, hio'], by rw [tz, htrq], hwq, .inr (.inr ⟨?_, x0z⟩)⟩
    rcases hta with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  rcases hse with ⟨hm, c, hc, hpcq, hx0⟩ | ⟨hm, hpcq, hx0⟩ | ⟨hm, hpcq⟩
  · obtain ⟨z, rz, cz, x8z, iz, tz, x0z⟩ := exitAt q' hrun' hpcq
    exact ⟨z, rz, cz, x8z, by rw [iz, hio'], by rw [tz, htrq], hwq,
      .inl ⟨hm, c, hc, by rw [x0z, hx0]⟩⟩
  · obtain ⟨z, rz, cz, x8z, iz, tz, x0z⟩ := exitAt q' hrun' hpcq
    exact ⟨z, rz, cz, x8z, by rw [iz, hio'], by rw [tz, htrq], hwq,
      .inr (.inl ⟨hm, by rw [x0z, hx0]⟩)⟩
  · obtain ⟨z, rz, cz, x8z, iz, tz, x0z⟩ := trapAt q' hfq' hrun' hpcq
    exact ⟨z, rz, cz, x8z, by rw [iz, hio'], by rw [tz, htrq], hwq,
      .inr (.inr ⟨.inl hm, x0z⟩)⟩

/-- The executable of `genWasiElf` reaches `exit_group` for the reply sequence `R` when Talos's
runs of `_start` from `nativeStore` under the shim's environment with `R` and the module's flat
calls `calls`, which lie in `shimCalls`, have the footprint of the action `action` with enough
fuel, for arm64's open flags and the launch `⟨args, environ, false⟩`.  The conclusion is that of
`wasiElf_footprint`. -/
theorem wasiElf_footprint_with {m : Module} {k : Nat} {room : UInt64} {cap : Nat} {nb len : Nat}
    {calls : List LeanExe.Wasi.Call} (hk : bytesOk (genWasiElf m k room cap) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (wasiLayout m k room cap))
    (himp : m.imports = ABI.importsWith calls) (hsup : ∀ c ∈ calls, c ∈ shimCalls)
    (hroom16 : room.toNat % 16 = 0) (hroom : wasiStackBound m k ≤ room.toNat)
    {action : Action Unit} {aborts : Bool}
    (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)} {top : UInt64}
    (hfoot : ∃ bound, ∀ fuel ≥ bound,
      Footprint arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R action
        nativeWorld aborts
        (Wasm.run fuel m k (nativeStore m cap nativeWorld) []
          (linuxEnv arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R calls)))
    (hl : ElfLoaded (byteAt nb) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform (wasiLayout m k room cap) p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap))) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap)) q.core.pc =
        some svcWord ∧ q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ [] T ls ∧
        Carried R 0 ls ∧
        (∀ e ∈ ls, WritesNative (wasiShimLayout m k room cap) (cap * 65536) e) ∧
        ((∃ c, Exec (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
            action nativeWorld.world T (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
            action nativeWorld.world T (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
            action nativeWorld.world T (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          (aborts = true ∧ (∃ residual,
            Prefix (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
              action nativeWorld.world T residual w) ∧ q.core.x 0 = 2)) := by
  obtain ⟨bound, hb⟩ := hfoot
  have hf := hb bound (Nat.le_refl _)
  cases hr : Wasm.run bound m k (nativeStore m cap nativeWorld) []
      (linuxEnv arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R calls) with
  | Trap final msg =>
    rw [hr] at hf
    obtain ⟨T, ls, hev, himg, hcar, -, -, hcls⟩ := hf
    have hev' : final.host.world.events = ls := hev
    obtain ⟨q, rq, cq, x8q, ioq, trq, hwq, hend⟩ := wasiElf_run hk hseg himp hsup hroom16 hroom R p
      hl hstack hpc htr hr
    rw [hev'] at trq hwq
    refine ⟨q, rq, cq, x8q, ioq, T, ls, final.host.world, trq, himg, hcar, hwq, ?_⟩
    have d1 : exitTrap ≠ exitRejected := by decide
    have d2 : exitTrap ≠ shimTrap := by decide
    have d3 : exitTrap ≠ "unreachable" := by decide
    have d4 : exitTrap ≠ "out of bounds memory access" := by decide
    have d5 : exitTrap ≠ "integer divide by zero" := by decide
    have d6 : exitRejected ≠ shimTrap := by decide
    have d7 : exitRejected ≠ "unreachable" := by decide
    have d8 : exitRejected ≠ "out of bounds memory access" := by decide
    have d9 : exitRejected ≠ "integer divide by zero" := by decide
    have d10 : shimTrap ≠ "unreachable" := by decide
    rcases hcls with ⟨c, hm, hex⟩ | ⟨hm, hex⟩ | ⟨hm, hex⟩ | ⟨hab, hm, hpre⟩ <;> subst hm
    · rcases hend with ⟨-, c', hc', hx0⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · have := hex.exited_marker
        change final.host.world.exited = some c at this
        rw [hc'] at this
        exact .inl ⟨c, hex, by rw [hx0, Option.some.inj this]⟩
      · exact absurd h d1
      · rcases h with h | h | h | h
        · exact absurd h d2
        · exact absurd h d3
        · exact absurd h d4
        · exact absurd h d5
    · rcases hend with ⟨h, -⟩ | ⟨-, hx0⟩ | ⟨h, -⟩
      · exact absurd h.symm d1
      · exact .inr (.inl ⟨hex, hx0⟩)
      · rcases h with h | h | h | h
        · exact absurd h d6
        · exact absurd h d7
        · exact absurd h d8
        · exact absurd h d9
    · rcases hend with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hx0⟩
      · exact absurd h.symm d2
      · exact absurd h.symm d6
      · exact .inr (.inr (.inl ⟨hex, hx0⟩))
    · rcases hend with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hx0⟩
      · exact absurd h.symm d3
      · exact absurd h.symm d7
      · exact .inr (.inr (.inr ⟨hab, hpre, hx0⟩))
  | _ => rw [hr] at hf; exact hf.elim

/-- The executable of `genWasiElf` reaches `exit_group` for every reply sequence `R`, when
Talos's runs of `_start` from `nativeStore` under the shim's environment with the module's flat
calls `calls`, which lie in `shimCalls`, have the footprint of the action `action` with enough
fuel, for arm64's open flags and every launch.  Linux starts the process with the arguments `args` and the environment
`environ` on its initial stack, and the launch `⟨args, environ, false⟩` grants no preopened
directory.  The process's trace holds the layer events `ls`, the images of the WASI events `T` of
a run of `action` under `linuxHost` from a world with no events: each event holds its reply of
`R`, and each writes within the `cap` pages of linear memory or is a `clock_gettime` into the
timespec.  The run is an accepted exit whose status X0 holds, an exit whose status the shim
rejects, with X0 at 1, a trap of the shim at a request that it refuses or a result outside Linux's
range, with X0 at 2, or, when `aborts` is true, a guest trap after a prefix of `action`, with X0
at 2. -/
theorem wasiElf_footprint {m : Module} {k : Nat} {room : UInt64} {cap : Nat} {nb len : Nat}
    {calls : List LeanExe.Wasi.Call} (hk : bytesOk (genWasiElf m k room cap) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (wasiLayout m k room cap))
    (himp : m.imports = ABI.importsWith calls) (hsup : ∀ c ∈ calls, c ∈ shimCalls)
    (hroom16 : room.toNat % 16 = 0) (hroom : wasiStackBound m k ≤ room.toNat)
    {action : Action Unit} {aborts : Bool}
    (hfoot : ∀ I R, ∃ bound, ∀ fuel ≥ bound,
      Footprint arm64Flags (wasiShimLayout m k room cap) I R action nativeWorld aborts
        (Wasm.run fuel m k (nativeStore m cap nativeWorld) []
          (linuxEnv arm64Flags (wasiShimLayout m k room cap) I R calls)))
    (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)} {top : UInt64}
    (hl : ElfLoaded (byteAt nb) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform (wasiLayout m k room cap) p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap))) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap)) q.core.pc =
        some svcWord ∧ q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ [] T ls ∧
        Carried R 0 ls ∧
        (∀ e ∈ ls, WritesNative (wasiShimLayout m k room cap) (cap * 65536) e) ∧
        ((∃ c, Exec (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
            action nativeWorld.world T (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
            action nativeWorld.world T (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
            action nativeWorld.world T (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          (aborts = true ∧ (∃ residual,
            Prefix (linuxHost arm64Flags (wasiShimLayout m k room cap) ⟨args, environ, false⟩ R)
              action nativeWorld.world T residual w) ∧ q.core.x 0 = 2)) :=
  wasiElf_footprint_with hk hseg himp hsup hroom16 hroom R p (hfoot ⟨args, environ, false⟩ R) hl
    hstack hpc htr

end Verified.ShimA64
