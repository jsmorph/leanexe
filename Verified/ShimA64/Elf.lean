import Verified.ShimA64.Stubs
import LeanExe.A64.Proof.WasiProgram

/-!
The executable of `genWasiElf` from its entry to `exit_group`.  The
runtime of `genElfWith` reaches `main` (`elfWith_main`), `main` calls `_start` (`run_wasiFront`)
with the module's initial store at the native cap in the area, `nativeStore`, and the simulation
of `_start` over `shimMachine`, whose code map `wasiCode` holds the routine `SVC #0; RET` and the
program, follows Talos's run of `_start` under the shim's environment.  When that run traps at an
accepted exit or a rejected one, the process stands at the exit word with the status in X0, and
when it traps in the shim or the guest, the process stands at the trap stub, which sets status 2
and branches to the exit word.  From there the runtime makes `exit_group`.  `wasiElf_run` states
this for every reply sequence and every fuel at which Talos's run traps: the process's trace holds
the layer events of the final world, each of whose output regions lies within the native cap's
linear memory, and X0 holds the status.  `wasiElf_footprint` takes the trap from a footprint
premise, which excludes a return of `_start` and every run that does not finish.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-- The layout of the executable of `genWasiElf`, and an empty layout when the generator fails. -/
def wasiLayout (m : Module) (k : Nat) (room : UInt64) (cap : Nat) : ElfLayout :=
  match genWasiElf m k room cap with
  | .ok (_, L) => L
  | .error _ => ⟨0, 0, 0, 0, 0, 0⟩

/-- The world in which a native run starts: no layer event, no exit, and no WASI event. -/
def nativeWorld : Observed LinuxWorld := ⟨⟨[], none⟩, []⟩

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

theorem wasiMain_length {a e room : UInt64} {is : List Instr} (hg : wasiMain a e room = .ok is) :
    is.length = 13 := by
  unfold wasiMain at hg
  cases hb : bField (after a 8) e with
  | error err => simp [hb, bind, Except.bind] at hg
  | ok g =>
  simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  rfl

/-- The executable of `genWasiElf` from its entry to `exit_group`, for every reply sequence `R` and
every fuel at which Talos's run of `_start` from `nativeStore` under the shim's environment traps
with the store `final` and the message `msg`: the run of `ProcReachWith` over
`LeanExe.Linux.table` reaches `SVC #0` with X8 at 94, its trace holds the layer events of the
final world, each of whose output regions lies within the `cap` pages of linear memory, and X0
holds the accepted exit's status, 1 for a rejected exit, or 2 for a trap of the shim or of the
guest.  The premises are the kernel's check of the file, its program headers, a stack's room that
is a multiple of 16 and holds `wasiStackBound`, the loader's placement of the file, the program
counter at the entry, and an empty trace. -/
theorem wasiElf_run {m : Module} {k : Nat} {room : UInt64} {cap : Nat} {nb len : Nat}
    (hk : bytesOk (genWasiElf m k room cap) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (wasiLayout m k room cap))
    (hroom16 : room.toNat % 16 = 0) (hroom : wasiStackBound m k ≤ room.toNat)
    (R : Linux.Replies) (p : Proc) (hl : ElfLoaded (byteAt nb) p.core.mem)
    (hpc : p.core.pc = elfEntry) (htr : p.trace = [])
    {fuel : Nat} {final : Store (Observed LinuxWorld)} {msg : String}
    (hres : Wasm.run fuel m k (nativeStore m cap nativeWorld) []
      (linuxEnv (layoutAt (wasiLayout m k room cap).area) R) = .Trap final msg) :
    ∃ q, ProcReachWith Linux.table R (elfPlatform (wasiLayout m k room cap))
        (fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap))) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap)) q.core.pc =
        some svcWord ∧ q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      q.trace = final.host.world.events.map A64.Event.sys ∧
      (∀ e ∈ final.host.world.events,
        WritesWithin (layoutAt (wasiLayout m k room cap).area) (cap * 65536) e) ∧
      ((msg = exitTrap ∧ ∃ c, final.host.world.exited = some c ∧ q.core.x 0 = c) ∨
        (msg = exitRejected ∧ q.core.x 0 = 1) ∨
        ((msg = shimTrap ∨ msg = "unreachable" ∨ msg = "out of bounds memory access" ∨
          msg = "integer divide by zero") ∧ q.core.x 0 = 2)) := by
  obtain ⟨bytes, L, hg, -, hbyte⟩ := of_bytesOk hk
  have hL : wasiLayout m k room cap = L := by simp only [wasiLayout, hg]
  rw [hL] at hseg hres ⊢
  obtain ⟨prog, -, hprog, hLeq, hbound, -⟩ := gen_elfWith hg
  obtain ⟨is, p0, hgp, hprogC, hrdC, -, hdom', hbase', hp0, pc0, f0, tr0, h30, hal, htop, hstk,
    h17, hdata, hamap, habove, hU, hio0, hexit⟩ :=
    elfWith_main hg hbyte hseg hroom16 p hl hpc htr rfl
  have hprogeq : prog = is := by
    have := hprog.symm.trans hgp
    exact Except.ok.inj this
  subst hprogeq
  obtain ⟨gts, e, main, rd, wr, ex, tr, fns, himp, hok, hgt, hgl, hen, hmg, hrdg, hwrg, hexg,
    htrg, hfg, his, hall⟩ := gen_wasiProgram hgp
  -- the machine's code
  have hcodeEnd : L.codeEnd = 176 + 4 * (18 + prog.length) := by rw [hLeq]; rfl
  have hdataOff : L.codeEnd ≤ L.dataOff := by rw [hLeq]; simp only [elfLayoutOf, roundUp]; omega
  have hA : (after elfExitWord 1).toNat + 4 * prog.length < 2 ^ 55 := by
    have : (after elfExitWord 1).toNat = elfBase.toNat + 176 + 72 := by decide
    rw [this]
    simp only [elfBase, UInt64.reduceToNat] at hbound ⊢
    omega
  have hsvcA : svcRetAddr.toNat + 8 ≤ (after elfExitWord 1).toNat := by decide
  have hdomW := wasiCode_dom (svc := svcRetAddr) (is := prog) (a := after elfExitWord 1)
    (by decide) hA
  have hkW := wasiCode_keeps (svc := svcRetAddr) (a := after elfExitWord 1) hall
  have hWsub : ∀ a w, wasiCode svcRetAddr (after elfExitWord 1) prog a = some w →
      fetchFrom p.core.mem elfEntry (elfWords L) a = some w :=
    wasiCode_sub (OpsAt.drop (l1 := [.ins (.movz 8 63 0)]) hrdC) hprogC
  have cAll : CodeAt (wasiCode svcRetAddr (after elfExitWord 1) prog) (after elfExitWord 1) prog :=
    wasiCode_prog hsvcA (by omega)
  generalize hW : wasiCode svcRetAddr (after elfExitWord 1) prog = W at hdomW hkW hWsub cAll
  have hsvcW : OpsAt W svcRetAddr [.svc, .ins (.ret 30)] := by rw [← hW]; exact wasiCode_svc
  generalize hA' : after elfExitWord 1 = A at *
  -- the parts of the program
  have lm := wasiMain_length hmg
  have lr := readStub_length hrdg
  have lw := writeStub_length hwrg
  obtain ⟨fx1, gx3, hfx1, hgx3, rfl⟩ := exitStub_ok hexg
  obtain ⟨gt, hgt1, rfl⟩ := trapStub_ok htrg
  rw [his] at cAll
  have c6 := CodeAt.split W cAll (n := 215) (by simp [lm, lr, lw, errnoRoutine, errnoTable])
  have c5 := CodeAt.split W c6.1 (n := 109) (by simp [lm, lr, lw])
  have c4 := CodeAt.split W c5.1 (n := 107) (by simp [lm, lr, lw])
  have c3 := CodeAt.split W c4.1 (n := 103) (by simp [lm, lr, lw])
  have c2 := CodeAt.split W c3.1 (n := 59) (by simp [lm, lr])
  have c1 := CodeAt.split W c2.1 (n := 13) (by simp [lm])
  -- the machine and its calls
  let S : Shared :=
    { trapUnreachable := wasiTrapAt A, trapBounds := wasiTrapAt A, trapDiv := wasiTrapAt A,
      trapStack := wasiTrapAt A, cap, globalTypes := gts, byteStores := true }
  let M := shimMachine R (elfPlatform L) W hdomW hkW L.area elfExitWord (cap * 65536)
  let need := wasiStackNeed m (m.funcs.length + 1)
  have h64 : m.memIs64 = false := memIs64_of_areaOk hok
  have hcalls := wasi_calls_ok M (need := need) himp h64 (fun _ => hU) rfl
    (readStub_sim (R := R) (P := elfPlatform L) (code := W) (hdom := hdomW) (hk := hkW)
      (area := L.area) (base := elfExitWord) (size := cap * 65536) S (need 0) hrdg c1.2 hsvcW
      c5.2 hU (Nat.le_refl _))
    (writeStub_sim (R := R) (P := elfPlatform L) (code := W) (hdom := hdomW) (hk := hkW)
      (area := L.area) (base := elfExitWord) (size := cap * 65536) S (need 1) hwrg c2.2 hsvcW
      c5.2 hU)
    (exitStub_sim (R := R) (P := elfPlatform L) (code := W) (hdom := hdomW) (hk := hkW)
      (area := L.area) (base := elfExitWord) (size := cap * 65536) S (need 2)
      (is := [.subsImm 31 0 126, .bcond 3 fx1, .movz 0 1 0, .b gx3])
      hexg c3.2)
    hfg c6.2 (fun k f hle hf => wasiStackNeed_ok (definedFunc_of hle hf) _)
  -- the end of a run: the exit word, or the trap stub and then the exit word
  have hp0w := hp0.toWith Linux.table R
  have exitAt : ∀ q : Proc, ProcRunWith Linux.table R (elfPlatform L)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q → q.core.pc = elfExitWord →
      ∃ z, ProcReachWith Linux.table R (elfPlatform L)
          (fetchFrom p.core.mem elfEntry (elfWords L)) p z ∧
        fetchFrom p.core.mem elfEntry (elfWords L) z.core.pc = some svcWord ∧ z.core.x 8 = 94 ∧
        z.core.io = q.core.io ∧ z.trace = q.trace ∧ z.core.x 0 = q.core.x 0 := by
    intro q hq hpcq
    obtain ⟨z, rz, cz, x8z, x0z, trz, ioz⟩ := hexit q (.inr hpcq)
    exact ⟨z, hp0w.trans (hq.thenWith hdom' (by rw [hpcq]; exact hbase') (rz.toWith _ _)), cz,
      x8z, ioz, trz, x0z⟩
  have trapAt : ∀ q : Proc, q.fpcr = fpcrValue → ProcRunWith Linux.table R (elfPlatform L)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q → q.core.pc = wasiTrapAt A →
      ∃ z, ProcReachWith Linux.table R (elfPlatform L)
          (fetchFrom p.core.mem elfEntry (elfWords L)) p z ∧
        fetchFrom p.core.mem elfEntry (elfWords L) z.core.pc = some svcWord ∧ z.core.x 8 = 94 ∧
        z.core.io = q.core.io ∧ z.trace = q.trace ∧ z.core.x 0 = 2 := by
    intro q hf hq hpcq
    have ct := CodeAt.cons.mp c4.2
    obtain ⟨s1, r1, p1, x01, -, -, -, io1⟩ := step_movz (elfPlatform L) W (s := q.core) (d := 0)
      (imm := 2) (hw := 0) (by decide) (by rw [hpcq]; exact ct.1)
    obtain ⟨s2, r2, p2, x2, -, -, io2⟩ := step_b (elfPlatform L) W (s := s1) (g := gt)
      (target := elfExitWord) (by rw [p1, hpcq, ← after_one]; exact (CodeAt.cons.mp ct.2).1)
      (by rw [p1, hpcq, ← after_one]; exact bField_target hgt1)
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
  obtain ⟨t, rt, pt, x30t, spt, x18t, x17t, iot, memt⟩ :=
    run_wasiFront (elfPlatform L) W hmg c1.1 pc0 hal fun j hj => by
      rw [stack_main p0.core.sp room j]
      exact hstk _ (by omega)
  let q1 : Proc := { p0 with core := t }
  have hq1 : ProcRunWith Linux.table R (elfPlatform L) W p0 q1 := ProcRunWith.ofReach f0 rt
  have hsp16 : (p0.core.sp - 16).toNat = p0.core.sp.toNat - 16 := by
    rw [toNat_sub_le (by show 16 ≤ _; unfold areaSize at habove; omega)]
    rfl
  have hlim : (p0.core.sp - 16 - room).toNat = p0.core.sp.toNat - 16 - room.toNat := by
    rw [toNat_sub_le (by rw [hsp16]; unfold areaSize at habove; omega), hsp16]
  have hd1 : (t.sp - t.x 18).toNat = room.toNat := by
    rw [spt, x18t, toNat_sub_le (by rw [hlim, hsp16]; omega), hlim, hsp16]
    unfold areaSize at habove
    omega
  have hstk1 : StackOk (elfPlatform L) t := by
    refine ⟨by rw [spt]; exact sub_aligned (k := 16) hal (by decide), ?_, ?_⟩
    · rw [spt, x18t, hlim, hsp16]
      unfold areaSize at habove
      omega
    · intro j hj
      rw [hd1] at hj
      rw [x18t]
      exact hstk j (by omega)
  have hsr1 : M.SR S.cap S.globalTypes (nativeStore m cap nativeWorld) q1 := by
    refine ⟨StoreRel.mapHost (storeRel_init (elfPlatform L) hok hgt hgl (fun j hj => ?_)
      (fun j hj => by rw [x17t, h17]; exact hamap j hj) ?_) _, f0, by
        show t.x 17 = L.area
        rw [x17t, h17], ⟨tr0, fun e he => by
          change e ∈ ([] : List Linux.Event) at he
          cases he⟩⟩
    · have := L.area.toNat_lt
      unfold areaSize at habove hj
      have hjl : (L.area + UInt64.ofNat j).toNat < (p0.core.sp - 16).toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat', hsp16]
        simp only [Nat.reducePow] at *
        omega
      rw [memt, x17t, h17, store64_other _ _ _ _ (below_slot (Nat.le_refl _)
        (by rw [hsp16]; omega) (by decide) hjl)]
      exact hdata j hj
    · rw [x17t, h17, x18t, hlim]
      unfold areaSize at habove ⊢
      omega
  -- the call of `_start`
  obtain ⟨f, fis, hmem, hpr, hgen, hcd⟩ := gen_functions W (sigOf_wasiTable _ _ _ _ _) hfg c6.2 _
    (entryIn_mem hen)
  obtain ⟨hle, hf⟩ := mem_wasiFuncs hmem
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
  have hrun' : ProcRunWith Linux.table R (elfPlatform L)
      (fetchFrom p.core.mem elfEntry (elfWords L)) p0 q' :=
    ProcRunWith.mono hWsub (ProcRunWith.trans hdomW hq1 rq')
  have hio' : q'.core.io = p.core.io := by
    change q'.core.io = t.io at ioq'
    rw [ioq', iot, hio0]
  obtain ⟨htrq, hwq⟩ := htr'
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

/-- The executable of `genWasiElf` reaches `exit_group` for every reply sequence `R`,
when Talos's runs of `_start` from `nativeStore` under the shim's environment have the
footprint of the action `action` with enough fuel.  The process's trace holds the layer events
`ls`, the images of the WASI events `T` of a run of `action` under `linuxHost` from a world with no
events: each event holds its reply of `R`, and the output region of each lies within the `cap`
pages of linear memory.  The run is an accepted exit whose status X0 holds, an exit whose status
the shim rejects, with X0 at 1, a trap of the shim at a result outside Linux's range, with X0 at
2, or, when `aborts` is true, a guest trap after a prefix of `action`, with X0 at 2. -/
theorem wasiElf_footprint {m : Module} {k : Nat} {room : UInt64} {cap : Nat} {nb len : Nat}
    (hk : bytesOk (genWasiElf m k room cap) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (wasiLayout m k room cap))
    (hroom16 : room.toNat % 16 = 0) (hroom : wasiStackBound m k ≤ room.toNat)
    {action : Action Unit} {aborts : Bool}
    (hfoot : ∀ R, ∃ bound, ∀ fuel ≥ bound,
      Footprint (layoutAt (wasiLayout m k room cap).area) R action nativeWorld aborts
        (Wasm.run fuel m k (nativeStore m cap nativeWorld) []
          (linuxEnv (layoutAt (wasiLayout m k room cap).area) R)))
    (R : Linux.Replies) (p : Proc) (hl : ElfLoaded (byteAt nb) p.core.mem)
    (hpc : p.core.pc = elfEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (elfPlatform (wasiLayout m k room cap))
        (fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap))) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords (wasiLayout m k room cap)) q.core.pc =
        some svcWord ∧ q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧ Images T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesWithin (layoutAt (wasiLayout m k room cap).area) (cap * 65536) e) ∧
        ((∃ c, Exec (linuxHost (layoutAt (wasiLayout m k room cap).area) R) action
            nativeWorld.world T (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost (layoutAt (wasiLayout m k room cap).area) R) action nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost (layoutAt (wasiLayout m k room cap).area) R) action nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          (aborts = true ∧ (∃ residual, Prefix (linuxHost (layoutAt (wasiLayout m k room cap).area)
            R) action nativeWorld.world T residual w) ∧ q.core.x 0 = 2)) := by
  obtain ⟨bound, hb⟩ := hfoot R
  have hf := hb bound (Nat.le_refl _)
  cases hr : Wasm.run bound m k (nativeStore m cap nativeWorld) []
      (linuxEnv (layoutAt (wasiLayout m k room cap).area) R) with
  | Trap final msg =>
    rw [hr] at hf
    obtain ⟨T, ls, hev, himg, hcar, -, -, hcls⟩ := hf
    have hev' : final.host.world.events = ls := hev
    obtain ⟨q, rq, cq, x8q, ioq, trq, hwq, hend⟩ := wasiElf_run hk hseg hroom16 hroom R p hl hpc
      htr hr
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

end Verified.ShimA64
