import LeanExe.M7.Board
import LeanExe.M7.Proof.Init
import LeanExe.M7.Proof.Runs
import LeanExe.M7.Proof.Setup

/-!
The run of a program with requests on the NUCLEO-F767ZI from reset, in the model.  `Flash code n
len` states that the code map holds the file's bytes in flash, from `0x08000000` and from
`0x00200000`, and `Reset code flashItcm b` that `b` is the state that reset gives from the vector
table at `0x00200000`.  `boardWith_run` states, for an initialization `ops` whose accesses name
device registers, every sequence `σ` of the values that device reads return, and every number `N`
of windows, that the model reaches the loop's head of `main` with the trace of the initialization
followed by the accesses of the first `N` windows, whose reads take the values of `σ` after the
initialization's `initReads ops` reads, and `boardWith_runs` that the run never stops.
`board_run` and `board_runs` are their instances for `init`.  `init_addrs` and
`initOvrdis_addrs` list the registers of the two initializations in the order of their accesses,
all in RCC, GPIOD, and USART3, and `windows_confined` states that every access of the windows of a
step whose requests name `USART_ISR`, `USART_RDR`, or `USART_TDR` is an access of one of those
registers.

The theorems hold of the processor under the conditions of the model: a power-on reset, or an
NRST reset with DHCSR, DEMCR, the FPB, the DWT, the ITM, and the DBGMCU registers at their
power-on values, with BOOT0 low and BOOT_ADD0 0x0080; software watchdogs, which this board's
option bytes select (OPTCR reads 0xFFFFAAFD, IWDG_SW and WWDG_SW set), so that no watchdog runs;
and no interrupt, NMI, debug halt, debugger access, or DMA during the run.  The reset of
`st-flash` does not meet the first condition: it leaves DHCSR's C_DEBUGEN set and DBGMCU_APB1_FZ
at 0x1800, which a system reset keeps, and with C_DEBUGEN set a debug event halts the processor.
`tools/baremetal/stlink_nrst.py` writes those registers' power-on values over SWD, leaves debug
mode, and then pulses NRST.

`boardWith_setup` runs the image of a program whose module has an area, laid out by
`areaBootWith ops`, from reset to the initialization's start: the setup leaves the module's
initial store in the area at DTCM's base, below the stack's limit `areaEnd`.  `areaBoardWith_run`
states for such a program what `boardWith_run` states for a program without an area, from the
step's call fact `StepCall` with its invariant and from a fit condition that adds the area's size,
and `areaBoardWith_runs` that its run never stops.  `board_setup`, `areaBoard_run`, and
`areaBoard_runs` are their instances for `init`, and each counted form `*_run_steps` has its
instance in the same way.
-/

namespace LeanExe.M7.Nucleo

open Wasm LeanExe.ProofKit LeanExe.CallGraph LeanExe.Pipeline LeanExe.Requests LeanExe.M7

/-- The code map holds the `len` bytes of the number `n` in the board's flash, from `0x08000000`
on the AXIM interface and from `0x00200000` on the ITCM interface. -/
structure Flash (code : UInt32 → Option UInt16) (n len : Nat) : Prop where
  axim : FileAt code n len flashAxim
  itcm : FileAt code n len flashItcm

theorem ram_of {a : UInt32} (h1 : 0x20000000 ≤ a.toNat) (h2 : a.toNat < 0x20020000) :
    Ram platform a :=
  ⟨by simp only [platform, decide_eq_true_eq]; omega,
    by simp only [platform, decide_eq_false_iff_not]; omega⟩

/-- The 65,536 registers of the requests lie in the platform's device window. -/
theorem devWindow : DevWindow platform devBase := by
  refine ⟨by decide, fun j hj => ?_⟩
  simp only [platform, devBase, decide_eq_true_eq, UInt32.toNat_add, UInt32.toNat_ofNat',
    UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The stack below an outgoing area of `n` slots at the top of DTCM, down to the limit `lim` in
DTCM, for a step that needs `need` bytes below it. -/
theorem stackOk_of {lim : UInt32} {n need : Nat} (hl : 0x20000000 ≤ lim.toNat)
    (hfit : lim.toNat + 8 * n + need ≤ 0x20020000) (s : State)
    (h : s.sp = stackTop - UInt32.ofNat (8 * n)) : StackOk platform lim n need s := by
  have hs : s.sp.toNat = 0x20020000 - 8 * n := by
    rw [h, UInt32.toNat_sub, UInt32.toNat_ofNat']
    simp only [stackTop, Nat.reducePow]
    rw [show (UInt32.toNat 0x20020000) = 0x20020000 from rfl]
    omega
  refine ⟨mod4_of_toNat (by rw [hs]; omega), fun j hj => ram_of ?_ ?_, by omega, by omega,
    fun j hj => ram_of ?_ ?_, by omega⟩
  all_goals
    simp only [UInt32.toNat_add, UInt32.toNat_ofNat', hs, Nat.reducePow] at *
    omega

/-- The stack below an outgoing area of `n` slots at the top of DTCM, for a step that needs
`need` bytes below it. -/
theorem stackOk {n need : Nat} (hfit : 8 * n + need ≤ 0x20000) (s : State)
    (h : s.sp = stackTop - UInt32.ofNat (8 * n)) : StackOk platform stackLimit n need s :=
  stackOk_of (by decide) (by rw [show stackLimit.toNat = 0x20000000 from rfl]; omega) s h

theorem init_ok : ∀ op ∈ init, OpOk platform op := by decide

theorem initOvrdis_ok : ∀ op ∈ initOvrdis, OpOk platform op := by decide

theorem initReads_eq : initReads init = 11 := rfl

theorem initReads_ovrdis : initReads initOvrdis = 11 := rfl

/-- The initialization's accesses, read-modify-writes whose written values are functions of the
values read, reach the loop's base with `initTrace init` appended. -/
theorem initRuns (σ : Nat → UInt32) (code : UInt32 → Option UInt16) :
    InitRuns platform σ code (initCode init) (initTrace init) (initReads init) :=
  init_runs init init_ok

/-- The registers of the initialization's accesses, in their order: RCC's `DCKCFGR2`,
`AHB1ENR`, and `APB1ENR`, GPIOD's `OSPEEDR`, `OTYPER`, `PUPDR`, `AFRH`, and `MODER`, and
USART3's `CR2`, `BRR`, and `CR1`. -/
theorem init_addrs (σ : Nat → UInt32) :
    (initTrace init σ).map Access.addr =
      [rccDckcfgr2, rccDckcfgr2, rccAhb1enr, rccAhb1enr, rccAhb1enr, rccApb1enr, rccApb1enr,
        rccApb1enr, gpiodOspeedr, gpiodOspeedr, gpiodOtyper, gpiodOtyper, gpiodPupdr, gpiodPupdr,
        gpiodAfrh, gpiodAfrh, gpiodModer, gpiodModer, usartCr2, usartCr2, usartBrr, usartCr1] :=
  rfl

/-- The registers of the accesses of `initOvrdis`, in their order: those of `init` with
`USART_CR3` between `USART_BRR` and `USART_CR1`. -/
theorem initOvrdis_addrs (σ : Nat → UInt32) :
    (initTrace initOvrdis σ).map Access.addr =
      [rccDckcfgr2, rccDckcfgr2, rccAhb1enr, rccAhb1enr, rccAhb1enr, rccApb1enr, rccApb1enr,
        rccApb1enr, gpiodOspeedr, gpiodOspeedr, gpiodOtyper, gpiodOtyper, gpiodPupdr, gpiodPupdr,
        gpiodAfrh, gpiodAfrh, gpiodModer, gpiodModer, usartCr2, usartCr2, usartBrr, usartCr3,
        usartCr1] :=
  rfl

/-- The register blocks of RCC, GPIOD, and USART3. -/
abbrev InitBlock (a : UInt32) : Prop :=
  (0x40023800 ≤ a.toNat ∧ a.toNat < 0x40023C00) ∨ (0x40020C00 ≤ a.toNat ∧ a.toNat < 0x40021000) ∨
    (0x40004800 ≤ a.toNat ∧ a.toNat < 0x40004C00)

/-- Every access of an initialization whose registers, in the order of its accesses, form the
list `as` lies in RCC, GPIOD, or USART3 when every register of `as` does. -/
theorem confined_of_addrs {ops : List InitOp} {as : List UInt32}
    (haddrs : ∀ σ, (initTrace ops σ).map Access.addr = as) (has : ∀ a ∈ as, InitBlock a)
    (σ : Nat → UInt32) : ∀ e ∈ initTrace ops σ, InitBlock e.addr :=
  fun _ he => has _ (haddrs σ ▸ List.mem_map_of_mem he)

/-- Every access of the initialization lies in RCC, GPIOD, or USART3. -/
theorem init_confined (σ : Nat → UInt32) : ∀ e ∈ initTrace init σ, InitBlock e.addr :=
  confined_of_addrs init_addrs (by decide) σ

/-- Every access of `initOvrdis` lies in RCC, GPIOD, or USART3. -/
theorem initOvrdis_confined (σ : Nat → UInt32) :
    ∀ e ∈ initTrace initOvrdis σ, InitBlock e.addr :=
  confined_of_addrs initOvrdis_addrs (by decide) σ

theorem event_addr {G : Type} (tick : G → UInt64 → G × UInt64) (σ' : Nat → UInt32)
    (r : ReqState G) :
    (reqEvent (devBus devBase) tick σ' r).addr =
      devBase + UInt32.ofNat (4 * (reqReg (tick r.state r.last).2).toNat) := by
  unfold reqEvent
  split <;> rfl

/-- Every access of the windows of a step whose requests name `USART_ISR`, index `0x1207`,
`USART_RDR`, index `0x1209`, or `USART_TDR`, index `0x120A`, is an access of one of those
registers. -/
theorem windows_confined {G : Type} {tick : G → UInt64 → G × UInt64}
    (hreq : ∀ s v, reqReg (tick s v).2 = 0x1207 ∨ reqReg (tick s v).2 = 0x1209 ∨
      reqReg (tick s v).2 = 0x120A) (g : G) (σ' : Nat → UInt32) : ∀ N,
    ∀ e ∈ windows (reqTrace (devBus devBase) tick g σ') N,
      e.addr = usartIsr ∨ e.addr = usartRdr ∨ e.addr = usartTdr
  | 0 => fun _ he => absurd he List.not_mem_nil
  | N + 1 => fun e he => by
      rw [windows] at he
      rcases List.mem_append.mp he with h | h
      · exact windows_confined hreq g σ' N e h
      · rw [reqTrace, List.mem_singleton] at h
        rw [h, event_addr]
        rcases hreq (reqRun tick g σ' N).state (reqRun tick g σ' N).last with h | h | h <;>
          rw [h] <;> decide

theorem length_windows {α G : Type} (B : Bus α) (tick : G → UInt64 → G × UInt64) (g : G)
    (σ' : Nat → UInt32) : ∀ N, (windows (reqTrace B tick g σ') N).length = N
  | 0 => rfl
  | N + 1 => by
      rw [windows, List.length_append, length_windows B tick g σ' N]
      rfl

/-- A program with requests from reset on the board with the initialization `ops`, whose
accesses name device registers: for every sequence `σ` of the values that device reads return and
every number `N` of windows, the image of step `k` of `m` from the state `g0`, whose bytes the
kernel's check `hk` finds in flash, reaches the loop's head of `main` with the initialization's
accesses followed by those of the first `N` windows, which read `σ` from the value after the
initialization's reads.  The theorem holds under the run conditions of the module's header. -/
theorem boardWith_run {ops : List InitOp} (hops : ∀ op ∈ ops, OpOk platform op) {G : Type}
    [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hna : usesArea m k = false) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535)
    (hk : bootFileOk (bootWith ops) (programWith ops m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) (N : Nat) :
    ∃ t, Reach platform σ code b t ∧ t.pc = loopHeadWith ops s0 ∧
      t.trace = initTrace ops σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads ops))) N :=
  boot_run (B := bootWith ops) hwords hlen himpl hPre hm hcov hna devWindow hat hcap
    (show 2 ≤ 126 by decide) (initCode_wide ops) hk hf.itcm (show flashItcm.toNat % 4 = 0 by decide)
    (init_runs ops hops) (show stackTop.toNat % 4 = 0 by decide)
    (by rw [show (bootWith ops).sp.toNat = 0x20020000 from rfl]; omega)
    (fun s hs => stackOk hfit s hs) g0 hs0 b hb N

/-- The run of `boardWith_run`, counted: the initialization's steps, and window `i` in at most 16
steps of `main` and the cost of Talos's run of the step from the window's state.  The theorem
holds under the run conditions of the module's header. -/
theorem boardWith_run_steps {ops : List InitOp} (hops : ∀ op ∈ ops, OpOk platform op) {G : Type}
    [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hna : usesArea m k = false) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535)
    (hk : bootFileOk (bootWith ops) (programWith ops m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) (N : Nat) :
    Counted platform σ code b (loopHeadWith ops s0) N
      (WindowBound m k words tick g0 (fun j => σ (j + initReads ops)))
      (fun i => initTrace ops σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads ops))) i) :=
  boot_run_steps (B := bootWith ops) hwords hlen himpl hPre hm hcov hna devWindow hat hcap
    (show 2 ≤ 126 by decide) (initCode_wide ops) hk hf.itcm (show flashItcm.toNat % 4 = 0 by decide)
    (init_runs ops hops) (show stackTop.toNat % 4 = 0 by decide)
    (by rw [show (bootWith ops).sp.toNat = 0x20020000 from rfl]; omega)
    (fun s hs => stackOk hfit s hs) g0 hs0 b hb N

/-- The run of `boardWith_run` succeeds for every number of steps: the model never stops. -/
theorem boardWith_runs {ops : List InitOp} (hops : ∀ op ∈ ops, OpOk platform op) {G : Type}
    [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hna : usesArea m k = false) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535)
    (hk : bootFileOk (bootWith ops) (programWith ops m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) : ∀ j, ∃ t, run platform σ code j b = some t :=
  runs_forever (c := (initTrace ops σ).length) fun N => by
    obtain ⟨t, r, -, tr⟩ := boardWith_run (σ := σ) hops hwords hlen himpl hPre hm hcov hna hat
      hcap hk hfit g0 hs0 hf b hb N
    exact ⟨t, r, by rw [tr, List.length_append, length_windows]⟩

/-- `boardWith_run` for the initialization `init`. -/
theorem board_run {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hna : usesArea m k = false) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535) (hk : bootFileOk boot (program m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) (N : Nat) :
    ∃ t, Reach platform σ code b t ∧ t.pc = loopHead s0 ∧
      t.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads init))) N :=
  boardWith_run init_ok hwords hlen himpl hPre hm hcov hna hat hcap hk hfit g0 hs0 hf b hb N

/-- `boardWith_run_steps` for the initialization `init`. -/
theorem board_run_steps {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hna : usesArea m k = false) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535) (hk : bootFileOk boot (program m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) (N : Nat) :
    Counted platform σ code b (loopHead s0) N
      (WindowBound m k words tick g0 (fun j => σ (j + initReads init)))
      (fun i => initTrace init σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads init))) i) :=
  boardWith_run_steps init_ok hwords hlen himpl hPre hm hcov hna hat hcap hk hfit g0 hs0 hf b hb N

/-- `boardWith_runs` for the initialization `init`. -/
theorem board_runs {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hna : usesArea m k = false) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535) (hk : bootFileOk boot (program m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) : ∀ j, ∃ t, run platform σ code j b = some t :=
  boardWith_runs init_ok hwords hlen himpl hPre hm hcov hna hat hcap hk hfit g0 hs0 hf b hb

/-- The bytes of the generator's area lie in DTCM. -/
theorem area_ram : ∀ j < areaSize areaPages, Ram platform (areaHeader + UInt32.ofNat j) :=
  fun j hj => by
    have h := toNat_add_ofNat (a := areaHeader) (k := j)
      (by rw [show areaHeader.toNat = 536870912 from rfl]; unfold areaSize areaPages at hj; omega)
    rw [show areaHeader.toNat = 536870912 from rfl] at h
    unfold areaSize areaPages at hj
    exact ram_of (by omega) (by omega)

theorem areaEnd_toNat : areaEnd.toNat = areaHeader.toNat + areaSize areaPages := by decide

/-- The image of a program whose module `am` has an area, laid out by `areaBootWith ops` with the
program of step `k` of `m`, whose bytes the kernel's check `hk` finds in flash, run from reset to
the start of the initialization `ops`: SP holds the top of DTCM, LR 0xFFFFFFFF, the trace is
empty, and the machine holds the store in which `am` starts in the area at DTCM's base, below the
stack's limit at the area's end.  The theorem holds under the run conditions of the module's
header. -/
theorem boardWith_setup {ops : List InitOp} {am m : Module} {gts : List ValueType} {k : Nat}
    {s0 : List UInt64} {n len : Nat} (hok : setupOk am areaPages = true)
    (hgt : globalTypesOf am = some gts)
    (hk : bootFileOk (areaBootWith ops am)
      (bootProgram (areaBootWith ops am) m k s0 areaEnd devBase) n len = true)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) :
    ∃ t, Reach platform σ code b t ∧
      t.pc = after (bootWith ops).reset (setupCode areaHeader areaPages am).length ∧
      CodeAt code t.pc (initCode ops) ∧ t.sp = stackTop ∧ t.lr = 0xFFFFFFFF ∧ t.trace = [] ∧
      t.reads = 0 ∧ StoreRel platform areaHeader areaEnd areaPages gts (initStore am areaPages) t :=
  setup_boot (B := bootWith ops) hok hgt (by decide) area_ram (Nat.le_of_eq areaEnd_toNat.symm)
    (show 2 ≤ 126 by decide) (initCode_wide ops) hk hf.itcm (show stackTop.toNat % 4 = 0 by decide)
    (show flashItcm.toNat % 4 = 0 by decide) b hb

/-- A program whose module `m` has an area, from reset on the board with the initialization `ops`,
whose accesses name device registers: for every sequence `σ` of the values that device reads
return and every number `N` of windows, the image of step `k` of `m` from the state `g0` in the
layout `areaBootWith ops m`, whose bytes the kernel's check `hk` finds in flash, runs the setup of
the area, which leaves the store in which `m` starts there, and reaches the loop's head of `main`
with the initialization's accesses followed by those of the first `N` windows, which read `σ`
from the value after the initialization's reads.  The step's call keeps the invariant `J`, which
holds of the initial store with the heap `heap`, and the area, the outgoing area of `main`, and
the stack's bound fit in DTCM.  The theorem holds under the run conditions of the module's
header. -/
theorem areaBoardWith_run {ops : List InitOp} (hops : ∀ op ∈ ops, OpOk platform op) {G : Type}
    {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat} {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {J : Heap → Store Unit → Prop} (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hcov : reachCovered m k = true) (hok : setupOk m areaPages = true) {heap : Heap}
    (hat : heap.At (initStore m areaPages)) (hJ : J heap (initStore m areaPages))
    (hk : bootFileOk (areaBootWith ops m)
      (bootProgram (areaBootWith ops m) m k s0 areaEnd devBase) n len = true)
    (hfit : areaSize areaPages + 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G)
    (hs0 : words g0 = s0) {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    (hf : Flash code n len) (b : State) (hb : Reset code flashItcm b) (N : Nat) :
    ∃ t, Reach platform σ code b t ∧ t.pc = areaLoopHeadWith ops m s0 ∧
      t.trace = initTrace ops σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads ops))) N := by
  have he : areaEnd.toNat = 0x20011000 := by decide
  have ha : areaSize areaPages = 69632 := rfl
  exact setupBoot_run (B := bootWith ops) hlen hcall hm hcov hok area_ram
    (Nat.le_of_eq areaEnd_toNat.symm) devWindow hat hJ (show 2 ≤ 126 by decide)
    (initCode_wide ops) hk hf.itcm (show flashItcm.toNat % 4 = 0 by decide) (init_runs ops hops)
    (show stackTop.toNat % 4 = 0 by decide)
    (by rw [show (bootWith ops).sp.toNat = 0x20020000 from rfl]; omega)
    (fun s hs => stackOk_of (by rw [he]; decide) (by rw [he]; omega) s hs) g0 hs0 b hb N

/-- The run of `areaBoardWith_run`, counted: the setup's and the initialization's steps, and
window `i` in at most 16 steps of `main` and the cost of Talos's run of the step from the window's
state.  The theorem holds under the run conditions of the module's header. -/
theorem areaBoardWith_run_steps {ops : List InitOp} (hops : ∀ op ∈ ops, OpOk platform op)
    {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat} {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {J : Heap → Store Unit → Prop} (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hcov : reachCovered m k = true) (hok : setupOk m areaPages = true) {heap : Heap}
    (hat : heap.At (initStore m areaPages)) (hJ : J heap (initStore m areaPages))
    (hk : bootFileOk (areaBootWith ops m)
      (bootProgram (areaBootWith ops m) m k s0 areaEnd devBase) n len = true)
    (hfit : areaSize areaPages + 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G)
    (hs0 : words g0 = s0) {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    (hf : Flash code n len) (b : State) (hb : Reset code flashItcm b) (N : Nat) :
    Counted platform σ code b (areaLoopHeadWith ops m s0) N
      (WindowBound m k words tick g0 (fun j => σ (j + initReads ops)))
      (fun i => initTrace ops σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads ops))) i) := by
  have he : areaEnd.toNat = 0x20011000 := by decide
  have ha : areaSize areaPages = 69632 := rfl
  exact setupBoot_run_steps (B := bootWith ops) hlen hcall hm hcov hok area_ram
    (Nat.le_of_eq areaEnd_toNat.symm) devWindow hat hJ (show 2 ≤ 126 by decide)
    (initCode_wide ops) hk hf.itcm (show flashItcm.toNat % 4 = 0 by decide) (init_runs ops hops)
    (show stackTop.toNat % 4 = 0 by decide)
    (by rw [show (bootWith ops).sp.toNat = 0x20020000 from rfl]; omega)
    (fun s hs => stackOk_of (by rw [he]; decide) (by rw [he]; omega) s hs) g0 hs0 b hb N

/-- The run of `areaBoardWith_run` succeeds for every number of steps: the model never stops. -/
theorem areaBoardWith_runs {ops : List InitOp} (hops : ∀ op ∈ ops, OpOk platform op) {G : Type}
    {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat} {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {J : Heap → Store Unit → Prop} (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hcov : reachCovered m k = true) (hok : setupOk m areaPages = true) {heap : Heap}
    (hat : heap.At (initStore m areaPages)) (hJ : J heap (initStore m areaPages))
    (hk : bootFileOk (areaBootWith ops m)
      (bootProgram (areaBootWith ops m) m k s0 areaEnd devBase) n len = true)
    (hfit : areaSize areaPages + 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G)
    (hs0 : words g0 = s0) {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    (hf : Flash code n len) (b : State) (hb : Reset code flashItcm b) :
    ∀ j, ∃ t, run platform σ code j b = some t :=
  runs_forever (c := (initTrace ops σ).length) fun N => by
    obtain ⟨t, r, -, tr⟩ := areaBoardWith_run (σ := σ) hops hlen hcall hm hcov hok hat hJ hk hfit
      g0 hs0 hf b hb N
    exact ⟨t, r, by rw [tr, List.length_append, length_windows]⟩

/-- `boardWith_setup` for the initialization `init`. -/
theorem board_setup {am m : Module} {gts : List ValueType} {k : Nat} {s0 : List UInt64}
    {n len : Nat} (hok : setupOk am areaPages = true) (hgt : globalTypesOf am = some gts)
    (hk : bootFileOk (areaBoot am) (bootProgram (areaBoot am) m k s0 areaEnd devBase) n len = true)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) :
    ∃ t, Reach platform σ code b t ∧
      t.pc = after boot.reset (setupCode areaHeader areaPages am).length ∧
      CodeAt code t.pc (initCode init) ∧ t.sp = stackTop ∧ t.lr = 0xFFFFFFFF ∧ t.trace = [] ∧
      t.reads = 0 ∧ StoreRel platform areaHeader areaEnd areaPages gts (initStore am areaPages) t :=
  boardWith_setup hok hgt hk hf b hb

/-- `areaBoardWith_run` for the initialization `init`. -/
theorem areaBoard_run {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat}
    {words : G → List UInt64} (hlen : ∀ g, (words g).length = s0.length)
    {tick : G → UInt64 → G × UInt64} {J : Heap → Store Unit → Prop}
    (hcall : StepCall m k words tick J) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hok : setupOk m areaPages = true) {heap : Heap} (hat : heap.At (initStore m areaPages))
    (hJ : J heap (initStore m areaPages))
    (hk : bootFileOk (areaBoot m) (bootProgram (areaBoot m) m k s0 areaEnd devBase) n len = true)
    (hfit : areaSize areaPages + 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G)
    (hs0 : words g0 = s0) {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    (hf : Flash code n len) (b : State) (hb : Reset code flashItcm b) (N : Nat) :
    ∃ t, Reach platform σ code b t ∧ t.pc = areaLoopHead m s0 ∧
      t.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads init))) N :=
  areaBoardWith_run init_ok hlen hcall hm hcov hok hat hJ hk hfit g0 hs0 hf b hb N

/-- `areaBoardWith_run_steps` for the initialization `init`. -/
theorem areaBoard_run_steps {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat}
    {words : G → List UInt64} (hlen : ∀ g, (words g).length = s0.length)
    {tick : G → UInt64 → G × UInt64} {J : Heap → Store Unit → Prop}
    (hcall : StepCall m k words tick J) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hok : setupOk m areaPages = true) {heap : Heap} (hat : heap.At (initStore m areaPages))
    (hJ : J heap (initStore m areaPages))
    (hk : bootFileOk (areaBoot m) (bootProgram (areaBoot m) m k s0 areaEnd devBase) n len = true)
    (hfit : areaSize areaPages + 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G)
    (hs0 : words g0 = s0) {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    (hf : Flash code n len) (b : State) (hb : Reset code flashItcm b) (N : Nat) :
    Counted platform σ code b (areaLoopHead m s0) N
      (WindowBound m k words tick g0 (fun j => σ (j + initReads init)))
      (fun i => initTrace init σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads init))) i) :=
  areaBoardWith_run_steps init_ok hlen hcall hm hcov hok hat hJ hk hfit g0 hs0 hf b hb N

/-- `areaBoardWith_runs` for the initialization `init`. -/
theorem areaBoard_runs {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {n len : Nat}
    {words : G → List UInt64} (hlen : ∀ g, (words g).length = s0.length)
    {tick : G → UInt64 → G × UInt64} {J : Heap → Store Unit → Prop}
    (hcall : StepCall m k words tick J) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hok : setupOk m areaPages = true) {heap : Heap} (hat : heap.At (initStore m areaPages))
    (hJ : J heap (initStore m areaPages))
    (hk : bootFileOk (areaBoot m) (bootProgram (areaBoot m) m k s0 areaEnd devBase) n len = true)
    (hfit : areaSize areaPages + 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G)
    (hs0 : words g0 = s0) {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    (hf : Flash code n len) (b : State) (hb : Reset code flashItcm b) :
    ∀ j, ∃ t, run platform σ code j b = some t :=
  areaBoardWith_runs init_ok hlen hcall hm hcov hok hat hJ hk hfit g0 hs0 hf b hb

end LeanExe.M7.Nucleo
