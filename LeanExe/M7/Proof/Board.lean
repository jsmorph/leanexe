import LeanExe.M7.Board
import LeanExe.M7.Proof.Init
import LeanExe.M7.Proof.Runs
import LeanExe.M7.Proof.Setup

/-!
The run of a program with requests on the NUCLEO-F767ZI from reset, in the model.  `Flash code n
len` states that the code map holds the file's bytes in flash, from `0x08000000` and from
`0x00200000`, and `Reset code flashItcm b` that `b` is the state that reset gives from the vector
table at `0x00200000`.  `board_run` states, for every sequence `σ` of the values that device reads
return and every number `N` of windows, that the model reaches the loop's head of `main` with
the trace of the initialization followed by the accesses of the first `N` windows, whose reads
take the values of `σ` after the initialization's `initReads init` reads, and `board_runs` that
the run never stops.  `init_addrs` lists the initialization's registers in the order of its
accesses, all in RCC, GPIOD, and USART3, and `windows_confined` states that every access of the
windows of a step whose requests name `USART_ISR`, `USART_RDR`, or `USART_TDR` is an access of one
of those registers.

The theorems hold of the processor under the conditions of the model: a power-on reset, with
BOOT0 low and BOOT_ADD0 0x0080; software watchdogs, which this board's option bytes select
(OPTCR reads 0xFFFFAAFD, IWDG_SW and WWDG_SW set), so that no watchdog runs; and no interrupt,
NMI, debug halt, debugger access, or DMA during the run.  A reset over SWD with the probe attached
is not a power-on reset: the probe leaves DHCSR's C_DEBUGEN and DEMCR set, which the model does
not track.

`board_setup` runs the image of a program whose module has a memory, laid out by `areaBoot`, from
reset to the initialization's start: the setup leaves the module's initial store in the area at
DTCM's base, below the stack's limit `areaLimit cap`, when the area fits in DTCM.
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

/-- The stack below an outgoing area of `n` slots at the top of DTCM, for a step that needs
`need` bytes below it. -/
theorem stackOk {n need : Nat} (hfit : 8 * n + need ≤ 0x20000) (s : State)
    (h : s.sp = stackTop - UInt32.ofNat (8 * n)) : StackOk platform stackLimit n need s := by
  have hs : s.sp.toNat = 0x20020000 - 8 * n := by
    rw [h, UInt32.toNat_sub, UInt32.toNat_ofNat']
    simp only [stackTop, Nat.reducePow]
    rw [show (UInt32.toNat 0x20020000) = 0x20020000 from rfl]
    omega
  have hl : stackLimit.toNat = 0x20000000 := rfl
  refine ⟨mod4_of_toNat (by rw [hs]; omega), fun j hj => ram_of ?_ ?_, by omega, by omega,
    fun j hj => ram_of ?_ ?_, by omega⟩
  all_goals
    simp only [UInt32.toNat_add, UInt32.toNat_ofNat', hs, hl, Nat.reducePow] at *
    omega

theorem init_ok : ∀ op ∈ init, OpOk platform op := by
  intro op hop
  simp only [init, List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp only [OpOk, DevReg] <;> decide

theorem initReads_eq : initReads init = 11 := rfl

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

/-- The register blocks of RCC, GPIOD, and USART3. -/
def InitBlock (a : UInt32) : Prop :=
  (0x40023800 ≤ a.toNat ∧ a.toNat < 0x40023C00) ∨ (0x40020C00 ≤ a.toNat ∧ a.toNat < 0x40021000) ∨
    (0x40004800 ≤ a.toNat ∧ a.toNat < 0x40004C00)

/-- Every access of the initialization lies in RCC, GPIOD, or USART3. -/
theorem init_confined (σ : Nat → UInt32) : ∀ e ∈ initTrace init σ, InitBlock e.addr := by
  intro e he
  have hm := List.mem_map_of_mem (f := Access.addr) he
  rw [init_addrs] at hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> rw [h] <;> unfold InitBlock <;> decide

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

/-- A program with requests from reset on the board: for every sequence `σ` of the values that
device reads return and every number `N` of windows, the image of step `k` of `m` from the state
`g0`, whose bytes the kernel's check `hk` finds in flash, reaches the loop's head of `main` with
the initialization's accesses followed by those of the first `N` windows, which read `σ` from
the value after the initialization's reads.  The theorem holds under the run conditions of the
module's header. -/
theorem board_run {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hcap : st.memoryCap m 0 ≤ 65535)
    (hk : bootFileOk boot (program m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) (N : Nat) :
    ∃ t, Reach platform σ code b t ∧ t.pc = loopHead s0 ∧
      t.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) tick g0 (fun j => σ (j + initReads init))) N :=
  boot_run (B := boot) hwords hlen himpl hPre hm hcov devWindow hat hcap (by decide)
    (initCode_wide init) hk hf.itcm (by decide) (initRuns σ code) (by decide)
    (by rw [show boot.sp.toNat = 0x20020000 from rfl]; omega)
    (fun s hs => stackOk hfit s hs) g0 hs0 b hb N

/-- The run of `board_run` succeeds for every number of steps: the model never stops. -/
theorem board_runs {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hcap : st.memoryCap m 0 ≤ 65535)
    (hk : bootFileOk boot (program m k s0) n len = true)
    (hfit : 8 * (s0.length + 1) + stackBound m k ≤ 0x20000) (g0 : G) (hs0 : words g0 = s0)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) : ∀ j, ∃ t, run platform σ code j b = some t :=
  runs_forever (c := (initTrace init σ).length) fun N => by
    obtain ⟨t, r, -, tr⟩ := board_run (σ := σ) hwords hlen himpl hPre hm hcov hat hcap hk hfit g0
      hs0 hf b hb N
    exact ⟨t, r, by rw [tr, List.length_append, length_windows]⟩

/-- The bytes of an area of `cap` pages at DTCM's base lie in DTCM when the area fits. -/
theorem area_ram {cap : Nat} (hcap : areaSize cap ≤ 0x20000) :
    ∀ j < areaSize cap, Ram platform (areaBase + UInt32.ofNat j) := fun j hj => by
  have h := toNat_add_ofNat (a := areaBase) (k := j)
    (by rw [show areaBase.toNat = 536870912 from rfl]; omega)
  rw [show areaBase.toNat = 536870912 from rfl] at h
  exact ram_of (by omega) (by omega)

theorem areaLimit_toNat {cap : Nat} (hcap : areaSize cap ≤ 0x20000) :
    (areaLimit cap).toNat = areaBase.toNat + areaSize cap :=
  toNat_add_ofNat (by rw [show areaBase.toNat = 536870912 from rfl]; omega)

/-- The image of a program whose module `am` has a memory of `cap` pages, laid out by `areaBoot`
with the program of step `k` of `m`, whose bytes the kernel's check `hk` finds in flash, run from
reset to the initialization's start: SP holds the top of DTCM, LR 0xFFFFFFFF, the trace is empty,
and the machine holds the store in which `am` starts in the area at DTCM's base, below the stack's
limit at the area's end.  The theorem holds under the run conditions of the module's header. -/
theorem board_setup {am m : Module} {cap : Nat} {gts : List ValueType} {k : Nat}
    {s0 : List UInt64} {n len : Nat} (hok : setupOk am cap = true)
    (hgt : globalTypesOf am = some gts) (hcap : areaSize cap ≤ 0x20000)
    (hk : bootFileOk (areaBoot am cap)
      (bootProgram (areaBoot am cap) m k s0 (areaLimit cap) devBase) n len = true)
    {σ : Nat → UInt32} {code : UInt32 → Option UInt16} (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) :
    ∃ t, Reach platform σ code b t ∧ t.pc = after boot.reset (setupCode areaBase cap am).length ∧
      CodeAt code t.pc (initCode init) ∧ t.sp = stackTop ∧ t.lr = 0xFFFFFFFF ∧ t.trace = [] ∧
      t.reads = 0 ∧ StoreRel platform areaBase (areaLimit cap) cap gts (initStore am cap) t :=
  setup_boot (B := boot) hok hgt (by decide) (area_ram hcap)
    (Nat.le_of_eq (areaLimit_toNat hcap).symm) (by decide) (initCode_wide init) hk hf.itcm
    (by decide) (by decide) b hb

end LeanExe.M7.Nucleo
