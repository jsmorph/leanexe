import LeanExe.M7.Board
import LeanExe.M7.Proof.Init
import LeanExe.M7.Proof.Runs

/-!
The run of a program with requests on the NUCLEO-F767ZI from reset, in the model.  `Flash code n
len` states that the code map holds the file's bytes in flash, from `0x08000000` and from
`0x00200000`, and `Reset code flashItcm b` that `b` is the state that reset gives from the vector
table at `0x00200000`.  `board_run` states, for every sequence `σ` of the values that device reads
return and every number `N` of windows, that the model reaches the loop's head of `main` with
the trace of the initialization followed by the accesses of the first `N` windows, whose reads
take the values of `σ` after the initialization's `initReads init` reads.  `init_addrs` lists the
initialization's registers in the order of its accesses, all in RCC, GPIOD, and USART3.

The theorems hold of the processor under the conditions of the model: a power-on reset, with
BOOT0 low and BOOT_ADD0 0x0080; software watchdogs, which this board's option bytes select
(OPTCR reads 0xFFFFAAFD, IWDG_SW and WWDG_SW set), so that no watchdog runs; and no interrupt,
NMI, debug halt, debugger access, or DMA during the run.  A reset over SWD with the probe attached
is not a power-on reset: the probe leaves DHCSR's C_DEBUGEN and DEMCR set, which the model does
not track.
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

end LeanExe.M7.Nucleo
