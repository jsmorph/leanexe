import Verified.Reflect.Command
import TestSupport.Native.Common
import LeanExe.Native.Proof.Req
import LeanExe.Native.Requests
import Verified.Bare
import Verified.Call

/-!
The step of the request protocol's test (`docs/native-bare-metal.md`): an echo over a UART that
`main` drives one register access per window.  The step returns the new state and a request: a
read of a register, or a write of a value to a register.  The register map is a parameter, as in
`Uart` of `LeanExe/Native/Proof/Records.lean`: the indices of the receive, transmit, and status
registers, the status bit `rxFull` that is set while the receiver holds a byte, and the status
bits `txMask` that equal `txRoom` while the transmitter has room.  The echo reads the status until
the receiver holds a byte, reads the byte, reads the status until the transmitter has room, and
writes the byte with bit 5 flipped.  The state's low byte is the phase, which names the register
that the last request read, and its second byte holds the byte to send.  `cmsdkTick`
instantiates the map for the CMSDK APB UART0 of QEMU's `mps2-an500`, and `usart3Tick` for USART3
of the STM32F767ZI.
-/

namespace TestSupport.Bare

open LeanExe.Native (readReq writeReq)

/-- The echo's step from the state `s` and the value `v` that the last request read, for the
register map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom`. -/
def echoTick (rx tx status rxFull txMask txRoom s v : UInt64) : UInt64 × UInt64 :=
  let phase := s &&& 255
  if phase == 0 then
    if v &&& rxFull != 0 then (1, readReq rx) else (0, readReq status)
  else if phase == 1 then
    ((2 : UInt64) ||| (((v &&& 255) ^^^ 32) <<< 8), readReq status)
  else if phase == 2 then
    if v &&& txMask == txRoom then (3, writeReq tx (s >>> 8)) else (s, readReq status)
  else (0, readReq status)

/-- The echo for the CMSDK APB UART0 of `mps2-an500`, whose registers lie `0x4000` bytes above
`lx_reg`: data at index `0x1000` for both directions, status at index `0x1001`, bit 1 set while
the receive buffer is full, and bit 0 set while the transmit buffer is full. -/
def cmsdkTick (s v : UInt64) : UInt64 × UInt64 := echoTick 0x1000 0x1000 0x1001 2 1 0 s v

/-- The echo for USART3 of the STM32F767ZI, whose registers lie `0x4800` bytes above `lx_reg`
at `0x40000000` (`USART3_BASE` and `USART_TypeDef` in ST's `stm32f767xx.h`): `USART_RDR` at
index `0x1209`, `USART_TDR` at index `0x120A`, `USART_ISR` at index `0x1207`, `RXNE` in bit 5,
and `TXE` in bit 7, set while the transmit data register is empty. -/
def usart3Tick (s v : UInt64) : UInt64 × UInt64 :=
  echoTick 0x1209 0x120A 0x1207 0x20 0x80 0x80 s v

/-- The ticks that a down-counting 32-bit timer has counted from the reading `t0` to the reading
`t1`. -/
def elapsed (t0 t1 : UInt64) : UInt64 := (t0 - t1) &&& 0xFFFFFFFF

/-- The echo with a deadline, from the state `s` and the value `v` that the last request read,
for the register map of `echoTick` and the index `timer` of a down-counting timer's value: after
reading a byte, it reads the timer; before writing the reply, the byte with bit 5 flipped, it
reads the timer again, and it writes the reply only when fewer than `limit` ticks have passed,
dropping the byte otherwise.  The state is the phase plus 256 times the reply plus 65,536 times
the timer reading taken after the byte arrived. -/
def deadlineTick (rx tx status timer rxFull txMask txRoom limit s v : UInt64) :
    UInt64 × UInt64 :=
  let phase := s % 256
  let reply := (s / 256) % 256
  let stamp := (s / 65536) % 0x100000000
  if phase == 0 then
    if v &&& rxFull != 0 then (1, readReq rx) else (0, readReq status)
  else if phase == 1 then
    (2 + 256 * ((v % 256) ^^^ 32), readReq timer)
  else if phase == 2 then
    (3 + 256 * reply + 65536 * (v % 0x100000000), readReq status)
  else if phase == 3 then
    if v &&& txMask == txRoom then (s + 1, readReq timer) else (s, readReq status)
  else if phase == 4 then
    if elapsed stamp v < limit then (5, writeReq tx reply) else (5, readReq status)
  else (0, readReq status)

/-- The echo with a deadline of `0x1000000` ticks for UART0 and Timer0 of `mps2-an500`, whose
value register is index 1.  QEMU 8.2.2 clocks Timer0 with the system clock of 25 MHz
(`SYSCLK_FRQ` in `hw/arm/mps2.c`), so the limit is 671 ms. -/
def deadlineCmsdkTick (s v : UInt64) : UInt64 × UInt64 :=
  deadlineTick 0x1000 0x1000 0x1001 1 2 1 0 0x1000000 s v

verified_compile (pages := 1) (cap := 1) reqCompiled := [readReq, writeReq, echoTick, cmsdkTick,
  elapsed, deadlineTick, deadlineCmsdkTick, usart3Tick]

/-! ## Polling -/

open LeanExe.Native in
theorem readReq_status : reqWrite (readReq 0x1001) = false := by decide

open LeanExe.Native in
theorem readReq_data : reqWrite (readReq 0x1000) = false := by decide

open LeanExe.Native in
/-- `cmsdkTick` requests a write only from the phase that follows a status read, and only when
the value read shows room in the transmitter. -/
theorem cmsdkTick_write (s v : UInt64) (hw : reqWrite (cmsdkTick s v).2 = true) :
    s &&& 255 = 2 ∧ v &&& 1 = 0 := by
  simp only [cmsdkTick, echoTick] at hw
  split at hw
  · split at hw <;> simp [readReq_status, readReq_data] at hw
  · split at hw
    · simp [readReq_status] at hw
    · split at hw
      · rename_i h2
        split at hw
        · rename_i ht
          exact ⟨by simpa using h2, by simpa using ht⟩
        · simp [readReq_status] at hw
      · simp [readReq_status] at hw

open LeanExe.Native in
/-- `cmsdkTick` enters the phase 2 only with a request to read the status register. -/
theorem cmsdkTick_phase2 (s v : UInt64) (h : (cmsdkTick s v).1 &&& 255 = 2) :
    (cmsdkTick s v).2 = readReq 0x1001 := by
  simp only [cmsdkTick, echoTick] at h ⊢
  split <;> rename_i h0
  · split <;> rename_i hr
    · rw [ite_eq_left h0, ite_eq_left hr] at h
      exact absurd h (by show ¬ (1 : UInt64) &&& 255 = 2; decide)
    · rfl
  · split <;> rename_i h1
    · rfl
    · split <;> rename_i h2
      · split <;> rename_i ht
        · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2, ite_eq_left ht] at h
          exact absurd h (by show ¬ (3 : UInt64) &&& 255 = 2; decide)
        · rfl
      · rfl

open LeanExe.Native in
/-- In every run of the echo from the state 3, a window that requests a write follows a window
that read the status register, and the value read has bit 0, the transmitter's full flag,
clear.  The first window reads the status. -/
theorem echo_write_after_room (σ : Nat → LClight.int) (n : Nat)
    (hw : reqWrite (cmsdkTick (reqRun cmsdkTick 3 σ (n + 1)).state
      (reqRun cmsdkTick 3 σ (n + 1)).last).2 = true) :
    (cmsdkTick (reqRun cmsdkTick 3 σ n).state (reqRun cmsdkTick 3 σ n).last).2 =
      readReq 0x1001 ∧
      (reqRun cmsdkTick 3 σ (n + 1)).last &&& 1 = 0 := by
  obtain ⟨hph, hroom⟩ := cmsdkTick_write _ _ hw
  refine ⟨cmsdkTick_phase2 _ _ ?_, hroom⟩
  have e : (reqRun cmsdkTick 3 σ (n + 1)).state =
      (cmsdkTick (reqRun cmsdkTick 3 σ n).state (reqRun cmsdkTick 3 σ n).last).1 := by
    simp only [reqRun, reqNext]
    split <;> rfl
  rw [← e]
  exact hph

open LeanExe.Native in
theorem echo_first_read : reqWrite (cmsdkTick 3 0).2 = false := by decide

open LeanExe.Native in
theorem readReq_timer : reqWrite (readReq 1) = false := by decide

open LeanExe.Native in
/-- The echo with a deadline requests a write only in the phase that follows a timer read, and
only when fewer than the limit's ticks have passed since the reading in the state. -/
theorem deadlineCmsdkTick_write (s v : UInt64) (hw : reqWrite (deadlineCmsdkTick s v).2 = true) :
    s % 256 = 4 ∧ elapsed ((s / 65536) % 0x100000000) v < 0x1000000 := by
  simp only [deadlineCmsdkTick, deadlineTick] at hw
  split at hw
  · split at hw <;> simp [readReq_status, readReq_data] at hw
  · split at hw
    · simp [readReq_timer] at hw
    · split at hw
      · simp [readReq_status] at hw
      · split at hw
        · split at hw <;> simp [readReq_status, readReq_timer] at hw
        · split at hw
          · rename_i h4
            split at hw
            · rename_i hl
              exact ⟨by simpa using h4, hl⟩
            · simp [readReq_status] at hw
          · simp [readReq_status] at hw

open LeanExe.Native in
/-- The echo with a deadline enters the phase 4 only with a request to read the timer. -/
theorem deadlineCmsdkTick_phase4 (s v : UInt64) (h : (deadlineCmsdkTick s v).1 % 256 = 4) :
    (deadlineCmsdkTick s v).2 = readReq 1 := by
  simp only [deadlineCmsdkTick, deadlineTick] at h ⊢
  split <;> rename_i h0
  · split <;> rename_i hr
    · rw [ite_eq_left h0, ite_eq_left hr] at h
      exact absurd h (by decide)
    · rw [ite_eq_left h0, ite_eq_right hr] at h
      exact absurd h (by decide)
  · split <;> rename_i h1
    · rfl
    · split <;> rename_i h2
      · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2] at h
        have := congrArg UInt64.toNat h
        simp [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, UInt64.toNat_div] at this
        omega
      · split <;> rename_i h3
        · split <;> rename_i ht
          · rfl
          · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, ite_eq_right ht] at h
            have h3' : s % 256 = 3 := by simpa using h3
            rw [h3'] at h
            exact absurd h (by decide)
        · split <;> rename_i h4
          · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4] at h
            split at h <;> simp at h
          · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] at h
            exact absurd h (by decide)

open LeanExe.Native in
/-- In every run of the echo with a deadline from the state 5, a window that requests a write
follows a window that read the timer, and fewer than `0x1000000` ticks separate the reading
stored in the state from the value read. -/
theorem deadline_write_on_time (σ : Nat → LClight.int) (n : Nat)
    (hw : reqWrite (deadlineCmsdkTick (reqRun deadlineCmsdkTick 5 σ (n + 1)).state
      (reqRun deadlineCmsdkTick 5 σ (n + 1)).last).2 = true) :
    (deadlineCmsdkTick (reqRun deadlineCmsdkTick 5 σ n).state
        (reqRun deadlineCmsdkTick 5 σ n).last).2 = readReq 1 ∧
      elapsed (((reqRun deadlineCmsdkTick 5 σ (n + 1)).state / 65536) % 0x100000000)
        (reqRun deadlineCmsdkTick 5 σ (n + 1)).last < 0x1000000 := by
  obtain ⟨hph, hok⟩ := deadlineCmsdkTick_write _ _ hw
  refine ⟨deadlineCmsdkTick_phase4 _ _ ?_, hok⟩
  have e : (reqRun deadlineCmsdkTick 5 σ (n + 1)).state =
      (deadlineCmsdkTick (reqRun deadlineCmsdkTick 5 σ n).state
        (reqRun deadlineCmsdkTick 5 σ n).last).1 := by
    simp only [reqRun, reqNext]
    split <;> rfl
  rw [← e]
  exact hph

open Wasm LClight LeanExe.Native in
/-- The program with requests around `cmsdkTick`, from the state 3, runs forever: for every
sequence `σ` of the values that its volatile loads read, window `n` performs the one register
access that `cmsdkTick` requests from the state and the last value read. -/
theorem echo_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre reqCompiled.translation (reqMain 5 [3])) E0
      (reqTrace cmsdkTick 3 σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := reqCompiled.cmsdkTick.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64])
    (rs0 := [.i64, .i64]) (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] .Tvoid cc_default := by
    rw [entry_type reqCompiled.translation_eq hfd hsig]
    rfl
  have h2 : 2 ≤ reqCompiled.translation.nres := by
    rw [translate_nres reqCompiled.translation_eq,
      translate_funcs_eq reqCompiled.translation_eq reqCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact req_program (n := 1) reqCompiled.translation_eq hpre hfd hty h2 A X
    (heapAt_nativeStore hAt0 1) (words := fun g : UInt64 => [g]) (fun _ => rfl)
    (reqRuns_of_nativeA (n := 0) (fun _ => rfl) (fun _ => rfl) hnat (fun _ _ _ => trivial)
      (by decide)) 3 σ

open Wasm LClight LeanExe.Native in
/-- The program with requests around `usart3Tick`, from the state 3, runs forever: for every
sequence `σ` of the values that its volatile loads read, window `n` performs the one register
access that `usart3Tick` requests from the state and the last value read. -/
theorem echo_usart3_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre reqCompiled.translation (reqMain 9 [3])) E0
      (reqTrace usart3Tick 3 σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := reqCompiled.usart3Tick.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64])
    (rs0 := [.i64, .i64]) (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] .Tvoid cc_default := by
    rw [entry_type reqCompiled.translation_eq hfd hsig]
    rfl
  have h2 : 2 ≤ reqCompiled.translation.nres := by
    rw [translate_nres reqCompiled.translation_eq,
      translate_funcs_eq reqCompiled.translation_eq reqCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact req_program (n := 1) reqCompiled.translation_eq hpre hfd hty h2 A X
    (heapAt_nativeStore hAt0 1) (words := fun g : UInt64 => [g]) (fun _ => rfl)
    (reqRuns_of_nativeA (n := 0) (fun _ => rfl) (fun _ => rfl) hnat (fun _ _ _ => trivial)
      (by decide)) 3 σ

open Wasm LClight LeanExe.Native in
/-- The program with requests around `deadlineCmsdkTick`, from the state 5, runs forever: for
every sequence `σ` of the values that its volatile loads read, window `n` performs the one
register access that `deadlineCmsdkTick` requests from the state and the last value read. -/
theorem deadline_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre reqCompiled.translation (reqMain 8 [5])) E0
      (reqTrace deadlineCmsdkTick 5 σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := reqCompiled.deadlineCmsdkTick.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64])
    (rs0 := [.i64, .i64]) (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] .Tvoid cc_default := by
    rw [entry_type reqCompiled.translation_eq hfd hsig]
    rfl
  have h2 : 2 ≤ reqCompiled.translation.nres := by
    rw [translate_nres reqCompiled.translation_eq,
      translate_funcs_eq reqCompiled.translation_eq reqCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact req_program (n := 1) reqCompiled.translation_eq hpre hfd hty h2 A X
    (heapAt_nativeStore hAt0 1) (words := fun g : UInt64 => [g]) (fun _ => rfl)
    (reqRuns_of_nativeA (n := 0) (fun _ => rfl) (fun _ => rfl) hnat (fun _ _ _ => trivial)
      (by decide)) 5 σ

end TestSupport.Bare
