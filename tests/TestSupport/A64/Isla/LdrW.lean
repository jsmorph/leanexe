import LeanExe.A64.Isla.Walk

/-!
Theorems of `Agrees` for `LDR Wt, [Xn|SP, #(4 * imm)]` of `LeanExe/A64/Machine.lean` at the
UART's data register `0x09000000` or flag register `0x09000018`, for every value of the fields
`imm12`, `Rn`, and `Rt`, register 31 included.  The traces are `ldr-w-uart` of `tests/isla/tcg`,
`tests/isla/kvm`, and `tests/isla/sme` with the arguments `memory`, under the profiles `tcg`,
`kvm`, and `sme`.  The three traces differ in the exception entry of the alignment fault, which
writes more fields of `PSTATE` under `kvm` and `sme`, and in `sme` reads `PSTATE.SM` there alone,
so each profile has its own proof.  `tests/isla/theorems.sh` elaborates the module and prints the
axioms of its theorems.

A theorem states as premises, in the model's terms, the constraints that the trace's `assume`
events and fixed reads check.  The mask constraint of `traces.sh` puts `u.ttbr0`, the value of
`TTBR0_NS`, at a multiple of 32 in the RAM GiB, and the memory holds the descriptor
`0x0060000000000401` of the first GiB at `u.ttbr0`, which the walk reads.  The address, register
`Rn`, the stack pointer for 31, plus the scaled immediate, lies where the reset constraint puts it,
at one of the two registers.  On a misaligned stack pointer `exec` fails, so the paths to the
alignment fault's exception entry need no counterpart, and every other path writes `SEE` and no
other register outside the model.

The trace reads the register's four bytes into a declared variable once, at the address `P.uart`
or `P.uart + 0x18` that `exec`'s success gives, and by reading 12 of `Trace.lean` the read's value
must be the value `v` that `Platform.devLoad` gives there, and the path continues with the UART's
state `io` that it gives.  Register `t` receives the variable zero-extended, so every path ends in
`exec`'s state `{ s.devRead t v with io }`, and `dev_bwd` builds the path that gives the variable
`v`'s value.  Each theorem rests on lemmas for the four cases of register 31 among `Rn` and `Rt`,
one for each direction.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk
instead of that of all the lemmas that would elaborate at once. -/
set_option Elab.async false

attribute [local congr] run_congr runSome_congr

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a device load is `exec`'s
state, the load of the device's value with the UART's state after the read. -/
macro "dev_end" : tactic => `(tactic| (
  done_end
  try simp only [setRegAt_pc, setRegAt_31 rfl]
  first
    | exact devRead_io_eq _ _ _ _
    | exact devRead_io_31 _ (by assumption) _ _))

/-! The load at the UART under `tcg`. -/

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Wt, [Xn|SP, #(4 * imm)]` at the UART under `tcg`. -/
def devTcg : Footprint := isla_trace% "tests/isla/tcg/ldr-w-uart"

isla_nodes devTcg

set_option maxRecDepth 100000 in
theorem devTcg_n0 : devTcg.trace = devTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx devTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem devTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : t.val = 31)
    (h : devTcg.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem devTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : t.val = 31) :
    devTcg.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem devTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : devTcg.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem devTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    devTcg.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem devTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : devTcg.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem devTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    devTcg.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem devTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : devTcg.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem devTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    devTcg.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devTcg_n0, show devTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

/-- The trace of `LDR Wt, [Xn|SP, #(4 * imm)]` at the UART's data or flag register under `tcg`
agrees with `exec` for every value of the fields, register 31 included, from every state that meets
the configuration's constraints, with the value and the UART's state that `Platform.devLoad`
gives. -/
theorem dev_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] devTcg (memFields t n imm)
      (.ldrW t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show devTcg.opcode = [.bits 10 0b1011100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := devTcg.ctx_of σ u hσ
    obtain ⟨⟨v, io⟩, hl⟩ := Option.isSome_iff_exists.mp (exec_ldrW_devLoad hs)
    obtain ⟨-, -, rfl⟩ := exec_ldrW hs hl
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact devTcg_fwd_sp_zr hc httbr ha hs hl hn ht h
      · exact devTcg_fwd_sp_r hc httbr ha hs hl hn ht h
      · exact devTcg_fwd_x_zr hc httbr ha hs hl hn ht h
      · exact devTcg_fwd_x_r hc httbr ha hs hl hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact devTcg_bwd_sp_zr hc httbr hd ha hs hl hn ht
      · exact devTcg_bwd_sp_r hc httbr hd ha hs hl hn ht
      · exact devTcg_bwd_x_zr hc httbr hd ha hs hl hn ht
      · exact devTcg_bwd_x_r hc httbr hd ha hs hl hn ht

/-! The load at the UART under `kvm`. -/

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Wt, [Xn|SP, #(4 * imm)]` at the UART under `kvm`. -/
def devKvm : Footprint := isla_trace% "tests/isla/kvm/ldr-w-uart"

isla_nodes devKvm

set_option maxRecDepth 100000 in
theorem devKvm_n0 : devKvm.trace = devKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx devKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem devKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : t.val = 31)
    (h : devKvm.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem devKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : t.val = 31) :
    devKvm.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem devKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : devKvm.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem devKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    devKvm.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem devKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : devKvm.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem devKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    devKvm.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem devKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : devKvm.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem devKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    devKvm.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devKvm_n0, show devKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

/-- The trace of `LDR Wt, [Xn|SP, #(4 * imm)]` at the UART's data or flag register under `kvm`
agrees with `exec` for every value of the fields, register 31 included, from every state that meets
the configuration's constraints, with the value and the UART's state that `Platform.devLoad`
gives. -/
theorem dev_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] devKvm (memFields t n imm)
      (.ldrW t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show devKvm.opcode = [.bits 10 0b1011100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := devKvm.ctx_of σ u hσ
    obtain ⟨⟨v, io⟩, hl⟩ := Option.isSome_iff_exists.mp (exec_ldrW_devLoad hs)
    obtain ⟨-, -, rfl⟩ := exec_ldrW hs hl
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact devKvm_fwd_sp_zr hc httbr ha hs hl hn ht h
      · exact devKvm_fwd_sp_r hc httbr ha hs hl hn ht h
      · exact devKvm_fwd_x_zr hc httbr ha hs hl hn ht h
      · exact devKvm_fwd_x_r hc httbr ha hs hl hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact devKvm_bwd_sp_zr hc httbr hd ha hs hl hn ht
      · exact devKvm_bwd_sp_r hc httbr hd ha hs hl hn ht
      · exact devKvm_bwd_x_zr hc httbr hd ha hs hl hn ht
      · exact devKvm_bwd_x_r hc httbr hd ha hs hl hn ht

/-! The load at the UART under `sme`. -/

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Wt, [Xn|SP, #(4 * imm)]` at the UART under `sme`. -/
def devSme : Footprint := isla_trace% "tests/isla/sme/ldr-w-uart"

isla_nodes devSme

set_option maxRecDepth 100000 in
theorem devSme_n0 : devSme.trace = devSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx devSme (sme.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devSme` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem devSme_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : t.val = 31)
    (h : devSme.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devSme` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem devSme_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : t.val = 31) :
    devSme.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devSme` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem devSme_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : devSme.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devSme` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem devSme_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    devSme.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devSme` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem devSme_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : devSme.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devSme` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem devSme_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    devSme.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `devSme` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem devSme_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} {o : Outcome} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : devSme.Run P (memFields t n imm) s σ o) :
    o = .done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run at h
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdl]
    all_goals dev_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `devSme` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem devSme_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s : State} {v : UInt32} {io : Io} {σ : Sys} (hσ : devSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018)
    (hs : exec P (.ldrW t n imm) s = some { s.devRead t v with io })
    (hl : P.devLoad s.io (s.xsp n + .ofNat (4 * imm.val)) = some (v, io))
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    devSme.Run P (memFields t n imm) s σ (.done { s.devRead t v with io }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hdev, -⟩ := exec_ldrW hs hl
    have hdl := devLoad_ofNat hl
    have hdn : (s.xsp n + .ofNat (4 * imm.val)).toNat = (P.uart + 0x18).toNat ∨
        (s.xsp n + .ofNat (4 * imm.val)).toNat = P.uart.toNat :=
      hdev.imp (congrArg UInt64.toNat) (congrArg UInt64.toNat)
    have hu18 : (P.uart + 0x18).toNat = (P.uart.toNat + 24) % 18446744073709551616 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have : P.uart.toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (4 * imm.val)).toNat =
        ((s.xsp n).toNat + 4 * imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    rw [xsp_lt (by omega)] at hx ha hdn hdl
    unfold Footprint.Run
    rw [devSme_n0, show devSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    dev_bwd v using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc, hdl]
    all_goals first
      | exact hT
      | (apply Eq.symm; dev_end; done)
      | mem_side hσ [hn, ht]

/-- The trace of `LDR Wt, [Xn|SP, #(4 * imm)]` at the UART's data or flag register under `sme`
agrees with `exec` for every value of the fields, register 31 included, from every state that meets
the configuration's constraints, with the value and the UART's state that `Platform.devLoad`
gives. -/
theorem dev_sme (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000000 ∨
      (s.xsp n + .ofNat (4 * imm.val)).toNat = 0x09000018) :
    Agrees P (sme.sys .memory u) ["SEE", "__BranchTaken"] devSme (memFields t n imm)
      (.ldrW t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show devSme.opcode = [.bits 10 0b1011100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := devSme.ctx_of σ u hσ
    obtain ⟨⟨v, io⟩, hl⟩ := Option.isSome_iff_exists.mp (exec_ldrW_devLoad hs)
    obtain ⟨-, -, rfl⟩ := exec_ldrW hs hl
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact devSme_fwd_sp_zr hc httbr ha hs hl hn ht h
      · exact devSme_fwd_sp_r hc httbr ha hs hl hn ht h
      · exact devSme_fwd_x_zr hc httbr ha hs hl hn ht h
      · exact devSme_fwd_x_r hc httbr ha hs hl hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact devSme_bwd_sp_zr hc httbr hd ha hs hl hn ht
      · exact devSme_bwd_sp_r hc httbr hd ha hs hl hn ht
      · exact devSme_bwd_x_zr hc httbr hd ha hs hl hn ht
      · exact devSme_bwd_x_r hc httbr hd ha hs hl hn ht

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.dev_tcg
#print axioms TestSupport.A64.Isla.dev_kvm
#print axioms TestSupport.A64.Isla.dev_sme
