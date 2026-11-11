import LeanExe.A64.Isla.Walk

/-!
Theorems of `Agrees` for `LDRB Wt, [Xn|SP, #imm]` of `LeanExe/A64/Machine.lean` with the byte in
the RAM GiB, for every value of the fields `imm12`, `Rn`, and `Rt`, register 31 included.  The
traces are `ldrb` of `tests/isla/tcg`, `tests/isla/kvm`, and `tests/isla/sme` with the arguments
`memory`, under the profiles `tcg`, `kvm`, and `sme`.  The traces differ in the exception entry of
the alignment fault, which writes more fields of `PSTATE` under `kvm` and `sme`, and in `sme`
reads `PSTATE.SM` there alone, so each profile has its own proof.  `tests/isla/theorems.sh`
elaborates the module and prints the axioms of its theorems.

A theorem states as premises, in the model's terms, the constraints that the trace's `assume`
events and fixed reads check.  The mask constraint of `traces.sh` puts `u.ttbr0`, the value of
`TTBR0_NS`, at a multiple of 32 in the RAM GiB, and the memory holds the descriptor
`0x0040000040000705` of `LeanExe/A64/Table.lean` at `u.ttbr0 + 8`, which the walk reads.  The
address, register `Rn`, the stack pointer for 31, plus the immediate, lies where the reset
constraint puts it, in the RAM GiB.  On a misaligned stack pointer `exec` fails, so the paths to
the alignment fault's exception entry need no counterpart, and every other path writes `SEE` and
no other register outside the model.  The trace reads the byte from the state's memory by the
rule of `Trace.Run` for a read of memory, which reading 12 of `Trace.lean` leaves to memory for a
read of 1 byte, and register `t` receives it zero-extended.  The proofs walk the traces with the
tactics of `LeanExe/A64/Isla/Walk.lean`, and each theorem rests on lemmas for the four cases of
register 31 among `Rn` and `Rt`, one for each direction.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk
instead of that of all the lemmas that would elaborate at once. -/
set_option Elab.async false

attribute [local congr] run_congr runSome_congr

/-- A byte that the trace reads, as a word. -/
theorem bytes_one (m : UInt64 → UInt8) (a : UInt64) :
    UInt64.ofNat (bytes m a 1) = (m a).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := UInt8.toNat_lt (m a)
  simp only [bytes, Nat.mul_zero, Nat.add_zero, UInt64.toNat_ofNat', UInt8.toNat_toUInt64,
    Nat.reducePow]
  omega

/-- The address `x + c` as the trace computes it, with the immediate `c` reduced modulo
`2 ^ 64`. -/
theorem byte_addr (x : UInt64) (c : Nat) :
    UInt64.ofNat ((x.toNat + c % 18446744073709551616) % 18446744073709551616) =
      x + UInt64.ofNat c := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, Nat.reducePow, Nat.mod_mod]

/-! The model's side: `exec` of the form and the end of a path. -/

/-- `exec` of a byte load: the stack pointer's check passes, and the state loads the byte into
register `t`, zero-extended. -/
theorem exec_ldrb {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.ldrb t n imm) s = some s') : s.spAligned n = true ∧
      s' = { s.setX t (s.mem (s.xsp n + .ofNat imm.val)).toUInt64 with pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · rename_i h1
    rw [Bool.and_eq_true] at h1
    exact ⟨h1.1, (Option.some.inj hs).symm⟩
  · cases hs

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a byte load is `exec`'s, whose
state `hs` states. -/
syntax "ldrb_end " term:max : tactic
macro_rules
  | `(tactic| ldrb_end $hs) => `(tactic| (
    done_end
    rw [$hs:term]
    simp (disch := omega) only [setX_eq_setRegAt, setRegAt_pc, bytes_one, byte_addr, ofNat_mod64,
      UInt64.ofNat_add, UInt64.ofNat_toNat, UInt64.reduceOfNat, UInt64.add_zero, xsp_lt, xsp_31,
      setRegAt_31, setRegAt_lt, State.mk.injEq, and_true, true_and, and_self]))

/-! The byte load under `tcg`. -/

set_option maxRecDepth 100000 in
/-- The footprint of `LDRB Wt, [Xn|SP, #imm]` in RAM under `tcg`. -/
def ldrbTcg : Footprint := isla_trace% "tests/isla/tcg/ldrb"

isla_nodes ldrbTcg

set_option maxRecDepth 100000 in
theorem ldrbTcg_n0 : ldrbTcg.trace = ldrbTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrbTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrbTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrbTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrbTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrbTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrbTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrbTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrbTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrbTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrbTcg_n0, show ldrbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `LDRB Wt, [Xn|SP, #imm]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldrb_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] ldrbTcg (memFields t n imm)
      (.ldrb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show ldrbTcg.opcode = [.bits 10 0b0011100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := ldrbTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrbTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrbTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrbTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrbTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrbTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrbTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrbTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrbTcg_bwd_x_r hc httbr hd ha hs hn ht

/-! The byte load under `kvm`. -/

set_option maxRecDepth 100000 in
/-- The footprint of `LDRB Wt, [Xn|SP, #imm]` in RAM under `kvm`. -/
def ldrbKvm : Footprint := isla_trace% "tests/isla/kvm/ldrb"

isla_nodes ldrbKvm

set_option maxRecDepth 100000 in
theorem ldrbKvm_n0 : ldrbKvm.trace = ldrbKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrbKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrbKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrbKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrbKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrbKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrbKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrbKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrbKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrbKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrbKvm_n0, show ldrbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `LDRB Wt, [Xn|SP, #imm]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldrb_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] ldrbKvm (memFields t n imm)
      (.ldrb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show ldrbKvm.opcode = [.bits 10 0b0011100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := ldrbKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrbKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrbKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrbKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrbKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrbKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrbKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrbKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrbKvm_bwd_x_r hc httbr hd ha hs hn ht

/-! The byte load under `sme`. -/

set_option maxRecDepth 100000 in
/-- The footprint of `LDRB Wt, [Xn|SP, #imm]` in RAM under `sme`. -/
def ldrbSme : Footprint := isla_trace% "tests/isla/sme/ldrb"

isla_nodes ldrbSme

set_option maxRecDepth 100000 in
theorem ldrbSme_n0 : ldrbSme.trace = ldrbSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrbSme (sme.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbSme` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrbSme_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrbSme.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbSme` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrbSme_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrbSme.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbSme` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrbSme_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrbSme.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbSme` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrbSme_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrbSme.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbSme` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrbSme_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrbSme.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbSme` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrbSme_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrbSme.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrbSme` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrbSme_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrbSme.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldrb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrbSme` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrbSme_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrbSme.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.ldrb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrbSme.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldrb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrbSme_n0, show ldrbSme.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldrb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `LDRB Wt, [Xn|SP, #imm]` in the RAM GiB under `sme` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldrb_sme (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (sme.sys .memory u) ["SEE", "__BranchTaken"] ldrbSme (memFields t n imm)
      (.ldrb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show ldrbSme.opcode = [.bits 10 0b0011100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := ldrbSme.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 633),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrbSme_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrbSme_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrbSme_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrbSme_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrbSme_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrbSme_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrbSme_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrbSme_bwd_x_r hc httbr hd ha hs hn ht

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.ldrb_tcg
#print axioms TestSupport.A64.Isla.ldrb_kvm
#print axioms TestSupport.A64.Isla.ldrb_sme
