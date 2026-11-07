import LeanExe.A64.Isla.Walk

/-!
Theorems of `Agrees` for `STRB Wt, [Xn|SP, #imm]` of `LeanExe/A64/Machine.lean`, with the byte in
the RAM GiB and with the byte at the UART's data register, for every value of the fields `imm12`,
`Rn`, and `Rt`, register 31 included.  The traces are those of `tests/isla/tcg` and
`tests/isla/kvm` with the arguments `memory`, under the profiles `tcg` and `kvm`: `strb` for the
RAM GiB and `strb-uart` for the UART.  The two traces of each case differ, among other places in
the exception entry of the alignment fault, which writes more fields of `PSTATE` under `kvm`, so
each profile has its own proof.  `tests/isla/theorems.sh` elaborates the module and prints the
axioms of its theorems.

A theorem states as premises, in the model's terms, the constraints that the trace's `assume`
events and fixed reads check.  The mask constraint of `traces.sh` puts `u.ttbr0`, the value of
`TTBR0_NS`, at a multiple of 32 in the RAM GiB.  The memory holds the descriptor of
`LeanExe/A64/Table.lean` that the walk reads: `0x0040000040000705` at `u.ttbr0 + 8` for a byte in
the RAM GiB, and `0x0060000000000401` at `u.ttbr0` for the UART's.  The address, register `Rn`, the
stack pointer for 31, plus the immediate, lies where the reset constraint puts it: in the RAM GiB,
or at `0x09000000`.  On a misaligned stack pointer `exec` fails, so the paths to the alignment
fault's exception entry need no counterpart, and every other path writes `SEE` and no other
register outside the model.

A byte store at `0x09000000` appends the byte to the output when `P.uart` is `0x09000000`, in the
trace through reading 5 of `Trace.lean` and in `exec` through its case of the UART.  For any other
`P.uart`, both store the byte in memory, so the theorems of the UART leave `P` open.  The proofs
walk the traces with the tactics of `LeanExe/A64/Isla/Walk.lean`, and each theorem rests on lemmas
for the four cases of register 31 among `Rn` and `Rt`, one for each direction.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk
instead of that of all the lemmas that would elaborate at once. -/
set_option Elab.async false

attribute [local congr] run_congr runSome_congr

theorem toUInt8_eq (x : UInt64) : x.toUInt8 = UInt8.ofNat (x.toNat % 256) := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_mod]

/-! The model's side: `exec` of the form and the end of a path. -/

/-- `exec` of a byte store: the stack pointer's check passes, and the state appends the byte to
the output at the UART and stores it elsewhere. -/
theorem exec_strb {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.strb t n imm) s = some s') : s.spAligned n = true ∧
      s' = if s.xsp n + .ofNat imm.val = P.uart then
          { s with out := s.out ++ [(s.x t).toUInt8], pc := s.pc + 4 }
        else
          { s with mem := store8 s.mem (s.xsp n + .ofNat imm.val) (s.x t).toUInt8,
                   pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · cases hs
  · rename_i h1
    refine ⟨by simpa using h1, ?_⟩
    split at hs
    · rename_i hu
      rw [ite_eq_left hu]
      exact (Option.some.inj hs).symm
    · rename_i hu
      rw [ite_eq_right hu]
      split at hs
      · exact (Option.some.inj hs).symm
      · cases hs

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a byte store is `exec`'s,
whose state `hs` states. -/
syntax "strb_end " term:max : tactic
macro_rules
  | `(tactic| strb_end $hs) => `(tactic| (
    done_end
    rw [$hs:term]
    split
    all_goals
      rename_i hu
      simp (disch := omega) only [xsp_lt, xsp_31] at hu
      simp (disch := omega) only [store, writeBytes_one, ofNat_mod64, UInt64.ofNat_add,
        UInt64.ofNat_toNat, xsp_lt, xsp_31, x_lt, x_31, toUInt8_eq, Nat.mod_mod, State.mk.injEq,
        List.append_cancel_left_eq, List.cons.injEq, and_true, true_and, and_self, ↓reduceIte,
        Nat.reducePow, UInt64.reduceToNat, Nat.zero_mod, hu]))

/-! The byte in the RAM GiB. -/

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` in RAM under `tcg`. -/
def strbTcg : Footprint := isla_trace% "tests/isla/tcg/strb"

isla_nodes strbTcg

set_option maxRecDepth 100000 in
theorem strbTcg_n0 : strbTcg.trace = strbTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strbTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem strb_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] strbTcg (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show strbTcg.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := strbTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact strbTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact strbTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact strbTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact strbTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact strbTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact strbTcg_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` in RAM under `kvm`. -/
def strbKvm : Footprint := isla_trace% "tests/isla/kvm/strb"

isla_nodes strbKvm

set_option maxRecDepth 100000 in
theorem strbKvm_n0 : strbKvm.trace = strbKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strbKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem strb_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] strbKvm (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show strbKvm.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := strbKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact strbKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact strbKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact strbKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact strbKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact strbKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact strbKvm_bwd_x_r hc httbr hd ha hs hn ht

/-! The byte at the UART's data register. -/

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` at the UART under `tcg`. -/
def uartTcg : Footprint := isla_trace% "tests/isla/tcg/strb-uart"

isla_nodes uartTcg

set_option maxRecDepth 100000 in
theorem uartTcg_n0 : uartTcg.trace = uartTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx uartTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` at the UART's data register under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem uart_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] uartTcg (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show uartTcg.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := uartTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact uartTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact uartTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact uartTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact uartTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact uartTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact uartTcg_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` at the UART under `kvm`. -/
def uartKvm : Footprint := isla_trace% "tests/isla/kvm/strb-uart"

isla_nodes uartKvm

set_option maxRecDepth 100000 in
theorem uartKvm_n0 : uartKvm.trace = uartKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx uartKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
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
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` at the UART's data register under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem uart_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] uartKvm (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show uartKvm.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := uartKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact uartKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact uartKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact uartKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact uartKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact uartKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact uartKvm_bwd_x_r hc httbr hd ha hs hn ht

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.strb_tcg
#print axioms TestSupport.A64.Isla.strb_kvm
#print axioms TestSupport.A64.Isla.uart_tcg
#print axioms TestSupport.A64.Isla.uart_kvm
