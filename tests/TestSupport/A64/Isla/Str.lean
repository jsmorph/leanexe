import LeanExe.A64.Isla.Walk

/-!
Theorems of `Agrees` for `STR Xt, [Xn|SP, #(8 * imm)]` of `LeanExe/A64/Machine.lean` with every
byte of the access in the RAM GiB, for every value of the fields `imm12`, `Rn`, and `Rt`, register
31 included.  The traces are those of `tests/isla/tcg` and `tests/isla/kvm` with the arguments
`memory`, under the profiles `tcg` and `kvm`.  The two traces differ: under `kvm`, FEAT_LSE2 lets
an unaligned access within 16 bytes run as one access, and the exception entry of the alignment
fault writes more fields of `PSTATE`, so each profile has its own proof.
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.

A theorem states as premises, in the model's terms, the constraints that the trace's `assume`
events and fixed reads check.  The mask constraint of `traces.sh` puts `u.ttbr0`, the value of
`TTBR0_NS`, at a multiple of 32 in the RAM GiB, and the memory holds the descriptor
`0x0040000040000705` of `LeanExe/A64/Table.lean` at `u.ttbr0 + 8`, which the walk reads.  The
access's address, register `Rn`, the stack pointer for 31, plus the scaled immediate, lies where
the reset constraint puts it, with every byte in the RAM GiB.  On a misaligned stack pointer
`exec` fails, so the paths to the alignment fault's exception entry need no counterpart, and every
other path writes `SEE` and no other register outside the model.

`STR` needs two more premises.  An unaligned doubleword store under `tcg`, or one that crosses a
16-byte boundary under `kvm`, writes its bytes one at a time and translates the address of each
byte after storing the bytes before it.  Reading 5 of `Trace.lean` sends a byte written at
`P.uart` to the output, while `exec` stores all eight bytes in memory, so the UART's byte must lie
outside Normal memory, and `mapped_uart` shows that no byte of the store is the UART's.  The walk
for each later byte reads the descriptor at `u.ttbr0 + 8` from the memory as the earlier stores
left it, so the eight bytes must lie clear of that descriptor, and `bytes_store_far` of the walk
keeps the descriptor's value across the stores of the earlier bytes.  The proofs walk the traces
with the tactics of `LeanExe/A64/Isla/Walk.lean`, and each theorem rests on lemmas for the four
cases of register 31 among `Rn` and `Rt`, one for each direction.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk
instead of that of all the lemmas that would elaborate at once. -/
set_option Elab.async false

attribute [local congr] run_congr runSome_congr

/-! Memory: eight byte stores as the model's `store64`. -/

theorem add_left_inj' (a d e : UInt64) : a + d = a + e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (· - a) h
    simpa only [UInt64.add_comm a, UInt64.add_sub_cancel] using this
  · intro h
    rw [h]

theorem add_eq_self (a d : UInt64) : a + d = a ↔ d = 0 := by
  have := add_left_inj' a d 0
  rwa [UInt64.add_zero] at this

theorem add_sub_left' (a d : UInt64) : a + d - a = d := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel]

theorem eq_add_sub (a b : UInt64) : b = a + (b - a) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_sub]
  have := toNat_lt a
  have := toNat_lt b
  omega

theorem byteOf_eq (v : UInt64) (k : Nat) (hk : k < 8) :
    byteOf v k = UInt8.ofNat (v.toNat / 2 ^ (8 * k) % 256) := by
  apply UInt8.toNat_inj.mp
  have h1 : 8 * k % 2 ^ 64 % 64 = 8 * k := by omega
  simp only [byteOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, h1, Nat.reducePow, Nat.mod_mod]

/-- Eight byte stores from `a`, the lowest byte first, are `store64`. -/
theorem store8_chain (m : UInt64 → UInt8) (a v : UInt64) :
    store8 (store8 (store8 (store8 (store8 (store8 (store8 (store8 m a (byteOf v 0))
      (a + 1) (byteOf v 1)) (a + 2) (byteOf v 2)) (a + 3) (byteOf v 3)) (a + 4) (byteOf v 4))
      (a + 5) (byteOf v 5)) (a + 6) (byteOf v 6)) (a + 7) (byteOf v 7) = store64 m a v := by
  funext b
  rw [eq_add_sub a b]
  generalize b - a = d
  simp only [store8, store64, add_left_inj', add_eq_self, add_sub_left']
  by_cases h0 : d = 0
  · subst h0; rfl
  by_cases h1 : d = 1
  · subst h1; rfl
  by_cases h2 : d = 2
  · subst h2; rfl
  by_cases h3 : d = 3
  · subst h3; rfl
  by_cases h4 : d = 4
  · subst h4; rfl
  by_cases h5 : d = 5
  · subst h5; rfl
  by_cases h6 : d = 6
  · subst h6; rfl
  by_cases h7 : d = 7
  · subst h7; rfl
  have h8 : ¬ d < 8 := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [← UInt64.toNat_inj] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [UInt64.reduceToNat] at h h0 h1 h2 h3 h4 h5 h6 h7
    omega
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]

/-- `writeBytes` of eight bytes is eight byte stores. -/
theorem writeBytes_eight (m : UInt64 → UInt8) (a : UInt64) (x : Nat) :
    writeBytes m a x 8 =
      store8 (store8 (store8 (store8 (store8 (store8 (store8 (store8 m a (.ofNat (x % 256)))
        (a + 1) (.ofNat (x / 256 % 256))) (a + 2) (.ofNat (x / 65536 % 256)))
        (a + 3) (.ofNat (x / 16777216 % 256))) (a + 4) (.ofNat (x / 4294967296 % 256)))
        (a + 5) (.ofNat (x / 1099511627776 % 256))) (a + 6) (.ofNat (x / 281474976710656 % 256)))
        (a + 7) (.ofNat (x / 72057594037927936 % 256)) := by
  funext b
  simp only [writeBytes, store8, UInt64.add_assoc, UInt64.reduceAdd, Nat.div_div_eq_div_mul,
    Nat.reduceMul]

/-! The model's side: `exec` of the form and the end of a path. -/

/-- A byte of the eight from `a` is not the UART's when the eight are Normal memory and the
UART's is not. -/
theorem mapped_uart {P : Platform} {a : UInt64} (hm : P.mapped a 8 = true)
    (hP : P.normal P.uart = false) (i : Nat) (hi : i < 8) : ¬ a + UInt64.ofNat i = P.uart := by
  intro h
  have : P.normal (a + UInt64.ofNat i) = true := by
    simp only [Platform.mapped, List.all_eq_true, List.mem_range] at hm
    exact hm i hi
  rw [h, hP] at this
  cases this

/-- `exec` of a doubleword store: the stack pointer's check passes, the eight bytes are Normal
memory, and the state stores register `t` there. -/
theorem exec_str {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.str t n imm) s = some s') : s.spAligned n = true ∧
      P.mapped (s.xsp n + .ofNat (8 * imm.val)) 8 = true ∧
      s' = { s with mem := store64 s.mem (s.xsp n + .ofNat (8 * imm.val)) (s.x t),
                    pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · rename_i h1
    rw [Bool.and_eq_true] at h1
    exact ⟨h1.1, h1.2, (Option.some.inj hs).symm⟩
  · cases hs

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a doubleword store is
`exec`'s, whose state `hs` states, with the facts in brackets that no byte of the store is the
UART's. -/
syntax "str_end " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| str_end $hs [$xs,*]) => `(tactic| (
    done_end
    rw [$hs:term]
    simp (disch := omega) only [store, writeBytes_one, writeBytes_eight, ofNat_mod64,
      UInt64.ofNat_add, UInt64.ofNat_toNat, UInt64.reduceOfNat, UInt64.add_zero, UInt64.add_assoc,
      UInt64.reduceAdd, xsp_lt, xsp_31, x_lt, x_31, ← store8_chain, byteOf_eq, Nat.reducePow,
      Nat.reduceMul, Nat.div_one, Nat.mod_mod, UInt64.reduceToNat, Nat.zero_div, Nat.zero_mod,
      State.mk.injEq, and_true, true_and, and_self, ↓reduceIte, Nat.reduceEqDiff, and_false,
      $xs,*]))

set_option maxRecDepth 100000 in
/-- The footprint of `STR Xt, [Xn|SP, #(8 * imm)]` in RAM under `tcg`. -/
def strTcg : Footprint := isla_trace% "tests/isla/tcg/str"

isla_nodes strTcg

set_option maxRecDepth 100000 in
theorem strTcg_n0 : strTcg.trace = strTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
        | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
        | mem_side hσ [hn, ht]

/-- The trace of `STR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem str_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (hP : P.normal P.uart = false) (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] strTcg (memFields t n imm)
      (.str t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show strTcg.opcode = [.bits 10 0b1111100100, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := strTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strTcg_fwd_sp_zr hc hP httbr ha hs hn ht h
      · exact strTcg_fwd_sp_r hc hP httbr ha hs hn ht h
      · exact strTcg_fwd_x_zr hc hP httbr ha hs hn ht h
      · exact strTcg_fwd_x_r hc hP httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strTcg_bwd_sp_zr hc hP httbr hd ha hs hn ht
      · exact strTcg_bwd_sp_r hc hP httbr hd ha hs hn ht
      · exact strTcg_bwd_x_zr hc hP httbr hd ha hov hs hn ht
      · exact strTcg_bwd_x_r hc hP httbr hd ha hov hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STR Xt, [Xn|SP, #(8 * imm)]` in RAM under `kvm`. -/
def strKvm : Footprint := isla_trace% "tests/isla/kvm/str"

isla_nodes strKvm

set_option maxRecDepth 100000 in
theorem strKvm_n0 : strKvm.trace = strKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
             | mem_side hσ [hn, ht])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  without_info
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
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
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
             | mem_side hσ [hn, ht])

/-- The trace of `STR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem str_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (hP : P.normal P.uart = false) (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] strKvm (memFields t n imm)
      (.str t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show strKvm.opcode = [.bits 10 0b1111100100, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := strKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strKvm_fwd_sp_zr hc hP httbr ha hs hn ht h
      · exact strKvm_fwd_sp_r hc hP httbr ha hs hn ht h
      · exact strKvm_fwd_x_zr hc hP httbr ha hs hn ht h
      · exact strKvm_fwd_x_r hc hP httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strKvm_bwd_sp_zr hc hP httbr hd ha hs hn ht
      · exact strKvm_bwd_sp_r hc hP httbr hd ha hs hn ht
      · exact strKvm_bwd_x_zr hc hP httbr hd ha hov hs hn ht
      · exact strKvm_bwd_x_r hc hP httbr hd ha hov hs hn ht

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.str_tcg
#print axioms TestSupport.A64.Isla.str_kvm
