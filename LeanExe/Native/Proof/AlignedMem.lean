import LeanExe.Native.Proof.MemOps
import LeanExe.ProofKit.AlignedDefs

/-!
Where the native proof consumes the alignment fact.  `load64Aligned` and `store64Aligned` are
the translations of `load64` and `store64` with the option `alignedAccess`, without the test
`(t & 7) == 0`: the address, the bound, and one word of `lx_mem`.  `sim_load64_aligned` and
`sim_store64_aligned` are `sim_load64` and `sim_store64` for those statements, with the premise
that the access of the Talos step is aligned, `AlignedOne`.  The branch of eight byte accesses
disappears, and the premise supplies the divisibility that `eval_wordAt` and
`eval_wordAt_lvalue` need.  `sim_load64L` and `sim_store64L` give `InstrSimL` for both values
of the option.
-/

namespace LeanExe.Native

open Wasm LClight LeanExe.ProofKit

/-- `load64` with offset `off` at the address in the `i32` slot at height `h`, without the
alignment test. -/
def load64Aligned (c : FCtx) (h : Nat) (off : UInt32) : statement :=
  .Ssequence (addrStmt (slotId h .i64) (tmp h .i32) off)
    (.Ssequence (boundsCheck 8 c.result (slotId h .i64))
      (.Sset (slotId h .i64) (wordAt c.cap (slotId h .i64))))

/-- `store64` with offset `off` at the address in the `i32` slot at height `h` of the value in the
`i64` slot above it, without the alignment test. -/
def store64Aligned (c : FCtx) (h : Nat) (off : UInt32) : statement :=
  .Ssequence (addrStmt (slotId h .i64) (tmp h .i32) off)
    (.Ssequence (boundsCheck 8 c.result (slotId h .i64))
      (.Sassign (wordAt c.cap (slotId h .i64)) (tmp (h + 1) .i64)))

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem sim_load64_aligned (hE : EnvOk E) (F : Nat) (off : UInt32) {L : List Label}
    {σr : List VT} (hb : curBase L ≤ σr.length) {α : Type} {st : Store α} {sl : Locals}
    {le : temp_env} {m : mem} {env : HostEnv α} (hinv : Inv E c (.i32 :: σr) st sl le m)
    (hal : AlignedOne F mod st sl (.load64 off) env) :
    Outcome A X E c L (some (.i64 :: σr)) (execOne F mod st sl (.load64 off) env)
      (load64Aligned c σr.length off) le m := by
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨a, vr, hvs, ha, hrest⟩ := pop1_i32 hinv.stack
      simp only [AlignedOne, hvs] at hal
      simp only [execOne.eq_def, hvs]
      have hmr := hinv.store.2
      have hcapE := hE.cap
      have hpg := hmr.le_cap
      have h32a := a.toNat_lt
      have h32o := off.toNat_lt
      have hq : (UInt64.ofNat (a.toNat + off.toNat)).toNat = a.toNat + off.toNat :=
        toNat_ofNat64 (by omega)
      have hx1 := exec_addr (A := A) (X := X) (E := E) (m := m) ha (slotId σr.length .i64) off
      have ht1 : (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))[
          slotId σr.length .i64]? = some (.Vlong (UInt64.ofNat (a.toNat + off.toNat))) :=
        te_insert_same _ _ _
      obtain ⟨vb, hvb, hbb⟩ := eval_bounds (A := A) hE hmr 8 (by omega) ht1 (by rw [hq]; omega)
        (lim_insert_slot _ _ _ hinv.lim)
      by_cases hob : a.toNat + off.toNat + 8 > st.mem.pages * 65536
      · rw [ite_eq_left hob]
        obtain ⟨m', hxt, hg, hs⟩ := trap_exec (A := A) (X := X)
          (le := le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))
          hE hinv.store hinv.status trapOutOfBounds c.result
        refine ⟨E0 ++ E0,
          le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))), m', ?_,
          hg, by rw [trapCode_oob]; exact hs, by rw [trapCode_oob]; decide⟩
        refine .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1
          (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ ?_ (trapOut_ne_normal _))
        refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hvb ?_ hxt
        show bool_val vb tint m = some true
        rw [hbb, hq]; simp; omega
      · rw [ite_eq_right hob]
        obtain ⟨hfit, hin⟩ := addr_fits hE hmr hob
        have hal' : (a.toNat + off.toNat) % 8 = 0 := hal (by omega)
        have hval : exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (.Sset (slotId σr.length .i64) (wordAt c.cap (slotId σr.length .i64))) E0
            ((le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))).insert
              (slotId σr.length .i64) (.Vlong (st.mem.read64 (a + off)))) m .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (eval_wordAt hE hmr c.cap ht1 (by rw [hq, hfit])
            (by rw [hfit]; exact hin) (by rw [hfit]; exact hal'))
        have hbo : exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (boundsCheck 8 c.result (slotId σr.length .i64)) E0
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            .Out_normal := by
          refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hvb ?_ (.exec_Sskip _ _ _)
          show bool_val vb tint m = some false
          rw [hbb, hq]; simp; omega
        have hfr : Frame σr.length le
            ((le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))).insert
              (slotId σr.length .i64) (.Vlong (st.mem.read64 (a + off)))) :=
          (Frame.insert_slot _ _ _ _ (Nat.le_refl _)).trans
            (Frame.insert_slot _ _ _ _ (Nat.le_refl _))
        refine ⟨.i64 :: σr, rfl, by simp; omega, E0 ++ (E0 ++ E0),
          (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))).insert
            (slotId σr.length .i64) (.Vlong (st.mem.read64 (a + off))), m,
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hbo hval),
          ?_, hfr.mono hb⟩
        exact { stack := ⟨rfl, te_insert_same _ _ _, hrest.frame hfr⟩
                locals := (hinv.locals.insert_other _ (fun i => slotId_ne_localId _ _ i)).insert_other _
                  (fun i => slotId_ne_localId _ _ i)
                store := hinv.store
                status := hinv.status
                brk := brk_insert_slot _ _ _ (brk_insert_slot _ _ _ hinv.brk)
                lim := lim_insert_slot _ _ _ (lim_insert_slot _ _ _ hinv.lim) }

theorem sim_store64_aligned (hE : EnvOk E) (F : Nat) (off : UInt32) {L : List Label}
    {σr : List VT} (hb : curBase L ≤ σr.length) {α : Type} {st : Store α} {sl : Locals}
    {le : temp_env} {m : mem} {env : HostEnv α}
    (hinv : Inv E c (.i64 :: .i32 :: σr) st sl le m)
    (hal : AlignedOne F mod st sl (.store64 off) env) :
    Outcome A X E c L (some σr) (execOne F mod st sl (.store64 off) env)
      (store64Aligned c σr.length off) le m := by
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, a, vr, hvs, hx, ha, hrest⟩ := pop_i64_i32 hinv.stack
      simp only [AlignedOne, hvs] at hal
      simp only [execOne.eq_def, hvs]
      have hmr := hinv.store.2
      have hcapE := hE.cap
      have hpg := hmr.le_cap
      have h32a := a.toNat_lt
      have h32o := off.toNat_lt
      have hq : (UInt64.ofNat (a.toNat + off.toNat)).toNat = a.toNat + off.toNat :=
        toNat_ofNat64 (by omega)
      have hx1 := exec_addr (A := A) (X := X) (E := E) (m := m) ha (slotId σr.length .i64) off
      have ht1 : (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))[
          slotId σr.length .i64]? = some (.Vlong (UInt64.ofNat (a.toNat + off.toNat))) :=
        te_insert_same _ _ _
      have hx' : (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))[
          slotId (σr.length + 1) .i64]? = some (.Vlong x) := by
        rw [te_insert_ne _ (slotId_ne_of_height _ _ (by omega))]; exact hx
      obtain ⟨vb, hvb, hbb⟩ := eval_bounds (A := A) hE hmr 8 (by omega) ht1 (by rw [hq]; omega)
        (lim_insert_slot _ _ _ hinv.lim)
      have hfr : Frame σr.length le
          (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) :=
        Frame.insert_slot _ _ _ _ (Nat.le_refl _)
      by_cases hob : a.toNat + off.toNat + 8 > st.mem.pages * 65536
      · rw [ite_eq_left hob]
        obtain ⟨m', hxt, hg, hs⟩ := trap_exec (A := A) (X := X)
          (le := le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))
          hE hinv.store hinv.status trapOutOfBounds c.result
        refine ⟨E0 ++ E0,
          le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))), m', ?_,
          hg, by rw [trapCode_oob]; exact hs, by rw [trapCode_oob]; decide⟩
        refine .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1
          (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ ?_ (trapOut_ne_normal _))
        refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hvb ?_ hxt
        show bool_val vb tint m = some true
        rw [hbb, hq]; simp; omega
      · rw [ite_eq_right hob]
        obtain ⟨hfit, hin⟩ := addr_fits hE hmr hob
        have hbo : exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (boundsCheck 8 c.result (slotId σr.length .i64)) E0
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            .Out_normal := by
          refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hvb ?_ (.exec_Sskip _ _ _)
          show bool_val vb tint m = some false
          rw [hbb, hq]; simp; omega
        have hst : ∃ m', exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (.Sassign (wordAt c.cap (slotId σr.length .i64)) (tmp (σr.length + 1) .i64)) E0
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m'
            .Out_normal ∧ Mem.SameExcept E.mem m m' ∧
            MemRel E (st.mem.write64 (a + off) x) st.memoryCaps m' := by
          have hal' : (a.toNat + off.toNat) % 8 = 0 := hal (by omega)
          have hvw := hmr.valid_word (i := (a + off).toNat) (by rw [hfit]; exact hin)
            (by rw [hfit]; exact hal')
          refine ⟨Mem.stored .Mint64 m E.mem (a + off).toNat (.Vlong x), ?_,
            Mem.SameExcept.of_stored _ _ _ _ _, hmr.store_word hE (a + off) x⟩
          refine .exec_Sassign _ _ _ _ _ _ _ _ _ _ _
            (eval_wordAt_lvalue hE c.cap ht1 (by rw [hq]; exact hal')) (.eval_Etempvar _ _ _ hx')
            (cast_ll m x) (.assign_loc_value _ .Mint64 _ rfl ?_)
          rw [storev_mem _ (by rw [hq]; simp [size_chunk]; omega) (by decide), hq, ← hfit]
          exact Mem.store_ok _ hvw
        obtain ⟨m', hx2, hs', hmr'⟩ := hst
        refine ⟨σr, rfl, hb, E0 ++ (E0 ++ E0),
          le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))), m',
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hbo hx2),
          ?_, hfr.mono hb⟩
        exact { stack := hrest.frame hfr
                locals := hinv.locals.insert_other _ (fun i => slotId_ne_localId _ _ i)
                store := ⟨GlobalsRel.sameExcept hinv.store.1 hs' hE.mem_not, hmr'⟩
                status := hinv.status.sameExcept hs' (Ne.symm hE.mem_status)
                brk := brk_insert_slot _ _ _ hinv.brk
                lim := lim_insert_slot _ _ _ hinv.lim }

/-- `load64` in either form of the translation: with the test, as `sim_load64` proves, or without
it, from the alignment of the access. -/
theorem sim_load64L (hE : EnvOk E) (F : Nat) (off : UInt32) {CallOk : Nat → Prop} :
    InstrSimL A X E mod c CallOk F (.load64 off) := by
  cases hc : c.alignedAccess
  · exact (sim_load64 hE F off hc).toL
  · intro L σ n s σ' n' h hbase _ _ α st sl le m env hal hinv
    rcases σ with _ | ⟨a0, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff, hc] at h
    obtain ⟨_, ⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    have hb : curBase L ≤ σr.length := by simp at hbase; omega
    exact sim_load64_aligned hE F off hb hinv (hal hc)

/-- `store64` in either form of the translation. -/
theorem sim_store64L (hE : EnvOk E) (F : Nat) (off : UInt32) {CallOk : Nat → Prop} :
    InstrSimL A X E mod c CallOk F (.store64 off) := by
  cases hc : c.alignedAccess
  · exact (sim_store64 hE F off hc).toL
  · intro L σ n s σ' n' h hbase _ _ α st sl le m env hal hinv
    rcases σ with _ | ⟨a0, _ | ⟨b0, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff, hc] at h
    obtain ⟨hb, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
    exact sim_store64_aligned hE F off hb hinv (hal hc)

end

end LeanExe.Native
