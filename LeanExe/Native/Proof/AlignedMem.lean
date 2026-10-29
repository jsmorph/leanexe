import LeanExe.Native.Proof.MemOps
import LeanExe.ProofKit.AlignedExec

/-!
Where the native proof consumes the alignment fact.  `load64Aligned` is the translation of
`load64` without the test `(t & 7) == 0`: the address, the bound, and one word of `lx_mem`.
`sim_load64_aligned` is `sim_load64` for that statement, with the premise that the access of the
Talos step is aligned, `AlignedOne`; the branch of eight byte loads disappears, and the premise
supplies the divisibility that `eval_wordAt` needs.  The other premises and the conclusion are
those of `InstrSim` for an `i32` address at height `σr.length`.
-/

namespace LeanExe.Native

open Wasm LClight LeanExe.ProofKit

/-- `load64` with offset `off` at the address in the `i32` slot at height `h`, without the
alignment test. -/
def load64Aligned (c : FCtx) (h : Nat) (off : UInt32) : statement :=
  .Ssequence (addrStmt (slotId h .i64) (tmp h .i32) off)
    (.Ssequence (boundsCheck 8 c.result (slotId h .i64))
      (.Sset (slotId h .i64) (wordAt c.cap (slotId h .i64))))

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

end

end LeanExe.Native
