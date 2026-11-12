import LeanExe.A64.Linux
import LeanExe.A64.Proof.ByteMemory

/-!
Facts about the process model of `LeanExe/A64/Linux.lean`.  `ProcReach.of_reach` lifts a run of
the program's model into the process's: a step of `step` fetches a word that decodes, which
`svcWord` does not (`decode_svcWord`), executes an instruction other than `MSR FPCR`, whose `exec`
fails, and reaches a program counter below 2^55 when the code map holds words only below 2^55 and
the run ends below it.  `run_svcCall` follows a call routine, `MOVZ X8, #nr`, `SVC #0`, and
`RET`, from its first word to the return, with the effect of `Kernel.svc`.  `svc_read` and
`svc_write` evaluate `Kernel.svc` for the calls of `read` and `write` that do not fail.
`StoreRel.writeList` gives the store relation after a read writes bytes into linear memory, and
`readList_bytes` the bytes that a write takes from it.
-/

namespace LeanExe.A64

open Wasm

theorem decode_svcWord : decode svcWord = none := by decide

theorem encode_ne_svcWord (i : Instr) : encode i ≠ svcWord := fun h => by
  have := decode_encode i
  rw [h, decode_svcWord] at this
  cases this

/-- A step of the program's model fetches, decodes, and executes an instruction. -/
theorem step_parts {P : Platform} {code : UInt64 → Option UInt32} {s t : State}
    (h : step P code s = some t) :
    ∃ w i, code s.pc = some w ∧ decode w = some i ∧ exec P i s = some t := by
  unfold step at h
  cases hc : code s.pc with
  | none => rw [hc] at h; cases h
  | some w =>
    rw [hc] at h
    cases hd : decode w with
    | none => simp [hd] at h
    | some i =>
      simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
      exact ⟨w, i, rfl, hd, h⟩

/-- The value that `MOVZ Xd, #v` writes. -/
theorem movz_value (v : Fin 65536) :
    UInt64.ofNat v.val <<< UInt64.ofNat (16 * (0 : Fin 4).val) = UInt64.ofNat v.val := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Fin.val_zero, Nat.mul_zero,
    Nat.zero_mod, Nat.shiftLeft_zero, Nat.mod_mod]

/-- An instruction that `exec` runs is not `MSR FPCR`. -/
theorem fpcrSource_of_exec {P : Platform} {i : Instr} {s t : State} (h : exec P i s = some t) :
    i.fpcrSource = none := by
  cases i <;> first | rfl | simp [exec] at h

/-- A step of the process at a word that decodes to an instruction that `exec` runs. -/
theorem pstep_exec {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32} {p : Proc}
    {w : UInt32} {i : Instr} {c : State} (hc : code p.core.pc = some w)
    (hd : decode w = some i) (hfp : i.isFP = false ∨ p.fpcr = fpcrValue)
    (he : exec P i p.core = some c) (ht : c.pc.toNat < 2 ^ 55) :
    pstep K P code p = some { p with core := c } := by
  have hw : w ≠ svcWord := fun e => by rw [e, decode_svcWord] at hd; cases hd
  have hs := fpcrSource_of_exec he
  have hn : ¬ (i.isFP = true ∧ p.fpcr ≠ fpcrValue) := fun ⟨h1, h2⟩ => by
    rcases hfp with h | h
    · rw [h] at h1; cases h1
    · exact h2 h
  unfold pstep
  simp only [hc, hw, ↓reduceIte, hd, hs, hn, he, ht]

/-- A step of the process at a placed instruction that `exec` runs. -/
theorem pstep_at {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32} {p : Proc}
    {i : Instr} {c : State} (hc : code p.core.pc = some (encode i))
    (hfp : i.isFP = false ∨ p.fpcr = fpcrValue) (he : exec P i p.core = some c)
    (ht : c.pc.toNat < 2 ^ 55) : pstep K P code p = some { p with core := c } :=
  pstep_exec hc (decode_encode i) hfp he ht

theorem ProcReach.trans {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32}
    {p q r : Proc} (h1 : ProcReach K P code p q) (h2 : ProcReach K P code q r) :
    ProcReach K P code p r := by
  induction h1 with
  | refl => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem ProcReach.single {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32}
    {p q : Proc} (h : pstep K P code p = some q) : ProcReach K P code p q :=
  .next h (.refl q)

/-- A run of the program's model starts at its end or at a word of the code. -/
theorem Reach.start {P : Platform} {code : UInt64 → Option UInt32} {s t : State}
    (h : Reach P code s t) : s = t ∨ ∃ w, code s.pc = some w := by
  cases h with
  | refl => exact .inl rfl
  | next hs _ =>
    obtain ⟨w, -, hc, -, -⟩ := step_parts hs
    exact .inr ⟨w, hc⟩

/-- A run of the program's model is a run of the process with `FPCR` at `fpcrValue`, its trace
unchanged, when the code holds words only below 2^55 and the run ends below 2^55. -/
theorem ProcReach.of_reach {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32}
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {s t : State} (h : Reach P code s t)
    (ht : t.pc.toNat < 2 ^ 55) (tr : List Event) :
    ProcReach K P code ⟨s, fpcrValue, tr⟩ ⟨t, fpcrValue, tr⟩ := by
  induction h with
  | refl => exact .refl _
  | next hs hr ih =>
    rename_i s1 s2 s3
    obtain ⟨w, i, hc, hd, he⟩ := step_parts hs
    have h2 : s2.pc.toNat < 2 ^ 55 := by
      rcases Reach.start hr with e | ⟨w2, hc2⟩
      · rw [e]; exact ht
      · exact hdom _ _ hc2
    exact .next (pstep_exec (p := ⟨s1, fpcrValue, tr⟩) hc hd (.inr rfl) he h2) (ih ht)

/-- A run of the program's model from a process whose `FPCR` holds `fpcrValue`. -/
theorem ProcReach.of_reach' {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32}
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {p : Proc} (hf : p.fpcr = fpcrValue)
    {t : State} (h : Reach P code p.core t) (ht : t.pc.toNat < 2 ^ 55) :
    ProcReach K P code p { p with core := t } := by
  obtain ⟨s, f, tr⟩ := p
  simp only at hf
  subst hf
  exact ProcReach.of_reach hdom h ht tr

/-! ## Call routines -/

/-- The words `ops` lie at `a`. -/
def OpsAt (code : UInt64 → Option UInt32) (a : UInt64) (ops : List Op) : Prop :=
  ∀ i (h : i < ops.length), code (after a i) = some ops[i].word

/-- The process `p` after `MOVZ X8, #nr` of a call routine: X8 at `nr` and the program counter at
the `SVC`. -/
def Proc.enter (p : Proc) (nr : UInt64) : Proc :=
  { p with core := { p.core.setX 8 nr with pc := p.core.pc + 4 } }

/-- The process `p` with its program counter at `a`. -/
def Proc.goto (p : Proc) (a : UInt64) : Proc := { p with core := { p.core with pc := a } }

@[simp] theorem Proc.enter_x8 (p : Proc) (nr : UInt64) : (p.enter nr).core.x 8 = nr := by
  exact State.x_setX_same (s := p.core) (by decide)

theorem Proc.enter_x (p : Proc) (nr : UInt64) {q : Fin 32} (h : q ≠ 8) :
    (p.enter nr).core.x q = p.core.x q := State.x_setX_ne (Ne.symm h)

@[simp] theorem Proc.enter_mem (p : Proc) (nr : UInt64) : (p.enter nr).core.mem = p.core.mem :=
  State.setX_mem

@[simp] theorem Proc.enter_sp (p : Proc) (nr : UInt64) : (p.enter nr).core.sp = p.core.sp :=
  State.setX_sp

@[simp] theorem Proc.enter_io (p : Proc) (nr : UInt64) : (p.enter nr).core.io = p.core.io :=
  State.setX_io

@[simp] theorem Proc.enter_pc (p : Proc) (nr : UInt64) :
    (p.enter nr).core.pc = p.core.pc + 4 := rfl

@[simp] theorem Proc.enter_trace (p : Proc) (nr : UInt64) : (p.enter nr).trace = p.trace := rfl

@[simp] theorem Proc.enter_fpcr (p : Proc) (nr : UInt64) : (p.enter nr).fpcr = p.fpcr := rfl

@[simp] theorem Proc.ret_x0 (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).core.x 0 = v := State.x_setX_same (s := p.core) (by decide)

theorem Proc.ret_x (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) {q : Fin 32}
    (h : q ≠ 0) : (p.ret v m e).core.x q = p.core.x q := State.x_setX_ne (Ne.symm h)

@[simp] theorem Proc.ret_mem (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).core.mem = m := rfl

@[simp] theorem Proc.ret_sp (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).core.sp = p.core.sp := State.setX_sp

@[simp] theorem Proc.ret_io (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).core.io = p.core.io := State.setX_io

@[simp] theorem Proc.ret_pc (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).core.pc = p.core.pc + 4 := rfl

@[simp] theorem Proc.ret_trace (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).trace = p.trace ++ [e] := rfl

@[simp] theorem Proc.ret_fpcr (p : Proc) (v : UInt64) (m : UInt64 → UInt8) (e : Event) :
    (p.ret v m e).fpcr = p.fpcr := rfl

@[simp] theorem Proc.goto_x (p : Proc) (a : UInt64) (q : Fin 32) :
    (p.goto a).core.x q = p.core.x q := rfl

@[simp] theorem Proc.goto_mem (p : Proc) (a : UInt64) : (p.goto a).core.mem = p.core.mem := rfl

@[simp] theorem Proc.goto_sp (p : Proc) (a : UInt64) : (p.goto a).core.sp = p.core.sp := rfl

@[simp] theorem Proc.goto_io (p : Proc) (a : UInt64) : (p.goto a).core.io = p.core.io := rfl

@[simp] theorem Proc.goto_pc (p : Proc) (a : UInt64) : (p.goto a).core.pc = a := rfl

@[simp] theorem Proc.goto_trace (p : Proc) (a : UInt64) : (p.goto a).trace = p.trace := rfl

@[simp] theorem Proc.goto_fpcr (p : Proc) (a : UInt64) : (p.goto a).fpcr = p.fpcr := rfl

/-- The run of a call routine at `a`, `MOVZ X8, #nr`, `SVC #0`, and `RET`, from its first word to
the return: the call's effect, `Kernel.svc` from the process with X8 at `nr`, and a return to the
address in X30, which the call keeps. -/
theorem run_svcCall {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32} {a : UInt64}
    {nr : Fin 65536} (hcode : OpsAt code a [.ins (.movz 8 nr 0), .svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {p q : Proc} (hpc : p.core.pc = a)
    (hsvc : K.svc P (p.enter (UInt64.ofNat nr.val)) = some q)
    (hq : q.core.pc = p.core.pc + 8) (h30 : q.core.x 30 = p.core.x 30)
    (hret : (p.core.x 30).toNat < 2 ^ 55) :
    ProcReach K P code p (q.goto (p.core.x 30)) := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, Op.word] at c0 c1 c2
  have h4 : p.core.pc + 4 = after a 1 := by rw [hpc]; simp [after]
  have hp1 : (p.core.pc + 4).toNat < 2 ^ 55 := by
    rw [h4]
    exact hdom _ _ c1
  have e0 : exec P (.movz 8 nr 0) p.core =
      some { p.core.setX 8 (UInt64.ofNat nr.val) with pc := p.core.pc + 4 } := by
    show some { p.core.setX 8 (UInt64.ofNat nr.val <<< UInt64.ofNat (16 * (0 : Fin 4).val)) with
      pc := p.core.pc + 4 } = _
    rw [movz_value]
  have s0 := pstep_at (K := K) (code := code) (p := p) (by rw [hpc]; exact c0) (.inl rfl) e0 hp1
  have s1 : pstep K P code { p with core := { p.core.setX 8 (UInt64.ofNat nr.val) with
      pc := p.core.pc + 4 } } = some q := by
    unfold pstep
    have hc1 : code (p.core.pc + 4) = some svcWord := by rw [h4]; exact c1
    simp only [hc1, ↓reduceIte]
    exact hsvc
  have e2 : exec P (.ret 30) q.core = some { q.core with pc := q.core.x 30 } := rfl
  have s2 := pstep_at (K := K) (code := code) (p := q) (i := .ret 30)
    (by rw [hq, hpc, show a + 8 = after a 2 by simp [after]]; exact c2) (.inl rfl) e2
    (by rw [h30]; exact hret)
  rw [h30] at s2
  exact .next s0 (.next s1 (.single s2))

/-! ## The calls of read and write -/

/-- The bytes of standard input that remain after the reads of the trace `tr`. -/
def Kernel.rest (K : Kernel) (tr : List Event) : List UInt8 := K.input.drop (stdinOf tr).length

/-- A `read` of descriptor 0 that does not fail returns the `r` bytes that remain or fewer, as
`size` gives, and writes them from X1. -/
theorem svc_read {K : Kernel} {P : Platform} {p : Proc} (h8 : p.core.x 8 = 63)
    (h0 : p.core.x 0 = 0) (hf : K.fail p.trace.length = none)
    (hmap : P.mapped (p.core.x 1) (p.core.x 2).toNat = true) :
    K.svc P p = some (p.ret
      (UInt64.ofNat (min (K.size p.trace.length + 1) (min (p.core.x 2).toNat
        (K.rest p.trace).length)))
      (writeList p.core.mem (p.core.x 1) ((K.rest p.trace).take
        (min (K.size p.trace.length + 1) (min (p.core.x 2).toNat (K.rest p.trace).length))))
      (.read ((K.rest p.trace).take
        (min (K.size p.trace.length + 1) (min (p.core.x 2).toNat (K.rest p.trace).length))))) := by
  unfold Kernel.svc
  simp only [h8, h0, true_and, true_or, ↓reduceIte, hf]
  unfold Kernel.rest
  simp only [hmap, ↓reduceIte]

/-- A `write` of descriptor 1 that does not fail takes the X2 bytes from X1 or fewer, as `size`
gives. -/
theorem svc_write {K : Kernel} {P : Platform} {p : Proc} (h8 : p.core.x 8 = 64)
    (h0 : p.core.x 0 = 1) (hf : K.fail p.trace.length = none)
    (hmap : P.mapped (p.core.x 1) (p.core.x 2).toNat = true) :
    K.svc P p = some (p.ret
      (UInt64.ofNat (min (K.size p.trace.length + 1) (p.core.x 2).toNat)) p.core.mem
      (.write (readList p.core.mem (p.core.x 1)
        (min (K.size p.trace.length + 1) (p.core.x 2).toNat)))) := by
  unfold Kernel.svc
  have h63 : ¬ p.core.x 8 = 63 := by rw [h8]; decide
  simp only [h8, h0, true_and, or_true, ↓reduceIte, hf]
  simp only [show ¬ (64 : UInt64) = 63 by decide, ↓reduceIte, hmap]

/-! ## Bytes that a call writes or reads -/

theorem writeList_other (m : UInt64 → UInt8) :
    ∀ (bs : List UInt8) (a b : UInt64), ¬ (b - a).toNat < bs.length → writeList m a bs b = m b
  | [], _, _, _ => rfl
  | v :: bs, a, b, h => by
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have e : (b - a).toNat = ((b - (a + 1)).toNat + 1) % 2 ^ 64 := by
      simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow] at *
      omega
    rw [writeList, writeList_other _ bs (a + 1) b (by
      simp only [List.length_cons] at h
      intro h'
      apply h
      rw [e]
      simp only [Nat.reducePow] at *
      omega)]
    refine store8_other _ _ _ _ fun e => h ?_
    rw [e, UInt64.sub_self]
    simp

end LeanExe.A64
