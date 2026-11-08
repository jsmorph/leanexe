import LeanExe.A64.Boot
import LeanExe.A64.Proof.Boot
import LeanExe.A64.Proof.Bits
import LeanExe.A64.Proof.Relation

/-!
A run of the program model lifts to a run of the boot model.  A step of the program model changes
only bytes that its platform maps as Normal memory, so the bytes of the translation table, which
`R` protects and `Boot.platform` therefore excludes, keep their values along a run.  `classify`
reads only the 32 bytes of the table, so the platform and every fetch check stay those of the
boot state at the start, and each step of the run is a step of `BootStep` by its rule `prog`.  A
step keeps the UART's output or appends to it, so `uartDone` holds after the run exactly when it
held before and the run wrote no byte to the UART.

While the MMU is off, a run of the program model with the platform `noMemory` that keeps the
UART's output lifts by the rule `plain`: such a run executes no system instruction, on which `exec`
stops, and no load or store, since `noMemory` maps no byte and its only store, to the UART,
appends to the output.  The rule requires a floating-point instruction to run with floating point
enabled, which firmware need not have done, so the run fetches from `withoutFP code`, the words of
the code map that decode to no floating-point instruction.
-/

namespace LeanExe.A64

theorem State.setXsp_mem {s : State} {r : Fin 32} {v : UInt64} : (s.setXsp r v).mem = s.mem := by
  unfold State.setXsp; split <;> rfl

theorem State.setXsp_out {s : State} {r : Fin 32} {v : UInt64} : (s.setXsp r v).out = s.out := by
  unfold State.setXsp; split <;> rfl

/-- A byte less than 8 bytes above `a` is Normal memory when the 8 bytes from `a` are. -/
theorem normal_of_mapped {P : Platform} {a b : UInt64} (hm : P.mapped a 8 = true)
    (h : b - a < 8) : P.normal b = true := by
  have hk : (b - a).toNat < 8 := UInt64.lt_iff_toNat_lt.mp h
  have := List.all_eq_true.mp hm _ (List.mem_range.mpr hk)
  rwa [UInt64.ofNat_toNat, UInt64.add_comm, UInt64.sub_add_cancel] at this

/-- An instruction keeps every byte that its platform does not map as Normal memory. -/
theorem exec_frame {P : Platform} {i : Instr} {s t : State} (h : exec P i s = some t)
    {a : UInt64} (ha : P.normal a = false) : t.mem a = s.mem a := by
  cases i
  case ldr r n imm =>
    simp only [exec] at h
    split at h
    · obtain rfl := Option.some.inj h
      simp
    · cases h
  case str r n imm =>
    simp only [exec] at h
    split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true] at hc
      show store64 s.mem _ _ a = s.mem a
      exact store64_other _ _ _ _ fun hlt => by simp [normal_of_mapped hc.2 hlt] at ha
    · cases h
  case strb r n imm =>
    simp only [exec] at h
    split at h
    · cases h
    split at h
    · obtain rfl := Option.some.inj h
      rfl
    split at h
    · rename_i hn
      obtain rfl := Option.some.inj h
      show store8 s.mem _ _ a = s.mem a
      simp only [store8]
      exact ite_eq_right fun e => by subst e; simp [hn] at ha
    · cases h
  all_goals
    simp only [exec, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [State.setXsp_mem, State.subs, State.fcmp, State.fcmpS]

/-- An instruction keeps the UART's output or appends to it. -/
theorem exec_out {P : Platform} {i : Instr} {s t : State} (h : exec P i s = some t) :
    s.out <+: t.out := by
  cases i
  case ldr r n imm =>
    simp only [exec] at h
    split at h
    · obtain rfl := Option.some.inj h
      simp
    · cases h
  case str r n imm =>
    simp only [exec] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact List.prefix_rfl
    · cases h
  case strb r n imm =>
    simp only [exec] at h
    split at h
    · cases h
    split at h
    · obtain rfl := Option.some.inj h
      exact List.prefix_append _ _
    split at h
    · obtain rfl := Option.some.inj h
      exact List.prefix_rfl
    · cases h
  all_goals
    simp only [exec, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [State.setXsp_out, State.subs, State.fcmp, State.fcmpS]

/-- The fetch, the decoding, and the execution of a step. -/
theorem step_some {P : Platform} {code : UInt64 → Option UInt32} {s t : State}
    (h : step P code s = some t) :
    ∃ w i, code s.pc = some w ∧ decode w = some i ∧ exec P i s = some t := by
  simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hc, i, hd, he⟩ := h
  exact ⟨w, i, hc, hd, he⟩

/-- A step keeps every byte that its platform does not map as Normal memory. -/
theorem step_frame {P : Platform} {code : UInt64 → Option UInt32} {s t : State}
    (h : step P code s = some t) {a : UInt64} (ha : P.normal a = false) : t.mem a = s.mem a := by
  obtain ⟨_, _, _, _, he⟩ := step_some h
  exact exec_frame he ha

/-- A run keeps the UART's output or appends to it. -/
theorem Reach.out {P : Platform} {code : UInt64 → Option UInt32} {s t : State}
    (h : Reach P code s t) : s.out <+: t.out := by
  induction h with
  | refl => exact List.prefix_rfl
  | next hs _ ih =>
    obtain ⟨_, _, _, _, he⟩ := step_some hs
    exact (exec_out he).trans ih

/-- The code map `code` without the words that decode to a floating-point instruction. -/
def withoutFP (code : UInt64 → Option UInt32) (a : UInt64) : Option UInt32 :=
  match code a with
  | some w => if (decode w).any Instr.isFP then none else some w
  | none => none

theorem withoutFP_some {code : UInt64 → Option UInt32} {a : UInt64} {w : UInt32}
    (h : withoutFP code a = some w) :
    code a = some w ∧ ∀ i, decode w = some i → i.isFP = false := by
  unfold withoutFP at h
  split at h
  · split at h
    · cases h
    · rename_i hc hf
      obtain rfl := Option.some.inj h
      refine ⟨hc, fun i hi => ?_⟩
      rw [hi] at hf
      simpa using hf
  · cases h

theorem withoutFP_of {code : UInt64 → Option UInt32} {a : UInt64} {i : Instr}
    (h : code a = some (encode i)) (hi : i.isFP = false) : withoutFP code a = some (encode i) := by
  simp [withoutFP, h, decode_encode, hi]

theorem CodeAt.noFP {code : UInt64 → Option UInt32} {a : UInt64} {is : List Instr}
    (h : CodeAt code a is) (hfp : ∀ i ∈ is, i.isFP = false) :
    CodeAt (withoutFP code) a is :=
  fun k hk => withoutFP_of (h k hk) (hfp _ (List.getElem_mem hk))

/-- An instruction that executes with the platform `noMemory` and keeps the UART's output is
neither a system instruction nor a load or store. -/
theorem plain_of_exec_noMemory {i : Instr} {s t : State} (h : exec noMemory i s = some t)
    (ho : t.out = s.out) : i.isSys = false ∧ i.accessesMemory = false := by
  have hm : ∀ a, noMemory.mapped a 8 = false := fun _ => rfl
  cases i
  case ldr r n imm => simp [exec, hm] at h
  case str r n imm => simp [exec, hm] at h
  case strb r n imm =>
    simp only [exec] at h
    split at h
    · cases h
    split at h
    · obtain rfl := Option.some.inj h
      have := congrArg List.length ho
      simp only [List.length_append, List.length_singleton] at this
      omega
    split at h
    · rename_i hn
      simp [noMemory] at hn
    · cases h
  all_goals first
    | exact ⟨rfl, rfl⟩
    | simp only [exec, reduceCtorEq] at h

/-- While SP_EL1 is the stack pointer and the MMU is off in both copies of `SCTLR_EL1`, a run of
the program model with the platform `noMemory` and the code map `withoutFP code` that keeps the
UART's output is a run of the boot model by its rule `plain`, which changes only the core, when the
code map's addresses and the run's last program counter lie below 2^55. -/
theorem bootReach_of_reach_off {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    {b : Boot} (hsp : b.spSel = true) (hoff : b.mmuOff) {c : State}
    (hr : Reach noMemory (withoutFP code) b.core c) (ho : c.out = b.core.out)
    (hend : c.pc.toNat < 2 ^ 55) :
    BootReach h R code b { b with core := c } := by
  suffices H : ∀ s, Reach noMemory (withoutFP code) s c → c.pc.toNat < 2 ^ 55 → c.out = s.out →
      ∀ b' : Boot, b'.core = s → b'.spSel = true → b'.mmuOff →
      BootReach h R code b' { b' with core := c } from
    H _ hr hend ho b rfl hsp hoff
  clear hr ho hsp hoff hend
  intro s hr
  induction hr with
  | refl =>
    intro _ _ b' hb _ _
    subst hb
    exact .refl _
  | @next s t u hs hr ih =>
    intro hend ho b' hb hsp hoff
    subst hb
    obtain ⟨w, i, hcw, hd, he⟩ := step_some hs
    obtain ⟨hc, hfp⟩ := withoutFP_some hcw
    have hst := exec_out he
    have ht : t.out = b'.core.out := (hst.eq_of_length (by
      have h1 := hst.length_le
      have h2 := hr.out.length_le
      rw [ho] at h2
      omega)).symm
    obtain ⟨hn, hm⟩ := plain_of_exec_noMemory he ht
    have hpc : t.pc.toNat < 2 ^ 55 := by
      cases hr with
      | refl => exact hend
      | next hs' _ =>
        obtain ⟨w', _, hc', _, _⟩ := step_some hs'
        exact hdom _ _ (withoutFP_some hc').1
    exact .next (.plain hc hd hsp (.inl hoff.1) (.inl hoff.2) hn hm (.inl (hfp i hd)) he
      (.inl hpc))
      (ih hend (by rw [ho, ht]) { b' with core := t } rfl hsp hoff)

/-- A run keeps every byte that its platform does not map as Normal memory. -/
theorem Reach.frame {P : Platform} {code : UInt64 → Option UInt32} {s t : State}
    (h : Reach P code s t) {a : UInt64} (ha : P.normal a = false) : t.mem a = s.mem a := by
  induction h with
  | refl => rfl
  | next hs _ ih => rw [ih, step_frame hs ha]

/-- `classify` reads only the 32 bytes of the table at `TTBR0_EL1`: two memories that agree on
them give every address the same type. -/
theorem classify_congr {h : Hw} {s : Sys} {mem mem' : UInt64 → UInt8}
    (hm : ∀ j < 32, mem (s.ttbr0 + UInt64.ofNat j) = mem' (s.ttbr0 + UInt64.ofNat j))
    (a : UInt64) : classify h s mem a = classify h s mem' a := by
  by_cases ha : 0x100000000 ≤ a
  · simp [classify, ha]
  · have hlt : a.toNat < 2 ^ 32 := by
      have : (0x100000000 : UInt64).toNat = 2 ^ 32 := rfl
      rw [UInt64.le_iff_toNat_le, this] at ha
      omega
    have hq : (a >>> (30 : UInt64)).toNat < 4 := by
      rw [UInt64.toNat_shiftRight, show (30 : UInt64).toNat % 64 = 30 from rfl,
        Nat.shiftRight_eq_div_pow]
      omega
    have hd : load64 mem (s.ttbr0 + (8 : UInt64) * (a >>> (30 : UInt64))) =
        load64 mem' (s.ttbr0 + (8 : UInt64) * (a >>> (30 : UInt64))) :=
      load64_congr fun k hk => by
        have := hm (8 * (a >>> (30 : UInt64)).toNat + k) (by omega)
        rwa [UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.ofNat_toNat, ← UInt64.add_assoc] at this
    unfold classify
    rw [hd]

/-- Under the hypotheses of `bootReach_of_reach`, a run of the program model from a state `s` whose
memory agrees with `b`'s on the table lifts to a run of the boot model from `b` with core `s`.
The run changes only the core and `uartDone`, which it keeps when it writes no byte to the UART and
clears otherwise. -/
theorem bootReach_of_reach_agree {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}
    {b : Boot} (hsp : b.spSel = true) (hsync : b.written = b.eff)
    (hcov : b.eff.covered h = true) (htlb : b.tlb = .clean)
    (hu : classify h b.eff b.core.mem uartAddr = some (.device true))
    (hR : ∀ j < 32, R (b.eff.ttbr0 + UInt64.ofNat j) = true)
    (hx : ∀ a w, code a = some w → ∃ x, classify h b.eff b.core.mem a = some (.normal x true))
    {s c : State} (hr : Reach (b.platform h R) code s c) :
    (∀ j < 32,
      s.mem (b.eff.ttbr0 + UInt64.ofNat j) = b.core.mem (b.eff.ttbr0 + UInt64.ofNat j)) →
    ∀ u, BootReach h R code { b with core := s, uartDone := u }
      { b with core := c, uartDone := u && c.out == s.out } := by
  induction hr with
  | refl =>
    intro _ u
    rw [beq_self_eq_true, Bool.and_true]
    exact .refl _
  | @next s t c hs hr ih =>
    intro hT u
    obtain ⟨w, i, hc, hd, he⟩ := step_some hs
    have hT' : ∀ j < 32, t.mem (b.eff.ttbr0 + UInt64.ofNat j) =
        b.core.mem (b.eff.ttbr0 + UInt64.ofNat j) := fun j hj => by
      have hn : (b.platform h R).normal (b.eff.ttbr0 + UInt64.ofNat j) = false := by
        simp [Boot.platform, hR j hj]
      rw [exec_frame he hn, hT j hj]
    have hcl := classify_congr (h := h) hT
    have hP : Boot.platform h R { b with core := s, uartDone := u } = b.platform h R := by
      simp only [Boot.platform, hcl]
    have hu' : (u && t.out == s.out && c.out == t.out) = (u && c.out == s.out) := by
      by_cases ht : t.out = s.out
      · rw [ht, beq_self_eq_true, Bool.and_true]
      · have hst := exec_out he
        have htc := hr.out
        have hcs : c.out ≠ s.out := fun e => ht (hst.eq_of_length (by
          have h1 := hst.length_le
          have h2 := htc.length_le
          rw [e] at h2
          omega)).symm
        rw [beq_false_of_ne ht, beq_false_of_ne hcs]
        simp
    have hr' := ih hT' (u && t.out == s.out)
    rw [hu'] at hr'
    refine .next (c := { b with core := t, uartDone := u && t.out == s.out }) ?_ hr'
    refine .prog hc hd hsp hsync hcov htlb
      (.inr ⟨htlb, (hx _ _ hc).imp fun _ e => (hcl _).trans e⟩) ((hcl _).trans hu) ?_
    rw [hP]
    exact he

/-- A run of the program model under the platform of `b` lifts to a run of the boot model by its
rule `prog` when SP_EL1 is the stack pointer, the written system registers are the effective
ones, translation is on in the covered configuration with valid TLBs, the table maps the UART as
writable Device memory and every address of the code as executable Normal memory, and `R`
protects the table's bytes.  The run's last state differs from `b` only in its core and in
`uartDone`, which holds at the end exactly when it holds in `b` and the run writes no byte to the
UART. -/
theorem bootReach_of_reach {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}
    {b : Boot} (hsp : b.spSel = true) (hsync : b.written = b.eff)
    (hcov : b.eff.covered h = true) (htlb : b.tlb = .clean)
    (hu : classify h b.eff b.core.mem uartAddr = some (.device true))
    (hR : ∀ j < 32, R (b.eff.ttbr0 + UInt64.ofNat j) = true)
    (hx : ∀ a w, code a = some w → ∃ x, classify h b.eff b.core.mem a = some (.normal x true))
    {c : State} (hr : Reach (b.platform h R) code b.core c) :
    BootReach h R code b { b with core := c, uartDone := b.uartDone && c.out == b.core.out } :=
  bootReach_of_reach_agree hsp hsync hcov htlb hu hR hx hr (fun _ _ => rfl) b.uartDone

end LeanExe.A64
