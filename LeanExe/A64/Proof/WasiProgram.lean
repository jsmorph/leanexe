import LeanExe.A64.Proof.WithMachine
import LeanExe.A64.Proof.WasiStubs
import LeanExe.A64.Proof.LinuxImage
import LeanExe.A64.Proof.Program

/-!
The program of `genWasiProgram` over a machine.  `gen_wasiProgram` unpacks the generator, and
`wasi_calls_ok` gives the simulation of every function of the module's table, the three stubs by
premises of `Machine.StubSim` and the module's functions by `Machine.calls_ok`, with the bounds
`wasiStackNeed` of the stack that a call uses, which count no stack for a stub.  `run_wasiFront`
runs `main` to the entry of `_start`.

A machine's runs read the code map `opsCode`, the words of a list of `Op` from an address, which
holds only the routine `SVC #0; RET` and the program, so every one of its instructions keeps X17;
`opsCode_sub` places it within the executable's code map.
-/

namespace LeanExe.A64

open Wasm

/-! ## The code of a list of words -/

/-- The code map of the words `ops` from `a`. -/
def opsCode (a : UInt64) (ops : List Op) (b : UInt64) : Option UInt32 :=
  if h : (b - a).toNat < 4 * ops.length ∧ (b - a).toNat % 4 = 0 then
    some (ops[(b - a).toNat / 4]'(by omega)).word
  else none

theorem after_sub (a : UInt64) (j : Nat) (hj : 4 * j < 2 ^ 64) :
    (after a j - a).toNat = 4 * j := by
  rw [after, UInt64.add_comm, UInt64.add_sub_cancel, UInt64.toNat_mul, UInt64.toNat_ofNat']
  have e4 : (4 : UInt64).toNat = 4 := rfl
  rw [e4]
  simp only [Nat.reducePow] at *
  omega

theorem opsCode_after {a : UInt64} {ops : List Op} (hn : 4 * ops.length < 2 ^ 64) :
    OpsAt (opsCode a ops) a ops := by
  intro j hj
  have hd := after_sub a j (by omega)
  unfold opsCode
  rw [dif_pos (by omega)]
  simp only [hd, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]

/-- A word of `opsCode a ops` is the word of an element of `ops`, at `after a j` for its index. -/
theorem opsCode_some {a : UInt64} {ops : List Op} {b : UInt64} {w : UInt32}
    (h : opsCode a ops b = some w) :
    ∃ j, ∃ hj : j < ops.length, b = after a j ∧ w = ops[j].word := by
  unfold opsCode at h
  split at h
  · rename_i hb
    obtain rfl := Option.some.inj h
    refine ⟨(b - a).toNat / 4, by omega, ?_, rfl⟩
    rw [after]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
    have e4 : (4 : UInt64).toNat = 4 := rfl
    rw [e4]
    have : b = a + (b - a) := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
    have hlt := (b - a).toNat_lt
    have hlt' := a.toNat_lt
    conv => lhs; rw [this, UInt64.toNat_add]
    simp only [Nat.reducePow] at *
    omega
  · cases h

/-- `opsCode a ops` lies within every code map that holds `ops` from `a`. -/
theorem opsCode_sub {code : UInt64 → Option UInt32} {a : UInt64} {ops : List Op}
    (h : OpsAt code a ops) {b : UInt64} {w : UInt32} (hb : opsCode a ops b = some w) :
    code b = some w := by
  obtain ⟨j, hj, rfl, rfl⟩ := opsCode_some hb
  exact h j hj

/-- The code map of the routine `SVC #0; RET` at `svc` and the program `is` from `a`. -/
def wasiCode (svc a : UInt64) (is : List Instr) (b : UInt64) : Option UInt32 :=
  (opsCode svc [.svc, .ins (.ret 30)] b).or (opsCode a (is.map .ins) b)

theorem wasiCode_sub {code : UInt64 → Option UInt32} {svc a : UInt64} {is : List Instr}
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hprog : CodeAt code a is) :
    ∀ b w, wasiCode svc a is b = some w → code b = some w := by
  intro b w hb
  unfold wasiCode at hb
  cases h1 : opsCode svc [.svc, .ins (.ret 30)] b with
  | some w1 =>
      rw [h1] at hb
      obtain rfl := Option.some.inj hb
      exact opsCode_sub hsvc h1
  | none =>
      rw [h1] at hb
      exact opsCode_sub (fun j hj => by simpa [Op.word] using hprog j (by simpa using hj)) hb

/-- Every instruction of the code map keeps X17 when every instruction of the program does. -/
theorem wasiCode_keeps {svc a : UInt64} {is : List Instr} (hk : is.all Instr.keepsX17 = true) :
    ∀ b w i, wasiCode svc a is b = some w → decode w = some i → i.keepsX17 = true := by
  intro b w i hb hd
  unfold wasiCode at hb
  cases h1 : opsCode svc [.svc, .ins (.ret 30)] b with
  | some w1 =>
      rw [h1] at hb
      obtain rfl := Option.some.inj hb
      obtain ⟨j, hj, -, rfl⟩ := opsCode_some h1
      simp only [List.length_cons, List.length_nil] at hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · simp [Op.word, decode_svcWord] at hd
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, Op.word, decode_encode,
          Option.some.injEq] at hd
        subst hd
        rfl
  | none =>
      rw [h1] at hb
      obtain ⟨j, hj, -, rfl⟩ := opsCode_some hb
      simp only [List.getElem_map, Op.word, decode_encode, Option.some.injEq] at hd
      subst hd
      exact List.all_eq_true.mp hk _ (List.getElem_mem _)

/-- The code map's words lie below `2^55` when the routine and the program end below it. -/
theorem wasiCode_dom {svc a : UInt64} {is : List Instr} (hsvc : svc.toNat + 8 < 2 ^ 55)
    (ha : a.toNat + 4 * is.length < 2 ^ 55) :
    ∀ b w, wasiCode svc a is b = some w → b.toNat < 2 ^ 55 := by
  intro b w hb
  unfold wasiCode at hb
  cases h1 : opsCode svc [.svc, .ins (.ret 30)] b with
  | some w1 =>
      obtain ⟨j, hj, rfl, -⟩ := opsCode_some h1
      simp only [List.length_cons, List.length_nil] at hj
      simp only [after, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
      have e4 : (4 : UInt64).toNat = 4 := rfl
      rw [e4]
      simp only [Nat.reducePow] at *
      omega
  | none =>
      rw [h1] at hb
      obtain ⟨j, hj, rfl, -⟩ := opsCode_some hb
      simp only [List.length_map] at hj
      simp only [after, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
      have e4 : (4 : UInt64).toNat = 4 := rfl
      rw [e4]
      simp only [Nat.reducePow] at *
      omega

/-! ## The generator's program -/

theorem gen_wasiProgram {m : Module} {k : Nat} {svc base room : UInt64} {cap : Nat}
    {is : List Instr} (hg : genWasiProgram m k svc base room cap = .ok is) :
    ∃ gts e main rd wr ex tr fns,
      m.imports = streamImports ∧ areaOk m cap = true ∧ globalTypesOf m = some gts ∧
      gts.length ≤ 511 ∧
      entryIn (wasiSig (wasiFuncs m)) (wasiFirstAt (after base 1)) (wasiFuncs m) k =
        some (e, [], []) ∧
      wasiMain (after base 1) e room = .ok main ∧
      readStub (wasiReadAt (after base 1)) svc (wasiTrapAt (after base 1))
        (wasiErrnoAt (after base 1)) = .ok rd ∧
      writeStub (wasiWriteAt (after base 1)) svc (wasiTrapAt (after base 1))
        (wasiErrnoAt (after base 1)) = .ok wr ∧
      exitStub (wasiExitAt (after base 1)) base = .ok ex ∧
      trapStub (wasiTrapAt (after base 1)) base = .ok tr ∧
      genFunctions (wasiTable (wasiReadAt (after base 1)) (wasiWriteAt (after base 1))
          (wasiExitAt (after base 1)) (wasiFirstAt (after base 1)) (wasiFuncs m))
        { trapUnreachable := wasiTrapAt (after base 1), trapBounds := wasiTrapAt (after base 1),
          trapDiv := wasiTrapAt (after base 1), trapStack := wasiTrapAt (after base 1), cap,
          globalTypes := gts, byteStores := true }
        (wasiFirstAt (after base 1)) (wasiFuncs m) = .ok fns ∧
      is = main ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ fns ∧
      is.all Instr.keepsX17 = true := by
  unfold genWasiProgram at hg
  by_cases himp : m.imports = streamImports
  swap
  · simp [himp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [himp, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hg
  cases hok : areaOk m cap with
  | false => simp [hok, throw, throwThe, MonadExceptOf.throw] at hg
  | true =>
  simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hg
  cases hgt : globalTypesOf m with
  | none => simp [hgt, throw, throwThe, MonadExceptOf.throw] at hg
  | some gts =>
  have hgl : gts.length ≤ 511 := by
    refine Classical.byContradiction fun h => ?_
    simp [hgt, h, throw, throwThe, MonadExceptOf.throw] at hg
  simp only [hgt, hgl, ↓reduceIte] at hg
  split at hg
  · rename_i e hen
    cases hmn : wasiMain (after base 1) e room with
    | error err => simp [hmn] at hg
    | ok main =>
    simp only [hmn] at hg
    cases hrd : readStub (wasiReadAt (after base 1)) svc (wasiTrapAt (after base 1))
        (wasiErrnoAt (after base 1)) with
    | error err => simp [hrd] at hg
    | ok rd =>
    simp only [hrd] at hg
    cases hwr : writeStub (wasiWriteAt (after base 1)) svc (wasiTrapAt (after base 1))
        (wasiErrnoAt (after base 1)) with
    | error err => simp [hwr] at hg
    | ok wr =>
    simp only [hwr] at hg
    cases hex : exitStub (wasiExitAt (after base 1)) base with
    | error err => simp [hex] at hg
    | ok ex =>
    simp only [hex] at hg
    cases htr : trapStub (wasiTrapAt (after base 1)) base with
    | error err => simp [htr] at hg
    | ok tr =>
    simp only [htr] at hg
    cases hfn : genFunctions (wasiTable (wasiReadAt (after base 1)) (wasiWriteAt (after base 1))
          (wasiExitAt (after base 1)) (wasiFirstAt (after base 1)) (wasiFuncs m))
        { trapUnreachable := wasiTrapAt (after base 1), trapBounds := wasiTrapAt (after base 1),
          trapDiv := wasiTrapAt (after base 1), trapStack := wasiTrapAt (after base 1), cap,
          globalTypes := gts, byteStores := true }
        (wasiFirstAt (after base 1)) (wasiFuncs m) with
    | error err => simp [hfn] at hg
    | ok fns =>
    simp only [hfn] at hg
    split at hg
    · rename_i hall
      obtain rfl := Except.ok.inj hg
      exact ⟨gts, e, main, rd, wr, ex, tr, fns, himp, rfl, rfl, hgl, hen, hmn, rfl, rfl, rfl,
        rfl, hfn, rfl, hall⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hg
  · simp [throw, throwThe, MonadExceptOf.throw] at hg

/-! ## The functions in Talos's numbering -/

/-- Function `j` of `m` in Talos's numbering, which counts the imports first. -/
def definedFunc (m : Module) (j : Nat) : Option Function :=
  if m.imports.length ≤ j then m.funcs[j - m.imports.length]? else none

theorem mem_wasiFuncs {m : Module} {j : Nat} {f : Function} (h : (j, f) ∈ wasiFuncs m) :
    m.imports.length ≤ j ∧ m.funcs[j - m.imports.length]? = some f := by
  unfold wasiFuncs at h
  obtain ⟨x, hx, he⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  exact List.mem_zipIdx_iff_getElem?.mp hx

/-- A bound on the bytes of stack that a call of function `k` uses, following calls `d` deep, as
`stackNeed` gives it with the functions in Talos's numbering and no stack for an import, whose stub
uses none. -/
def wasiStackNeed (m : Module) : Nat → Nat → Nat
  | 0, _ => 2 ^ 64
  | d + 1, k =>
      match definedFunc m k with
      | some f => min (2 ^ 64) (frameSize (f.params.length + f.locals.length) +
          CallGraph.callNeed (wasiStackNeed m d) f.body)
      | none => 0

/-- `wasiStackNeed` one call deeper than the module has functions, which reaches the end of every
chain of calls when the calls form no cycle. -/
def wasiStackBound (m : Module) (k : Nat) : Nat := wasiStackNeed m (m.funcs.length + 1) k

theorem wasiStackNeed_zero (m : Module) (k : Nat) : wasiStackNeed m 0 k = 2 ^ 64 := rfl

theorem wasiStackNeed_some {m : Module} {k : Nat} {f : Function} (hk : definedFunc m k = some f)
    (d : Nat) : wasiStackNeed m (d + 1) k = min (2 ^ 64)
      (frameSize (f.params.length + f.locals.length) +
        CallGraph.callNeed (wasiStackNeed m d) f.body) := by
  simp only [wasiStackNeed.eq_2, hk]

theorem wasiStackNeed_none {m : Module} {k : Nat} (hk : definedFunc m k = none) (d : Nat) :
    wasiStackNeed m (d + 1) k = 0 := by
  simp only [wasiStackNeed.eq_2, hk]

theorem wasiStackNeed_succ_le (m : Module) :
    ∀ d k, wasiStackNeed m (d + 1) k ≤ wasiStackNeed m d k
  | 0, k => by
      cases hk : definedFunc m k with
      | none => simp only [wasiStackNeed_none hk 0, Nat.zero_le]
      | some f =>
          rw [wasiStackNeed_some hk 0, wasiStackNeed_zero]
          exact Nat.min_le_left _ _
  | d + 1, k => by
      cases hk : definedFunc m k with
      | none => simp only [wasiStackNeed_none hk (d + 1), wasiStackNeed_none hk d, Nat.le_refl]
      | some f =>
          have h := CallGraph.callNeed_mono (wasiStackNeed_succ_le m d) f.body
          rw [wasiStackNeed_some hk (d + 1), wasiStackNeed_some hk d, Nat.min_def, Nat.min_def]
          split <;> split <;> omega

theorem wasiStackNeed_ok {m : Module} {k : Nat} {f : Function} (hk : definedFunc m k = some f) :
    ∀ d, NeedOk (wasiStackNeed m d) (frameSize (f.params.length + f.locals.length)) f.body
      (wasiStackNeed m d k)
  | 0 => .inl (Nat.le_of_eq (wasiStackNeed_zero m k).symm)
  | d + 1 => by
      have h := CallGraph.callNeed_mono (wasiStackNeed_succ_le m d) f.body
      unfold NeedOk
      rw [wasiStackNeed_some hk d, Nat.min_def]
      split <;> omega

theorem definedFunc_of {m : Module} {k : Nat} {f : Function} (hle : m.imports.length ≤ k)
    (hf : m.funcs[k - m.imports.length]? = some f) : definedFunc m k = some f := by
  unfold definedFunc
  rw [if_pos hle, hf]

/-! ## The table of calls -/

theorem sigOf_wasiTable (rd wr ex first : UInt64) (fs : List (Nat × Function)) :
    sigOf (wasiTable rd wr ex first fs) = wasiSig fs := by
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 =>
      simp only [sigOf, wasiTable, wasiSig, entryIn, Option.map_map]
      exact find_entriesFrom _ _ _ _

/-- The functions of the table of `genWasiProgram` simulate at every fuel over the machine `M`,
the three imports by their stubs and the module's functions by their generated code. -/
theorem wasi_calls_ok {P : Platform} {code : UInt64 → Option UInt32} {α : Type}
    (M : Machine P code α) {m : Module} {rd wr ex first : UInt64} {S : Shared}
    {need : Nat → Nat} (himp : m.imports = streamImports) (h64 : m.memIs64 = false)
    (hU : S.byteStores = true → P.normal P.uart = false) {hr hw hx : HostFn α}
    (henv : M.env.funcs = [hr, hw, hx])
    (hsr : M.StubSim S (need 0) [.i32, .i32, .i32, .i32] [.i32] hr rd)
    (hsw : M.StubSim S (need 1) [.i32, .i32, .i32, .i32] [.i32] hw wr)
    (hsx : M.StubSim S (need 2) [.i32] [] hx ex) {fns : List Instr}
    (hfg : genFunctions (wasiTable rd wr ex first (wasiFuncs m)) S first (wasiFuncs m) = .ok fns)
    (hcode : CodeAt code first fns)
    (hneed : ∀ k f, m.imports.length ≤ k → m.funcs[k - m.imports.length]? = some f →
      NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) :
    ∀ F, M.CallsOk F m (wasiTable rd wr ex first (wasiFuncs m)) S need := by
  refine Machine.calls_ok M h64 hU (fun k c hk => ?_) hneed
  match k, hk with
  | 0, hk =>
      obtain rfl := Option.some.inj hk.symm
      exact .inl ⟨_, hr, by rw [himp]; rfl, by rw [henv]; rfl, rfl, hsr⟩
  | 1, hk =>
      obtain rfl := Option.some.inj hk.symm
      exact .inl ⟨_, hw, by rw [himp]; rfl, by rw [henv]; rfl, rfl, hsw⟩
  | 2, hk =>
      obtain rfl := Option.some.inj hk.symm
      exact .inl ⟨_, hx, by rw [himp]; rfl, by rw [henv]; rfl, rfl, hsx⟩
  | j + 3, hk =>
      obtain ⟨f, fis, hmem, hpr, hgen, hcd⟩ :=
        gen_functions code (sigOf_wasiTable rd wr ex first (wasiFuncs m)) hfg hcode _
          (entryIn_mem hk)
      obtain ⟨hle, hf⟩ := mem_wasiFuncs hmem
      exact .inr ⟨f, fis, hle, hf, hpr, hgen, hcd⟩

/-! ## `main` -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The run of `wasiMain` from its entry to the entry of `_start`: X30 saved in `main`'s frame of
16 bytes, the stack's limit in X18 `room` bytes below it, and `BL` to `_start` with the return
address at `after A 9`. -/
theorem run_wasiFront {A e room : UInt64} {is : List Instr} (hg : wasiMain A e room = .ok is)
    (hcode : CodeAt code A is) {ms : State} (hpc : ms.pc = A) (hal : ms.sp % 16 = 0)
    (hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true) :
    ∃ t, Reach P code ms t ∧ t.pc = e ∧ t.x 30 = after A 9 ∧ t.sp = ms.sp - 16 ∧
      t.x 18 = ms.sp - 16 - room ∧ t.x 17 = ms.x 17 ∧ t.io = ms.io ∧
      t.mem = store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30) := by
  unfold wasiMain at hg
  cases hb : bField (after A 8) e with
  | error err => simp [hb, bind, Except.bind] at hg
  | ok g =>
  simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  have s1 := CodeAt.split code (l1 := [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0])
    (l2 := movImm 16 room ++ [.subReg 18 18 16, .bl g, .movz 0 0 0, .ldr 30 31 0,
      .addImm 31 31 16, .ret 30]) (n := 3)
    (by simpa only [List.append_assoc] using hcode) rfl
  have s2 := CodeAt.split code (l1 := movImm 16 room) (l2 := [.subReg 18 18 16, .bl g,
    .movz 0 0 0, .ldr 30 31 0, .addImm 31 31 16, .ret 30]) s1.2 (n := 4) rfl
  have c0 := (CodeAt.cons.mp s1.1).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).1
  have c2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).2).1
  rw [after_after] at c2
  have c7 := s2.2 0 (by simp)
  have c8 := s2.2 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c7 c8
  have halm : (ms.sp - 16) % 16 = 0 := sub_aligned (k := 16) hal (by decide)
  let t1 : State := { ms with sp := ms.sp - 16, pc := ms.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subImm 31 31 16) ms = some t1 := rfl
  let t2 : State :=
    { t1 with mem := store64 t1.mem (slotAddr t1.sp 0) (t1.x 30), pc := t1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.str 30 31 0) t1 = some t2 :=
    exec_str_sp P (i := 0) (by decide) halm fun j hj => by
      simpa using hmain j (by omega)
  let t2a : State := { t2.setX 18 (t2.sp + UInt64.ofNat 0) with pc := t2.pc + 4 }
  have e2a : LeanExe.A64.exec P (.addImm 18 31 0) t2 = some t2a := rfl
  have p2 : t2.pc = after A 2 := by
    show ms.pc + 4 + 4 = A + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  have p2a : t2a.pc = after A 3 := by
    show t2.pc + 4 = _
    rw [p2, ← after_succ]
  have h18a : t2a.x 18 = ms.sp - 16 := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
    exact add_ofNat_zero _
  have r2 : Reach P code ms t2a :=
    reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by show code (ms.pc + 4) = _; rw [hpc]; simpa [after] using c1) e2
        (reach_exec P code (by rw [p2]; exact c2) e2a (.refl _)))
  obtain ⟨t3a, r3a, p3a, hx16, hk3a, sp3a, mem3a, out3a⟩ :=
    run_movImm P code (d := 16) (v := room) (by decide) (s2.1) p2a
  obtain ⟨t3b, r3b, p3b, x3b, k3b, sp3b, m3b, io3b⟩ := step_subReg P code (s := t3a) (d := 18)
    (n := 18) (m := 16) (by decide) (by rw [p3a, after_after]; exact c7)
  have q3b : t3b.pc = after A 8 := by rw [p3b, p3a, after_after, ← after_succ]
  obtain ⟨t4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_bl P code (s := t3b) (target := e)
    (by rw [q3b]; exact c8) (by rw [q3b]; exact bField_target hb)
  have hx17 : t2a.x 17 = ms.x 17 := by
    rw [State.x_withPc, State.x_setX_ne (by decide)]
    rfl
  refine ⟨t4, r2.trans (r3a.trans (r3b.trans r4)), p4, by rw [x4, q3b, ← after_succ], ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [sp4, sp3b, sp3a]
    show (t2.setX 18 (t2.sp + UInt64.ofNat 0)).sp = _
    rw [State.setX_sp]
  · rw [k4 18 (by decide), x3b, hx16, hk3a 18 (by decide), h18a]
  · rw [k4 17 (by decide), k3b 17 (by decide), hk3a 17 (by decide), hx17]
  · rw [io4, io3b, out3a]
    rfl
  · rw [m4, m3b, mem3a]
    show (t2.setX 18 (t2.sp + UInt64.ofNat 0)).mem = _
    rw [State.setX_mem]
    rfl

end LeanExe.A64
