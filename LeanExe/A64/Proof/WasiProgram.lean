import LeanExe.A64.Proof.WithMachine
import LeanExe.A64.Proof.WasiStubs
import LeanExe.A64.Proof.LinuxImage
import LeanExe.A64.Proof.Program

/-!
The program of `genWasiProgram` over a machine.  `gen_wasiProgram` unpacks the generator, whose
flat stubs come from `flatStubs` by the imports after the stream imports (`mapM_flatStubFor`), and
`wasi_calls_ok` gives the simulation of every function of the module's table, the stream stubs
and the flat stubs by premises of `Machine.StubSim` and the module's functions by
`Machine.calls_ok`, with the bounds `wasiStackNeed` of the stack that a call uses, which count no
stack for a stub.  `run_wasiFront` runs `main` from its entry, through the store of X2 in the
scratch, to the entry of the startup routine, and `run_wasiStart` from the startup routine's
return to the entry of `_start`.

A machine's runs read the code map `wasiCode`, built with `opsCode` from the words of lists of
`Op`, which holds only the routine `SVC #0; RET` and the program, so every one of its instructions
keeps X17.  `wasiCode_sub` places it within the executable's code map.
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

/-- Every instruction of the code map meets `f` when the routine's `RET` and every instruction of
the program do. -/
theorem wasiCode_all {svc a : UInt64} {is : List Instr} {f : Instr → Bool}
    (hret : f (.ret 30) = true) (hk : is.all f = true) :
    ∀ b w i, wasiCode svc a is b = some w → decode w = some i → f i = true := by
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
        exact hret
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

theorem wasiCode_svc {svc a : UInt64} {is : List Instr} :
    OpsAt (wasiCode svc a is) svc [.svc, .ins (.ret 30)] := by
  intro j hj
  have := opsCode_after (a := svc) (ops := [.svc, .ins (.ret 30)]) (by decide) j hj
  unfold wasiCode
  rw [this]
  rfl

theorem wasiCode_prog {svc a : UInt64} {is : List Instr} (hsep : svc.toNat + 8 ≤ a.toNat)
    (hlen : a.toNat + 4 * is.length < 2 ^ 64) : CodeAt (wasiCode svc a is) a is := by
  intro j hj
  have h1 : opsCode svc [.svc, .ins (.ret 30)] (after a j) = none := by
    unfold opsCode
    rw [dif_neg]
    rintro ⟨h, -⟩
    simp only [List.length_cons, List.length_nil] at h
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, after, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
      have e4 : (4 : UInt64).toNat = 4 := rfl
      rw [e4]
      simp only [Nat.reducePow] at *
      omega)] at h
    rw [after, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat'] at h
    have e4 : (4 : UInt64).toNat = 4 := rfl
    rw [e4] at h
    simp only [Nat.reducePow] at *
    omega
  have h2 := opsCode_after (a := a) (ops := is.map .ins) (by simp; omega) j (by simpa using hj)
  unfold wasiCode
  rw [h1, h2]
  simp [Op.word]

/-! ## The generator's program -/

theorem flatStubFor_ok {d : ImportDecl} {s : FlatStub} (h : flatStubFor d = .ok s) :
    s ∈ flatStubs ∧ s.decl = d := by
  unfold flatStubFor at h
  split at h
  · rename_i heq
    obtain rfl := Except.ok.inj h
    exact ⟨List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
  · cases h

/-- The stubs that `flatStubFor` gives for the imports `ds` implement those imports, in order, and
lie in `flatStubs`. -/
theorem mapM_flatStubFor :
    ∀ {ds : List ImportDecl} {stubs : List FlatStub}, ds.mapM flatStubFor = .ok stubs →
      ds = stubs.map (·.decl) ∧ ∀ s ∈ stubs, s ∈ flatStubs
  | [], stubs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | d :: ds, stubs, h => by
    rw [List.mapM_cons] at h
    cases h1 : flatStubFor d with
    | error err => simp [h1, bind, Except.bind] at h
    | ok s =>
    cases h2 : ds.mapM flatStubFor with
    | error err => simp [h1, h2, bind, Except.bind] at h
    | ok ss =>
    simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hs, hd⟩ := flatStubFor_ok h1
    obtain ⟨hds, hss⟩ := mapM_flatStubFor h2
    refine ⟨by rw [hds, ← hd]; rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact hss x hx

/-- The number of instructions of the stubs `stubs`. -/
def stubsSize (stubs : List FlatStub) : Nat := (stubs.map (·.size)).sum

theorem stubsEnd_eq : ∀ (a : UInt64) (stubs : List FlatStub),
    stubsEnd a stubs = after a (stubsSize stubs)
  | a, [] => by simp [stubsEnd, stubsSize, after_zero]
  | a, s :: rest => by
    rw [stubsEnd, stubsEnd_eq, after_after]
    simp [stubsSize]

/-- The code of the stubs `stubs` from `a` and its parts: its length is `stubsSize stubs`, and
each table entry of `stubEntries a j stubs` is that of a stub of `stubs`, whose generator gives
the code at the entry's address. -/
theorem genStubs_code {code : UInt64 → Option UInt32} {svc tr en : UInt64} {sc : Nat} :
    ∀ {a : UInt64} {j : Nat} {stubs : List FlatStub} {is : List Instr},
      genStubs svc tr en sc a stubs = .ok is → CodeAt code a is →
      is.length = stubsSize stubs ∧
      ∀ c ∈ stubEntries a j stubs, ∃ i, ∃ hi : i < stubs.length, ∃ is' b,
        c = (j + i, b, stubs[i].decl.params, stubs[i].decl.results) ∧
        stubs[i].gen b svc tr en sc = .ok is' ∧ CodeAt code b is'
  | a, j, [], is, hg, _ => by
    simp only [genStubs, pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    exact ⟨rfl, fun c hc => by simp [stubEntries] at hc⟩
  | a, j, s :: rest, is, hg, hcode => by
    simp only [genStubs, bind, Except.bind] at hg
    cases h1 : s.gen a svc tr en sc with
    | error err => simp [h1] at hg
    | ok is₀ =>
    simp only [h1] at hg
    by_cases hl : is₀.length = s.size
    · cases h2 : genStubs svc tr en sc (after a s.size) rest with
      | error err => simp [hl, h2] at hg
      | ok is₁ =>
      simp only [hl, h2, pure, Except.pure, Except.ok.injEq, ↓reduceIte] at hg
      subst hg
      have hc := CodeAt.split code hcode hl
      obtain ⟨hlen, hent⟩ := genStubs_code (j := j + 1) h2 hc.2
      refine ⟨by simp [stubsSize, hl, hlen], fun c hc' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨0, by simp, is₀, a, by simp, h1, hc.1⟩
      · obtain ⟨i, hi, is', b, hce, hgi, hci⟩ := hent c hc'
        refine ⟨i + 1, by simpa using hi, is', b, ?_, by simpa using hgi, hci⟩
        rw [hce]
        simp only [List.getElem_cons_succ, Prod.mk.injEq, and_true]
        omega
    · simp [hl, throw, throwThe, MonadExceptOf.throw] at hg

theorem gen_wasiProgram {m : Module} {k : Nat} {svc base room : UInt64} {cap : Nat}
    {is : List Instr} (hg : genWasiProgram m k svc base room cap = .ok is) :
    ∃ stubs gts e main pre rd wr ex tr sts fns,
      m.imports = streamImports ++ stubs.map (·.decl) ∧ (∀ s ∈ stubs, s ∈ flatStubs) ∧
      room.toNat < 2 ^ 32 ∧ areaOk m cap = true ∧ globalTypesOf m = some gts ∧
      gts.length ≤ 511 ∧
      entryIn (wasiSig (stubEntries (wasiFlatAt (after base 1)) 3 stubs) (wasiFuncs m))
        (after (stubsEnd (wasiFlatAt (after base 1)) stubs) wasiStartup.length) (wasiFuncs m) k =
        some (e, [], []) ∧
      wasiMain (after base 1) (stubsEnd (wasiFlatAt (after base 1)) stubs) e room cap =
        .ok main ∧
      wasiPrefix (wasiPrefixAt (after base 1)) = .ok pre ∧
      readStub (wasiReadAt (after base 1)) svc (wasiTrapAt (after base 1))
        (wasiErrnoAt (after base 1)) = .ok rd ∧
      writeStub (wasiWriteAt (after base 1)) svc (wasiTrapAt (after base 1))
        (wasiErrnoAt (after base 1)) = .ok wr ∧
      exitStub (wasiExitAt (after base 1)) base = .ok ex ∧
      trapStub (wasiTrapAt (after base 1)) base = .ok tr ∧
      genStubs svc (wasiTrapAt (after base 1)) (wasiErrnoAt (after base 1)) (areaSize cap)
        (wasiFlatAt (after base 1)) stubs = .ok sts ∧
      genFunctions (wasiTable (wasiReadAt (after base 1)) (wasiWriteAt (after base 1))
          (wasiExitAt (after base 1)) (stubEntries (wasiFlatAt (after base 1)) 3 stubs)
          (after (stubsEnd (wasiFlatAt (after base 1)) stubs) wasiStartup.length) (wasiFuncs m))
        { trapUnreachable := wasiTrapAt (after base 1), trapBounds := wasiTrapAt (after base 1),
          trapDiv := wasiTrapAt (after base 1), trapStack := wasiTrapAt (after base 1), cap,
          globalTypes := gts, byteStores := true }
        (after (stubsEnd (wasiFlatAt (after base 1)) stubs) wasiStartup.length) (wasiFuncs m) =
        .ok fns ∧
      is = main ++ (pre ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ sts ++ wasiStartup ++ fns) ∧
      (pre ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ sts ++ wasiStartup ++ fns).all
        Instr.keepsX18 = true ∧
      is.all Instr.keepsX17 = true := by
  unfold genWasiProgram at hg
  by_cases himp : m.imports.take 3 = streamImports
  swap
  · simp [himp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [himp, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hg
  cases hst : (m.imports.drop 3).mapM flatStubFor with
  | error err => simp [hst] at hg
  | ok stubs =>
  simp only [hst] at hg
  obtain ⟨hdrop, hmem⟩ := mapM_flatStubFor hst
  have himp' : m.imports = streamImports ++ stubs.map (·.decl) := by
    rw [← hdrop, ← himp, List.take_append_drop]
  by_cases hroom : 4294967296 ≤ room.toNat
  · simp [hroom, throw, throwThe, MonadExceptOf.throw] at hg
  simp only [hroom, ↓reduceIte] at hg
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
    cases hmn : wasiMain (after base 1) (stubsEnd (wasiFlatAt (after base 1)) stubs) e room cap
      with
    | error err => simp [hmn] at hg
    | ok main =>
    simp only [hmn] at hg
    cases hpre : wasiPrefix (wasiPrefixAt (after base 1)) with
    | error err => simp [hpre] at hg
    | ok pre =>
    simp only [hpre] at hg
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
    cases hsts : genStubs svc (wasiTrapAt (after base 1)) (wasiErrnoAt (after base 1))
        (areaSize cap) (wasiFlatAt (after base 1)) stubs with
    | error err => simp [hsts] at hg
    | ok sts =>
    simp only [hsts] at hg
    cases hfn : genFunctions (wasiTable (wasiReadAt (after base 1)) (wasiWriteAt (after base 1))
          (wasiExitAt (after base 1)) (stubEntries (wasiFlatAt (after base 1)) 3 stubs)
          (after (stubsEnd (wasiFlatAt (after base 1)) stubs) wasiStartup.length) (wasiFuncs m))
        { trapUnreachable := wasiTrapAt (after base 1), trapBounds := wasiTrapAt (after base 1),
          trapDiv := wasiTrapAt (after base 1), trapStack := wasiTrapAt (after base 1), cap,
          globalTypes := gts, byteStores := true }
        (after (stubsEnd (wasiFlatAt (after base 1)) stubs) wasiStartup.length)
        (wasiFuncs m) with
    | error err => simp [hfn] at hg
    | ok fns =>
    simp only [hfn] at hg
    split at hg
    · rename_i hall18
      split at hg
      · rename_i hall
        obtain rfl := Except.ok.inj hg
        exact ⟨stubs, gts, e, main, pre, rd, wr, ex, tr, sts, fns, himp', hmem,
          Nat.lt_of_not_le hroom, rfl, rfl, hgl, hen, hmn, rfl, rfl, rfl, rfl, rfl, hsts, hfn, rfl,
          hall18, hall⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at hg
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

theorem sigOf_wasiTable (rd wr ex : UInt64)
    (flat : List (Nat × UInt64 × List ValueType × List ValueType)) (first : UInt64)
    (fs : List (Nat × Function)) :
    sigOf (wasiTable rd wr ex flat first fs) = wasiSig flat fs := by
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 =>
      simp only [sigOf, wasiTable, wasiSig]
      split
      · rfl
      · simp only [entryIn, Option.map_map]
        exact find_entriesFrom _ _ _ _

/-- The functions of the table of `genWasiProgram` simulate at every fuel over the machine `M`:
the three stream imports and the flat imports, whose entries `flat` holds, by their stubs, and the
module's functions by their generated code. -/
theorem wasi_calls_ok {P : Platform} {code : UInt64 → Option UInt32} {α : Type}
    (M : Machine P code α) {m : Module} {rd wr ex first : UInt64}
    {flat : List (Nat × UInt64 × List ValueType × List ValueType)} {S : Shared}
    {need : Nat → Nat} (himp : m.imports.take 3 = streamImports) (h64 : m.memIs64 = false)
    (hU : S.byteStores = true → P.normal P.uart = false) {hr hw hx : HostFn α}
    (henv : M.env.funcs.take 3 = [hr, hw, hx])
    (hsr : M.StubSim S (need 0) [.i32, .i32, .i32, .i32] [.i32] hr rd)
    (hsw : M.StubSim S (need 1) [.i32, .i32, .i32, .i32] [.i32] hw wr)
    (hsx : M.StubSim S (need 2) [.i32] [] hx ex)
    (hflat : ∀ c ∈ flat, ∃ imp hf, m.imports[c.1]? = some imp ∧ M.env.funcs[c.1]? = some hf ∧
      c.2.2 = (imp.params, imp.results) ∧ M.StubSim S (need c.1) imp.params imp.results hf c.2.1)
    {fns : List Instr}
    (hfg : genFunctions (wasiTable rd wr ex flat first (wasiFuncs m)) S first (wasiFuncs m) =
      .ok fns)
    (hcode : CodeAt code first fns)
    (hneed : ∀ k f, m.imports.length ≤ k → m.funcs[k - m.imports.length]? = some f →
      NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) :
    ∀ F, M.CallsOk F m (wasiTable rd wr ex flat first (wasiFuncs m)) S need := by
  have hi : ∀ i < 3, m.imports[i]? = streamImports[i]? := fun i hi => by
    rw [← himp, List.getElem?_take, if_pos hi]
  have he : ∀ i < 3, M.env.funcs[i]? = [hr, hw, hx][i]? := fun i hi => by
    rw [← henv, List.getElem?_take, if_pos hi]
  refine Machine.calls_ok M h64 hU (fun k c hk => ?_) hneed
  match k, hk with
  | 0, hk =>
      obtain rfl := Option.some.inj hk.symm
      exact .inl ⟨_, hr, by rw [hi 0 (by decide)]; rfl, by rw [he 0 (by decide)]; rfl, rfl, hsr⟩
  | 1, hk =>
      obtain rfl := Option.some.inj hk.symm
      exact .inl ⟨_, hw, by rw [hi 1 (by decide)]; rfl, by rw [he 1 (by decide)]; rfl, rfl, hsw⟩
  | 2, hk =>
      obtain rfl := Option.some.inj hk.symm
      exact .inl ⟨_, hx, by rw [hi 2 (by decide)]; rfl, by rw [he 2 (by decide)]; rfl, rfl, hsx⟩
  | j + 3, hk =>
      simp only [wasiTable] at hk
      split at hk
      · rename_i e hfe
        obtain rfl := Option.some.inj hk
        have hj : e.1 = j + 3 := by simpa using List.find?_some hfe
        obtain ⟨imp, hf, himp', hhf, hc, hstub⟩ := hflat e (List.mem_of_find?_eq_some hfe)
        rw [hj] at himp' hhf hstub
        exact .inl ⟨imp, hf, himp', hhf, hc, hstub⟩
      · obtain ⟨f, fis, hmem, hpr, hgen, hcd⟩ :=
          gen_functions code (sigOf_wasiTable rd wr ex flat first (wasiFuncs m)) hfg hcode _
            (entryIn_mem hk)
        obtain ⟨hle, hf⟩ := mem_wasiFuncs hmem
        exact .inr ⟨f, fis, hle, hf, hpr, hgen, hcd⟩

/-! ## `main` -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The run of `wasiMain` from its entry to the entry of the startup routine at `st`: X30 saved in
`main`'s frame of 16 bytes, the stack's limit in X18 `room` bytes below it, X2 stored at the
scratch's first word, `X17 + areaSize cap`, and `BL` to the startup routine with the return
address at `after A 15`. -/
theorem run_wasiFront {A st e room : UInt64} {cap : Nat} {is : List Instr}
    (hg : wasiMain A st e room cap = .ok is) (hcode : CodeAt code A is) {ms : State}
    (hpc : ms.pc = A) (hal : ms.sp % 16 = 0)
    (hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true)
    (hscr : ∀ k < 8, P.normal (ms.x 17 + UInt64.ofNat (areaSize cap) + UInt64.ofNat k) = true) :
    ∃ t, Reach P code ms t ∧ t.pc = st ∧ t.x 30 = after A 15 ∧ t.sp = ms.sp - 16 ∧
      t.x 18 = ms.sp - 16 - room ∧ t.x 17 = ms.x 17 ∧ t.io = ms.io ∧
      t.mem = store64 (store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30))
        (ms.x 17 + UInt64.ofNat (areaSize cap)) (ms.x 2) := by
  unfold wasiMain at hg
  cases hb1 : bField (after A 14) st with
  | error err => simp [hb1, bind, Except.bind] at hg
  | ok g1 =>
  cases hb2 : bField (after A 15) e with
  | error err => simp [hb1, hb2, bind, Except.bind] at hg
  | ok g2 =>
  simp only [hb1, hb2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  have s1 := CodeAt.split code (l1 := [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0])
    (l2 := movImm 16 room ++ [.subReg 18 18 16] ++ movImm 16 (UInt64.ofNat (areaSize cap)) ++
      [.addReg 16 17 16, .str 2 16 0, .bl g1, .bl g2, .movz 0 0 0, .ldr 30 31 0,
        .addImm 31 31 16, .ret 30]) (n := 3)
    (by simpa only [List.append_assoc] using hcode) rfl
  have s2 := CodeAt.split code (l1 := movImm 16 room)
    (l2 := [.subReg 18 18 16] ++ movImm 16 (UInt64.ofNat (areaSize cap)) ++
      [.addReg 16 17 16, .str 2 16 0, .bl g1, .bl g2, .movz 0 0 0, .ldr 30 31 0,
        .addImm 31 31 16, .ret 30]) (by simpa only [List.append_assoc] using s1.2) (n := 4) rfl
  have s3 := CodeAt.split code (l1 := [.subReg 18 18 16])
    (l2 := movImm 16 (UInt64.ofNat (areaSize cap)) ++
      [.addReg 16 17 16, .str 2 16 0, .bl g1, .bl g2, .movz 0 0 0, .ldr 30 31 0,
        .addImm 31 31 16, .ret 30]) (by simpa only [List.append_assoc] using s2.2) (n := 1) rfl
  have s4 := CodeAt.split code (l1 := movImm 16 (UInt64.ofNat (areaSize cap)))
    (l2 := [.addReg 16 17 16, .str 2 16 0, .bl g1, .bl g2, .movz 0 0 0, .ldr 30 31 0,
        .addImm 31 31 16, .ret 30]) s3.2 (n := 4) rfl
  have c0 := (CodeAt.cons.mp s1.1).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).1
  have c2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).2).1
  rw [after_after] at c2
  have c7 := (CodeAt.cons.mp s3.1).1
  simp only [after_after] at c7
  simp only [after_after] at s4
  have c12 := s4.2 0 (by simp)
  have c13 := s4.2 1 (by simp)
  have c14 := s4.2 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c12 c13 c14
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
  have hx17 : t2a.x 17 = ms.x 17 := by
    rw [State.x_withPc, State.x_setX_ne (by decide)]
    rfl
  have hx2 : t2a.x 2 = ms.x 2 := by
    rw [State.x_withPc, State.x_setX_ne (by decide)]
    rfl
  obtain ⟨t3a, r3a, p3a, hx16, hk3a, sp3a, mem3a, out3a⟩ :=
    run_movImm P code (d := 16) (v := room) (by decide) s2.1 p2a
  obtain ⟨t3b, r3b, p3b, x3b, k3b, sp3b, m3b, io3b⟩ := step_subReg P code (s := t3a) (d := 18)
    (n := 18) (m := 16) (by decide) (by rw [p3a, after_after]; exact c7)
  have q3b : t3b.pc = after A 8 := by rw [p3b, p3a, after_after, ← after_succ]
  obtain ⟨t4a, r4a, p4a, hx16', hk4a, sp4a, mem4a, out4a⟩ :=
    run_movImm P code (d := 16) (v := UInt64.ofNat (areaSize cap)) (by decide)
      s4.1 q3b
  obtain ⟨t4b, r4b, p4b, x4b, k4b, sp4b, m4b, io4b⟩ := step_addReg P code (s := t4a) (d := 16)
    (n := 17) (m := 16) (by decide) (by rw [p4a, after_after]; exact c12)
  have q4b : t4b.pc = after A 13 := by rw [p4b, p4a, after_after, ← after_succ]
  have x16b : t4b.x 16 = ms.x 17 + UInt64.ofNat (areaSize cap) := by
    rw [x4b, hk4a 17 (by decide), hx16', k3b 17 (by decide), hk3a 17 (by decide), hx17]
  have x2b : t4b.x 2 = ms.x 2 := by
    rw [k4b 2 (by decide), hk4a 2 (by decide), k3b 2 (by decide), hk3a 2 (by decide), hx2]
  let t5 : State := { t4b with
    mem := store64 t4b.mem (t4b.x 16 + UInt64.ofNat (8 * 0)) (t4b.x 2), pc := t4b.pc + 4 }
  have e5 : LeanExe.A64.exec P (.str 2 16 0) t4b = some t5 :=
    exec_str_base P (i := 0) (by decide) (by decide) fun k hk => by
      rw [x16b]
      simpa using hscr k hk
  have p5 : t5.pc = after A 14 := by show t4b.pc + 4 = _; rw [q4b, ← after_succ]
  obtain ⟨t6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_bl P code (s := t5) (target := st)
    (by rw [p5]; exact c14) (by rw [p5]; exact bField_target hb1)
  refine ⟨t6, r2.trans (r3a.trans (r3b.trans (r4a.trans (r4b.trans
    (reach_exec P code (by rw [q4b]; exact c13) e5 r6))))), p6,
    by rw [x6, p5, ← after_succ], ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp6]
    show t4b.sp = _
    rw [sp4b, sp4a, sp3b, sp3a]
    show (t2.setX 18 (t2.sp + UInt64.ofNat 0)).sp = _
    rw [State.setX_sp]
  · rw [k6 18 (by decide)]
    show t4b.x 18 = _
    rw [k4b 18 (by decide), hk4a 18 (by decide), x3b, hx16, hk3a 18 (by decide), h18a]
  · rw [k6 17 (by decide)]
    show t4b.x 17 = _
    rw [k4b 17 (by decide), hk4a 17 (by decide), k3b 17 (by decide), hk3a 17 (by decide), hx17]
  · rw [io6]
    show t4b.io = _
    rw [io4b, out4a, io3b, out3a]
    rfl
  · rw [m6]
    show store64 t4b.mem (t4b.x 16 + UInt64.ofNat (8 * 0)) (t4b.x 2) = _
    rw [Nat.mul_zero, add_ofNat_zero, x16b, x2b, m4b, mem4a, m3b, mem3a]
    rfl

/-- The run of `wasiMain` from the return of the startup routine to the entry of `_start`, with
the return address at `after A 16`. -/
theorem run_wasiStart {A st e room : UInt64} {cap : Nat} {is : List Instr}
    (hg : wasiMain A st e room cap = .ok is) (hcode : CodeAt code A is) {s : State}
    (hpc : s.pc = after A 15) :
    ∃ t, Reach P code s t ∧ t.pc = e ∧ t.x 30 = after A 16 ∧
      (∀ q : Fin 32, q ≠ 30 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  unfold wasiMain at hg
  cases hb1 : bField (after A 14) st with
  | error err => simp [hb1, bind, Except.bind] at hg
  | ok g1 =>
  cases hb2 : bField (after A 15) e with
  | error err => simp [hb1, hb2, bind, Except.bind] at hg
  | ok g2 =>
  simp only [hb1, hb2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  have c15 := hcode 15 (by simp [movImm])
  simp [movImm] at c15
  obtain ⟨t, r, p, x30, k, sp, m, io⟩ := step_bl P code (s := s) (target := e)
    (by rw [hpc]; exact c15) (by rw [hpc]; exact bField_target hb2)
  exact ⟨t, r, p, by rw [x30, hpc, ← after_succ], k, sp, m, io⟩

end LeanExe.A64
