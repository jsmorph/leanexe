import LeanExe.Native.Proof.Ctl

/-!
The program with requests (`reqMain` of `LeanExe/Native/Bare.lean`), which runs a step function
forever and performs, in each window, the one register access that the step requests: for every
sequence `σ` of the values that its volatile loads read, `req_program` states `LoopReacts` with
the initial trace `E0` and the window traces `reqTrace`.  `ReqState` is the state before a
window: the step's state, the last value read, and the number of reads so far.  The step's two
results are the new state and the request word `q`: bit 63 set requests a write of the low 32
bits of `q` to register `reqReg q`, and bit 63 clear a read of that register, whose value is the
`k`-th read's `σ k`.  `ReqRuns` is what the step must do from every store that the loop's
invariant allows, which `NativeA` gives for a step that cannot trap.
-/

namespace LeanExe.Native

open LClight Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The register of the request `q`, `(q >> 32) & 255`. -/
def reqReg (q : UInt64) : UInt64 := (q >>> UInt64.ofNat 32) &&& UInt64.ofNat 255

/-- Whether the request `q` is a write, bit 63. -/
def reqWrite (q : UInt64) : Bool := q >>> UInt64.ofNat 63 != UInt64.ofNat 0

/-- The offset of the register of the request `q` in `lx_reg`. -/
def regOfs (q : UInt64) : ptrofs := UInt64.ofNat (4 * (reqReg q).toNat)

/-- The state before a window: the step's state, the last value read, and the number of reads
so far. -/
structure ReqState where
  state : UInt64
  last : UInt64
  reads : Nat

/-- The state after a window. -/
def reqNext (tick : UInt64 → UInt64 → UInt64 × UInt64) (σ : Nat → int) (r : ReqState) :
    ReqState :=
  if reqWrite (tick r.state r.last).2 then ⟨(tick r.state r.last).1, 0, r.reads⟩
  else ⟨(tick r.state r.last).1, UInt64.ofNat (σ r.reads).toNat, r.reads + 1⟩

/-- The state before window `n`. -/
def reqRun (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64) (σ : Nat → int) :
    Nat → ReqState
  | 0 => ⟨s0, 0, 0⟩
  | n + 1 => reqNext tick σ (reqRun tick s0 σ n)

/-- The event of the window from the state `r`. -/
def reqEvent (tick : UInt64 → UInt64 → UInt64 × UInt64) (σ : Nat → int) (r : ReqState) :
    event :=
  if reqWrite (tick r.state r.last).2 then
    .Event_vstore .Mint32 regId (regOfs (tick r.state r.last).2)
      (.EVint (UInt32.ofNat ((tick r.state r.last).2.toNat % 2 ^ 32)))
  else .Event_vload .Mint32 regId (regOfs (tick r.state r.last).2) (.EVint (σ r.reads))

/-- The trace of window `n`: its one register access. -/
def reqTrace (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64) (σ : Nat → int)
    (n : Nat) : trace :=
  [reqEvent tick σ (reqRun tick s0 σ n)]

theorem reqTrace_ne (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64) (σ : Nat → int)
    (n : Nat) : reqTrace tick s0 σ n ≠ [] := by
  simp [reqTrace]

/-- The step `fd` computes `tick` from every store that the loop's invariant allows, leaving
its two results in the result globals 0 and 1. -/
def ReqRuns (A : Archi) (X : ExtSem) (cap : Nat) (m : Wasm.Module) (T : Translation)
    (fd : function) (tick : UInt64 → UInt64 → UInt64 × UInt64) : Prop :=
  ∀ E : Env, EnvOk E → E.globals.length = m.globals.length → E.cap = cap → T.nres ≤ E.nres →
    (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ bk, Genv.find_symbol E.ge (funId k) = some bk ∧
        Genv.find_funct_ptr E.ge bk = some (.Internal fd)) →
    ∀ (st : Store Unit) (heap : Heap), heap.At st →
      st.memoryCaps = (nativeStore m cap).memoryCaps →
    ∀ (s v : UInt64) (m1 : mem), StoreRel A E st m1 → StatusRel A E m1 0 →
      ∃ (t : trace) (m' : mem) (vres : val) (st' : Store Unit) (heap' : Heap),
        eval_funcall A X E.ge m1 (.Internal fd) [.Vlong s, .Vlong v] t m' vres ∧
        StoreRel A E st' m' ∧ StatusRel A E m' 0 ∧ heap'.At st' ∧
        st'.memoryCaps = (nativeStore m cap).memoryCaps ∧
        Mem.load A .Mint64 m' (E.res 0 .i64) 0 = some (.Vlong (tick s v).1) ∧
        Mem.load A .Mint64 m' (E.res 1 .i64) 0 = some (.Vlong (tick s v).2)

/-- `ReqRuns` of a step that cannot trap, from its theorem `NativeA` over the pairs of state and
last value, with a pair of words as its result. -/
theorem reqRuns_of_nativeA {A : Archi} {X : ExtSem} {cap : Nat} {m : Wasm.Module}
    {T : Translation} {fd : function} {tick : UInt64 → UInt64 → UInt64 × UInt64}
    {Pre : UInt64 × UInt64 → Heap → Store Unit → Prop}
    {Post : UInt64 × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (hnat : NativeA A X cap m T [.i64, .i64] [.i64, .i64] fd false
      (fun x : UInt64 × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hcap : cap ≤ 65535) :
    ReqRuns A X cap m T fd tick := by
  intro E hE hG hcap' hnres hF st heap hat hcaps s v m1 hst hs
  have hcapS : st.memoryCap m 0 ≤ 65535 := by
    simp [Store.memoryCap, hcaps, nativeStore, hcap]
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap' hnres hF st heap
    [.i64 s, .i64 v] (s, v) hat (hPre _ _ _) rfl Separate.nil hcapS (argsTyped_i64 [s, v]) m1
    hst hs
  rcases hres with ⟨hs', vs, heap', hr, hat', hown, hcaps', -, -⟩ | ⟨habs, -⟩
  · obtain ⟨ws, hws, -, -, -, hin⟩ := hr
    have hv : vs.reverse = [Wasm.Value.i64 (tick s v).1, .i64 (tick s v).2] := hown
    have hvs : vs = [.i64 (tick s v).2, .i64 (tick s v).1] := by
      simpa using congrArg List.reverse hv
    have hws' : ws = vs := by simpa using hws.symm
    subst hws'
    obtain ⟨v0, hv0, -, hl0⟩ := hin 0 (by decide)
    obtain ⟨v1, hv1, -, hl1⟩ := hin 1 (by decide)
    rw [hvs] at hv0 hv1
    simp at hv0 hv1
    subst hv0 hv1
    exact ⟨t, m', vres, final, heap', hcall, hst', hs', hat', hcaps'.trans hcaps, hl0, hl1⟩
  · cases habs

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem reqReg_lt (q : UInt64) : (reqReg q).toNat < 256 := by
  simp only [reqReg, UInt64.toNat_and]
  have := Nat.and_le_right (n := (q >>> UInt64.ofNat 32).toNat) (m := (UInt64.ofNat 255).toNat)
  have h255 : (UInt64.ofNat 255).toNat = 255 := rfl
  omega

theorem sem_add_reg (b : block) (k : UInt64) (m : mem) (hk : 4 * k.toNat < 2 ^ 32) :
    sem_binary_operation A .Oadd (.Vptr b Ptrofs.zero) regArray (.Vlong k) tulong m =
      some (.Vptr b (UInt64.ofNat (4 * k.toNat))) := by
  show some (val.Vptr b
    (Ptrofs.add A Ptrofs.zero (Ptrofs.mul A (Ptrofs.repr A 4) (Ptrofs.of_int64 A k)))) = _
  congr 2
  apply UInt64.toNat_inj.mp
  rw [toNat_ofNat64 (by omega)]
  rcases A with ⟨_ | _, _, _, _, _⟩
  all_goals
    simp only [Ptrofs.add, Ptrofs.mul, Ptrofs.repr, Ptrofs.of_int64, Ptrofs.unsigned, Ptrofs.zero,
      Int64.unsigned, Ptrofs.modulus, Ptrofs.wordsize]
    simp
    omega

theorem eval_reqIndex {le : temp_env} {m : mem} {q : UInt64}
    (hq : le[byteTemp]? = some (.Vlong q)) :
    eval_expr A ge empty_env le m reqIndex (.Vlong (reqReg q)) :=
  .eval_Ebinop _ _ _ _ _ _ _
    (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hq) (.eval_Econst_long _ _)
      (sem_shr_const A m q 32 (by omega)))
    (.eval_Econst_long _ _) (sem_and_ll A m _ _)

/-- `&lx_reg[(l6 >> 32) & 255]`. -/
theorem eval_regAddr {le : temp_env} {m : mem} {br : block} {q : UInt64}
    (hs : Genv.find_symbol ge regId = some br) (hq : le[byteTemp]? = some (.Vlong q)) :
    eval_expr A ge empty_env le m (.Eaddrof (regAt reqIndex) regPtr) (.Vptr br (regOfs q)) := by
  have harr : eval_expr A ge empty_env le m (.Evar regId regArray) (.Vptr br Ptrofs.zero) :=
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hs) (.deref_loc_reference rfl)
  have hk := reqReg_lt q
  exact .eval_Eaddrof _ _ _ _ (.eval_Ederef _ _ _ _
    (.eval_Ebinop _ _ _ _ _ _ _ harr (eval_reqIndex hq) (sem_add_reg br _ m (by omega))))

/-- The read of the request's register: one volatile load, which reads `v`. -/
theorem exec_regLoad {le : temp_env} {m : mem} {br : block}
    (hs : Genv.find_symbol ge regId = some br) (hv : Genv.block_is_volatile ge br = true)
    {q : UInt64} (hq : le[byteTemp]? = some (.Vlong q)) (v : int) :
    exec_stmt A X ge empty_env le m (regLoad reqIndex)
      [.Event_vload .Mint32 regId (regOfs q) (.EVint v)]
      ((le.insert lenLoadTemp (Val.load_result A .Mint32 (.Vint v))).insert nTemp
        (.Vlong (UInt64.ofNat v.toNat))) m .Out_normal :=
  exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Sbuiltin _ _ _ (some lenLoadTemp) (.EF_vload .Mint32) _ _ [.Vptr br (regOfs q)] _ m _
      (.eval_Econs _ _ _ _ _ _ _ (eval_regAddr hs hq) rfl .eval_Enil)
      (.volatile_load_sem_intro br (regOfs q) m _ _
        (.volatile_load_vol .Mint32 m br (regOfs q) regId (.EVint v) (.Vint v) hv hs
          (.ev_match_int v))))
    (.exec_Sset _ _ _ _ _ _
      (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)) (cast_uint_long A m v))))
    (by simp [E0])

/-- The write of the request's low 32 bits to its register: one volatile store. -/
theorem exec_regStore {le : temp_env} {m : mem} {br : block}
    (hs : Genv.find_symbol ge regId = some br) (hv : Genv.block_is_volatile ge br = true)
    {q : UInt64} (hq : le[byteTemp]? = some (.Vlong q)) :
    exec_stmt A X ge empty_env le m (regStore reqIndex (.Etempvar byteTemp tulong))
      [.Event_vstore .Mint32 regId (regOfs q) (.EVint (UInt32.ofNat (q.toNat % 2 ^ 32)))] le m
      .Out_normal :=
  .exec_Sbuiltin _ _ _ none (.EF_vstore .Mint32) _ _
    [.Vptr br (regOfs q), .Vint (UInt32.ofNat (q.toNat % 2 ^ 32))] _ m .Vundef
    (.eval_Econs _ _ _ _ _ _ _ (eval_regAddr hs hq) rfl
      (.eval_Econs _ _ _ _ _ _ _
        (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hq) (cast_long_uint A m q))
        (cast_i32 A m _) .eval_Enil))
    (.volatile_store_sem_intro br (regOfs q) m (.Vint _) _ m
      (.volatile_store_vol .Mint32 m br (regOfs q) regId (.EVint _) (.Vint _) hv hs
        (.ev_match_int _)))

theorem bool_reqWrite (m : mem) (q : UInt64) :
    bool_val A (.Vint (if q >>> UInt64.ofNat 63 ≠ UInt64.ofNat 0 then 1 else 0)) tint m =
      some (reqWrite q) := by
  rw [bool_int A m]
  congr 1
  unfold reqWrite
  generalize q >>> UInt64.ofNat 63 = x
  by_cases h : x = UInt64.ofNat 0
  · subst h
    decide
  · rw [if_pos h, show (x != UInt64.ofNat 0) = true from bne_iff_ne.mpr h]
    decide

/-- The access of the request in `l6`. -/
theorem exec_reqAccess {le : temp_env} {m : mem} {br : block}
    (hs : Genv.find_symbol ge regId = some br) (hv : Genv.block_is_volatile ge br = true)
    {q : UInt64} (hq : le[byteTemp]? = some (.Vlong q)) (v : int) :
    ∃ le', exec_stmt A X ge empty_env le m reqAccess
        [if reqWrite q then
          .Event_vstore .Mint32 regId (regOfs q) (.EVint (UInt32.ofNat (q.toNat % 2 ^ 32)))
        else .Event_vload .Mint32 regId (regOfs q) (.EVint v)] le' m .Out_normal ∧
      le'[nTemp]? = some (.Vlong (if reqWrite q then 0 else UInt64.ofNat v.toNat)) ∧
      le'[resTemp]? = le[resTemp]? := by
  have hcond : eval_expr A ge empty_env le m
      (.Ebinop .One (.Ebinop .Oshr (.Etempvar byteTemp tulong) (clong 63) tulong) (clong 0) tint)
      (.Vint (if q >>> UInt64.ofNat 63 ≠ UInt64.ofNat 0 then 1 else 0)) :=
    .eval_Ebinop _ _ _ _ _ _ _
      (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hq) (.eval_Econst_long _ _)
        (sem_shr_const A m q 63 (by omega)))
      (.eval_Econst_long _ _) (sem_ne_ll A m _ _)
  cases hw : reqWrite q
  · refine ⟨_, .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond
      (by show bool_val A _ tint m = _; rw [bool_reqWrite, hw]) (exec_regLoad hs hv hq v), te_insert_same _ _ _, ?_⟩
    rw [te_insert_ne _ (by decide), te_insert_ne _ (by decide)]
  · refine ⟨_, .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond
      (by show bool_val A _ tint m = _; rw [bool_reqWrite, hw])
      (exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (exec_regStore hs hv hq)
        (.exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _))) (by simp [E0])),
      te_insert_same _ _ _, ?_⟩
    rw [te_insert_ne _ (by decide)]

/-- `lxf_k(l0, l3);`, for a step whose two results go to the result globals. -/
theorem exec_stepVoid (k : Nat) {fd : function} {bk : block}
    (hsk : Genv.find_symbol ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (htyk : type_of_function fd = .Tfunction [tulong, tulong] .Tvoid cc_default)
    {le : temp_env} {m1 m' : mem} {vres : val} {s x : UInt64}
    (hs : le[resTemp]? = some (.Vlong s)) (hx : le[nTemp]? = some (.Vlong x))
    (hcall : eval_funcall A X ge m1 (.Internal fd) [.Vlong s, .Vlong x] E0 m' vres) :
    exec_stmt A X ge empty_env le m1
      (voidCall k [tulong, tulong] [.Etempvar resTemp tulong, .Etempvar nTemp tulong]) E0 le m'
      .Out_normal :=
  .exec_Scall _ _ _ none _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _ m' vres rfl
    (.eval_Elvalue _ _ _ _ _ (eval_lvalue_global hsk) (.deref_loc_reference rfl))
    (.eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hs) (cast_ll A m1 s)
      (.eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx) (cast_ll A m1 x) .eval_Enil))
    (by simp [Genv.find_funct, hfk]) htyk hcall

end

/-- The program with requests runs forever for every sequence `σ` of the values that its volatile
loads read: `main` calls `lx_init` with no event, and window `n` performs the access of
`reqTrace tick s0 σ n`, given the run of the step that `ReqRuns` states.  `heap` is the heap of
the store in which the translation starts, and the translation keeps at least two result
globals. -/
theorem req_program {m : Wasm.Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) {pre : List (ident × globdef (fundef function) type)}
    (hpre : PrefixOk pre) {k : Nat} {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (hty : type_of_function fd = .Tfunction [tulong, tulong] .Tvoid cc_default)
    (h2 : 2 ≤ T.nres) (A : Archi) (X : ExtSem) {heap : Heap}
    (hheap : heap.At (nativeStore m cap)) {tick : UInt64 → UInt64 → UInt64 × UInt64}
    (hruns : ReqRuns A X cap m T fd tick) (s0 : UInt64) (σ : Nat → int) :
    LoopReacts A X (reqProgram pre T (reqMain k s0)) E0 (reqTrace tick s0 σ) := by
  have hw := wholeOk_req h hpre.sqrt hpre.funs hpre.nodup hpre.ids (reqMain k s0)
  obtain ⟨decl, m0, m1, -, hinit, hmemi, hcalli, hst1, hs1, hE, hG, hcap, hnres, hF⟩ :=
    start_whole h hw A X
  set E := envWhole pre (reqTail (reqMain k s0)) T m.globals.length cap with hEdef
  have hidp : ∀ x : Nat, x ∈ (reqTail (reqMain k s0)).map (·.1) →
      x = 0 ∨ x = 4 ∨ x = 28 ∨ x = 32 := by
    intro x hx
    simp only [reqTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx
    · have : x = 0 := hx; omega
    · have : x = 4 := hx; omega
  have hq := genvQuiet_whole h hw hpre.ids hidp
  obtain ⟨bi, hsi, hdi⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (reqTail (reqMain k s0)) T) hw.nodup hmemi
  obtain ⟨br, hsr, hdr⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (reqTail (reqMain k s0)) T) hw.nodup
    (d := .Gvar regVar) (id := regId) (by simp [wholeDefs, reqTail])
  obtain ⟨bm, hsm, hdm⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (reqTail (reqMain k s0)) T) hw.nodup
    (d := .Gfun (.Internal (reqMain k s0))) (id := mainId) (by simp [wholeDefs, reqTail])
  have hvr : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (reqTail (reqMain k s0)) T)) br = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdr, regVar]
  obtain ⟨bk, hsk, hfk⟩ := hF k fd hfd
  have hr0 := hE.res 0 (by omega) .i64 rfl
  have hr1 := hE.res 1 (by omega) .i64 rfl
  let le0 := create_undef_temps reqTemps
  have hentry : function_entry2 (reqMain k s0) [] m0 empty_env le0 m0 :=
    .intro le0 rfl List.nodup_nil (by simp [var_names, reqMain]) rfl
  have hc1 := exec_initCall (X := X) (le := le0) hsi (Genv.find_funct_ptr_of_def hdi) rfl hcalli
  have hset0 : exec_stmt A X E.ge empty_env le0 m1 (.Sset resTemp (.Econst_long s0 tulong)) E0
      (le0.insert resTemp (.Vlong s0)) m1 .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  have hset1 : exec_stmt A X E.ge empty_env (le0.insert resTemp (.Vlong s0)) m1
      (.Sset nTemp (clong 0)) E0
      ((le0.insert resTemp (.Vlong s0)).insert nTemp (.Vlong (UInt64.ofNat 0))) m1 .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  refine ⟨reqTrace_ne tick s0 σ, bm, reqMain k s0, m0, m0, empty_env, le0,
    .Ssequence initCall (.Ssequence (.Sset resTemp (.Econst_long s0 tulong))
      (.Ssequence (.Sset nTemp (clong 0)) .Sskip)),
    .Ssequence .Sskip (reqWindow k), .Sskip,
    fun n le mm => ∃ (st : Store Unit) (hp : Heap), StoreRel A E st mm ∧ StatusRel A E mm 0 ∧
      hp.At st ∧ st.memoryCaps = (nativeStore m cap).memoryCaps ∧
      le[resTemp]? = some (.Vlong (reqRun tick s0 σ n).state) ∧
      le[nTemp]? = some (.Vlong (reqRun tick s0 σ n).last),
    hinit, hsm, Genv.find_funct_ptr_of_def hdm, rfl,
    .seq_after _ (.seq_before _ (.seq_before _ (.seq_before _ (.loop _ _)))), hentry,
    ⟨_, m1,
      exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hc1
        (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hset0
          (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hset1 (.exec_Sskip _ _ _)))) (by simp [E0]),
      nativeStore m cap, heap, hst1, hs1, hheap, rfl,
      by rw [te_insert_ne _ (by decide), te_insert_same]; rfl, te_insert_same _ _ _⟩, ?_⟩
  rintro n le mm ⟨st, hp, hstr, hstat, hat, hcaps, hrs, hrl⟩
  obtain ⟨t, m', vres, st', hp', hcall, hst', hs', hat', hcaps', hl0, hl1⟩ := hruns E hE hG hcap
    hnres hF st hp hat hcaps (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last mm hstr hstat
  have ht : t = E0 := funcall_quiet hq hcall (translation_fun_quiet h hfd (by
    show (4 * k + 3) % 4 = 3; omega))
  subst ht
  have hx1 := exec_stepVoid (X := X) k hsk hfk hty hrs hrl hcall
  have hset2 : exec_stmt A X E.ge empty_env le m' (.Sset resTemp (.Evar (resId 0 .i64) tulong)) E0
      (le.insert resTemp (.Vlong (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).1))
      m' .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (eval_global_long hr0 hl0)
  have hset3 : exec_stmt A X E.ge empty_env
      (le.insert resTemp (.Vlong (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).1))
      m' (.Sset byteTemp (.Evar (resId 1 .i64) tulong)) E0
      ((le.insert resTemp
        (.Vlong (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).1)).insert byteTemp
        (.Vlong (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).2)) m' .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (eval_global_long hr1 hl1)
  obtain ⟨le4, hacc, hn4, hr4⟩ := exec_reqAccess (X := X) (m := m') hsr hvr
    (te_insert_same _ _ _) (σ (reqRun tick s0 σ n).reads)
  have hwin : exec_stmt A X E.ge empty_env le mm (reqWindow k) _ le4 m' .Out_normal :=
    exec_seqList_cons (by simp) hx1 (exec_seqList_cons (by simp) hset2
      (exec_seqList_cons (by simp) hset3 hacc))
  refine ⟨le4, m', exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sskip _ _ _) hwin) (.exec_Sskip _ _ _)) ?_,
    st', hp', hst', hs', hat', hcaps', ?_, ?_⟩
  · simp only [E0, List.nil_append, List.append_nil, reqTrace, reqEvent]
  · rw [hr4, te_insert_ne _ (by decide), te_insert_same]
    cases hw : reqWrite (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).2 <;>
      simp [reqRun, reqNext, hw]
  · rw [hn4]
    cases hw : reqWrite (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).2 <;>
      simp [reqRun, reqNext, hw]

/-! ## The values that the windows read -/

theorem reqTrace_reads (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64)
    (σ : Nat → int) (n : Nat) :
    ReadsFrom σ (reqRun tick s0 σ n).reads (reqTrace tick s0 σ n) := by
  intro tp ev u h
  cases tp with
  | nil =>
      simp only [reqTrace, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      cases hw : reqWrite (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).2 <;>
        simp [reqEvent, hw, countVloads]
  | cons e tp => simp [reqTrace] at h

theorem reqTrace_count (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64)
    (σ : Nat → int) (n : Nat) :
    (reqRun tick s0 σ n).reads + countVloads (reqTrace tick s0 σ n) =
      (reqRun tick s0 σ (n + 1)).reads := by
  simp only [reqTrace, reqEvent, reqRun, reqNext]
  split <;> simp [countVloads, isVload, List.filter_cons]

theorem req_windows_reads (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64)
    (σ : Nat → int) :
    ∀ n, ReadsFrom σ 0 (windows (reqTrace tick s0 σ) n) ∧
      countVloads (windows (reqTrace tick s0 σ) n) = (reqRun tick s0 σ n).reads
  | 0 => ⟨fun tp ev u h => by simp [windows] at h, rfl⟩
  | n + 1 => by
      obtain ⟨hr, hc⟩ := req_windows_reads tick s0 σ n
      refine ⟨hr.append ?_, ?_⟩
      · rw [hc, Nat.zero_add]
        exact reqTrace_reads tick s0 σ n
      · rw [windows, countVloads_append, hc, reqTrace_count]

/-- The initial trace and the first `n` windows read `σ`: the `reads` premise of
`clight2_loop_to_asm` in `rocq/Clight2Asm.v`. -/
theorem req_reads (tick : UInt64 → UInt64 → UInt64 × UInt64) (s0 : UInt64) (σ : Nat → int)
    (n : Nat) : Reads σ (E0 ++ windows (reqTrace tick s0 σ) n) := by
  intro tp ev u h
  have h' := (req_windows_reads tick s0 σ n).1 tp ev u (by simpa [E0] using h)
  cases ev <;> simpa using h'

end LeanExe.Native
