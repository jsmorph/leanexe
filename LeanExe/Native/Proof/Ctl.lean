import LeanExe.Native.Proof.Input
import LeanExe.Native.Proof.Reacts
import LeanExe.Requests.Windows

/-!
The controller's program (`ctlMain` of `LeanExe/Native/Bare.lean`), which runs a step function
forever: for every sequence `σ` of the values that its volatile loads read, `ctl_program` states
`LoopReacts` with the initial trace `E0` and the window traces `ctlTrace`.  Window `n` reads the
word of `σ (8 n)` to `σ (8 n + 7)` from `lx_in[0]` to `lx_in[7]`, calls the step on the state and
the word, and stores the new state's eight bytes to `lx_out`.  The invariant of window `n` holds
a Talos store related to the C memory with `lx_status` 0, a heap for that store, the memory caps
of `nativeStore`, and the state `ctlState ctl s0 σ n` in `l0`.  `CtlRuns` is what the step must
do from every such store, which `NativeA` gives for a step that cannot trap.
-/

namespace LeanExe.Native

open LClight Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime
open LeanExe.Requests (windows)

/-- The input word of window `n`: the bytes that the loads of `σ (8 n)` to `σ (8 n + 7)` read,
the lowest first. -/
def ctlInput (σ : Nat → int) (n : Nat) : UInt64 := inLen fun j => σ (8 * n + j)

/-- The state after `n` windows. -/
def ctlState (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int) : Nat → UInt64
  | 0 => s0
  | n + 1 => ctl (ctlState ctl s0 σ n) (ctlInput σ n)

/-- The trace of window `n`: the eight loads of the input word and the stores of the new state's
eight bytes. -/
def ctlTrace (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int) (n : Nat) :
    trace :=
  inTrace (fun j => σ (8 * n + j)) 0 8 ++ outTrace (encodeWord (ctlState ctl s0 σ (n + 1)))

theorem ctlTrace_ne (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int) (n : Nat) :
    ctlTrace ctl s0 σ n ≠ [] := by
  simp [ctlTrace, inTrace]

/-- The step `fd` computes `ctl` from every store that the controller's invariant allows: from
a store related to the C memory with `lx_status` 0, with a heap and the memory caps of
`nativeStore`, the call on the state and the input word returns `ctl` of them and leaves a store
of the same kind. -/
def CtlRuns (A : Archi) (X : ExtSem) (cap : Nat) (m : Wasm.Module) (T : Translation)
    (fd : function) (ctl : UInt64 → UInt64 → UInt64) : Prop :=
  ∀ E : Env, EnvOk E → E.globals.length = m.globals.length → E.cap = cap → T.nres ≤ E.nres →
    (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ bk, Genv.find_symbol E.ge (funId k) = some bk ∧
        Genv.find_funct_ptr E.ge bk = some (.Internal fd)) →
    ∀ (st : Store Unit) (heap : Heap), heap.At st →
      st.memoryCaps = (nativeStore m cap).memoryCaps →
    ∀ (s x : UInt64) (m1 : mem), StoreRel A E st m1 → StatusRel A E m1 0 →
      ∃ (t : trace) (m' : mem) (st' : Store Unit) (heap' : Heap),
        eval_funcall A X E.ge m1 (.Internal fd) [.Vlong s, .Vlong x] t m' (.Vlong (ctl s x)) ∧
        StoreRel A E st' m' ∧ StatusRel A E m' 0 ∧ heap'.At st' ∧
        st'.memoryCaps = (nativeStore m cap).memoryCaps

/-- `CtlRuns` of a step that cannot trap, from its theorem `NativeA` over the pairs of state and
input. -/
theorem ctlRuns_of_nativeA {A : Archi} {X : ExtSem} {cap : Nat} {m : Wasm.Module}
    {T : Translation} {fd : function} {ctl : UInt64 → UInt64 → UInt64}
    {Pre : UInt64 × UInt64 → Heap → Store Unit → Prop}
    {Post : UInt64 × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (hnat : NativeA A X cap m T [.i64, .i64] [.i64] fd false
      (fun x : UInt64 × UInt64 => ctl x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hcap : cap ≤ 65535) :
    CtlRuns A X cap m T fd ctl := by
  intro E hE hG hcap' hnres hF st heap hat hcaps s x m1 hst hs
  have hcapS : st.memoryCap m 0 ≤ 65535 := by
    simp [Store.memoryCap, hcaps, nativeStore, hcap]
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap' hnres hF st heap
    [.i64 s, .i64 x] (s, x) hat (hPre _ _ _) rfl Separate.nil hcapS (argsTyped_i64 [s, x]) m1
    hst hs
  rcases hres with ⟨hs', vs, heap', hr, hat', hown, hcaps', -, -⟩ | ⟨habs, -⟩
  · obtain ⟨v, hvs, -, rfl⟩ := hr
    have hv : vs.reverse = [Wasm.Value.i64 (ctl s x)] := hown
    have hv' : v = .i64 (ctl s x) := by
      rw [show vs = [v] by simpa using hvs] at hv
      simpa using hv
    subst hv'
    exact ⟨t, m', final, heap', hcall, hst', hs', hat', hcaps'.trans hcaps⟩
  · cases habs

section

variable {A : Archi} {X : ExtSem} {ge : genv}

/-- `l0 = lxf_k(l0, l3);`. -/
theorem exec_stepCall (k : Nat) {fd : function} {bk : block}
    (hsk : Genv.find_symbol ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (htyk : type_of_function fd = .Tfunction [tulong, tulong] tulong cc_default)
    {le : temp_env} {m1 m' : mem} {vres : val} {s x : UInt64}
    (hs : le[resTemp]? = some (.Vlong s)) (hx : le[nTemp]? = some (.Vlong x))
    (hcall : eval_funcall A X ge m1 (.Internal fd) [.Vlong s, .Vlong x] E0 m' vres) :
    exec_stmt A X ge empty_env le m1
      (resultCall inCallTemp k [tulong, tulong] [.Etempvar resTemp tulong, .Etempvar nTemp tulong])
      E0 ((le.insert inCallTemp vres).insert resTemp vres) m' .Out_normal := by
  have hargs : eval_exprlist A ge empty_env le m1
      [.Etempvar resTemp tulong, .Etempvar nTemp tulong] [tulong, tulong] [.Vlong s, .Vlong x] :=
    .eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hs) (cast_ll A m1 s)
      (.eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx) (cast_ll A m1 x) .eval_Enil)
  have hfn : eval_expr A ge empty_env le m1
      (.Evar (funId k) (.Tfunction [tulong, tulong] tulong cc_default)) (.Vptr bk Ptrofs.zero) :=
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hsk) (.deref_loc_reference rfl)
  exact exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Scall _ _ _ (some inCallTemp) _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _
      m' vres rfl hfn hargs (by simp [Genv.find_funct, hfk]) htyk hcall)
    (.exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)))) (by simp [E0])

/-- One window: the loads of the input word from `σ'`, the call of the step, and the stores of
its result. -/
theorem exec_ctlWindow (k : Nat) {fd : function} {bk : block}
    (hsk : Genv.find_symbol ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (htyk : type_of_function fd = .Tfunction [tulong, tulong] tulong cc_default)
    {bn bo : block} (hsn : Genv.find_symbol ge inId = some bn)
    (hvn : Genv.block_is_volatile ge bn = true) (hso : Genv.find_symbol ge outId = some bo)
    (hvo : Genv.block_is_volatile ge bo = true) (σ' : Nat → int) {le : temp_env} {m1 m' : mem}
    {s y : UInt64} (hs : le[resTemp]? = some (.Vlong s))
    (hcall : eval_funcall A X ge m1 (.Internal fd) [.Vlong s, .Vlong (inLen σ')] E0 m'
      (.Vlong y)) :
    ∃ le', exec_stmt A X ge empty_env le m1 (ctlWindow k)
        (inTrace σ' 0 8 ++ outTrace (encodeWord y)) le' m' .Out_normal ∧
      le'[resTemp]? = some (.Vlong y) := by
  let lea := le.insert nTemp (.Vlong (UInt64.ofNat 0))
  let leb := lea.insert jTemp (.Vlong (UInt64.ofNat 0))
  have hsetn : exec_stmt A X ge empty_env le m1 (.Sset nTemp (clong 0)) E0 lea m1 .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  have hsetj : exec_stmt A X ge empty_env lea m1 (.Sset jTemp (clong 0)) E0 leb m1 .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  obtain ⟨le1, hlen, hn1, hother1⟩ := exec_lenLoop (X := X) (m := m1) hsn hvn σ' 8 0 leb
    (by omega)
    (by simp only [leb, lea]
        rw [te_insert_ne _ (Ne.symm nTemp_ne_jTemp), te_insert_same]
        rfl)
    (te_insert_same _ _ _)
  have hs1 : le1[resTemp]? = some (.Vlong s) := by
    rw [hother1 resTemp (by decide) (by decide) (by decide) (by decide)]
    simp only [leb, lea]
    rw [te_insert_ne _ (by decide), te_insert_ne _ (by decide)]
    exact hs
  have hcallX := exec_stepCall k hsk hfk htyk hs1 hn1 hcall
  have hr2 : ((le1.insert inCallTemp (.Vlong y)).insert resTemp (.Vlong y))[resTemp]? =
      some (.Vlong y) := te_insert_same _ _ _
  have hout := exec_wordOuts (A := A) (X := X) (m := m') hso hvo hr2 (List.range 8) (by simp)
    (fun j hj => List.mem_range.mp hj)
  refine ⟨_, exec_trace (exec_seqList_cons (by simp) hsetn (exec_seqList_cons (by simp) hsetj
    (exec_seqList_cons (by simp) hlen (exec_seqList_cons (by simp) hcallX hout)))) ?_, hr2⟩
  simp only [E0, List.nil_append]
  rfl

end

/-- The controller's program runs forever for every sequence `σ` of the values that its volatile
loads read: `main` calls `lx_init` with no event, and window `n` performs `ctlTrace ctl s0 σ n`,
given the run of the step that `CtlRuns` states.  `heap` is the heap of the store in which the
translation starts. -/
theorem ctl_program {m : Wasm.Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) {pre : List (ident × globdef (fundef function) type)}
    (hpre : PrefixOk pre) {k : Nat} {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (hty : type_of_function fd = .Tfunction [tulong, tulong] tulong cc_default)
    (A : Archi) (X : ExtSem) {heap : Heap} (hheap : heap.At (nativeStore m cap))
    {ctl : UInt64 → UInt64 → UInt64} (hruns : CtlRuns A X cap m T fd ctl) (s0 : UInt64)
    (σ : Nat → int) :
    LoopReacts A X (inProgram pre T (ctlMain k s0)) E0 (ctlTrace ctl s0 σ) := by
  have hw := wholeOk_in h hpre.sqrt hpre.funs hpre.nodup hpre.ids (ctlMain k s0)
  obtain ⟨decl, m0, m1, -, hinit, hmemi, hcalli, hst1, hs1, hE, hG, hcap, hnres, hF⟩ :=
    start_whole h hw A X
  set E := envWhole pre (inTail (ctlMain k s0)) T m.globals.length cap with hEdef
  have hidp : ∀ x : Nat, x ∈ (inTail (ctlMain k s0)).map (·.1) →
      x = 0 ∨ x = 4 ∨ x = 28 ∨ x = 32 := by
    intro x hx
    simp only [inTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx | hx
    · have : x = 32 := hx; omega
    · have : x = 28 := hx; omega
    · have : x = 4 := hx; omega
  have hq := genvQuiet_whole h hw hpre.ids hidp
  obtain ⟨bi, hsi, hdi⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (ctlMain k s0)) T) hw.nodup hmemi
  obtain ⟨bo, hso, hdo⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (ctlMain k s0)) T) hw.nodup
    (d := .Gvar outVar) (id := outId) (by simp [wholeDefs, inTail])
  obtain ⟨bn, hsn, hdn⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (ctlMain k s0)) T) hw.nodup
    (d := .Gvar inVar) (id := inId) (by simp [wholeDefs, inTail])
  obtain ⟨bm, hsm, hdm⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (ctlMain k s0)) T) hw.nodup
    (d := .Gfun (.Internal (ctlMain k s0))) (id := mainId) (by simp [wholeDefs, inTail])
  have hvo : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (inTail (ctlMain k s0)) T)) bo = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdo, outVar]
  have hvn : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (inTail (ctlMain k s0)) T)) bn = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdn, inVar]
  obtain ⟨bk, hsk, hfk⟩ := hF k fd hfd
  let le0 := create_undef_temps ctlTemps
  have hentry : function_entry2 (ctlMain k s0) [] m0 empty_env le0 m0 :=
    .intro le0 rfl List.nodup_nil (by simp [var_names, ctlMain]) rfl
  have hc1 := exec_initCall (X := X) (le := le0) hsi (Genv.find_funct_ptr_of_def hdi) rfl hcalli
  have hset0 : exec_stmt A X E.ge empty_env le0 m1 (.Sset resTemp (.Econst_long s0 tulong)) E0
      (le0.insert resTemp (.Vlong s0)) m1 .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  refine ⟨ctlTrace_ne ctl s0 σ, bm, ctlMain k s0, m0, m0, empty_env, le0,
    .Ssequence initCall (.Ssequence (.Sset resTemp (.Econst_long s0 tulong)) .Sskip),
    .Ssequence .Sskip (ctlWindow k), .Sskip,
    fun n le mm => ∃ (st : Store Unit) (hp : Heap), StoreRel A E st mm ∧ StatusRel A E mm 0 ∧
      hp.At st ∧ st.memoryCaps = (nativeStore m cap).memoryCaps ∧
      le[resTemp]? = some (.Vlong (ctlState ctl s0 σ n)),
    hinit, hsm, Genv.find_funct_ptr_of_def hdm, rfl,
    .seq_after _ (.seq_before _ (.seq_before _ (.loop _ _))), hentry,
    ⟨le0.insert resTemp (.Vlong s0), m1,
      exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hc1
        (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hset0 (.exec_Sskip _ _ _))) (by simp [E0]),
      nativeStore m cap, heap, hst1, hs1, hheap, rfl, te_insert_same _ _ _⟩, ?_⟩
  rintro n le mm ⟨st, hp, hstr, hsr, hat, hcaps, hr⟩
  obtain ⟨t, m', st', hp', hcall, hst', hs', hat', hcaps'⟩ := hruns E hE hG hcap hnres hF st hp
    hat hcaps (ctlState ctl s0 σ n) (ctlInput σ n) mm hstr hsr
  have ht : t = E0 := funcall_quiet hq hcall (translation_fun_quiet h hfd (by
    show (4 * k + 3) % 4 = 3; omega))
  subst ht
  obtain ⟨le', hx, hr'⟩ := exec_ctlWindow (X := X) k hsk hfk hty hsn hvn hso hvo
    (fun j => σ (8 * n + j)) hr hcall
  refine ⟨le', m', exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sskip _ _ _) hx) (.exec_Sskip _ _ _)) ?_,
    st', hp', hst', hs', hat', hcaps', hr'⟩
  simp only [E0, List.nil_append, List.append_nil]
  rfl

/-! ## The values that the windows read -/

/-- The loads of `t` read `σ` from position `c`: the `k`-th volatile load of `t` reads
`σ (c + k)`, and `t` has no system call. -/
def ReadsFrom (σ : Nat → int) (c : Nat) (t : trace) : Prop :=
  ∀ tp ev u, t = tp ++ ev :: u →
    match ev with
    | .Event_syscall _ _ _ => False
    | .Event_vload _ _ _ v => v = .EVint (σ (c + countVloads tp))
    | _ => True

theorem countVloads_append (t1 t2 : trace) :
    countVloads (t1 ++ t2) = countVloads t1 + countVloads t2 := by
  simp [countVloads, List.filter_append]

theorem countVloads_inTrace (σ : Nat → int) : ∀ (a d : Nat), countVloads (inTrace σ a d) = d
  | _, 0 => rfl
  | a, d + 1 => by
      simp only [inTrace]
      rw [countVloads_cons_inEvent, countVloads_inTrace σ (a + 1) d]

theorem countVloads_outTrace (bs : List UInt8) : countVloads (outTrace bs) = 0 := by
  simp [countVloads, outTrace, List.filter_map, isVload, Function.comp_def]

theorem ReadsFrom.append {σ : Nat → int} {c : Nat} {t1 t2 : trace} (h1 : ReadsFrom σ c t1)
    (h2 : ReadsFrom σ (c + countVloads t1) t2) : ReadsFrom σ c (t1 ++ t2) := by
  intro tp ev u h
  rcases List.append_eq_append_iff.mp h with ⟨a', rfl, ht2⟩ | ⟨c', ht1, hc'⟩
  · have e : c + countVloads (t1 ++ a') = c + countVloads t1 + countVloads a' := by
      rw [countVloads_append, Nat.add_assoc]
    rw [e]
    exact h2 a' ev u ht2
  · cases c' with
    | nil =>
        simp only [List.append_nil, List.nil_append] at ht1 hc'
        subst ht1
        have h' := h2 [] ev u (by simpa using hc'.symm)
        have e : c + countVloads t1 + countVloads [] = c + countVloads t1 := by
          simp [countVloads]
        rw [e] at h'
        exact h'
    | cons e c'' =>
        simp only [List.cons_append, List.cons.injEq] at hc'
        obtain ⟨rfl, -⟩ := hc'
        exact h1 tp ev c'' ht1

theorem ctlTrace_reads (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int)
    (n : Nat) : ReadsFrom σ (8 * n) (ctlTrace ctl s0 σ n) := by
  intro tp ev u h
  have h' := reads_inTrace_aux (fun j => σ (8 * n + j)) _ (fun e he => by
    simp only [outTrace, List.mem_map] at he
    obtain ⟨b, -, rfl⟩ := he
    exact ⟨_, _, _, _, rfl⟩) 8 0 tp ev u h
  cases ev <;> simpa using h'

theorem countVloads_ctlTrace (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int)
    (n : Nat) : countVloads (ctlTrace ctl s0 σ n) = 8 := by
  rw [ctlTrace, countVloads_append, countVloads_inTrace, countVloads_outTrace]

theorem ctl_windows_reads (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int) :
    ∀ n, ReadsFrom σ 0 (windows (ctlTrace ctl s0 σ) n) ∧
      countVloads (windows (ctlTrace ctl s0 σ) n) = 8 * n
  | 0 => ⟨fun tp ev u h => by simp [windows] at h, rfl⟩
  | n + 1 => by
      obtain ⟨hr, hc⟩ := ctl_windows_reads ctl s0 σ n
      refine ⟨hr.append ?_, ?_⟩
      · rw [hc, Nat.zero_add]
        exact ctlTrace_reads ctl s0 σ n
      · rw [windows, countVloads_append, hc, countVloads_ctlTrace]
        omega

/-- The initial trace and the first `n` windows read `σ`: the `reads` premise of
`clight2_loop_to_asm` in `rocq/Clight2Asm.v`. -/
theorem ctl_reads (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int) (n : Nat) :
    Reads σ (E0 ++ windows (ctlTrace ctl s0 σ) n) := by
  intro tp ev u h
  have h' := (ctl_windows_reads ctl s0 σ n).1 tp ev u (by simpa [E0] using h)
  cases ev <;> simpa using h'

end LeanExe.Native
