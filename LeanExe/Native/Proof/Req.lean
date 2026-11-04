import LeanExe.Native.Proof.Ctl

/-!
The program with requests (`reqMain` of `LeanExe/Native/Bare.lean`), which runs a step function
forever and performs, in each window, the one register access that the step requests: for every
sequence `σ` of the values that its volatile loads read, `req_program` states `LoopReacts` with
the initial trace `E0` and the window traces `reqTrace`.  The step's state has a type `G` whose
values are lists of words of one length, `words`, which `main` holds in temporaries.
`ReqState` is the state before a window: the step's state, the last value read, and the number
of reads so far.  The step's results are the new state and the request word `q`: bit 63 set
requests a write of the low 32 bits of `q` to register `reqReg q`, of 16 bits, and bit 63 clear
a read of that register, whose value is the `k`-th read's `σ k`.  `ReqRuns` is what the step
must do from every store that the loop's invariant allows, which `NativeA` gives for a step that
cannot trap.
-/

namespace LeanExe.Native

open LClight Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The register of the request `q`, `(q >> 32) & 65535`. -/
def reqReg (q : UInt64) : UInt64 := (q >>> UInt64.ofNat 32) &&& UInt64.ofNat 65535

/-- Whether the request `q` is a write, bit 63. -/
def reqWrite (q : UInt64) : Bool := q >>> UInt64.ofNat 63 != UInt64.ofNat 0

/-- The offset of the register of the request `q` in `lx_reg`. -/
def regOfs (q : UInt64) : ptrofs := UInt64.ofNat (4 * (reqReg q).toNat)

/-- The state before a window: the step's state, the last value read, and the number of reads
so far. -/
structure ReqState (G : Type) where
  state : G
  last : UInt64
  reads : Nat

variable {G : Type}

/-- The state after a window. -/
def reqNext (tick : G → UInt64 → G × UInt64) (σ : Nat → int) (r : ReqState G) :
    ReqState G :=
  if reqWrite (tick r.state r.last).2 then ⟨(tick r.state r.last).1, 0, r.reads⟩
  else ⟨(tick r.state r.last).1, UInt64.ofNat (σ r.reads).toNat, r.reads + 1⟩

/-- The state before window `n`. -/
def reqRun (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) : Nat → ReqState G
  | 0 => ⟨s0, 0, 0⟩
  | n + 1 => reqNext tick σ (reqRun tick s0 σ n)

/-- The event of the window from the state `r`. -/
def reqEvent (tick : G → UInt64 → G × UInt64) (σ : Nat → int) (r : ReqState G) : event :=
  if reqWrite (tick r.state r.last).2 then
    .Event_vstore .Mint32 regId (regOfs (tick r.state r.last).2)
      (.EVint (UInt32.ofNat ((tick r.state r.last).2.toNat % 2 ^ 32)))
  else .Event_vload .Mint32 regId (regOfs (tick r.state r.last).2) (.EVint (σ r.reads))

/-- The trace of window `n`: its one register access. -/
def reqTrace (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) (n : Nat) : trace :=
  [reqEvent tick σ (reqRun tick s0 σ n)]

theorem reqTrace_ne (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) (n : Nat) :
    reqTrace tick s0 σ n ≠ [] := by
  simp [reqTrace]

/-- The result globals hold the words `ws`, the first in the result global 0. -/
def ResultsAt (A : Archi) (E : Env) (ws : List UInt64) (m : mem) : Prop :=
  ∀ i w, ws[i]? = some w → Mem.load A .Mint64 m (E.res i .i64) 0 = some (.Vlong w)

/-- The step `fd` computes `tick` from every store that the loop's invariant allows, taking the
state's words and the last value and leaving the new state's words and the request in the
result globals. -/
def ReqRuns (A : Archi) (X : ExtSem) (cap : Nat) (m : Wasm.Module) (T : Translation)
    (fd : function) (words : G → List UInt64) (tick : G → UInt64 → G × UInt64) : Prop :=
  ∀ E : Env, EnvOk E → E.globals.length = m.globals.length → E.cap = cap → T.nres ≤ E.nres →
    (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ bk, Genv.find_symbol E.ge (funId k) = some bk ∧
        Genv.find_funct_ptr E.ge bk = some (.Internal fd)) →
    ∀ (st : Store Unit) (heap : Heap), heap.At st →
      st.memoryCaps = (nativeStore m cap).memoryCaps →
    ∀ (s : G) (v : UInt64) (m1 : mem), StoreRel A E st m1 → StatusRel A E m1 0 →
      ∃ (t : trace) (m' : mem) (vres : val) (st' : Store Unit) (heap' : Heap),
        eval_funcall A X E.ge m1 (.Internal fd) ((words s ++ [v]).map .Vlong) t m'
          vres ∧
        StoreRel A E st' m' ∧ StatusRel A E m' 0 ∧ heap'.At st' ∧
        st'.memoryCaps = (nativeStore m cap).memoryCaps ∧
        ResultsAt A E (words (tick s v).1 ++ [(tick s v).2]) m'

/-- `ReqRuns` of a step that cannot trap, from its theorem `NativeA` over the pairs of state and
last value, for a state of `n + 1` words with the words' values as its representation. -/
theorem reqRuns_of_nativeA [Scalar G] {A : Archi} {X : ExtSem} {cap : Nat} {m : Wasm.Module}
    {T : Translation} {fd : function} {words : G → List UInt64} {n : Nat}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = n + 1) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (hnat : NativeA A X cap m T (List.replicate (n + 2) .i64) (List.replicate (n + 2) .i64) fd
      false (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hcap : cap ≤ 65535) :
    ReqRuns A X cap m T fd words tick := by
  intro E hE hG hcap' hnres hF st heap hat hcaps s v m1 hst hs
  have hcapS : st.memoryCap m 0 ≤ 65535 := by
    simp [Store.memoryCap, hcaps, nativeStore, hcap]
  have hps : (words s ++ [v]).map (fun _ => VT.i64) = List.replicate (n + 2) VT.i64 := by
    simp only [List.map_append, List.map_const', hlen, List.length_singleton]
    exact List.replicate_append_replicate.trans (by rfl)
  have hb : Represent.borrowed heap st ((words s ++ [v]).map Value.i64) (s, v) := by
    show _ = Scalar.values s ++ Scalar.values v
    rw [hwords]
    simp [Scalar.values]
  have hargs := argsTyped_i64 (words s ++ [v])
  rw [hps] at hargs
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap' hnres hF st heap
    ((words s ++ [v]).map Value.i64) (s, v) hat (hPre _ _ _) hb Separate.nil hcapS hargs m1
    hst hs
  have hav := argVals_i64 (words s ++ [v])
  rw [hps] at hav
  rw [hav] at hcall
  rcases hres with ⟨hs', vs, heap', hr, hat', hown, hcaps', -, -⟩ | ⟨habs, -⟩
  · have hv : vs.reverse = (words (tick s v).1 ++ [(tick s v).2]).map Value.i64 := by
      have : vs.reverse = Scalar.values (tick s v).1 ++ Scalar.values (tick s v).2 := hown
      rw [this, hwords]
      simp [Scalar.values]
    have hlv : vs.length = n + 2 := by
      have := congrArg List.length hv
      simp [hlen] at this
      exact this
    have hdrop : ((words s ++ [v]).map Value.i64).reverse.drop
        (List.replicate (n + 2) VT.i64).length = [] := by
      simp [hlen]
    rw [hdrop, show List.replicate (n + 2) VT.i64 = .i64 :: .i64 :: List.replicate n .i64
      from rfl] at hr
    obtain ⟨ws, hws, -, -, hin⟩ := hr
    rw [show (VT.i64 :: VT.i64 :: List.replicate n VT.i64) = List.replicate (n + 2) VT.i64
      from rfl] at hin
    rw [List.append_nil] at hws
    subst hws
    refine ⟨t, m', vres, final, heap', hcall, hst', hs', hat', hcaps'.trans hcaps, ?_⟩
    intro i w hiw
    have hi : i < n + 2 := by
      have := (List.getElem?_eq_some_iff.mp hiw).1
      simp [hlen] at this
      omega
    obtain ⟨v', hv', -, hl⟩ := hin.2 i (by simp; omega)
    rw [List.take_of_length_le (by simp [hlv]), hv, List.getElem?_map, hiw] at hv'
    simp only [Option.map_some, Option.some.injEq] at hv'
    subst hv'
    simp only [List.getElem_replicate] at hl
    exact hl
  · cases habs

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem reqReg_lt (q : UInt64) : (reqReg q).toNat < 65536 := by
  simp only [reqReg, UInt64.toNat_and]
  have := Nat.and_le_right (n := (q >>> UInt64.ofNat 32).toNat) (m := (UInt64.ofNat 65535).toNat)
  have h255 : (UInt64.ofNat 65535).toNat = 65535 := rfl
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

/-- `&lx_reg[(l6 >> 32) & 65535]`. -/
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
      ∀ x, x ≠ nTemp → x ≠ lenLoadTemp → le'[x]? = le[x]? := by
  have hcond : eval_expr A ge empty_env le m
      (.Ebinop .One (.Ebinop .Oshr (.Etempvar byteTemp tulong) (clong 63) tulong) (clong 0) tint)
      (.Vint (if q >>> UInt64.ofNat 63 ≠ UInt64.ofNat 0 then 1 else 0)) :=
    .eval_Ebinop _ _ _ _ _ _ _
      (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hq) (.eval_Econst_long _ _)
        (sem_shr_const A m q 63 (by omega)))
      (.eval_Econst_long _ _) (sem_ne_ll A m _ _)
  cases hw : reqWrite q
  · refine ⟨_, .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond
      (by show bool_val A _ tint m = _; rw [bool_reqWrite, hw]) (exec_regLoad hs hv hq v),
      te_insert_same _ _ _, fun x hn hl => ?_⟩
    rw [te_insert_ne _ (Ne.symm hn), te_insert_ne _ (Ne.symm hl)]
  · refine ⟨_, .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond
      (by show bool_val A _ tint m = _; rw [bool_reqWrite, hw])
      (exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (exec_regStore hs hv hq)
        (.exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _))) (by simp [E0])),
      te_insert_same _ _ _, fun x hn _ => ?_⟩
    rw [te_insert_ne _ (Ne.symm hn)]

/-! ## The state's temporaries -/

theorem stTemp_ge (i : Nat) : 64 ≤ stTemp i := by
  show 64 ≤ 8 * (7 + i) + 8
  omega

theorem stTemp_lt {i j : Nat} (h : i < j) : stTemp i < stTemp j := by
  show 8 * (7 + i) + 8 < 8 * (7 + j) + 8
  omega

theorem stTemp_ne {i : Nat} {x : ident} (h : x < 64) : x ≠ stTemp i :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h (stTemp_ge i))

/-- The temporary environment `le` after the assignments of the values `vs` to the state's
temporaries from word `i` on. -/
def setState (i : Nat) : List val → temp_env → temp_env
  | [], le => le
  | v :: vs, le => setState (i + 1) vs (le.insert (stTemp i) v)

theorem setState_below : ∀ (i : Nat) (vs : List val) (le : temp_env) (x : ident),
    x < stTemp i → (setState i vs le)[x]? = le[x]?
  | _, [], _, _, _ => rfl
  | i, _ :: vs, le, x, hx => by
      rw [setState, setState_below (i + 1) vs _ x (Nat.lt_trans hx (stTemp_lt (by omega))),
        te_insert_ne _ (Nat.ne_of_gt hx)]

/-- The state's temporaries from word `i` on hold the words `ws`. -/
def StateIn (le : temp_env) (i : Nat) (ws : List UInt64) : Prop :=
  ∀ j w, ws[j]? = some w → le[stTemp (i + j)]? = some (.Vlong w)

theorem setState_in : ∀ (i : Nat) (ws : List UInt64) (le : temp_env),
    StateIn (setState i (ws.map .Vlong) le) i ws
  | _, [], _ => fun j w h => by simp at h
  | i, w :: ws, le => by
      intro j w' h
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          rw [List.map_cons, setState, setState_below (i + 1) _ _ _ (stTemp_lt (by omega)),
            Nat.add_zero, te_insert_same]
      | succ j =>
          rw [List.map_cons, setState, show i + (j + 1) = i + 1 + j by omega]
          exact setState_in (i + 1) ws _ j w' (by simpa using h)

/-- The assignments of the initial state's words, followed by `rest`. -/
theorem exec_stInit {e : env} {m : mem} (rest : statement) {t : trace} {le2 : temp_env}
    {m2 : mem} {out : outcome} : ∀ (i : Nat) (ws : List UInt64) (le : temp_env),
    exec_stmt A X ge e (setState i (ws.map .Vlong) le) m rest t le2 m2 out →
    exec_stmt A X ge e le m ((stInit i ws).foldr .Ssequence rest) t le2 m2 out
  | _, [], _, h => h
  | i, w :: ws, le, h => by
      rw [List.map_cons, setState] at h
      exact exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
        (.exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)) (exec_stInit rest (i + 1) ws _ h))
        (by simp [E0])

/-- The assignments of the result globals to the state's temporaries, followed by `rest`. -/
theorem exec_stSets {e : env} {m : mem} {rest : List statement} (hr : rest ≠ []) {t : trace}
    {le2 : temp_env} {m2 : mem} {out : outcome} : ∀ (i : Nat) (ws : List UInt64)
    (le : temp_env),
    (∀ j w le', ws[j]? = some w →
      eval_expr A ge e le' m (.Evar (resId (i + j) .i64) tulong) (.Vlong w)) →
    exec_stmt A X ge e (setState i (ws.map .Vlong) le) m (seqList rest) t le2 m2 out →
    exec_stmt A X ge e le m (seqList (stSets i ws.length ++ rest)) t le2 m2 out
  | _, [], _, _, h => h
  | i, w :: ws, le, hev, h => by
      rw [List.map_cons, setState] at h
      have hev' : ∀ j w' le', ws[j]? = some w' →
          eval_expr A ge e le' m (.Evar (resId (i + 1 + j) .i64) tulong) (.Vlong w') :=
        fun j w' le' hj => by
          have := hev (j + 1) w' le' (by simpa using hj)
          rwa [show i + (j + 1) = i + 1 + j by omega] at this
      have h0 := hev 0 w le (by simp)
      rw [Nat.add_zero] at h0
      exact exec_trace (exec_seqList_cons (by simp [hr])
        (.exec_Sset _ _ _ _ _ _ h0) (exec_stSets hr (i + 1) ws _ hev' h)) (by simp [E0])

/-- The arguments of the step: the state's words from word `i` on and the last value. -/
theorem eval_stArgs {e : env} {le : temp_env} {m : mem} {v : UInt64}
    (hv : le[nTemp]? = some (.Vlong v)) : ∀ (i : Nat) (ws : List UInt64), StateIn le i ws →
    eval_exprlist A ge e le m (stArgs i ws.length ++ [.Etempvar nTemp tulong])
      (List.replicate (ws.length + 1) tulong) ((ws ++ [v]).map .Vlong)
  | _, [], _ => .eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hv) (cast_ll A m v) .eval_Enil
  | i, w :: ws, h => by
      have h0 := h 0 w (by simp)
      rw [Nat.add_zero] at h0
      have h' : StateIn le (i + 1) ws := fun j w' hj => by
        have := h (j + 1) w' (by simpa using hj)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this
      exact .eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ h0) (cast_ll A m w)
        (eval_stArgs hv (i + 1) ws h')

/-- The call of the step on the state's words and the last value, whose results go to the
result globals. -/
theorem exec_stepCallN (k : Nat) {fd : function} {bk : block} {ws : List UInt64}
    (hsk : Genv.find_symbol ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (htyk : type_of_function fd =
      .Tfunction (List.replicate (ws.length + 1) tulong) .Tvoid cc_default)
    {le : temp_env} {m1 m' : mem} {vres : val} {v : UInt64} (hs : StateIn le 0 ws)
    (hv : le[nTemp]? = some (.Vlong v))
    (hcall : eval_funcall A X ge m1 (.Internal fd) ((ws ++ [v]).map .Vlong) E0 m' vres) :
    exec_stmt A X ge empty_env le m1
      (voidCall k (List.replicate (ws.length + 1) tulong)
        (stArgs 0 ws.length ++ [.Etempvar nTemp tulong])) E0 le m' .Out_normal :=
  .exec_Scall _ _ _ none _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _ m' vres rfl
    (.eval_Elvalue _ _ _ _ _ (eval_lvalue_global hsk) (.deref_loc_reference rfl))
    (eval_stArgs hv 0 ws hs) (by simp [Genv.find_funct, hfk]) htyk hcall

end

/-- The loop of `seqList`, after the statements `pre`. -/
theorem loopEntry_seqList (body post : statement) : ∀ pre : List statement,
    LoopEntry (seqList (pre ++ [.Sloop body post])) (pre.foldr .Ssequence .Sskip) body post
  | [] => .loop body post
  | p :: pre => by
      have : seqList ((p :: pre) ++ [.Sloop body post]) =
          .Ssequence p (seqList (pre ++ [.Sloop body post])) := by
        cases pre <;> rfl
      rw [this]
      exact .seq_before p (loopEntry_seqList body post pre)

/-- The program with requests runs forever for every sequence `σ` of the values that its volatile
loads read: `main` calls `lx_init` with no event, and window `n` performs the access of
`reqTrace tick s0 σ n`, given the run of the step that `ReqRuns` states.  `heap` is the heap of
the store in which the translation starts, the step's type takes the state's words and the last
value, and the translation keeps a result global for each of them. -/
theorem req_program {m : Wasm.Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) {pre : List (ident × globdef (fundef function) type)}
    (hpre : PrefixOk pre) {k n : Nat} {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (hty : type_of_function fd =
      .Tfunction (List.replicate (n + 1) tulong) .Tvoid cc_default)
    (hn : n + 1 ≤ T.nres) (A : Archi) (X : ExtSem) {heap : Heap}
    (hheap : heap.At (nativeStore m cap)) {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = n) {tick : G → UInt64 → G × UInt64}
    (hruns : ReqRuns A X cap m T fd words tick) (s0 : G) (σ : Nat → int) :
    LoopReacts A X (reqProgram pre T (reqMain k (words s0))) E0 (reqTrace tick s0 σ) := by
  have hw := wholeOk_req h hpre.sqrt hpre.funs hpre.nodup hpre.ids (reqMain k (words s0))
  obtain ⟨decl, m0, m1, -, hinit, hmemi, hcalli, hst1, hs1, hE, hG, hcap, hnres, hF⟩ :=
    start_whole h hw A X
  set E := envWhole pre (reqTail (reqMain k (words s0))) T m.globals.length cap with hEdef
  have hidp : ∀ x : Nat, x ∈ (reqTail (reqMain k (words s0))).map (·.1) →
      x = 0 ∨ x = 4 ∨ x = 28 ∨ x = 32 := by
    intro x hx
    simp only [reqTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx
    · have : x = 0 := hx; omega
    · have : x = 4 := hx; omega
  have hq := genvQuiet_whole h hw hpre.ids hidp
  obtain ⟨bi, hsi, hdi⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (reqTail (reqMain k (words s0))) T) hw.nodup hmemi
  obtain ⟨br, hsr, hdr⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (reqTail (reqMain k (words s0))) T) hw.nodup
    (d := .Gvar regVar) (id := regId) (by simp [wholeDefs, reqTail])
  obtain ⟨bm, hsm, hdm⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (reqTail (reqMain k (words s0))) T) hw.nodup
    (d := .Gfun (.Internal (reqMain k (words s0)))) (id := mainId)
    (by simp [wholeDefs, reqTail])
  have hvr : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (reqTail (reqMain k (words s0))) T)) br = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdr, regVar]
  obtain ⟨bk, hsk, hfk⟩ := hF k fd hfd
  have hres : ∀ i, i ≤ n → Genv.find_symbol E.ge (resId i .i64) = some (E.res i .i64) :=
    fun i hi => hE.res i (by omega) .i64 rfl
  let le0 := create_undef_temps (reqTemps (words s0).length)
  have hentry : function_entry2 (reqMain k (words s0)) [] m0 empty_env le0 m0 :=
    .intro le0 rfl List.nodup_nil (by simp [var_names, reqMain]) rfl
  have hc1 := exec_initCall (X := X) (le := le0) hsi (Genv.find_funct_ptr_of_def hdi) rfl hcalli
  have hbody : (reqMain k (words s0)).fn_body = .Ssequence
      (seqList ((initCall :: (stInit 0 (words s0) ++ [statement.Sset nTemp (clong 0)])) ++
        [statement.Sloop (.Ssequence .Sskip (reqWindow k (words s0).length)) .Sskip]))
      (.Sreturn (some (.Econst_int 0 tint))) := by
    simp [reqMain, reqBody]
  set leI := (setState 0 ((words s0).map .Vlong) le0).insert nTemp (.Vlong (UInt64.ofNat 0))
    with hleI
  have hnset : exec_stmt A X E.ge empty_env (setState 0 ((words s0).map .Vlong) le0) m1
      (.Ssequence (.Sset nTemp (clong 0)) .Sskip) E0 leI m1 .Out_normal :=
    exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
      (.exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)) (.exec_Sskip _ _ _)) (by simp [E0])
  have hinit0 : exec_stmt A X E.ge empty_env le0 m1
      ((stInit 0 (words s0) ++ [statement.Sset nTemp (clong 0)]).foldr .Ssequence .Sskip) E0
      leI m1 .Out_normal := by
    rw [List.foldr_append]
    exact exec_stInit _ 0 (words s0) le0 hnset
  have hinitAll : exec_stmt A X E.ge empty_env le0 m0
      ((initCall :: (stInit 0 (words s0) ++ [statement.Sset nTemp (clong 0)])).foldr
        .Ssequence .Sskip) E0 leI m1 .Out_normal :=
    exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hc1 hinit0) (by simp [E0])
  refine ⟨reqTrace_ne tick s0 σ, bm, reqMain k (words s0), m0, m0, empty_env, le0,
    (initCall :: (stInit 0 (words s0) ++ [statement.Sset nTemp (clong 0)])).foldr
      .Ssequence .Sskip,
    .Ssequence .Sskip (reqWindow k (words s0).length), .Sskip,
    fun i le mm => ∃ (st : Store Unit) (hp : Heap), StoreRel A E st mm ∧ StatusRel A E mm 0 ∧
      hp.At st ∧ st.memoryCaps = (nativeStore m cap).memoryCaps ∧
      StateIn le 0 (words (reqRun tick s0 σ i).state) ∧
      le[nTemp]? = some (.Vlong (reqRun tick s0 σ i).last),
    hinit, hsm, Genv.find_funct_ptr_of_def hdm, rfl, ?_, hentry,
    ⟨leI, m1, hinitAll, nativeStore m cap, heap, hst1, hs1, hheap, rfl, ?_, te_insert_same _ _ _⟩, ?_⟩
  · rw [hbody]
    exact .seq_after _ (loopEntry_seqList _ _ _)
  · intro j w hj
    rw [hleI, te_insert_ne _ (stTemp_ne (by decide))]
    exact setState_in 0 (words s0) le0 j w hj
  rintro i le mm ⟨st, hp, hstr, hstat, hat, hcaps, hrs, hrl⟩
  set r := reqRun tick s0 σ i with hr
  obtain ⟨t, m', vres, st', hp', hcall, hst', hs', hat', hcaps', hout⟩ := hruns E hE hG hcap
    hnres hF st hp hat hcaps r.state r.last mm hstr hstat
  have ht : t = E0 := funcall_quiet hq hcall (translation_fun_quiet h hfd (by
    show (4 * k + 3) % 4 = 3; omega))
  subst ht
  have hty' : type_of_function fd = .Tfunction (List.replicate ((words r.state).length + 1) tulong)
      .Tvoid cc_default := by rw [hlen]; exact hty
  have hx1 := exec_stepCallN (X := X) k hsk hfk hty' hrs hrl hcall
  set q := (tick r.state r.last).2 with hqdef
  set ws' := words (tick r.state r.last).1 with hws'
  have hlen' : ws'.length = n := hlen _
  have hevs : ∀ j w le', ws'[j]? = some w →
      eval_expr A E.ge empty_env le' m' (.Evar (resId (0 + j) .i64) tulong) (.Vlong w) := by
    intro j w le' hj
    have hjl : j < n := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    rw [Nat.zero_add]
    exact eval_global_long (hres j (by omega)) (hout j w (by simp [List.getElem?_append_left
      (show j < ws'.length by omega), hj]))
  have hevq : eval_expr A E.ge empty_env (setState 0 (ws'.map .Vlong) le) m'
      (.Evar (resId n .i64) tulong) (.Vlong q) :=
    eval_global_long (hres n le_rfl) (hout n q (by
      rw [List.getElem?_append_right (by omega), hlen', Nat.sub_self]; rfl))
  have hset3 : exec_stmt A X E.ge empty_env (setState 0 (ws'.map .Vlong) le) m'
      (.Sset byteTemp (.Evar (resId n .i64) tulong)) E0
      ((setState 0 (ws'.map .Vlong) le).insert byteTemp (.Vlong q)) m' .Out_normal :=
    .exec_Sset _ _ _ _ _ _ hevq
  obtain ⟨le4, hacc, hn4, hr4⟩ := exec_reqAccess (X := X) (m := m') hsr hvr
    (te_insert_same _ _ _) (σ r.reads)
  have htail : exec_stmt A X E.ge empty_env (setState 0 (ws'.map .Vlong) le) m'
      (seqList [.Sset byteTemp (.Evar (resId n .i64) tulong), reqAccess]) _ le4 m'
      .Out_normal :=
    exec_seqList_cons (by simp) hset3 hacc
  have hsets := exec_stSets (X := X)
    (rest := ([.Sset byteTemp (.Evar (resId n .i64) tulong), reqAccess] : List statement))
    (by simp) 0 ws' le hevs htail
  rw [hlen'] at hsets
  rw [hlen] at hx1
  have hwin0 := exec_seqList_cons (by simp) hx1 hsets
  have hwin : exec_stmt A X E.ge empty_env le mm (reqWindow k (words s0).length)
      (E0 ++ (E0 ++ [reqEvent tick σ r])) le4 m' .Out_normal := by
    rw [hlen s0]
    exact hwin0
  refine ⟨le4, m', exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sskip _ _ _) hwin) (.exec_Sskip _ _ _)) ?_,
    st', hp', hst', hs', hat', hcaps', ?_, ?_⟩
  · simp only [E0, List.nil_append, List.append_nil, reqTrace, hr]
  · intro j w hj
    have hsn : (reqRun tick s0 σ (i + 1)).state = (tick r.state r.last).1 := by
      simp only [reqRun, reqNext, hr]
      split <;> rfl
    rw [hsn] at hj
    rw [hr4 _ (stTemp_ne (x := nTemp) (by decide)).symm
      (stTemp_ne (x := lenLoadTemp) (by decide)).symm,
      te_insert_ne _ (stTemp_ne (x := byteTemp) (by decide))]
    exact setState_in 0 ws' le j w hj
  · rw [hn4]
    cases hw : reqWrite q <;> simp [reqRun, reqNext, ← hr, ← hqdef, hw]

/-! ## The values that the windows read -/

theorem reqTrace_reads (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) (n : Nat) :
    ReadsFrom σ (reqRun tick s0 σ n).reads (reqTrace tick s0 σ n) := by
  intro tp ev u h
  cases tp with
  | nil =>
      simp only [reqTrace, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      cases hw : reqWrite (tick (reqRun tick s0 σ n).state (reqRun tick s0 σ n).last).2 <;>
        simp [reqEvent, hw, countVloads]
  | cons e tp => simp [reqTrace] at h

theorem reqTrace_count (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) (n : Nat) :
    (reqRun tick s0 σ n).reads + countVloads (reqTrace tick s0 σ n) =
      (reqRun tick s0 σ (n + 1)).reads := by
  simp only [reqTrace, reqEvent, reqRun, reqNext]
  split <;> simp [countVloads, isVload, List.filter_cons]

theorem req_windows_reads (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) :
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
theorem req_reads (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → int) (n : Nat) :
    Reads σ (E0 ++ windows (reqTrace tick s0 σ) n) := by
  intro tp ev u h
  have h' := (req_windows_reads tick s0 σ n).1 tp ev u (by simpa [E0] using h)
  cases ev <;> simpa using h'

end LeanExe.Native
