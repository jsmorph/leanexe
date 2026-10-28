import LeanExe.Native.Proof.Quiet
import LeanExe.ProofKit.Array
import LeanExe.Native.Proof.Native

/-!
The run of `main` of a bare-metal program (`LeanExe/Native/Bare.lean`), statement by statement:
the call of `lx_init`, the call of the entry, the test of `lx_status`, and the stores of the
result's bytes to `lx_out`, each a volatile store that emits one event.  A result of the kind
`words` lies in the result globals of the C memory, so `OutOk` takes the environment and the
memory.
-/

namespace LeanExe.Native

open LClight

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem exec_seqList_cons {e : env} {le : temp_env} {m : mem} {s : statement}
    {l : List statement} {t1 : trace} {le1 : temp_env} {m1 : mem} {t2 : trace} {le2 : temp_env}
    {m2 : mem} {out : outcome} (hl : l ≠ [])
    (h1 : exec_stmt A X ge e le m s t1 le1 m1 .Out_normal)
    (h2 : exec_stmt A X ge e le1 m1 (seqList l) t2 le2 m2 out) :
    exec_stmt A X ge e le m (seqList (s :: l)) (t1 ++ t2) le2 m2 out := by
  match l, hl with
  | _ :: _, _ => exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2

theorem exec_seqList_stop {e : env} {le : temp_env} {m : mem} {s : statement}
    {l : List statement} {t1 : trace} {le1 : temp_env} {m1 : mem} {out : outcome}
    (h1 : exec_stmt A X ge e le m s t1 le1 m1 out) (hout : out ≠ .Out_normal) :
    exec_stmt A X ge e le m (seqList (s :: l)) t1 le1 m1 out := by
  match l with
  | [] => exact h1
  | _ :: _ => exact .exec_Sseq_2 _ _ _ _ _ _ _ _ _ h1 hout

/-- A sequence of two lists of statements, the first of which completes. -/
theorem exec_seqList_append {e : env} :
    ∀ (l1 l2 : List statement) {le : temp_env} {m : mem} {t1 : trace} {le1 : temp_env}
      {m1 : mem} {t2 : trace} {le2 : temp_env} {m2 : mem} {out : outcome},
      exec_stmt A X ge e le m (seqList l1) t1 le1 m1 .Out_normal →
      exec_stmt A X ge e le1 m1 (seqList l2) t2 le2 m2 out →
      exec_stmt A X ge e le m (seqList (l1 ++ l2)) (t1 ++ t2) le2 m2 out
  | [], _, _, _, _, _, _, _, _, _, _, h1, h2 => by
      cases h1
      exact h2
  | [_], [], _, _, _, _, _, _, _, _, _, h1, h2 => by
      cases h2
      simpa [E0] using h1
  | [_], _ :: _, _, _, _, _, _, _, _, _, _, h1, h2 => .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
  | _ :: s' :: l1, l2, _, _, _, _, _, _, _, _, _, h1, h2 => by
      cases h1 with
      | exec_Sseq_1 _ _ _ _ _ ta le' m' tb _ _ _ ha hb =>
          have h := exec_seqList_append (s' :: l1) l2 hb h2
          rw [List.append_assoc]
          exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ ha h
      | exec_Sseq_2 _ _ _ _ _ _ _ _ _ _ hout => exact absurd rfl hout

theorem exec_trace {e : env} {le : temp_env} {m : mem} {s : statement} {t t' : trace}
    {le' : temp_env} {m' : mem} {out : outcome} (h : exec_stmt A X ge e le m s t le' m' out)
    (ht : t = t') : exec_stmt A X ge e le m s t' le' m' out := ht ▸ h

/-- `lx_init();`. -/
theorem exec_initCall {le : temp_env} {m m' : mem} {fi : function} {bi : block} {vres : val}
    (hs : Genv.find_symbol ge initId = some bi) (hf : Genv.find_funct_ptr ge bi = some (.Internal fi))
    (hty : type_of_function fi = .Tfunction [] .Tvoid cc_default)
    (hcall : eval_funcall A X ge m (.Internal fi) [] E0 m' vres) :
    exec_stmt A X ge empty_env le m initCall E0 le m' .Out_normal :=
  .exec_Scall _ _ _ none (.Evar initId (.Tfunction [] .Tvoid cc_default)) [] [] .Tvoid cc_default
    (.Vptr bi Ptrofs.zero) [] (.Internal fi) E0 m' vres rfl
    (.eval_Elvalue _ _ _ _ _ (eval_lvalue_global hs) (.deref_loc_reference rfl)) .eval_Enil
    (by simp [Genv.find_funct, hf]) hty hcall

theorem eval_consts (le : temp_env) (m : mem) : ∀ args : List UInt64,
    eval_exprlist A ge empty_env le m (args.map fun a => .Econst_long a tulong)
      (args.map fun _ => tulong) (args.map .Vlong)
  | [] => .eval_Enil
  | _ :: as => .eval_Econs _ _ _ _ _ _ _ (.eval_Econst_long _ _) rfl (eval_consts le m as)

/-- `l0 = lxf_k(args);`. -/
theorem exec_entryCall {le : temp_env} {m m' : mem} {fd : function} {bk : block} {t : trace}
    {vres : val} (k : Nat) (args : List UInt64) (hs : Genv.find_symbol ge (funId k) = some bk)
    (hf : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (hty : type_of_function fd = .Tfunction (args.map fun _ => tulong) tulong cc_default)
    (hcall : eval_funcall A X ge m (.Internal fd) (args.map .Vlong) t m' vres) :
    exec_stmt A X ge empty_env le m (entryCall k args) (t ++ E0)
      ((le.insert callTemp vres).insert resTemp vres) m' .Out_normal :=
  .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Scall _ _ _ (some callTemp) _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _ m' vres
      rfl (.eval_Elvalue _ _ _ _ _ (eval_lvalue_global hs) (.deref_loc_reference rfl))
      (eval_consts le m args) (by simp [Genv.find_funct, hf]) hty hcall)
    (.exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)))

/-- `lxf_k(args);`, for an entry that returns `void`. -/
theorem exec_voidCall {le : temp_env} {m m' : mem} {fd : function} {bk : block} {t : trace}
    {vres : val} (k : Nat) (args : List UInt64) (hs : Genv.find_symbol ge (funId k) = some bk)
    (hf : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (hty : type_of_function fd = .Tfunction (args.map fun _ => tulong) .Tvoid cc_default)
    (hcall : eval_funcall A X ge m (.Internal fd) (args.map .Vlong) t m' vres) :
    exec_stmt A X ge empty_env le m
      (voidCall k (args.map fun _ => tulong) (args.map fun a => .Econst_long a tulong)) t le m'
      .Out_normal :=
  .exec_Scall _ _ _ none _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _ m' vres
    rfl (.eval_Elvalue _ _ _ _ _ (eval_lvalue_global hs) (.deref_loc_reference rfl))
    (eval_consts le m args) (by simp [Genv.find_funct, hf]) hty hcall

end

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem eval_statusTest {le : temp_env} {m : mem} {code : Nat} (hE : EnvOk E)
    (h : StatusRel E m code) (hc : code < 2 ^ 32) :
    eval_expr A E.ge empty_env le m (.Ebinop .One (.Evar statusId tuint) (.Econst_int 0 tuint) tint)
      (.Vint (if code ≠ 0 then 1 else 0)) := by
  refine .eval_Ebinop _ _ _ _ _ _ _ (eval_global_int hE.status h.1) (.eval_Econst_int _ _) ?_
  show sem_binary_operation A .One (.Vint (UInt32.ofNat code)) tuint (.Vint (UInt32.ofNat 0))
    tuint m = _
  rw [sem_ne_ii]
  by_cases h0 : code = 0
  · subst h0; simp
  · have : UInt32.ofNat code ≠ 0 := fun e => h0 ((uint32_ofNat_eq_zero hc).mp e)
    simp [this, h0]

/-- The test of `lx_status` when it is 0. -/
theorem exec_statusTest_ok {le : temp_env} {m : mem} (hE : EnvOk E) (h : StatusRel E m 0) :
    exec_stmt A X E.ge empty_env le m statusTest E0 le m .Out_normal := by
  refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ (eval_statusTest hE h (by decide)) ?_
    (by simpa using .exec_Sskip _ _ _)
  show bool_val _ tint m = _
  simpa using bool_int m 0

/-- The test of `lx_status` when it is `code`, not 0: `main` returns `code`. -/
theorem exec_statusTest_trap {le : temp_env} {m : mem} {code : Nat} (hE : EnvOk E)
    (h : StatusRel E m code) (h0 : code ≠ 0) (hc : code < 2 ^ 32) :
    exec_stmt A X E.ge empty_env le m statusTest E0 le m
      (.Out_return (some (.Vint (UInt32.ofNat code), tint))) := by
  refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ (eval_statusTest hE h hc) ?_
    (.exec_Sreturn_some _ _ _ _ _ (.eval_Ecast _ _ _ _ (eval_global_int hE.status h.1) rfl))
  show bool_val _ tint m = _
  simpa [h0] using bool_int m 1

end

section

variable {A : Archi} {X : ExtSem} {ge : genv}

/-- `lx_out = (unsigned int) e;` emits one event and changes nothing else. -/
theorem exec_outStore {le : temp_env} {m : mem} {e : expr} {n : UInt32} {bo : block}
    (hs : Genv.find_symbol ge outId = some bo) (hv : Genv.block_is_volatile ge bo = true)
    (he : eval_expr A ge empty_env le m (.Ecast e tuint) (.Vint n)) :
    exec_stmt A X ge empty_env le m (outStore e)
      [.Event_vstore .Mint32 outId Ptrofs.zero (.EVint n)] le m .Out_normal :=
  .exec_Sbuiltin _ _ _ none (.EF_vstore .Mint32) _ _ [.Vptr bo Ptrofs.zero, .Vint n] _ m .Vundef
    (.eval_Econs _ _ _ _ _ _ _ (.eval_Eaddrof _ _ _ _ (eval_lvalue_global hs)) rfl
      (.eval_Econs _ _ _ _ _ _ _ he rfl .eval_Enil))
    (.volatile_store_sem_intro bo Ptrofs.zero m (.Vint n) _ m
      (.volatile_store_vol .Mint32 m bo Ptrofs.zero outId (.EVint n) (.Vint n) hv hs
        (.ev_match_int n)))

theorem byte_of_and (x : UInt64) :
    UInt32.ofNat ((x &&& UInt64.ofNat 255).toNat % 2 ^ 32) = UInt32.ofNat x.toUInt8.toNat := by
  congr 1
  rw [UInt64.toNat_and, show (UInt64.ofNat 255).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_toUInt8]
  omega

/-- Byte `j` of the word in `l0`. -/
theorem exec_wordOut {le : temp_env} {m : mem} {y : UInt64} {bo : block}
    (hs : Genv.find_symbol ge outId = some bo) (hv : Genv.block_is_volatile ge bo = true)
    (hr : le[resTemp]? = some (.Vlong y)) {j : Nat} (hj : j < 8) :
    exec_stmt A X ge empty_env le m (wordOut j)
      (outTrace [(y >>> UInt64.ofNat (8 * j)).toUInt8]) le m .Out_normal := by
  have h := exec_outStore (X := X)
    (e := .Ebinop .Oand (.Ebinop .Oshr (.Etempvar resTemp tulong) (clong (8 * j)) tulong)
      (clong 255) tulong) hs hv
    (.eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _
      (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hr) (.eval_Econst_long _ _)
        (sem_shr_const A m y (8 * j) (by omega))) (.eval_Econst_long _ _) (sem_and_ll A m _ _))
      (cast_long_uint m _))
  rw [byte_of_and] at h
  exact h

/-- The stores of the bytes `js` of the word in `l0`. -/
theorem exec_wordOuts {le : temp_env} {m : mem} {y : UInt64} {bo : block}
    (hs : Genv.find_symbol ge outId = some bo) (hv : Genv.block_is_volatile ge bo = true)
    (hr : le[resTemp]? = some (.Vlong y)) :
    ∀ js : List Nat, js ≠ [] → (∀ j ∈ js, j < 8) →
      exec_stmt A X ge empty_env le m (seqList (js.map wordOut))
        (outTrace (js.map fun j => (y >>> UInt64.ofNat (8 * j)).toUInt8)) le m .Out_normal
  | [j], _, hj => exec_wordOut hs hv hr (hj j (by simp))
  | j :: j' :: js, _, hj =>
      exec_trace (exec_seqList_cons (by simp) (exec_wordOut hs hv hr (hj j (by simp)))
        (exec_wordOuts hs hv hr (j' :: js) (by simp) fun x hx => hj x (by simp [hx])))
        (by simp [outTrace])

end

section

variable {A : Archi} {X : ExtSem} {E : Env}

/-- Byte `j` of the word in the result global `i`. -/
theorem exec_globalOut (hE : EnvOk E) {le : temp_env} {m : mem} {y : UInt64} {bo : block}
    (hs : Genv.find_symbol E.ge outId = some bo) (hv : Genv.block_is_volatile E.ge bo = true)
    {i : Nat} (hi : i < E.nres) (hl : Mem.load .Mint64 m (E.res i .i64) 0 = some (.Vlong y))
    {j : Nat} (hj : j < 8) :
    exec_stmt A X E.ge empty_env le m (globalOut i j)
      (outTrace [(y >>> UInt64.ofNat (8 * j)).toUInt8]) le m .Out_normal := by
  have hev : eval_expr A E.ge empty_env le m (.Evar (resId i .i64) tulong) (.Vlong y) :=
    eval_res (t := .i64) (v := .i64 y) hE hi rfl hl
  have h := exec_outStore (X := X)
    (e := .Ebinop .Oand (.Ebinop .Oshr (.Evar (resId i .i64) tulong) (clong (8 * j)) tulong)
      (clong 255) tulong) hs hv
    (.eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _
      (.eval_Ebinop _ _ _ _ _ _ _ hev (.eval_Econst_long _ _)
        (sem_shr_const A m y (8 * j) (by omega))) (.eval_Econst_long _ _) (sem_and_ll A m _ _))
      (cast_long_uint m _))
  rw [byte_of_and] at h
  exact h

/-- The stores of the bytes `js` of the word in the result global `i`. -/
theorem exec_globalOuts (hE : EnvOk E) {le : temp_env} {m : mem} {y : UInt64} {bo : block}
    (hs : Genv.find_symbol E.ge outId = some bo) (hv : Genv.block_is_volatile E.ge bo = true)
    {i : Nat} (hi : i < E.nres) (hl : Mem.load .Mint64 m (E.res i .i64) 0 = some (.Vlong y)) :
    ∀ js : List Nat, js ≠ [] → (∀ j ∈ js, j < 8) →
      exec_stmt A X E.ge empty_env le m (seqList (js.map (globalOut i)))
        (outTrace (js.map fun j => (y >>> UInt64.ofNat (8 * j)).toUInt8)) le m .Out_normal
  | [j], _, hj => exec_globalOut hE hs hv hi hl (hj j (by simp))
  | j :: j' :: js, _, hj =>
      exec_trace (exec_seqList_cons (by simp) (exec_globalOut hE hs hv hi hl (hj j (by simp)))
        (exec_globalOuts hE hs hv hi hl (j' :: js) (by simp) fun x hx => hj x (by simp [hx])))
        (by simp [outTrace])

/-- The stores of the bytes of the words `w 0` to `w (k - 1)` in the first `k` result globals. -/
theorem exec_wordsOut (hE : EnvOk E) {le : temp_env} {m : mem} {bo : block}
    (hs : Genv.find_symbol E.ge outId = some bo) (hv : Genv.block_is_volatile E.ge bo = true)
    (w : Nat → UInt64) :
    ∀ k, k ≤ E.nres →
      (∀ i < k, Mem.load .Mint64 m (E.res i .i64) 0 = some (.Vlong (w i))) →
      exec_stmt A X E.ge empty_env le m
        (seqList ((List.range k).flatMap fun i => (List.range 8).map (globalOut i)))
        (outTrace (encodeWords ((List.range k).map w))) le m .Out_normal
  | 0, _, _ => by
      simpa [encodeWords, outTrace, seqList, E0] using
        (exec_stmt.exec_Sskip (A := A) (X := X) (ge := E.ge) empty_env le m)
  | k + 1, hk, hl => by
      have h1 := exec_wordsOut (le := le) hE hs hv w k (by omega) fun i hi => hl i (by omega)
      have h2 := exec_globalOuts (A := A) (X := X) (le := le) hE hs hv (i := k) (by omega)
        (hl k (by omega)) (List.range 8) (by simp) fun j hj => List.mem_range.mp hj
      have h := exec_seqList_append _ _ h1 h2
      rw [List.range_succ (n := k), List.flatMap_append, List.map_append]
      simpa [encodeWords, outTrace, encodeWord, List.flatMap_append] using h

end

/-! ## The bytes of words and arrays in memory -/

theorem toUInt8_shift (x : UInt64) {j : Nat} (hj : j < 8) :
    (x >>> UInt64.ofNat (8 * j)).toUInt8 = nbyte x.toNat j := by
  apply UInt8.toNat_inj.mp
  rw [nbyte_toNat, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  have h8 : (UInt64.ofNat (8 * j)).toNat % 64 = 8 * j := by
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
    omega
  rw [h8, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul]]

theorem encodeWord_nbyte (x : UInt64) :
    encodeWord x = (List.range 8).map fun j => nbyte x.toNat j := by
  apply List.map_congr_left
  intro j hj
  exact toUInt8_shift x (List.mem_range.mp hj)

/-- The bytes that `Mem.read64` reads. -/
theorem bytes_read64 (wm : Wasm.Mem) (a : UInt32) {j : Nat} (hj : j < 8) :
    wm.bytes (a.toNat + j) = nbyte (wm.read64 a).toNat j := by
  rw [← read64_eq_word]
  have hlen : ((List.range 8).map fun j => wm.bytes (a.toNat + j)).length = 8 := by simp
  obtain ⟨h0, h1⟩ := int_of_bytes_bounds ((List.range 8).map fun j => wm.bytes (a.toNat + j))
  rw [hlen] at h1
  have hx : ((Int64.repr (int_of_bytes ((List.range 8).map fun j => wm.bytes (a.toNat + j)))).toNat
      : _root_.Int) = int_of_bytes ((List.range 8).map fun j => wm.bytes (a.toNat + j)) := by
    simp only [Int64.repr, Int64.modulus]
    rw [UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; norm_num at h1 ⊢; omega)]
    norm_num at h1 ⊢
    omega
  have e := bytes_of_int_of_bytes ((List.range 8).map fun j => wm.bytes (a.toNat + j))
  rw [hlen, ← hx, bytes_of_int_nat] at e
  have e' := congrArg (fun l => l[j]?) e
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some] at e'
  exact (Option.some.inj e').symm

/-- The `n` bytes of memory from `q`. -/
def memBytes (wm : Wasm.Mem) (q n : Nat) : List UInt8 := (List.range n).map fun a => wm.bytes (q + a)

theorem memBytes_add (wm : Wasm.Mem) (q a b : Nat) :
    memBytes wm q (a + b) = memBytes wm q a ++ memBytes wm (q + a) b := by
  simp only [memBytes, List.range_add, List.map_append, List.map_map, Function.comp_def,
    Nat.add_assoc]

theorem memBytes_succ (wm : Wasm.Mem) (q d : Nat) :
    memBytes wm q (d + 1) = wm.bytes q :: memBytes wm (q + 1) d := by
  simp only [memBytes, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
    Nat.add_zero, Nat.succ_eq_add_one]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [Nat.add_assoc, Nat.add_comm a 1]

theorem memBytes_word (wm : Wasm.Mem) {q : Nat} (hq : q < 2 ^ 32) :
    memBytes wm q 8 = encodeWord (wm.read64 (UInt32.ofNat q)) := by
  rw [encodeWord_nbyte]
  apply List.map_congr_left
  intro j hj
  have := bytes_read64 wm (UInt32.ofNat q) (List.mem_range.mp hj)
  rwa [UInt32.toNat_ofNat_of_lt' hq] at this

theorem memBytes_words (wm : Wasm.Mem) :
    ∀ (l : List UInt64) (q : Nat), q + 8 * l.length ≤ 2 ^ 32 →
      (∀ i (h : i < l.length), wm.read64 (UInt32.ofNat (q + 8 * i)) = l[i]) →
      memBytes wm q (8 * l.length) = l.flatMap encodeWord
  | [], _, _, _ => rfl
  | x :: l, q, hq, hw => by
      rw [List.length_cons, Nat.mul_succ, Nat.add_comm, memBytes_add,
        memBytes_word wm (by simp at hq; omega), List.flatMap_cons]
      have h0 := hw 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at h0
      rw [h0, memBytes_words wm l (q + 8) (by simp at hq; omega) fun i h => by
        have := hw (i + 1) (by simp; omega)
        rw [show q + 8 * (i + 1) = q + 8 + 8 * i by omega] at this
        simpa using this]

/-- The bytes of an array in memory are `encodeArray` of its elements. -/
theorem memBytes_array {st : Wasm.Store Unit} {p : UInt64} {ws : Array UInt64}
    (h : LeanExe.ProofKit.UInt64Array.At st p ws) :
    memBytes st.mem p.toNat (8 * ws.size + 8) = encodeArray ws := by
  obtain ⟨hfit, -, hlen, hws⟩ := h
  rw [Nat.add_comm, memBytes_add, memBytes_word _ (by omega)]
  have hp : UInt32.ofNat p.toNat = p.toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega),
      LeanExe.ProofKit.Memory.toUInt32_toNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [hp, hlen, encodeArray]
  congr 1
  rw [← Array.length_toList]
  apply memBytes_words _ _ _ (by simp; omega)
  intro i hi
  rw [Array.length_toList] at hi
  rw [Array.getElem_toList, ← hws i hi]
  congr 1
  have hw := LeanExe.ProofKit.UInt64Array.wordAddress_toNat (ptr := p) (words := ws.size + 1)
    (word := i + 1) (by omega) (by omega)
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega)]
  simp only [LeanExe.ProofKit.UInt64Array.wordAddress] at hw
  rw [hw]
  omega

/-! ## The output of an array -/

section

variable {A : Archi} {X : ExtSem} {E : Env}

/-- `(unsigned int) ((unsigned char *) lx_mem)[l0 + l2]`. -/
theorem eval_byteUint (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (hm : MemRel E wm caps m) (cap : Nat) {le : temp_env} {p i : UInt64}
    (hr : le[resTemp]? = some (.Vlong p)) (hi : le[idxTemp]? = some (.Vlong i))
    (hin : (p + i).toNat < 65536 * E.cap) :
    eval_expr A E.ge empty_env le m
      (.Ecast (byteAt cap (.Ebinop .Oadd (.Etempvar resTemp tulong) (.Etempvar idxTemp tulong)
        tulong)) tuint)
      (.Vint (UInt32.ofNat (wm.bytes (p + i).toNat).toNat)) := by
  have he : eval_expr A E.ge empty_env le m
      (.Ebinop .Oadd (.Etempvar resTemp tulong) (.Etempvar idxTemp tulong) tulong) (.Vlong (p + i)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hr) (.eval_Etempvar _ _ _ hi) (sem_add_ll A m p i)
  refine .eval_Ecast _ _ (.Vint (UInt32.ofNat (wm.bytes (p + i).toNat).toNat)) _
    (.eval_Elvalue _ _ _ _ _ (eval_byteAt_lvalue hE cap he rfl)
      (.deref_loc_value .Mint8unsigned _ rfl ?_)) rfl
  have := hE.cap
  rw [loadv_mem _ (by simp [size_chunk]; omega) (by decide)]
  exact hm.load_byte hin

theorem resTemp_ne_lenTemp : resTemp ≠ lenTemp := by decide
theorem resTemp_ne_idxTemp : resTemp ≠ idxTemp := by decide
theorem lenTemp_ne_idxTemp : lenTemp ≠ idxTemp := by decide

theorem toNat_add_ofNat {p : UInt64} {i : Nat} (h : p.toNat + i < 2 ^ 64) :
    (p + UInt64.ofNat i).toNat = p.toNat + i := by
  rw [UInt64.toNat_add, toNat_ofNat64 (by omega), Nat.mod_eq_of_lt h]

/-- The loop writes the `d` bytes from `l0 + l2`, while `l2` counts up to `l1`. -/
theorem exec_bytesLoop (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (hm : MemRel E wm caps m) (cap : Nat) {bo : block}
    (hs : Genv.find_symbol E.ge outId = some bo) (hv : Genv.block_is_volatile E.ge bo = true)
    {p N : UInt64} (hfit : p.toNat + N.toNat ≤ 65536 * E.cap) :
    ∀ (d i : Nat) (le : temp_env), i + d = N.toNat → le[resTemp]? = some (.Vlong p) →
      le[lenTemp]? = some (.Vlong N) → le[idxTemp]? = some (.Vlong (UInt64.ofNat i)) →
      ∃ le', exec_stmt A X E.ge empty_env le m (bytesLoop cap)
        (outTrace (memBytes wm (p.toNat + i) d)) le' m .Out_normal
  | 0, i, le, hd, hr, hn, hi => by
      have hcap := hE.cap
      have hlt : ¬ UInt64.ofNat i < N := by
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 (by omega)]
        omega
      have hcond : eval_expr A E.ge empty_env le m
          (.Ebinop .Olt (.Etempvar idxTemp tulong) (.Etempvar lenTemp tulong) tint) (.Vint 0) :=
        .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hi) (.eval_Etempvar _ _ _ hn)
          (by show sem_binary_operation A .Olt (.Vlong _) tulong (.Vlong N) tulong m = _
              rw [sem_lt_ll]; simp [hlt])
      refine ⟨le, exec_trace (.exec_Sloop_stop1 _ _ _ _ _ E0 le m .Out_break .Out_normal
        (.exec_Sseq_2 _ _ _ _ _ _ _ _ _
          (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond
            (by show bool_val _ tint m = _; simpa using bool_int m 0)
            (by simpa using .exec_Sbreak _ _ _)) (by simp))
        .Out_break_or_return_B) (by simp [memBytes, outTrace, E0])⟩
  | d + 1, i, le, hd, hr, hn, hi => by
      have hcap := hE.cap
      have hlt : UInt64.ofNat i < N := by
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 (by omega)]
        omega
      have hcond : eval_expr A E.ge empty_env le m
          (.Ebinop .Olt (.Etempvar idxTemp tulong) (.Etempvar lenTemp tulong) tint) (.Vint 1) :=
        .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hi) (.eval_Etempvar _ _ _ hn)
          (by show sem_binary_operation A .Olt (.Vlong _) tulong (.Vlong N) tulong m = _
              rw [sem_lt_ll]; simp [hlt])
      have hpi : (p + UInt64.ofNat i).toNat = p.toNat + i := toNat_add_ofNat (by omega)
      have hstore := exec_outStore (X := X) hs hv
        (eval_byteUint (A := A) hE hm cap hr hi (by rw [hpi]; omega))
      rw [hpi] at hstore
      have hinc : eval_expr A E.ge empty_env le m
          (.Ebinop .Oadd (.Etempvar idxTemp tulong) (clong 1) tulong)
          (.Vlong (UInt64.ofNat (i + 1))) := by
        refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hi) (.eval_Econst_long _ _) ?_
        show sem_binary_operation A .Oadd (.Vlong _) tulong (.Vlong _) tulong m = _
        rw [sem_add_ll]
        congr 2
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
          toNat_ofNat64 (by omega), Nat.mod_eq_of_lt (by omega)]
      let le1 := le.insert idxTemp (.Vlong (UInt64.ofNat (i + 1)))
      obtain ⟨le', hrest⟩ := exec_bytesLoop hE hm cap hs hv hfit d (i + 1) le1 (by omega)
        (by rw [te_insert_ne _ (Ne.symm resTemp_ne_idxTemp)]; exact hr)
        (by rw [te_insert_ne _ (Ne.symm lenTemp_ne_idxTemp)]; exact hn) (te_insert_same _ _ _)
      refine ⟨le', exec_trace (.exec_Sloop_loop _ _ _ _ _ _ le1 m .Out_normal E0 le1 m _ le' m
        .Out_normal
        (.exec_Sseq_1 _ _ _ _ _ _ le m _ le1 m _
          (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond
            (by show bool_val _ tint m = _; simpa using bool_int m 1)
            (.exec_Sskip _ _ _))
          (.exec_Sseq_1 _ _ _ _ _ _ le m _ le1 m _ hstore (.exec_Sset _ _ _ _ _ _ hinc)))
        .Out_normal_or_continue_N (.exec_Sskip _ _ _) hrest) ?_⟩
      rw [memBytes_succ, show p.toNat + i + 1 = p.toNat + (i + 1) by omega]
      simp [outTrace, E0]

end

/-! ## The output statements -/

section

variable {A : Archi} {X : ExtSem} {E : Env}

/-- The statements that write an array: the length word read from memory, the number of bytes,
the index, and the loop. -/
theorem exec_arrayOut (hE : EnvOk E) {st : Wasm.Store Unit} {caps : List Nat} {m : mem}
    (hm : MemRel E st.mem caps m) (cap : Nat) {bo : block}
    (hs : Genv.find_symbol E.ge outId = some bo) (hv : Genv.block_is_volatile E.ge bo = true)
    {le : temp_env} {p : UInt64} {ws : Array UInt64} (hr : le[resTemp]? = some (.Vlong p))
    (hat : LeanExe.ProofKit.UInt64Array.At st p ws) :
    ∃ le', exec_stmt A X E.ge empty_env le m (seqList (outStmts cap .array))
      (outTrace (encodeArray ws)) le' m .Out_normal := by
  have hfit := hat.1
  have hpages := hat.2.1
  have hcap := hm.le_cap
  have hp32 := LeanExe.ProofKit.UInt64Array.At.pointerAddress_toNat hat
  have hE8 := hE.cap
  let L := UInt64.ofNat ws.size
  have hL : L.toNat = ws.size := toNat_ofNat64 (by omega)
  have hload := eval_loadBytes (A := A) hE hm cap hr 7 (by decide) (by omega)
  have hl : lbval st.mem p.toNat 7 = L := by rw [← hp32, lbval_read64, hat.2.2.1]
  rw [hl] at hload
  let le1 := le.insert lenTemp (.Vlong L)
  let N := UInt64.ofNat 8 * L + UInt64.ofNat 8
  have hN : N.toNat = 8 * ws.size + 8 := by
    show (UInt64.ofNat 8 * L + UInt64.ofNat 8).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_mul, toNat_ofNat64 (by omega), hL,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hn : eval_expr A E.ge empty_env le1 m
      (.Ebinop .Oadd (.Ebinop .Omul (clong 8) (.Etempvar lenTemp tulong) tulong) (clong 8) tulong)
      (.Vlong N) :=
    .eval_Ebinop _ _ _ _ _ _ _
      (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Econst_long _ _) (.eval_Etempvar _ _ _ (te_insert_same _ _ _))
        (by show sem_binary_operation A .Omul (.Vlong _) tulong (.Vlong _) tulong m = _
            rw [sem_mul_ll]))
      (.eval_Econst_long _ _)
      (by show sem_binary_operation A .Oadd (.Vlong _) tulong (.Vlong _) tulong m = _
          rw [sem_add_ll])
  let le2 := le1.insert lenTemp (.Vlong N)
  let le3 := le2.insert idxTemp (.Vlong (UInt64.ofNat 0))
  have hr3 : le3[resTemp]? = some (.Vlong p) := by
    simp only [le3, le2, le1]
    rw [te_insert_ne _ (Ne.symm resTemp_ne_idxTemp), te_insert_ne _ (Ne.symm resTemp_ne_lenTemp),
      te_insert_ne _ (Ne.symm resTemp_ne_lenTemp)]
    exact hr
  have hn3 : le3[lenTemp]? = some (.Vlong N) := by
    simp only [le3]
    rw [te_insert_ne _ (Ne.symm lenTemp_ne_idxTemp)]
    exact te_insert_same _ _ _
  obtain ⟨le', hloop⟩ := exec_bytesLoop (X := X) hE hm cap hs hv (p := p) (N := N)
    (by rw [hN]; omega) N.toNat 0 le3 (by omega) hr3 hn3 (te_insert_same _ _ _)
  rw [Nat.add_zero, hN, memBytes_array hat] at hloop
  refine ⟨le', exec_trace (exec_seqList_cons (by simp) (.exec_Sset _ _ _ _ _ _ hload)
    (exec_seqList_cons (by simp) (.exec_Sset _ _ _ _ _ _ hn)
      (exec_seqList_cons (by simp) (.exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)) hloop)))
    (by simp [E0])⟩

/-- What the entry's result gives `main` to write: a word, the address of an array that `At`
describes, or the words in the first `k` result globals of the memory `m`. -/
def OutOk (E : Env) (kind : OutKind) (st : Wasm.Store Unit) (m : mem) (vres : val)
    (bs : List UInt8) : Prop :=
  match kind with
  | .word => ∃ y, vres = .Vlong y ∧ bs = encodeWord y
  | .array => ∃ p ws, vres = .Vlong p ∧ LeanExe.ProofKit.UInt64Array.At st p ws ∧ bs = encodeArray ws
  | .words k => ∃ w : Nat → UInt64, k ≤ E.nres ∧
      (∀ i < k, Mem.load .Mint64 m (E.res i .i64) 0 = some (.Vlong (w i))) ∧
      bs = encodeWords ((List.range k).map w)

/-- The return type of the entry of a result of the kind `kind`. -/
def outRet : OutKind → type
  | .words _ => .Tvoid
  | _ => tulong

theorem exec_outStmts (hE : EnvOk E) {st : Wasm.Store Unit} {caps : List Nat} {m : mem}
    (hm : MemRel E st.mem caps m) (cap : Nat) (kind : OutKind) {bo : block}
    (hs : Genv.find_symbol E.ge outId = some bo) (hv : Genv.block_is_volatile E.ge bo = true)
    {le : temp_env} {vres : val} {bs : List UInt8}
    (hr : outRet kind = tulong → le[resTemp]? = some vres)
    (hout : OutOk E kind st m vres bs) :
    ∃ le', exec_stmt A X E.ge empty_env le m (seqList (outStmts cap kind)) (outTrace bs) le' m
      .Out_normal := by
  cases kind with
  | word =>
      obtain ⟨y, rfl, rfl⟩ := hout
      exact ⟨le, exec_wordOuts hs hv (hr rfl) (List.range 8) (by decide)
        fun j hj => List.mem_range.mp hj⟩
  | array =>
      obtain ⟨p, ws, rfl, hat, rfl⟩ := hout
      exact exec_arrayOut hE hm cap hs hv (hr rfl) hat
  | words k =>
      obtain ⟨w, hk, hl, rfl⟩ := hout
      exact ⟨le, exec_wordsOut hE hs hv w k hk hl⟩

end

/-! ## `main` and the program -/

section

variable {A : Archi} {X : ExtSem}

/-- The call of the entry: `l0` holds the result for a kind other than `words`. -/
theorem exec_entryStmt {E : Env} (k : Nat) (args : List UInt64) (kind : OutKind)
    {fd : function} {bk : block} (hsk : Genv.find_symbol E.ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr E.ge bk = some (.Internal fd))
    (htyk : type_of_function fd = .Tfunction (args.map fun _ => tulong) (outRet kind) cc_default)
    {le : temp_env} {m1 m' : mem} {vres : val}
    (hcall : eval_funcall A X E.ge m1 (.Internal fd) (args.map .Vlong) E0 m' vres) :
    ∃ le2, exec_stmt A X E.ge empty_env le m1 (entryStmt kind k args) E0 le2 m' .Out_normal ∧
      (outRet kind = tulong → le2[resTemp]? = some vres) := by
  cases kind with
  | words _ => exact ⟨le, exec_voidCall k args hsk hfk htyk hcall, fun h => nomatch h⟩
  | word =>
      exact ⟨_, exec_trace (exec_entryCall k args hsk hfk htyk hcall) (by simp [E0]),
        fun _ => te_insert_same _ _ _⟩
  | array =>
      exact ⟨_, exec_trace (exec_entryCall k args hsk hfk htyk hcall) (by simp [E0]),
        fun _ => te_insert_same _ _ _⟩

/-- The run of `main` from `m0`, given the run of `lx_init` from `m0` to `m1` and the call of
the entry from `m1`: `main` returns 0 after writing `bs`, or returns `code` when the entry leaves
`lx_status` set to `code`. -/
theorem eval_main {E : Env} (hE : EnvOk E) (cap k : Nat) (args : List UInt64) (kind : OutKind)
    {fi : function} {bi : block} (hsi : Genv.find_symbol E.ge initId = some bi)
    (hfi : Genv.find_funct_ptr E.ge bi = some (.Internal fi))
    (htyi : type_of_function fi = .Tfunction [] .Tvoid cc_default)
    {fd : function} {bk : block} (hsk : Genv.find_symbol E.ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr E.ge bk = some (.Internal fd))
    (htyk : type_of_function fd = .Tfunction (args.map fun _ => tulong) (outRet kind) cc_default)
    {bo : block} (hso : Genv.find_symbol E.ge outId = some bo)
    (hvo : Genv.block_is_volatile E.ge bo = true)
    {m0 m1 m' : mem} {vi vres : val} (hinit : eval_funcall A X E.ge m0 (.Internal fi) [] E0 m1 vi)
    (hcall : eval_funcall A X E.ge m1 (.Internal fd) (args.map .Vlong) E0 m' vres)
    {st : Wasm.Store Unit} {caps : List Nat} (hm : MemRel E st.mem caps m') :
    (∀ bs, StatusRel E m' 0 → OutOk E kind st m' vres bs →
      eval_funcall A X E.ge m0 (.Internal (bareMain cap k args kind)) [] (outTrace bs) m'
        (.Vint 0)) ∧
    (∀ code, StatusRel E m' code → code ≠ 0 → code < 2 ^ 32 →
      eval_funcall A X E.ge m0 (.Internal (bareMain cap k args kind)) [] E0 m'
        (.Vint (UInt32.ofNat code))) := by
  let le0 := create_undef_temps (mainTemps kind)
  have hentry : function_entry2 (bareMain cap k args kind) [] m0 empty_env le0 m0 :=
    .intro le0 rfl List.nodup_nil (by simp [var_names, bareMain]) rfl
  have hc1 := exec_initCall (X := X) (le := le0) hsi hfi htyi hinit
  obtain ⟨le2, hc2, hr⟩ := exec_entryStmt (le := le0) k args kind hsk hfk htyk hcall
  have hl : [initCall, entryStmt kind k args, statusTest] ++ outStmts cap kind =
      initCall :: entryStmt kind k args :: statusTest :: outStmts cap kind := rfl
  refine ⟨fun bs hs hout => ?_, fun code hs h0 hc => ?_⟩
  · obtain ⟨le', hout'⟩ := exec_outStmts (X := X) hE hm cap kind hso hvo hr hout
    have hfirst := exec_seqList_cons (l := [entryStmt kind k args, statusTest]) (by simp) hc1
      (exec_seqList_cons (l := [statusTest]) (by simp) hc2 (exec_statusTest_ok hE hs))
    have hbody := exec_seqList_append _ _ hfirst hout'
    refine .eval_funcall_internal _ _ _ _ _ le0 le' m0 m' _ _ m' hentry
      (exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hbody
        (.exec_Sreturn_some _ _ _ _ _ (.eval_Econst_int _ _))) (by simp [E0]))
      ⟨(fun h => by cases h), rfl⟩ rfl
  · have hbody := exec_seqList_cons (by simp) hc1 (exec_seqList_cons (by simp)
      hc2 (exec_seqList_stop (l := outStmts cap kind) (exec_statusTest_trap hE hs h0 hc)
        (by simp)))
    rw [← hl] at hbody
    refine .eval_funcall_internal _ _ _ _ _ le0 le2 m0 m' _ _ m' hentry
      (exec_trace (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ hbody (by simp)) (by simp [E0]))
      ⟨(fun h => by cases h), rfl⟩ rfl

end

/-- CompCert's declarations that the theorem about a bare-metal program assumes, which the
per-build check confirms: functions with distinct identifiers, among them `__builtin_fsqrt` as
the translation declares it, numbered as `wholeOk_of` assumes. -/
structure PrefixOk (pre : List (ident × globdef (fundef function) type)) : Prop where
  sqrt : (sqrtId, sqrtDef) ∈ pre
  funs : ∀ d ∈ pre, ∃ f, d.2 = .Gfun f
  nodup : (pre.map (·.1)).Nodup
  ids : ∀ x : Nat, x ∈ pre.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1)

/-- The call of the entry `fd` on `args` in every environment that meets the hypotheses of
`NativeA`, from every memory related to `nativeStore` with `lx_status` 0: it returns with
`lx_status` 0 and a result that gives the bytes `bs`, or, when `aborts`, it ends with `lx_status`
holding the code of `unreachable`. -/
def EntryRuns (A : Archi) (X : ExtSem) (cap : Nat) (m : Wasm.Module) (T : Translation)
    (fd : function) (args : List UInt64) (kind : OutKind) (aborts : Bool) (bs : List UInt8) :
    Prop :=
  ∀ E : Env, EnvOk E → E.globals.length = m.globals.length → E.cap = cap → T.nres ≤ E.nres →
    (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) →
    ∀ m1, StoreRel E (nativeStore m cap) m1 → StatusRel E m1 0 →
      ∃ t m' vres st', eval_funcall A X E.ge m1 (.Internal fd) (args.map .Vlong) t m' vres ∧
        StoreRel E st' m' ∧
        ((StatusRel E m' 0 ∧ OutOk E kind st' m' vres bs) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

/-- The bare-metal program of a translation terminates with the trace of the bytes `bs` and
the result 0, or, when the entry may abort, with no event and the code of `unreachable`, given
the run of the entry that `EntryRuns` states. -/
theorem bare_program {m : Wasm.Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) {pre : List (ident × globdef (fundef function) type)}
    (hpre : PrefixOk pre) {k : Nat} {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (args : List UInt64) (kind : OutKind)
    (hty : type_of_function fd = .Tfunction (args.map fun _ => tulong) (outRet kind) cc_default)
    (A : Archi) (X : ExtSem) {aborts : Bool} {bs : List UInt8}
    (hruns : EntryRuns A X cap m T fd args kind aborts bs) :
    bigstep_program_terminates A X (bareProgram pre T (bareMain cap k args kind)) (outTrace bs) 0 ∨
      (aborts = true ∧ bigstep_program_terminates A X (bareProgram pre T (bareMain cap k args kind))
        E0 (UInt32.ofNat trapUnreachable)) := by
  have hw := wholeOk_bare h hpre.sqrt hpre.funs hpre.nodup hpre.ids (bareMain cap k args kind)
  obtain ⟨decl, m0, m1, -, hinit, hmemi, hcalli, hst1, hs1, hE, hG, hcap, hnres, hF⟩ :=
    start_whole h hw A X
  have hidp : ∀ x : Nat, x ∈ (bareTail (bareMain cap k args kind)).map (·.1) →
      x = 4 ∨ x = 28 ∨ x = 32 := by
    intro x hx
    simp only [bareTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx
    · have : x = 28 := hx; omega
    · have : x = 4 := hx; omega
  have hq := genvQuiet_whole h hw hpre.ids hidp
  have hqf : QuietF trCallable (.Internal fd) := translation_fun_quiet h hfd (by
    show (4 * k + 3) % 4 = 3; omega)
  obtain ⟨bi, hsi, hdi⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (bareTail (bareMain cap k args kind)) T) hw.nodup hmemi
  obtain ⟨bk, hsk, hfk⟩ := hF k fd hfd
  obtain ⟨bo, hso, hdo⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (bareTail (bareMain cap k args kind)) T) hw.nodup
    (d := .Gvar outVar) (id := outId)
    (by simp [wholeDefs, bareTail])
  obtain ⟨bm, hsm, hdm⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (bareTail (bareMain cap k args kind)) T) hw.nodup
    (d := .Gfun (.Internal (bareMain cap k args kind))) (id := mainId)
    (by simp [wholeDefs, bareTail])
  have hvo : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (bareTail (bareMain cap k args kind)) T)) bo = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdo, outVar]
  obtain ⟨t, m', vres, st', hc, hst', hres⟩ := hruns _ hE hG hcap hnres hF m1 hst1 hs1
  have ht : t = E0 := funcall_quiet hq hc hqf
  subst ht
  have hmain := eval_main hE cap k args kind hsi (Genv.find_funct_ptr_of_def hdi) rfl hsk hfk hty
    hso hvo hcalli hc hst'.2
  rcases hres with ⟨hs', hout⟩ | ⟨hab, hs'⟩
  · exact .inl (.bigstep_program_terminates_intro bm _ m0 m' _ 0 hinit hsm
      (Genv.find_funct_ptr_of_def hdm) rfl (hmain.1 bs hs' hout))
  · exact .inr ⟨hab, .bigstep_program_terminates_intro bm _ m0 m' _ _ hinit hsm
      (Genv.find_funct_ptr_of_def hdm) rfl (hmain.2 _ hs' (by decide) (by decide))⟩


/-- The type of the translation of a function with parameters `ps` and results `rs`. -/
theorem entry_type {m : Wasm.Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {k : Nat} {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs) {ps rs : List VT}
    (hsig : ∀ g, m.funcs[k]? = some g → signatureOf g = some (ps, rs)) :
    type_of_function fd = funType ps rs := by
  obtain ⟨-, -, hspec⟩ := translate_spec h
  obtain ⟨g, hg, -, htr, -⟩ := hspec k fd hfd
  obtain ⟨ps', rs', hsig', hty, -⟩ := trFunction_sig htr
  rw [hsig g hg] at hsig'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig')
  exact hty

open LeanExe.Pipeline in
/-- A result of type `UInt64` gives its eight bytes. -/
theorem outOk_word {E : Env} {vs rest : List Wasm.Value} {vres : val} {m' : mem} {heap' : Heap}
    {final : Wasm.Store Unit} {y : UInt64} (hr : ResultRel E [.i64] vs rest vres m')
    (hrest : rest = []) (hown : Represent.owned heap' final vs.reverse y) :
    OutOk E .word final m' vres (encodeWord y) := by
  subst hrest
  obtain ⟨v, rfl, -, rfl⟩ := hr
  have hv : [v] = [Wasm.Value.i64 y] := hown
  cases hv
  exact ⟨y, rfl, rfl⟩

open LeanExe.Pipeline in
/-- A result of type `Array UInt64` gives the bytes of the array in memory. -/
theorem outOk_array {E : Env} {vs rest : List Wasm.Value} {vres : val} {m' : mem} {heap' : Heap}
    {final : Wasm.Store Unit} {ws : Array UInt64} (hr : ResultRel E [.i64] vs rest vres m')
    (hrest : rest = []) (hown : Represent.owned heap' final vs.reverse ws) :
    OutOk E .array final m' vres (encodeArray ws) := by
  subst hrest
  obtain ⟨v, rfl, -, rfl⟩ := hr
  obtain ⟨ptr, hv, hO⟩ := hown
  have hv' : v = .i64 ptr := by simpa using hv
  subst hv'
  exact ⟨ptr, ws, rfl, hO.values, rfl⟩


/-! ## From the native theorems -/

theorem allHas_i64 : ∀ args : List UInt64,
    AllHas (args.map fun _ => VT.i64) (args.map Wasm.Value.i64)
  | [] => trivial
  | _ :: as => ⟨rfl, allHas_i64 as⟩

theorem argVals_i64 (args : List UInt64) :
    argVals (args.map fun _ => VT.i64) (args.map Wasm.Value.i64).reverse = args.map val.Vlong := by
  simp [argVals, List.take_of_length_le, Function.comp_def, cval]

theorem argsTyped_i64 (args : List UInt64) :
    ArgsTyped (args.map fun _ => VT.i64) (args.map Wasm.Value.i64).reverse := by
  refine ⟨by simp, ?_⟩
  rw [List.take_of_length_le (by simp), List.reverse_reverse]
  exact allHas_i64 args

theorem funType_i64 (args : List UInt64) :
    funType (args.map fun _ => VT.i64) [.i64] =
      .Tfunction (args.map fun _ => tulong) tulong cc_default := by
  simp [funType, retOf, VT.ty, tulong]

open LeanExe.Pipeline in
theorem heapAt_nativeStore {heap : Heap} {m : Wasm.Module} (h : heap.At (m.initialStore : Wasm.Store Unit))
    (cap : Nat) : heap.At (nativeStore m cap) :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

theorem sig_eq {m : Wasm.Module} {k : Nat} {ps ps0 rs rs0 : List VT}
    (hsig : ∀ g, m.funcs[k]? = some g → signatureOf g = some (ps, rs))
    (h0 : (m.funcs[k]?).bind signatureOf = some (ps0, rs0)) : ps = ps0 ∧ rs = rs0 := by
  cases hk : m.funcs[k]? with
  | none => rw [hk] at h0; cases h0
  | some g =>
      rw [hk] at h0
      rw [show (some g).bind signatureOf = signatureOf g from rfl, hsig g hk] at h0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h0)
      exact ⟨rfl, rfl⟩

open LeanExe.Pipeline in
/-- The theorem of a bare-metal program from `NativeImpl` of its entry `k`, which takes words and
returns one word, for the argument `x` whose words are `args`, from the module's initial store
with the heap `heap`. -/
theorem bare_of_nativeA {α β : Type} [Represent α] [Represent β] {A : Archi} {X : ExtSem}
    {cap : Nat} {m : Wasm.Module} {T : Translation} (h : translate cap m = some T)
    {pre : List (ident × globdef (fundef function) type)} (hpre : PrefixOk pre) {k : Nat}
    {aborts : Bool} {f : α → β} {Pre : α → Heap → Wasm.Store Unit → Prop}
    {Post : α → Heap → Wasm.Store Unit → Heap → Wasm.Store Unit → Prop}
    (hn : ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
      (∀ g, m.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
      NativeA A X cap m T ps rs fd aborts f Pre Post)
    (args : List UInt64)
    (hk : (m.funcs[k]?).bind signatureOf = some (args.map fun _ => .i64, [.i64]))
    (kind : OutKind) (hkind : outRet kind = tulong) (x : α) (heap : Heap) {bs : List UInt8}
    (hheap : heap.At (m.initialStore : Wasm.Store Unit)) (hPre : Pre x heap (nativeStore m cap))
    (hb : Represent.borrowed heap (nativeStore m cap) (args.map Wasm.Value.i64) x)
    (hsep : Separate (nativeStore m cap) (Represent.moves (nativeStore m cap) (args.map .i64) x)
      (Represent.reads (nativeStore m cap) (args.map .i64) x))
    (hcap : cap ≤ 65535)
    (hout : ∀ (E : Env) vs vres m' (heap' : Heap) final, ResultRel E [.i64] vs [] vres m' →
      Represent.owned heap' final vs.reverse (f x) → OutOk E kind final m' vres bs) :
    bigstep_program_terminates A X (bareProgram pre T (bareMain cap k args kind)) (outTrace bs) 0 ∨
      (aborts = true ∧ bigstep_program_terminates A X (bareProgram pre T (bareMain cap k args kind))
        E0 (UInt32.ofNat trapUnreachable)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := hn
  obtain ⟨rfl, rfl⟩ := sig_eq hsig hk
  have hty := entry_type h hfd hsig
  rw [funType_i64] at hty
  have hty : type_of_function fd = .Tfunction (args.map fun _ => tulong) (outRet kind)
      cc_default := by rw [hkind]; exact hty
  refine bare_program h hpre hfd args kind hty A X fun E hE hG hcap' hnres hF m1 hst hs => ?_
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap' hnres hF
    (nativeStore m cap) heap (args.map .i64) x (heapAt_nativeStore hheap cap) hPre hb hsep hcap
    (argsTyped_i64 args) m1 hst hs
  rw [argVals_i64] at hcall
  refine ⟨t, m', vres, final, hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | habort
  · have hd : (args.map Wasm.Value.i64).reverse.drop (args.map fun _ => VT.i64).length = [] := by
      simp
    rw [hd] at hr
    exact .inl ⟨hs', hout E vs vres m' heap' final hr hown⟩
  · exact .inr habort

end LeanExe.Native
