import LeanExe.Native.Proof.Quiet
import LeanExe.ProofKit.Array

/-!
The run of `main` of a bare-metal program (`LeanExe/Native/Bare.lean`), statement by statement:
the call of `lx_init`, the call of the entry, the test of `lx_status`, and the stores of the
result's bytes to `lx_out`, each a volatile store that emits one event.
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

end LeanExe.Native
