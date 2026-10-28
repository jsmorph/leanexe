import LeanExe.Native.Proof.Main

/-!
The run of `main` with input (`inMain` of `LeanExe/Native/Bare.lean`), statement by statement.
The input is a sequence `σ` of the 32-bit event values that the volatile loads of `lx_in` read,
one per load in the order of the loads; the program uses the low byte of each.  The first eight
give the length, `inLen σ`, and the next `inLen σ` the message.  A load of offset `a` records
`Event_vload Mint8unsigned inId a (EVint (σ a))`, so the `k`-th load of the trace reads `σ k`.
-/

namespace LeanExe.Native

open LClight

/-! ## The input -/

/-- The byte that `main` takes from the event value `v`: its low eight bits. -/
def inByteOf (v : int) : UInt64 := UInt64.ofNat (v.toNat % 256)

/-- The event of the load of offset `a` that reads `v`. -/
def inEvent (a : Nat) (v : int) : event :=
  .Event_vload .Mint8unsigned inId (UInt64.ofNat a) (.EVint v)

/-- The loads of the `d` offsets from `a`, which read `σ a` to `σ (a + d - 1)`. -/
def inTrace (σ : Nat → int) : Nat → Nat → trace
  | _, 0 => []
  | a, d + 1 => inEvent a (σ a) :: inTrace σ (a + 1) d

theorem inTrace_add (σ : Nat → int) : ∀ (a d1 d2 : Nat),
    inTrace σ a (d1 + d2) = inTrace σ a d1 ++ inTrace σ (a + d1) d2
  | a, 0, d2 => by simp [inTrace]
  | a, d1 + 1, d2 => by
      rw [show d1 + 1 + d2 = (d1 + d2) + 1 by omega]
      simp only [inTrace, List.cons_append]
      rw [inTrace_add σ (a + 1) d1 d2, show a + 1 + d1 = a + (d1 + 1) by omega]

/-- The length that the first `j` loads give, as the loop of `main` combines them:
`l3 | l6 << 8 j` for each byte `l6`. -/
def lenAcc (σ : Nat → int) : Nat → UInt64
  | 0 => 0
  | j + 1 => lenAcc σ j ||| (inByteOf (σ j) <<< UInt64.ofNat (8 * j))

/-- The length of the message, from the first eight loads. -/
def inLen (σ : Nat → int) : UInt64 := lenAcc σ 8

/-- The byte of the message at index `j`, from the load of offset `8 + j`. -/
def inMsgByte (σ : Nat → int) (j : Nat) : UInt8 := (σ (8 + j)).toUInt8

/-! ## Expressions and the volatile load -/

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem sem_add_in (b : block) (k : UInt64) (m : mem) :
    sem_binary_operation A .Oadd (.Vptr b Ptrofs.zero) inArray (.Vlong k) tulong m =
      some (.Vptr b k) := by
  show some (val.Vptr b
    (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 k)))) = _
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [Ptrofs.add, Ptrofs.mul, Ptrofs.repr, Ptrofs.of_int64, Ptrofs.unsigned, Ptrofs.zero,
    Int64.unsigned, Ptrofs.modulus]
  have := k.toNat_lt
  simp
  omega

theorem cast_inByte (v : int) (m : mem) :
    sem_cast (Val.load_result .Mint8unsigned (.Vint v)) inByte tulong m =
      some (.Vlong (inByteOf v)) := by
  show some (val.Vlong (cast_int_long .Unsigned (LClight.Int.zero_ext 8 v))) = _
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [cast_int_long, LClight.Int.zero_ext, LClight.Int.repr, LClight.Int.unsigned,
    Int64.repr, LClight.Int.modulus, Int64.modulus, inByteOf]
  simp
  omega

/-- `x = lx_in[i];` through the temporary `t`: one load, which reads `v`. -/
theorem exec_inLoad {le : temp_env} {m : mem} {bi : block}
    (hs : Genv.find_symbol ge inId = some bi) (hv : Genv.block_is_volatile ge bi = true)
    {t x : ident} {i : expr} {k : UInt64} (hi : eval_expr A ge empty_env le m i (.Vlong k))
    (hty : typeof i = tulong) (v : int) :
    exec_stmt A X ge empty_env le m (inLoad t x i)
      [.Event_vload .Mint8unsigned inId k (.EVint v)]
      ((le.insert t (Val.load_result .Mint8unsigned (.Vint v))).insert x (.Vlong (inByteOf v))) m
      .Out_normal := by
  have harr : eval_expr A ge empty_env le m (.Evar inId inArray) (.Vptr bi Ptrofs.zero) :=
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hs) (.deref_loc_reference rfl)
  have hadd : eval_expr A ge empty_env le m (.Ebinop .Oadd (.Evar inId inArray) i inPtr)
      (.Vptr bi k) :=
    .eval_Ebinop _ _ _ _ _ _ _ harr hi (by rw [hty]; exact sem_add_in bi k m)
  have haddr : eval_expr A ge empty_env le m
      (.Eaddrof (.Ederef (.Ebinop .Oadd (.Evar inId inArray) i inPtr) inByte) inPtr)
      (.Vptr bi k) :=
    .eval_Eaddrof _ _ _ _ (.eval_Ederef _ _ _ _ hadd)
  exact exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Sbuiltin _ _ _ (some t) (.EF_vload .Mint8unsigned) _ _ [.Vptr bi k] _ m _
      (.eval_Econs _ _ _ _ _ _ _ haddr rfl .eval_Enil)
      (.volatile_load_sem_intro bi k m _ _
        (.volatile_load_vol .Mint8unsigned m bi k inId (.EVint v) (.Vint v) hv hs
          (.ev_match_int v))))
    (.exec_Sset _ _ _ _ _ _
      (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)) (cast_inByte v m))))
    (by simp [E0])

end

/-! ## The loop that reads the length -/

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem nTemp_ne_jTemp : nTemp ≠ jTemp := by decide
theorem nTemp_ne_byteTemp : nTemp ≠ byteTemp := by decide
theorem jTemp_ne_byteTemp : jTemp ≠ byteTemp := by decide
theorem nTemp_ne_lenLoadTemp : nTemp ≠ lenLoadTemp := by decide
theorem jTemp_ne_lenLoadTemp : jTemp ≠ lenLoadTemp := by decide

theorem eval_incr {le : temp_env} {m : mem} {x : ident} {j : Nat} (hj : j + 1 < 2 ^ 64)
    (h : le[x]? = some (.Vlong (UInt64.ofNat j))) :
    eval_expr A ge empty_env le m (.Ebinop .Oadd (.Etempvar x tulong) (clong 1) tulong)
      (.Vlong (UInt64.ofNat (j + 1))) := by
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ h) (.eval_Econst_long _ _) ?_
  show sem_binary_operation A .Oadd (.Vlong _) tulong (.Vlong _) tulong m = _
  rw [sem_add_ll]
  congr 2
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
    toNat_ofNat64 (by omega), Nat.mod_eq_of_lt (by omega)]

theorem eval_lt_const {le : temp_env} {m : mem} {x : ident} {j c : Nat} (hj : j < 2 ^ 64)
    (hc : c < 2 ^ 64) (h : le[x]? = some (.Vlong (UInt64.ofNat j))) :
    eval_expr A ge empty_env le m (.Ebinop .Olt (.Etempvar x tulong) (clong c) tint)
      (.Vint (if j < c then 1 else 0)) := by
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ h) (.eval_Econst_long _ _) ?_
  show sem_binary_operation A .Olt (.Vlong _) tulong (.Vlong _) tulong m = _
  rw [sem_lt_ll]
  have e : (UInt64.ofNat j < UInt64.ofNat c) ↔ j < c := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 hj, toNat_ofNat64 hc]
  by_cases hjc : j < c <;> simp [e, hjc]

/-- One pass of the length loop: the load of offset `j` and the update of `l3` and `l5`. -/
theorem lenAcc_succ_eval {le : temp_env} {m : mem} (σ : Nat → int) {j : Nat} (hj : j < 8)
    (hn : le[nTemp]? = some (.Vlong (lenAcc σ j)))
    (hjv : le[jTemp]? = some (.Vlong (UInt64.ofNat j)))
    (hb : le[byteTemp]? = some (.Vlong (inByteOf (σ j)))) :
    eval_expr A ge empty_env le m
      (.Ebinop .Oor (.Etempvar nTemp tulong)
        (.Ebinop .Oshl (.Etempvar byteTemp tulong)
          (.Ebinop .Omul (clong 8) (.Etempvar jTemp tulong) tulong) tulong) tulong)
      (.Vlong (lenAcc σ (j + 1))) := by
  have hmul : eval_expr A ge empty_env le m
      (.Ebinop .Omul (clong 8) (.Etempvar jTemp tulong) tulong)
      (.Vlong (UInt64.ofNat (8 * j))) := by
    refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Econst_long _ _) (.eval_Etempvar _ _ _ hjv) ?_
    show sem_binary_operation A .Omul (.Vlong _) tulong (.Vlong _) tulong m = _
    rw [sem_mul_ll]
    congr 2
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
      toNat_ofNat64 (by omega), Nat.mod_eq_of_lt (by omega)]
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hn)
    (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hb) hmul
      (sem_shl_const A m _ (8 * j) (by omega))) ?_
  show sem_binary_operation A .Oor (.Vlong _) tulong (.Vlong _) tulong m = _
  rw [sem_or_ll]
  rfl

/-- The loop reads the `d` bytes of the length from offset `j`, while `l5` counts up to 8. -/
theorem exec_lenLoop {m : mem} {bi : block} (hs : Genv.find_symbol ge inId = some bi)
    (hv : Genv.block_is_volatile ge bi = true) (σ : Nat → int) :
    ∀ (d j : Nat) (le : temp_env), j + d = 8 →
      le[nTemp]? = some (.Vlong (lenAcc σ j)) →
      le[jTemp]? = some (.Vlong (UInt64.ofNat j)) →
      ∃ le', exec_stmt A X ge empty_env le m lenLoop (inTrace σ j d) le' m .Out_normal ∧
        le'[nTemp]? = some (.Vlong (inLen σ)) ∧
        ∀ x, x ≠ nTemp → x ≠ jTemp → x ≠ byteTemp → x ≠ lenLoadTemp →
          le'[x]? = le[x]?
  | 0, j, le, hd, hn, hjv => by
      have hcond : eval_expr A ge empty_env le m
          (.Ebinop .Olt (.Etempvar jTemp tulong) (clong 8) tint) (.Vint 0) := by
        simpa [show ¬ j < 8 by omega] using
          eval_lt_const (A := A) (ge := ge) (m := m) (c := 8) (by omega) (by omega) hjv
      refine ⟨le, exec_trace (.exec_Sloop_stop1 _ _ _ _ _ E0 le m .Out_break .Out_normal
        (.exec_Sseq_2 _ _ _ _ _ _ _ _ _
          (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond
            (by show bool_val _ tint m = _; simpa using bool_int m 0)
            (by simpa using .exec_Sbreak _ _ _)) (by simp))
        .Out_break_or_return_B) (by simp [inTrace, E0]), ?_, fun _ _ _ _ _ => rfl⟩
      have : j = 8 := by omega
      subst this
      exact hn
  | d + 1, j, le, hd, hn, hjv => by
      have hcond : eval_expr A ge empty_env le m
          (.Ebinop .Olt (.Etempvar jTemp tulong) (clong 8) tint) (.Vint 1) := by
        simpa [show j < 8 by omega] using
          eval_lt_const (A := A) (ge := ge) (m := m) (c := 8) (by omega) (by omega) hjv
      have hload := exec_inLoad (A := A) (X := X) (m := m) (t := lenLoadTemp) (x := byteTemp) hs hv
        (.eval_Etempvar _ _ _ hjv) rfl (σ j)
      let le1 := (le.insert lenLoadTemp (Val.load_result .Mint8unsigned (.Vint (σ j)))).insert
        byteTemp (.Vlong (inByteOf (σ j)))
      have hn1 : le1[nTemp]? = some (.Vlong (lenAcc σ j)) := by
        simp only [le1]
        rw [te_insert_ne _ (Ne.symm nTemp_ne_byteTemp),
          te_insert_ne _ (Ne.symm nTemp_ne_lenLoadTemp)]
        exact hn
      have hj1 : le1[jTemp]? = some (.Vlong (UInt64.ofNat j)) := by
        simp only [le1]
        rw [te_insert_ne _ (Ne.symm jTemp_ne_byteTemp),
          te_insert_ne _ (Ne.symm jTemp_ne_lenLoadTemp)]
        exact hjv
      have hb1 : le1[byteTemp]? = some (.Vlong (inByteOf (σ j))) := te_insert_same _ _ _
      have hacc := lenAcc_succ_eval (A := A) (ge := ge) (m := m) σ (by omega) hn1 hj1 hb1
      let le2 := le1.insert nTemp (.Vlong (lenAcc σ (j + 1)))
      have hj2 : le2[jTemp]? = some (.Vlong (UInt64.ofNat j)) := by
        simp only [le2]
        rw [te_insert_ne _ nTemp_ne_jTemp]
        exact hj1
      have hinc := eval_incr (A := A) (ge := ge) (m := m) (by omega) hj2
      let le3 := le2.insert jTemp (.Vlong (UInt64.ofNat (j + 1)))
      obtain ⟨le', hrest, hn', hother⟩ := exec_lenLoop hs hv σ d (j + 1) le3 (by omega)
        (by simp only [le3]; rw [te_insert_ne _ (Ne.symm nTemp_ne_jTemp)]
            exact te_insert_same _ _ _)
        (te_insert_same _ _ _)
      refine ⟨le', exec_trace (.exec_Sloop_loop _ _ _ _ _ _ le3 m .Out_normal E0 le3 m _ le' m
        .Out_normal
        (.exec_Sseq_1 _ _ _ _ _ _ le m _ le3 m _
          (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond
            (by show bool_val _ tint m = _; simpa using bool_int m 1)
            (.exec_Sskip _ _ _))
          (.exec_Sseq_1 _ _ _ _ _ _ le1 m _ le3 m _ hload
            (.exec_Sseq_1 _ _ _ _ _ _ le2 m _ le3 m _ (.exec_Sset _ _ _ _ _ _ hacc)
              (.exec_Sset _ _ _ _ _ _ hinc))))
        .Out_normal_or_continue_N (.exec_Sskip _ _ _) hrest) (by simp [inTrace, inEvent, E0]),
        hn', fun x h1 h2 h3 h4 => ?_⟩
      rw [hother x h1 h2 h3 h4]
      simp only [le3, le2, le1]
      rw [te_insert_ne _ (Ne.symm h2), te_insert_ne _ (Ne.symm h1), te_insert_ne _ (Ne.symm h3),
        te_insert_ne _ (Ne.symm h4)]

end

/-! ## The copy of the message -/

/-- `wm` with the `j` bytes `b 0` to `b (j - 1)` from the address `q`. -/
def withBytes (wm : Wasm.Mem) (q j : Nat) (b : Nat → UInt8) : Wasm.Mem :=
  { wm with bytes := fun i => if q ≤ i ∧ i < q + j then b (i - q) else wm.bytes i }

theorem withBytes_zero (wm : Wasm.Mem) (q : Nat) (b : Nat → UInt8) : withBytes wm q 0 b = wm := by
  cases wm
  simp only [withBytes, Wasm.Mem.mk.injEq, true_and]
  funext i
  split_ifs with h
  · omega
  · rfl

theorem withBytes_succ (wm : Wasm.Mem) (q j : Nat) (b : Nat → UInt8) :
    ({ pages := (withBytes wm q j b).pages,
       bytes := fun i => if i = q + j then b j else (withBytes wm q j b).bytes i } : Wasm.Mem) =
      withBytes wm q (j + 1) b := by
  simp only [withBytes, Wasm.Mem.mk.injEq, true_and]
  funext i
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem byte_inByteOf (v : int) : UInt8.ofNat (inByteOf v).toNat = v.toUInt8 := by
  unfold inByteOf
  rw [toNat_ofNat64 (by omega)]
  apply UInt8.toNat_inj.mp
  simp

theorem MemRel.store_byte_at {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m m' : mem}
    (hE : EnvOk E) (h : MemRel E wm caps m) (hs : Mem.SameExcept E.mem m m') {a : Nat}
    {y : UInt8}
    (hc : ∀ i : Nat, ZMap.get (i : _root_.Int) (Mem.contents_of m' E.mem) =
      if i = a then .Byte y else ZMap.get (i : _root_.Int) (Mem.contents_of m E.mem)) :
    MemRel E { wm with bytes := fun i => if i = a then y else wm.bytes i } caps m' := by
  refine h.of_contents hE hs rfl fun i hi => ?_
  rw [hc i]
  show _ = memval.Byte (if i = a then y else wm.bytes i)
  split_ifs with hia
  · rfl
  · exact h.bytes i hi

section

variable {A : Archi} {X : ExtSem} {E : Env}

/-- `((unsigned char *) lx_mem)[e] = (unsigned char) x;`: the store of the low byte of the word
in `vid` at the address that `e` gives. -/
theorem exec_byteStoreAt (hE : EnvOk E) {le : temp_env} (cap : Nat) {e : expr} {vid : ident}
    {a x : UInt64} {m : mem} (ha : eval_expr A E.ge empty_env le m e (.Vlong a))
    (hty : typeof e = tulong) (hv : le[vid]? = some (.Vlong x)) (hin : a.toNat < 65536 * E.cap)
    (hp : ∀ i : Nat, i < 65536 * E.cap → Mem.perm m E.mem i .Cur .Writable) :
    ∃ m', exec_stmt A X E.ge empty_env le m
        (.Sassign (byteAt cap e) (.Ecast (.Etempvar vid tulong) tuchar)) E0 le m' .Out_normal ∧
      Mem.SameExcept E.mem m m' ∧
      ∀ i : Nat, ZMap.get (i : _root_.Int) (Mem.contents_of m' E.mem) =
        if i = a.toNat then .Byte (UInt8.ofNat x.toNat)
        else ZMap.get (i : _root_.Int) (Mem.contents_of m E.mem) := by
  have hcap := hE.cap
  have hlv := eval_byteAt_lvalue hE cap ha hty
  have hva : Mem.valid_access m .Mint8unsigned E.mem (a.toNat : Nat) .Writable := by
    refine ⟨fun ofs h1 h2 => ?_, ⟨(a.toNat : Nat), by simp [align_chunk]⟩⟩
    have h2' : ofs < ((a.toNat : Nat) : _root_.Int) + 1 := h2
    have : ofs = ((a.toNat : Nat) : _root_.Int) := by omega
    subst this
    exact hp _ hin
  refine ⟨Mem.stored .Mint8unsigned m E.mem (a.toNat : Nat)
      (.Vint (UInt32.ofNat (x.toNat % 256))), ?_, Mem.SameExcept.of_stored _ _ _ _ _, ?_⟩
  · refine .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ hlv
      (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hv) (cast_cbyte x m))
      (cast_uchar _ m) (.assign_loc_value _ .Mint8unsigned _ rfl ?_)
    have e := storev_mem (m := m) (b := E.mem) (v := .Vint (UInt32.ofNat (x.toNat % 256)))
      .Mint8unsigned (q := a) (by simp [size_chunk]; omega) (by decide)
    rw [e]
    exact Mem.store_ok _ hva
  · intro i
    rw [Mem.contents_stored_same, encode_cbyte]
    split
    · rename_i hi
      subst hi
      have e := Mem.setN_at [.Byte (UInt8.ofNat x.toNat)] ((a.toNat : Nat) : _root_.Int)
        (Mem.contents_of m E.mem) 0 (by simp)
      simpa using e
    · rename_i hi
      rcases Nat.lt_or_ge i a.toNat with hlt | hge
      · exact Mem.setN_outside _ _ _ _ (by omega)
      · exact Mem.setN_above _ _ _ _ (by simp; omega)

theorem jTemp_ne_nTemp : jTemp ≠ nTemp := by decide
theorem jTemp_ne_ptrTemp : jTemp ≠ ptrTemp := by decide
theorem jTemp_ne_copyLoadTemp : jTemp ≠ copyLoadTemp := by decide
theorem byteTemp_ne_copyLoadTemp : byteTemp ≠ copyLoadTemp := by decide
theorem nTemp_ne_copyLoadTemp : nTemp ≠ copyLoadTemp := by decide
theorem ptrTemp_ne_copyLoadTemp : ptrTemp ≠ copyLoadTemp := by decide
theorem ptrTemp_ne_byteTemp : ptrTemp ≠ byteTemp := by decide

/-- The loop copies the bytes of the message from index `j` on, while `l5` counts up to the
length in `l3`. -/
theorem exec_copyLoop (hE : EnvOk E) (cap : Nat) {bi : block}
    (hs : Genv.find_symbol E.ge inId = some bi) (hv : Genv.block_is_volatile E.ge bi = true)
    (σ : Nat → int) {wm : Wasm.Mem} {caps : List Nat} {p n : UInt64}
    (hfit : p.toNat + 8 + n.toNat ≤ 65536 * E.cap) :
    ∀ (d j : Nat) (le : temp_env) (m : mem), j + d = n.toNat →
      le[jTemp]? = some (.Vlong (UInt64.ofNat j)) → le[nTemp]? = some (.Vlong n) →
      le[ptrTemp]? = some (.Vlong p) →
      MemRel E (withBytes wm (p.toNat + 8) j (inMsgByte σ)) caps m →
      ∃ le' m', exec_stmt A X E.ge empty_env le m (copyLoop cap) (inTrace σ (8 + j) d) le' m'
          .Out_normal ∧
        MemRel E (withBytes wm (p.toNat + 8) n.toNat (inMsgByte σ)) caps m' ∧
        Mem.SameExcept E.mem m m' ∧
        ∀ x, x ≠ jTemp → x ≠ byteTemp → x ≠ copyLoadTemp → le'[x]? = le[x]?
  | 0, j, le, m, hd, hjv, hn, hp, hm => by
      have hcap := hE.cap
      have hlt : ¬ UInt64.ofNat j < n := by
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 (by omega)]
        omega
      have hcond : eval_expr A E.ge empty_env le m
          (.Ebinop .Olt (.Etempvar jTemp tulong) (.Etempvar nTemp tulong) tint) (.Vint 0) :=
        .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hjv) (.eval_Etempvar _ _ _ hn)
          (by show sem_binary_operation A .Olt (.Vlong _) tulong (.Vlong n) tulong m = _
              rw [sem_lt_ll]; simp [hlt])
      refine ⟨le, m, exec_trace (.exec_Sloop_stop1 _ _ _ _ _ E0 le m .Out_break .Out_normal
        (.exec_Sseq_2 _ _ _ _ _ _ _ _ _
          (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond
            (by show bool_val _ tint m = _; simpa using bool_int m 0)
            (by simpa using .exec_Sbreak _ _ _)) (by simp))
        .Out_break_or_return_B) (by simp [inTrace, E0]), ?_, Mem.SameExcept.refl _ _,
        fun _ _ _ _ => rfl⟩
      rw [show n.toNat = j by omega]
      exact hm
  | d + 1, j, le, m, hd, hjv, hn, hp, hm => by
      have hcap := hE.cap
      have hlt : UInt64.ofNat j < n := by
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 (by omega)]
        omega
      have hcond : eval_expr A E.ge empty_env le m
          (.Ebinop .Olt (.Etempvar jTemp tulong) (.Etempvar nTemp tulong) tint) (.Vint 1) :=
        .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hjv) (.eval_Etempvar _ _ _ hn)
          (by show sem_binary_operation A .Olt (.Vlong _) tulong (.Vlong n) tulong m = _
              rw [sem_lt_ll]; simp [hlt])
      have hidx : eval_expr A E.ge empty_env le m
          (.Ebinop .Oadd (clong 8) (.Etempvar jTemp tulong) tulong)
          (.Vlong (UInt64.ofNat (8 + j))) := by
        refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Econst_long _ _) (.eval_Etempvar _ _ _ hjv) ?_
        show sem_binary_operation A .Oadd (.Vlong _) tulong (.Vlong _) tulong m = _
        rw [sem_add_ll]
        congr 2
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
          toNat_ofNat64 (by omega), Nat.mod_eq_of_lt (by omega)]
      have hload := exec_inLoad (A := A) (X := X) (m := m) (t := copyLoadTemp) (x := byteTemp)
        hs hv hidx rfl (σ (8 + j))
      let le1 := (le.insert copyLoadTemp
        (Val.load_result .Mint8unsigned (.Vint (σ (8 + j))))).insert
          byteTemp (.Vlong (inByteOf (σ (8 + j))))
      have hp1 : le1[ptrTemp]? = some (.Vlong p) := by
        simp only [le1]
        rw [te_insert_ne _ (Ne.symm ptrTemp_ne_byteTemp),
          te_insert_ne _ (Ne.symm ptrTemp_ne_copyLoadTemp)]
        exact hp
      have hj1 : le1[jTemp]? = some (.Vlong (UInt64.ofNat j)) := by
        simp only [le1]
        rw [te_insert_ne _ (Ne.symm jTemp_ne_byteTemp),
          te_insert_ne _ (Ne.symm jTemp_ne_copyLoadTemp)]
        exact hjv
      have hn1 : le1[nTemp]? = some (.Vlong n) := by
        simp only [le1]
        rw [te_insert_ne _ (Ne.symm nTemp_ne_byteTemp),
          te_insert_ne _ (Ne.symm nTemp_ne_copyLoadTemp)]
        exact hn
      have hb1 : le1[byteTemp]? = some (.Vlong (inByteOf (σ (8 + j)))) := te_insert_same _ _ _
      have haddr : eval_expr A E.ge empty_env le1 m
          (.Ebinop .Oadd (.Ebinop .Oadd (.Etempvar ptrTemp tulong) (clong 8) tulong)
            (.Etempvar jTemp tulong) tulong)
          (.Vlong (UInt64.ofNat (p.toNat + 8 + j))) := by
        refine .eval_Ebinop _ _ _ _ _ _ _
          (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hp1) (.eval_Econst_long _ _)
            (sem_add_ll A m _ _)) (.eval_Etempvar _ _ _ hj1) ?_
        show sem_binary_operation A .Oadd (.Vlong _) tulong (.Vlong _) tulong m = _
        rw [sem_add_ll]
        congr 2
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_add, toNat_ofNat64 (by omega),
          toNat_ofNat64 (by omega), toNat_ofNat64 (by omega)]
        omega
      obtain ⟨m1, hstore, hs1, hc1⟩ := exec_byteStoreAt (X := X) hE cap haddr rfl hb1
        (by rw [toNat_ofNat64 (by omega)]; omega) hm.perm
      rw [toNat_ofNat64 (by omega), byte_inByteOf] at hc1
      have hm0 := MemRel.store_byte_at hE hm hs1 hc1
      have hm1 : MemRel E (withBytes wm (p.toNat + 8) (j + 1) (inMsgByte σ)) caps m1 := by
        rw [← withBytes_succ]
        exact hm0
      have hinc := eval_incr (A := A) (ge := E.ge) (m := m1) (by omega) hj1
      let le2 := le1.insert jTemp (.Vlong (UInt64.ofNat (j + 1)))
      obtain ⟨le', m', hrest, hm', hs', hother⟩ := exec_copyLoop hE cap hs hv σ hfit d (j + 1)
        le2 m1 (by omega) (te_insert_same _ _ _)
        (by simp only [le2]; rw [te_insert_ne _ jTemp_ne_nTemp]; exact hn1)
        (by simp only [le2]; rw [te_insert_ne _ jTemp_ne_ptrTemp]; exact hp1) hm1
      refine ⟨le', m', exec_trace (.exec_Sloop_loop _ _ _ _ _ _ le2 m1 .Out_normal E0 le2 m1 _ le'
        m' .Out_normal
        (.exec_Sseq_1 _ _ _ _ _ _ le m _ le2 m1 _
          (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond
            (by show bool_val _ tint m = _; simpa using bool_int m 1)
            (.exec_Sskip _ _ _))
          (.exec_Sseq_1 _ _ _ _ _ _ le1 m _ le2 m1 _ hload
            (.exec_Sseq_1 _ _ _ _ _ _ le1 m1 _ le2 m1 _ hstore (.exec_Sset _ _ _ _ _ _ hinc))))
        .Out_normal_or_continue_N (.exec_Sskip _ _ _) hrest) ?_, hm', hs1.trans hs', ?_⟩
      · rw [show 8 + (j + 1) = 8 + j + 1 by omega]
        simp [inTrace, inEvent, E0]
      · intro x h1 h2 h3
        rw [hother x h1 h2 h3]
        simp only [le2, le1]
        rw [te_insert_ne _ (Ne.symm h1), te_insert_ne _ (Ne.symm h2), te_insert_ne _ (Ne.symm h3)]

end

/-! ## The array of the message in the heap -/

section

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- The store after `main` writes the length word `w` at `p` and the `n` bytes `b 0` to
`b (n - 1)` from `p + 8`. -/
def inputStore (st : Store Unit) (p w : UInt64) (n : Nat) (b : Nat → UInt8) : Store Unit :=
  { st with mem := withBytes (st.mem.write64 p.toUInt32 w) (p.toNat + 8) n b }

theorem inputStore_memoryCap (st : Store Unit) (p w : UInt64) (n : Nat) (b : Nat → UInt8)
    (m : Module) (i : Nat) : (inputStore st p w n b).memoryCap m i = st.memoryCap m i := rfl

theorem allocateStore_memoryCap (heap : Heap) (st : Store Unit) (need s : UInt64) (m : Module)
    (i : Nat) : (heap.allocateStore st need s).memoryCap m i = st.memoryCap m i := by
  unfold Store.memoryCap
  rw [Heap.allocateStore_memoryCaps]

/-- The `w` words of the array at `p`, from `p + 8`. -/
def inputWords (st : Store Unit) (p : UInt64) (w : Nat) : Array UInt64 :=
  Array.ofFn (n := w) fun i => st.mem.read64 (p + UInt64.ofNat (8 * (i.val + 1))).toUInt32

/-- The number of words of a message of `n` bytes. -/
def wordsOf (n : Nat) : Nat := (n + 7) / 8

/-- The payload that `main` asks `alloc` for: the length word and the words. -/
def needOf (n : Nat) : UInt64 := allocSize (UInt64.ofNat (8 + 8 * wordsOf n))

theorem needOf_toNat {n : Nat} (hn : n ≤ inMax) : 8 + 8 * wordsOf n ≤ (needOf n).toNat := by
  have h := le_allocSize (bytes := UInt64.ofNat (8 + 8 * wordsOf n))
    (by rw [toNat_ofNat64 (by unfold wordsOf inMax at *; omega)]; unfold wordsOf inMax at *; omega)
  rwa [toNat_ofNat64 (by unfold wordsOf inMax at *; omega)] at h

/-- After the allocation of `needOf n` bytes and the writes of `main`, the allocator invariant
holds, the block holds an owned array of `wordsOf n` words, the writes lie inside the block,
and byte `i` of the array is `b i` for each `i < n`. -/
theorem input_owned {heap : Heap} {st : Store Unit} (hAt : heap.At st) {n : Nat}
    (hn : n ≤ inMax) (b : Nat → UInt8) (hFits : heap.Fits (needOf n)) :
    let p := FixedArrayAllocate.root heap.top (needOf n) heap.free
    let st' := inputStore (heap.allocateStore st (needOf n) 1) p
      (UInt64.ofNat (wordsOf n)) n b
    (heap.allocate (needOf n)).At st' ∧
      (heap.allocate (needOf n)).Owned st' p (inputWords st' p (wordsOf n)) ∧
      WritesWithin (heap.allocateStore st (needOf n) 1) st' p.toNat
        (allocatedCapacity (needOf n) heap.free).toNat ∧
      ∀ i < n, ((inputWords st' p (wordsOf n))[i / 8]! >>> UInt64.ofNat (8 * (i % 8))).toUInt8 =
        b i := by
  intro p st'
  have hBlock : (heap.allocate (needOf n)).Block (heap.allocateStore st (needOf n) 1) p
      (allocatedCapacity (needOf n) heap.free) 1 := hAt.allocate_block 1 hFits
  have hcap := allocated_capacity (needOf n) heap.free
  have hneed := needOf_toNat hn
  have hw : 8 + n ≤ 8 + 8 * wordsOf n := by unfold wordsOf; omega
  have haddr : p.toNat + (allocatedCapacity (needOf n) heap.free).toNat < 4294967296 :=
    hBlock.address
  have hp32 : p.toUInt32.toNat = p.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have hWrites : WritesWithin (heap.allocateStore st (needOf n) 1) st' p.toNat
      (allocatedCapacity (needOf n) heap.free).toNat := by
    refine ⟨rfl, rfl, fun a ha => ?_⟩
    show (withBytes _ _ _ _).bytes a = _
    simp only [withBytes]
    rw [ite_cond_eq_false _ _ (eq_false (by omega)),
      Memory.write64_bytes_outside _ _ _ (by rw [hp32]; omega)]
  refine ⟨(hAt.allocate 1 hFits).writesWithin hBlock hWrites, ?_, hWrites, ?_⟩
  · refine (hBlock.writesWithin hWrites).owned ⟨by simp [inputWords]; omega, ?_, ?_, ?_⟩
      (by simp [inputWords]; omega)
    · have : p.toNat + (allocatedCapacity (needOf n) heap.free).toNat ≤ st'.mem.pages * 65536 :=
        (hBlock.writesWithin hWrites).memory
      simp [inputWords]
      omega
    · show (withBytes _ _ _ _).read64 _ = _
      rw [Memory.read64_congr (m2 := (heap.allocateStore st (needOf n) 1).mem.write64 p.toUInt32
          (UInt64.ofNat (wordsOf n))) p.toUInt32 fun i hi => by
            simp only [withBytes]; rw [ite_cond_eq_false _ _ (eq_false (by omega))],
        Memory.read64_write64]
      simp [inputWords]
    · intro i hi
      simp only [inputWords, Array.getElem_ofFn]
      try rfl
  · intro i hi
    have hi8 : i / 8 < wordsOf n := by unfold wordsOf; omega
    have hsz : (inputWords st' p (wordsOf n)).size = wordsOf n := by simp [inputWords]
    rw [getElem!_pos (inputWords st' p (wordsOf n)) (i / 8) (by omega)]
    simp only [inputWords, Array.getElem_ofFn]
    have hq : (p + UInt64.ofNat (8 * (i / 8 + 1))).toUInt32.toNat = p.toNat + 8 + 8 * (i / 8) := by
      rw [Memory.toUInt32_toNat, UInt64.toNat_add, toNat_ofNat64 (by omega)]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [toUInt8_shift _ (by omega), ← bytes_read64 _ _ (by omega), hq]
    show (withBytes _ _ _ _).bytes _ = _
    simp only [withBytes]
    rw [ite_cond_eq_true _ _ (eq_true (by omega))]
    congr 1
    omega

end

/-! ## The statements around the loops -/

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem wordsOf_le {n : Nat} (hn : n ≤ inMax) : wordsOf n ≤ 2 ^ 21 := by
  unfold wordsOf inMax at *
  omega

/-- `(l3 + 7ULL) >> 3ULL`, the number of words of the array. -/
theorem eval_wordCount {le : temp_env} {m : mem} {n : UInt64}
    (hn : le[nTemp]? = some (.Vlong n)) (hlen : n.toNat ≤ inMax) :
    eval_expr A ge empty_env le m wordCount (.Vlong (UInt64.ofNat (wordsOf n.toNat))) := by
  have hadd : eval_expr A ge empty_env le m
      (.Ebinop .Oadd (.Etempvar nTemp tulong) (clong 7) tulong) (.Vlong (n + UInt64.ofNat 7)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hn) (.eval_Econst_long _ _)
      (sem_add_ll A m _ _)
  refine .eval_Ebinop _ _ _ _ _ _ _ hadd (.eval_Econst_long _ _)
    ((sem_shr_const A m _ 3 (by omega)).trans ?_)
  congr 2
  apply UInt64.toNat_inj.mp
  have : n.toNat + 7 < 2 ^ 64 := by unfold inMax at hlen; omega
  rw [UInt64.toNat_shiftRight, UInt64.toNat_add, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
    toNat_ofNat64 (by unfold wordsOf inMax at *; omega), Nat.mod_eq_of_lt this,
    Nat.shiftRight_eq_div_pow]
  unfold wordsOf
  norm_num

/-- `8ULL + wordCount * 8ULL`, the bytes that `main` asks `alloc` for. -/
theorem eval_allocArg {le : temp_env} {m : mem} {n : UInt64}
    (hn : le[nTemp]? = some (.Vlong n)) (hlen : n.toNat ≤ inMax) :
    eval_expr A ge empty_env le m
      (.Ebinop .Oadd (clong 8) (.Ebinop .Omul wordCount (clong 8) tulong) tulong)
      (.Vlong (UInt64.ofNat (8 + 8 * wordsOf n.toNat))) := by
  have hw := wordsOf_le hlen
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Econst_long _ _)
    (.eval_Ebinop _ _ _ _ _ _ _ (eval_wordCount hn hlen) (.eval_Econst_long _ _)
      (sem_mul_ll A m _ _)) ((sem_add_ll A m _ _).trans ?_)
  congr 2
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_mul, toNat_ofNat64 (n := 8) (by omega),
    toNat_ofNat64 (n := wordsOf n.toNat) (by omega),
    toNat_ofNat64 (n := 8 + 8 * wordsOf n.toNat) (by omega)]
  omega

theorem eval_tooLong {le : temp_env} {m : mem} {n : UInt64} (hn : le[nTemp]? = some (.Vlong n)) :
    eval_expr A ge empty_env le m (.Ebinop .Ogt (.Etempvar nTemp tulong) (clong inMax) tint)
      (.Vint (if inMax < n.toNat then 1 else 0)) := by
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hn) (.eval_Econst_long _ _) ?_
  show sem_binary_operation A .Ogt (.Vlong n) tulong (.Vlong (UInt64.ofNat inMax)) tulong m = _
  rw [sem_gt_ll]
  have e : (UInt64.ofNat inMax < n) ↔ inMax < n.toNat := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 (by unfold inMax; omega)]
  by_cases h : inMax < n.toNat <;> simp [e, h]

/-- `if (l3 > inMax) return (int) 64U;` for a length above `inMax`. -/
theorem exec_tooLong {le : temp_env} {m : mem} {n : UInt64} (hn : le[nTemp]? = some (.Vlong n))
    (h : inMax < n.toNat) :
    exec_stmt A X ge empty_env le m tooLongTest E0 le m
      (.Out_return (some (.Vint (UInt32.ofNat inTooLong), tint))) := by
  have hc := eval_tooLong (A := A) (ge := ge) (m := m) hn
  rw [ite_cond_eq_true _ _ (eq_true h)] at hc
  exact .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc
    (by show bool_val _ tint m = _; simpa using bool_int m 1)
    (.exec_Sreturn_some _ _ _ _ _ (.eval_Ecast _ _ _ _ (.eval_Econst_int _ _) rfl))

/-- The test of the length for a length of at most `inMax`. -/
theorem exec_notTooLong {le : temp_env} {m : mem} {n : UInt64} (hn : le[nTemp]? = some (.Vlong n))
    (h : n.toNat ≤ inMax) :
    exec_stmt A X ge empty_env le m tooLongTest E0 le m .Out_normal := by
  have hc := eval_tooLong (A := A) (ge := ge) (m := m) hn
  rw [ite_cond_eq_false _ _ (eq_false (by omega))] at hc
  exact .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc
    (by show bool_val _ tint m = _; simpa using bool_int m 0) (.exec_Sskip _ _ _)

/-- `l4 = lxf_0(8ULL + wordCount * 8ULL);`. -/
theorem exec_allocCall {le : temp_env} {m m' : mem} {fA : function} {bA : block} {n : UInt64}
    {vres : val} (hs : Genv.find_symbol ge (funId 0) = some bA)
    (hf : Genv.find_funct_ptr ge bA = some (.Internal fA))
    (hty : type_of_function fA = .Tfunction [tulong] tulong cc_default)
    (hn : le[nTemp]? = some (.Vlong n)) (hlen : n.toNat ≤ inMax)
    (hcall : eval_funcall A X ge m (.Internal fA)
      [.Vlong (UInt64.ofNat (8 + 8 * wordsOf n.toNat))] E0 m' vres) :
    exec_stmt A X ge empty_env le m allocCall E0
      ((le.insert allocTemp vres).insert ptrTemp vres) m' .Out_normal :=
  exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (.exec_Scall _ _ _ (some allocTemp) _ _ _ _ _ (.Vptr bA Ptrofs.zero) _ (.Internal fA) _ m'
      vres rfl (.eval_Elvalue _ _ _ _ _ (eval_lvalue_global hs) (.deref_loc_reference rfl))
      (.eval_Econs _ _ _ _ _ _ _ (eval_allocArg hn hlen) rfl .eval_Enil)
      (by simp [Genv.find_funct, hf]) hty hcall)
    (.exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)))) (by simp [E0])

/-- The call of the entry on the array's address and the length: `l0` holds the result for a
kind other than `words`. -/
theorem exec_inEntry (k : Nat) (kind : OutKind) {fd : function} {bk : block}
    (hsk : Genv.find_symbol ge (funId k) = some bk)
    (hfk : Genv.find_funct_ptr ge bk = some (.Internal fd))
    (htyk : type_of_function fd = .Tfunction [tulong, tulong] (outRet kind) cc_default)
    {le : temp_env} {m1 m' : mem} {vres : val} {p n : UInt64}
    (hp : le[ptrTemp]? = some (.Vlong p)) (hn : le[nTemp]? = some (.Vlong n))
    (hcall : eval_funcall A X ge m1 (.Internal fd) [.Vlong p, .Vlong n] E0 m' vres) :
    ∃ le2, exec_stmt A X ge empty_env le m1 (inEntry kind k) E0 le2 m' .Out_normal ∧
      (outRet kind = tulong → le2[resTemp]? = some vres) := by
  have hargs : eval_exprlist A ge empty_env le m1
      [.Etempvar ptrTemp tulong, .Etempvar nTemp tulong] [tulong, tulong] [.Vlong p, .Vlong n] :=
    .eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hp) rfl
      (.eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hn) rfl .eval_Enil)
  have hfn : eval_expr A ge empty_env le m1 (.Evar (funId k) (.Tfunction [tulong, tulong]
      (outRet kind) cc_default)) (.Vptr bk Ptrofs.zero) :=
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hsk) (.deref_loc_reference rfl)
  cases kind with
  | words _ =>
      exact ⟨le, .exec_Scall _ _ _ none _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _ m'
        vres rfl hfn hargs (by simp [Genv.find_funct, hfk]) htyk hcall, fun h => nomatch h⟩
  | word =>
      exact ⟨_, exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
        (.exec_Scall _ _ _ (some inCallTemp) _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _
          m' vres rfl hfn hargs (by simp [Genv.find_funct, hfk]) htyk hcall)
        (.exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)))) (by simp [E0]),
        fun _ => te_insert_same _ _ _⟩
  | array =>
      exact ⟨_, exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
        (.exec_Scall _ _ _ (some inCallTemp) _ _ _ _ _ (.Vptr bk Ptrofs.zero) _ (.Internal fd) _
          m' vres rfl hfn hargs (by simp [Genv.find_funct, hfk]) htyk hcall)
        (.exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)))) (by simp [E0]),
        fun _ => te_insert_same _ _ _⟩

end

/-! ## The program with input -/

section

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem nTemp_ne_ptrTemp : nTemp ≠ ptrTemp := by decide
theorem nTemp_ne_allocTemp : nTemp ≠ allocTemp := by decide
theorem ptrTemp_ne_jTemp : ptrTemp ≠ jTemp := by decide

/-- The trace and the result of the program with input for the input `σ`: the eight loads of
the length and the result 64 for a length above `inMax`; the eight loads and the code of
`unreachable` when `alloc` traps; the loads of the length and of the message and the code of
`unreachable` when the entry may abort and traps; and otherwise the loads, the stores of
`out n b` for the length `n` and the bytes `b` of the message, and the result 0. -/
def InResult (σ : Nat → int) (aborts : Bool) (out : Nat → (Nat → UInt8) → List UInt8)
    (t : trace) (r : int) : Prop :=
  (inMax < (inLen σ).toNat ∧ r = UInt32.ofNat inTooLong ∧ t = inTrace σ 0 8) ∨
  ((inLen σ).toNat ≤ inMax ∧
    ((r = UInt32.ofNat trapUnreachable ∧ t = inTrace σ 0 8) ∨
      (aborts = true ∧ r = UInt32.ofNat trapUnreachable ∧
        t = inTrace σ 0 (8 + (inLen σ).toNat)) ∨
      (r = 0 ∧ t = inTrace σ 0 (8 + (inLen σ).toNat) ++
        outTrace (out (inLen σ).toNat (inMsgByte σ)))))

/-- The call of the entry `fd` on the array that `main` builds from the heap `heap` for each
length `n` and bytes `b`, in every environment that meets the hypotheses of `NativeA`, from every
memory related to the store after `main`'s writes with `lx_status` 0: it returns with
`lx_status` 0 and a result that gives the bytes `out n b`, or, when `aborts`, it ends with
`lx_status` holding the code of `unreachable`. -/
def EntryInRuns (A : Archi) (X : ExtSem) (cap : Nat) (m : Wasm.Module) (T : Translation)
    (fd : function) (kind : OutKind) (aborts : Bool) (heap : Heap)
    (out : Nat → (Nat → UInt8) → List UInt8) : Prop :=
  ∀ n, n ≤ inMax → heap.Fits (needOf n) → ∀ b : Nat → UInt8,
    ∀ E : Env, EnvOk E → E.globals.length = m.globals.length → E.cap = cap →
      T.nres ≤ E.nres →
      (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
        ∃ bk, Genv.find_symbol E.ge (funId k) = some bk ∧
          Genv.find_funct_ptr E.ge bk = some (.Internal fd)) →
      ∀ m1, StoreRel E (inputStore (heap.allocateStore (nativeStore m cap) (needOf n) 1)
          (FixedArrayAllocate.root heap.top (needOf n) heap.free) (UInt64.ofNat (wordsOf n)) n b)
          m1 →
        StatusRel E m1 0 →
        ∃ t m' vres st', eval_funcall A X E.ge m1 (.Internal fd)
            [.Vlong (FixedArrayAllocate.root heap.top (needOf n) heap.free),
              .Vlong (UInt64.ofNat n)] t m' vres ∧
          StoreRel E st' m' ∧
          ((StatusRel E m' 0 ∧ OutOk E kind st' m' vres (out n b)) ∨
            (aborts = true ∧ StatusRel E m' trapUnreachable))

/-- The program with input of a translation, for every input `σ`, terminates with a trace and a
result that `InResult` describes, given the run of the entry that `EntryInRuns` states.  The
module's function 0 is `alloc`, and `heap` is the heap of the store in which the translation
starts. -/
theorem input_program {m : Wasm.Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) {pre : List (ident × globdef (fundef function) type)}
    (hpre : PrefixOk pre) {typeIdx : Nat} (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (h0 : 0 ∈ T.funcs) {k : Nat} {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs) (kind : OutKind)
    (hty : type_of_function fd = .Tfunction [tulong, tulong] (outRet kind) cc_default)
    (A : Archi) (X : ExtSem) {aborts : Bool} {heap : Heap}
    (hheap : heap.At (nativeStore m cap)) (hcapS : (nativeStore m cap).memoryCap m 0 ≤ 65535)
    {out : Nat → (Nat → UInt8) → List UInt8}
    (hruns : EntryInRuns A X cap m T fd kind aborts heap out) (σ : Nat → int) :
    ∃ t r, bigstep_program_terminates A X (inProgram pre T (inMain cap k kind)) t r ∧
      InResult σ aborts out t r := by
  have hw := wholeOk_in h hpre.sqrt hpre.funs hpre.nodup hpre.ids (inMain cap k kind)
  obtain ⟨decl, m0, m1, -, hinit, hmemi, hcalli, hst1, hs1, hE, hG, hcap, hnres, hF⟩ :=
    start_whole h hw A X
  set E := envWhole pre (inTail (inMain cap k kind)) T m.globals.length cap with hEdef
  have hidp : ∀ x : Nat, x ∈ (inTail (inMain cap k kind)).map (·.1) →
      x = 4 ∨ x = 28 ∨ x = 32 := by
    intro x hx
    simp only [inTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx | hx
    · have : x = 32 := hx; omega
    · have : x = 28 := hx; omega
    · have : x = 4 := hx; omega
  have hq := genvQuiet_whole h hw hpre.ids hidp
  obtain ⟨bi, hsi, hdi⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (inMain cap k kind)) T) hw.nodup hmemi
  obtain ⟨bo, hso, hdo⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (inMain cap k kind)) T) hw.nodup
    (d := .Gvar outVar) (id := outId) (by simp [wholeDefs, inTail])
  obtain ⟨bn, hsn, hdn⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (inMain cap k kind)) T) hw.nodup
    (d := .Gvar inVar) (id := inId) (by simp [wholeDefs, inTail])
  obtain ⟨bm, hsm, hdm⟩ := Genv.find_add_globals (Genv.empty_genv [])
    (wholeDefs pre (inTail (inMain cap k kind)) T) hw.nodup
    (d := .Gfun (.Internal (inMain cap k kind))) (id := mainId) (by simp [wholeDefs, inTail])
  have hvo : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (inTail (inMain cap k kind)) T)) bo = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdo, outVar]
  have hvn : Genv.block_is_volatile (Genv.add_globals (Genv.empty_genv [])
      (wholeDefs pre (inTail (inMain cap k kind)) T)) bn = true := by
    simp [Genv.block_is_volatile, Genv.find_var_info, hdn, inVar]
  obtain ⟨bk, hsk, hfk⟩ := hF k fd hfd
  -- `main` from its entry: the call of `lx_init`, and the loop that reads the length.
  let le0 := create_undef_temps (inTemps kind)
  have hentry : function_entry2 (inMain cap k kind) [] m0 empty_env le0 m0 :=
    .intro le0 rfl List.nodup_nil (by simp [var_names, inMain]) rfl
  let L1 : List statement := [initCall, .Sset nTemp (clong 0), .Sset jTemp (clong 0), lenLoop]
  let L2 : List statement := tooLongTest :: allocCall :: statusTest :: .Sset byteTemp wordCount ::
    lengthWord cap :: .Sset jTemp (clong 0) :: copyLoop cap :: inEntry kind k :: statusTest ::
    outStmts cap kind
  have hbody : inBody cap k kind = seqList (L1 ++ L2) := rfl
  have hret : ∀ {t : trace} {le' : temp_env} {m' : mem} (r : int),
      exec_stmt A X E.ge empty_env le0 m0 (seqList (L1 ++ L2)) t le' m'
        (.Out_return (some (.Vint r, tint))) →
      bigstep_program_terminates A X (inProgram pre T (inMain cap k kind)) t r := by
    intro t le' m' r hb
    rw [← hbody] at hb
    exact .bigstep_program_terminates_intro bm _ m0 m' _ r hinit hsm
      (Genv.find_funct_ptr_of_def hdm) rfl
      (.eval_funcall_internal _ _ _ _ _ le0 le' m0 m' _ _ m' hentry
        (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ hb (by simp)) ⟨(fun h => by cases h), rfl⟩ rfl)
  have hnorm : ∀ {t : trace} {le' : temp_env} {m' : mem},
      exec_stmt A X E.ge empty_env le0 m0 (seqList (L1 ++ L2)) t le' m' .Out_normal →
      bigstep_program_terminates A X (inProgram pre T (inMain cap k kind)) t 0 := by
    intro t le' m' hb
    rw [← hbody] at hb
    exact .bigstep_program_terminates_intro bm _ m0 m' _ 0 hinit hsm
      (Genv.find_funct_ptr_of_def hdm) rfl
      (.eval_funcall_internal _ _ _ _ _ le0 le' m0 m' _ _ m' hentry
        (exec_trace (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hb
          (.exec_Sreturn_some _ _ _ _ _ (.eval_Econst_int _ _))) (by simp [E0]))
        ⟨(fun h => by cases h), rfl⟩ rfl)
  have hc1 := exec_initCall (X := X) (le := le0) hsi (Genv.find_funct_ptr_of_def hdi) rfl hcalli
  let le0a := le0.insert nTemp (.Vlong (UInt64.ofNat 0))
  let le0b := le0a.insert jTemp (.Vlong (UInt64.ofNat 0))
  have hsetn : exec_stmt A X E.ge empty_env le0 m1 (.Sset nTemp (clong 0)) E0 le0a m1
      .Out_normal := .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  have hsetj : exec_stmt A X E.ge empty_env le0a m1 (.Sset jTemp (clong 0)) E0 le0b m1
      .Out_normal := .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  obtain ⟨le1, hlenX, hn1, -⟩ := exec_lenLoop (X := X) (m := m1) hsn hvn σ 8 0 le0b (by omega)
    (by simp only [le0b, le0a]
        rw [te_insert_ne _ (Ne.symm nTemp_ne_jTemp), te_insert_same]
        rfl)
    (te_insert_same _ _ _)
  have hpre1 : exec_stmt A X E.ge empty_env le0 m0 (seqList L1)
      (E0 ++ (E0 ++ (E0 ++ inTrace σ 0 8))) le1 m1 .Out_normal :=
    exec_seqList_cons (by simp) hc1 (exec_seqList_cons (by simp) hsetn
      (exec_seqList_cons (by simp) hsetj hlenX))
  set n := inLen σ with hn
  by_cases hlong : inMax < n.toNat
  · -- The length exceeds `inMax`.
    refine ⟨_, _, hret _ (exec_seqList_append L1 L2 hpre1
      (exec_seqList_stop (exec_tooLong hn1 hlong) (by simp))),
      .inl ⟨hlong, rfl, by simp [E0]⟩⟩
  have hlen : n.toNat ≤ inMax := by omega
  have hntl := exec_notTooLong (A := A) (X := X) (ge := E.ge) (m := m1) hn1 hlen
  -- The call of `alloc`.
  have hw21 := wordsOf_le hlen
  have hbytes : (UInt64.ofNat (8 + 8 * wordsOf n.toNat)).toNat ≤ 4294967296 := by
    rw [toNat_ofNat64 (by omega)]
    omega
  obtain ⟨fA, hfA, tA, mA, vA, stA, hcallA, hstA, hresA⟩ := alloc_native (A := A) (X := X) h
    hFunc h0 hE hG hcap hnres hF heap (nativeStore m cap)
    (UInt64.ofNat (8 + 8 * wordsOf n.toNat)) hheap hbytes hcapS m1 hst1 hs1
  obtain ⟨bA, hsA, hfA'⟩ := hF 0 fA hfA
  have htA : tA = E0 := funcall_quiet hq hcallA (translation_fun_quiet h hfA (by decide))
  subst htA
  have htyA : type_of_function fA = .Tfunction [tulong] tulong cc_default := by
    have e := entry_type h hfA (ps := [.i64]) (rs := [.i64]) (fun g hg => by
      rw [hFunc] at hg
      cases hg
      rfl)
    rw [e]
    exact funType_i64 [0]
  have hallocX := exec_allocCall (X := X) (le := le1) hsA hfA' htyA hn1 hlen hcallA
  rcases hresA with ⟨hsA0, hFits, rfl, rfl⟩ | hsAtrap
  swap
  · -- `alloc` traps.
    refine ⟨_, _, hret _ (exec_seqList_append L1 L2 hpre1 (exec_seqList_cons (by simp) hntl
      (exec_seqList_cons (by simp) hallocX (exec_seqList_stop
        (exec_statusTest_trap (A := A) (X := X) hE hsAtrap (by decide) (by decide)) (by simp))))),
      .inr ⟨hlen, .inl ⟨rfl, by simp [E0]⟩⟩⟩
  -- The allocation succeeds: the length word and the copy of the message.
  have hFits' : heap.Fits (needOf n.toNat) := hFits
  let p := FixedArrayAllocate.root heap.top (needOf n.toNat) heap.free
  let le2 := (le1.insert allocTemp (.Vlong p)).insert ptrTemp (.Vlong p)
  have hstat := exec_statusTest_ok (A := A) (X := X) (le := le2) hE hsA0
  have hle2n : le2[nTemp]? = some (.Vlong n) := by
    simp only [le2]
    rw [te_insert_ne _ (Ne.symm nTemp_ne_ptrTemp), te_insert_ne _ (Ne.symm nTemp_ne_allocTemp)]
    exact hn1
  have hwc := eval_wordCount (A := A) (ge := E.ge) (m := mA) hle2n hlen
  let le3 := le2.insert byteTemp (.Vlong (UInt64.ofNat (wordsOf n.toNat)))
  have hsetb : exec_stmt A X E.ge empty_env le2 mA (.Sset byteTemp wordCount) E0 le3 mA
      .Out_normal := .exec_Sset _ _ _ _ _ _ hwc
  have hBlock : (heap.allocate (needOf n.toNat)).Block
      (heap.allocateStore (nativeStore m cap) (needOf n.toNat) 1) p
      (allocatedCapacity (needOf n.toNat) heap.free) 1 := hheap.allocate_block 1 hFits'
  have hcapA := allocated_capacity (needOf n.toNat) heap.free
  have hneed := needOf_toNat hlen
  have hpages : (heap.allocateStore (nativeStore m cap) (needOf n.toNat) 1).mem.pages ≤ E.cap :=
    hstA.2.le_cap
  have hmemA : p.toNat + (allocatedCapacity (needOf n.toNat) heap.free).toNat ≤
      (heap.allocateStore (nativeStore m cap) (needOf n.toNat) 1).mem.pages * 65536 :=
    hBlock.memory
  have haddrA : p.toNat + (allocatedCapacity (needOf n.toNat) heap.free).toNat < 4294967296 :=
    hBlock.address
  have hwn : 8 + n.toNat ≤ 8 + 8 * wordsOf n.toNat := by unfold wordsOf; omega
  have hfit : p.toNat + 8 + n.toNat ≤ 65536 * E.cap := by omega
  have hp3 : le3[ptrTemp]? = some (.Vlong p) := by
    simp only [le3, le2]
    rw [te_insert_ne _ (Ne.symm ptrTemp_ne_byteTemp)]
    exact te_insert_same _ _ _
  have hb3 : le3[byteTemp]? = some (.Vlong (UInt64.ofNat (wordsOf n.toNat))) :=
    te_insert_same _ _ _
  obtain ⟨mB, hstoreB, hsameB, hcB⟩ := exec_storeBytes (A := A) (X := X) hE cap
    (t := ptrTemp) (vid := byteTemp) hp3 hb3 7 0 mA (by omega) (by omega) hstA.2.perm
  have hmB := MemRel.store_bytes hE hstA.2 hsameB hcB p.toUInt32
    (by rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)])
  let le4 := le3.insert jTemp (.Vlong (UInt64.ofNat 0))
  have hsetj2 : exec_stmt A X E.ge empty_env le3 mB (.Sset jTemp (clong 0)) E0 le4 mB
      .Out_normal := .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  have hle4n : le4[nTemp]? = some (.Vlong n) := by
    simp only [le4, le3]
    rw [te_insert_ne _ (Ne.symm nTemp_ne_jTemp), te_insert_ne _ (Ne.symm nTemp_ne_byteTemp)]
    exact hle2n
  have hle4p : le4[ptrTemp]? = some (.Vlong p) := by
    simp only [le4]
    rw [te_insert_ne _ (Ne.symm ptrTemp_ne_jTemp)]
    exact hp3
  obtain ⟨le5, mC, hcopy, hmC, hsameC, hother5⟩ := exec_copyLoop (A := A) (X := X) hE cap hsn
    hvn σ (wm := (heap.allocateStore (nativeStore m cap) (needOf n.toNat) 1).mem.write64 p.toUInt32
      (UInt64.ofNat (wordsOf n.toNat))) hfit n.toNat 0 le4 mB (by omega) (te_insert_same _ _ _)
    hle4n hle4p (by rw [withBytes_zero]; exact hmB)
  have hstC : StoreRel E (inputStore (heap.allocateStore (nativeStore m cap) (needOf n.toNat) 1) p
      (UInt64.ofNat (wordsOf n.toNat)) n.toNat (inMsgByte σ)) mC :=
    ⟨GlobalsRel.sameExcept hstA.1 (hsameB.trans hsameC) hE.mem_not, hmC⟩
  have hsC : StatusRel E mC 0 := hsA0.sameExcept (hsameB.trans hsameC) (Ne.symm hE.mem_status)
  -- The call of the entry.
  obtain ⟨tE, mE, vE, stE, hcallE, hstE, hresE⟩ := hruns n.toNat hlen hFits' (inMsgByte σ) E hE
    hG hcap hnres hF mC hstC hsC
  have htE : tE = E0 := funcall_quiet hq hcallE (translation_fun_quiet h hfd (by
    show (4 * k + 3) % 4 = 3; omega))
  subst htE
  rw [UInt64.ofNat_toNat] at hcallE
  have hle5p : le5[ptrTemp]? = some (.Vlong p) := by
    rw [hother5 ptrTemp (by decide) (by decide) (by decide)]
    exact hle4p
  have hle5n : le5[nTemp]? = some (.Vlong n) := by
    rw [hother5 nTemp (by decide) (by decide) (by decide)]
    exact hle4n
  obtain ⟨le6, hentryX, hr6⟩ := exec_inEntry (X := X) k kind hsk hfk hty hle5p hle5n hcallE
  rcases hresE with ⟨hsE0, hout⟩ | ⟨hab, hsEtrap⟩
  · -- The entry returns: the output.
    obtain ⟨le7, hout7⟩ := exec_outStmts (A := A) (X := X) hE hstE.2 cap kind hso hvo hr6 hout
    have t9 := exec_seqList_append [statusTest] _ (exec_statusTest_ok (A := A) (X := X) hE hsE0)
      hout7
    have t8 := exec_seqList_cons (by simp) hentryX t9
    have t7 := exec_seqList_cons (by simp) hcopy t8
    have t6 := exec_seqList_cons (by simp) hsetj2 t7
    have t5 := exec_seqList_cons (by simp) hstoreB t6
    have t4 := exec_seqList_cons (by simp) hsetb t5
    have t3 := exec_seqList_cons (by simp) hstat t4
    have t2 := exec_seqList_cons (by simp) hallocX t3
    have t1 := exec_seqList_cons (by simp) hntl t2
    refine ⟨_, _, hnorm (exec_seqList_append L1 L2 hpre1 t1),
      .inr ⟨hlen, .inr (.inr ⟨rfl, ?_⟩)⟩⟩
    rw [← hn]
    simp [E0, inTrace_add]
  · -- The entry traps.
    have t8 := exec_seqList_cons (by simp) hentryX (exec_seqList_stop (l := outStmts cap kind)
      (exec_statusTest_trap (A := A) (X := X) hE hsEtrap (by decide) (by decide)) (by simp))
    have t7 := exec_seqList_cons (by simp) hcopy t8
    have t6 := exec_seqList_cons (by simp) hsetj2 t7
    have t5 := exec_seqList_cons (by simp) hstoreB t6
    have t4 := exec_seqList_cons (by simp) hsetb t5
    have t3 := exec_seqList_cons (by simp) hstat t4
    have t2 := exec_seqList_cons (by simp) hallocX t3
    have t1 := exec_seqList_cons (by simp) hntl t2
    refine ⟨_, _, hret _ (exec_seqList_append L1 L2 hpre1 t1),
      .inr ⟨hlen, .inr (.inl ⟨hab, rfl, ?_⟩)⟩⟩
    rw [← hn]
    simp [E0, inTrace_add]

end

/-! ## The values that the trace reads -/

def isVload : event → Bool
  | .Event_vload _ _ _ _ => true
  | _ => false

/-- The number of volatile loads of `t`. -/
def countVloads (t : trace) : Nat := (t.filter isVload).length

/-- `reads` of `rocq/Clight2Asm.v`: the trace `t` has no system call, and its `k`-th volatile
load reads `EVint (σ k)`. -/
def Reads (σ : Nat → int) (t : trace) : Prop :=
  ∀ tp ev u, t = tp ++ ev :: u →
    match ev with
    | .Event_syscall _ _ _ => False
    | .Event_vload _ _ _ v => v = .EVint (σ (countVloads tp))
    | _ => True

theorem countVloads_cons_inEvent (a : Nat) (v : int) (t : trace) :
    countVloads (inEvent a v :: t) = countVloads t + 1 := by
  simp [countVloads, inEvent, isVload, List.filter_cons]

theorem reads_inTrace_aux (σ : Nat → int) (rest : trace)
    (hrest : ∀ e ∈ rest, ∃ c i o v, e = .Event_vstore c i o v) :
    ∀ (d a : Nat) (tp : trace) (ev : event) (u : trace),
      inTrace σ a d ++ rest = tp ++ ev :: u →
      match ev with
      | .Event_syscall _ _ _ => False
      | .Event_vload _ _ _ v => v = .EVint (σ (a + countVloads tp))
      | _ => True
  | 0, a, tp, ev, u, h => by
      simp only [inTrace, List.nil_append] at h
      have hmem : ev ∈ rest := by rw [h]; simp
      obtain ⟨c, i, o, v, rfl⟩ := hrest ev hmem
      trivial
  | d + 1, a, [], ev, u, h => by
      simp only [inTrace, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [inEvent, countVloads]
  | d + 1, a, e :: tp, ev, u, h => by
      simp only [inTrace, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have ih := reads_inTrace_aux σ rest hrest d (a + 1) tp ev u h
      rw [countVloads_cons_inEvent]
      split at ih <;> simp_all [Nat.add_assoc, Nat.add_comm 1]

/-- A trace of the loads of the first `c` offsets followed by stores to `lx_out` reads `σ`. -/
theorem reads_inTrace (σ : Nat → int) (c : Nat) (bs : List UInt8) :
    Reads σ (inTrace σ 0 c ++ outTrace bs) := by
  intro tp ev u h
  have := reads_inTrace_aux σ (outTrace bs) (fun e he => by
    simp only [outTrace, List.mem_map] at he
    obtain ⟨b, -, rfl⟩ := he
    exact ⟨_, _, _, _, rfl⟩) c 0 tp ev u h
  simpa using this

theorem reads_inTrace_nil (σ : Nat → int) (c : Nat) : Reads σ (inTrace σ 0 c) := by
  have := reads_inTrace σ c []
  simpa [outTrace] using this

theorem InResult.reads {σ : Nat → int} {aborts : Bool}
    {out : Nat → (Nat → UInt8) → List UInt8} {t : trace} {r : int}
    (h : InResult σ aborts out t r) : Reads σ t := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩
  · exact reads_inTrace_nil σ 8
  · exact reads_inTrace_nil σ 8
  · exact reads_inTrace_nil σ _
  · exact reads_inTrace σ _ _

end LeanExe.Native
