import LeanExe.Native.Proof.MemBytes
import LeanExe.Native.Proof.Control

/-!
The simulation of the memory instructions.  `MemRel` survives a change of memory that keeps the
blocks of the globals, `lx_status`, and `lx_pages` (`SameExcept`), and the stores that `store64`
and `memory.grow` perform carry it to Talos's new memory.  `load64` and `store64` compute the
address in the slot of their address with `addrStmt`, trap with `boundsCheck` when the eight
bytes do not lie below `lx_pages × 65536`, and then access one word of `lx_mem` when the address
is a multiple of 8 and eight bytes otherwise; `lbval` is the value that `loadBytes` combines,
which is `Mem.read64`.  Each `sim_` lemma states `InstrSim` for one instruction.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## The relation under changes of memory -/

theorem GlobalsRel.sameExcept {E : Env} {gs : List Value} {m m' : mem} {b : block}
    (h : GlobalsRel E gs m) (hs : Mem.SameExcept b m m') (hb : b ∉ E.globals) :
    GlobalsRel E gs m' := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨n, hn, hl, hv⟩ := h.2 i hi
  have hne : E.globals[i] ≠ b := fun e => hb (e ▸ List.getElem_mem hi)
  exact ⟨n, hn, by rw [hs.load_eq hne]; exact hl, by rw [hs.valid_access_eq]; exact hv⟩

theorem StatusRel.sameExcept {E : Env} {m m' : mem} {b : block} {k : Nat} (h : StatusRel E m k)
    (hs : Mem.SameExcept b m m') (hb : E.status ≠ b) : StatusRel E m' k :=
  ⟨by rw [hs.load_eq hb]; exact h.1, by rw [hs.valid_access_eq]; exact h.2⟩

/-- A change of the contents of `lx_mem` that holds the bytes of a Talos memory of the same
pages. -/
theorem MemRel.of_contents {E : Env} {wm wm' : Wasm.Mem} {caps : List Nat} {m m' : mem}
    (hE : EnvOk E) (h : MemRel E wm caps m) (hs : Mem.SameExcept E.mem m m')
    (hp : wm'.pages = wm.pages)
    (hb : ∀ i : Nat, i < 65536 * E.cap →
      ZMap.get (i : _root_.Int) (Mem.contents_of m' E.mem) = .Byte (wm'.bytes i)) :
    MemRel E wm' caps m' where
  pages := by rw [hs.load_eq (fun e => hE.mem_pages e.symm), hp]; exact h.pages
  pagesW := by rw [hs.valid_access_eq]; exact h.pagesW
  le_cap := hp ▸ h.le_cap
  memCap := h.memCap
  bytes := hb
  perm := fun i hi => by rw [hs.perm_eq]; exact h.perm i hi

/-- `lx_pages` set to `p`, the pages of a grown memory. -/
theorem MemRel.grow {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m : mem} (hE : EnvOk E)
    (h : MemRel E wm caps m) (p : Nat) (hp : p ≤ E.cap) :
    MemRel E { wm with pages := p } caps (Mem.stored .Mint32 m E.pages 0 (.Vint (UInt32.ofNat p))) where
  pages := Mem.load_stored_int _ _ _ _ h.pagesW
  pagesW := h.pagesW
  le_cap := hp
  memCap := h.memCap
  bytes := fun i hi => by
    rw [Mem.contents_stored_other _ _ _ _ _ _ (fun e => hE.mem_pages e.symm)]; exact h.bytes i hi
  perm := h.perm

theorem MemRel.valid_byte {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {i : Nat} (hi : i < 65536 * E.cap) :
    Mem.valid_access m .Mint8unsigned E.mem i .Writable := by
  refine ⟨fun ofs h1 h2 => ?_, ⟨i, by simp [align_chunk]⟩⟩
  have h2' : ofs < (i : _root_.Int) + 1 := h2
  have : ofs = (i : _root_.Int) := by omega
  subst this
  exact h.perm i hi

theorem MemRel.valid_word {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {i : Nat} (hi : i + 8 ≤ 65536 * E.cap) (hal : i % 8 = 0) :
    Mem.valid_access m .Mint64 E.mem i .Writable := by
  refine ⟨fun ofs h1 h2 => ?_, ?_⟩
  · have h2' : ofs < (i : _root_.Int) + 8 := h2
    have hofs : ofs = ((ofs.toNat : Nat) : _root_.Int) := by omega
    rw [hofs]
    exact h.perm _ (by omega)
  · show (8 : _root_.Int) ∣ (i : _root_.Int)
    exact Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hal)

theorem MemRel.load_byte {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {i : Nat} (hi : i < 65536 * E.cap) :
    Mem.load .Mint8unsigned m E.mem i = some (.Vint (UInt32.ofNat (wm.bytes i).toNat)) := by
  unfold Mem.load
  rw [ite_eq_left (Mem.valid_access_readable (h.valid_byte hi))]
  show some (decode_val .Mint8unsigned [ZMap.get (i : _root_.Int) (Mem.contents_of m E.mem)]) = _
  rw [h.bytes i hi, decode_byte]

theorem MemRel.load_word {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) (a : UInt32) (hi : a.toNat + 8 ≤ 65536 * E.cap)
    (hal : a.toNat % 8 = 0) :
    Mem.load .Mint64 m E.mem a.toNat = some (.Vlong (wm.read64 a)) := by
  unfold Mem.load
  rw [ite_eq_left (Mem.valid_access_readable (h.valid_word hi hal)),
    show size_chunk_nat .Mint64 = 8 from rfl, Mem.getN_map]
  have e : ((List.range 8).map fun (j : Nat) =>
      ZMap.get ((a.toNat : _root_.Int) + (j : _root_.Int)) (Mem.contents_of m E.mem)) =
      inj_bytes ((List.range 8).map fun j => wm.bytes (a.toNat + j)) := by
    simp only [inj_bytes, List.map_map]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [Function.comp]
    rw [show (a.toNat : _root_.Int) + (j : _root_.Int) = ((a.toNat + j : Nat) : _root_.Int) by
      push_cast; rfl, h.bytes _ (by omega)]
  rw [e]
  simp only [decode_val, Mem.proj_inj_bytes, decode_int]
  rw [read64_eq_word]

theorem encode_long_get (x : UInt64) (j : Nat) (hj : j < 8) :
    (encode_val .Mint64 (.Vlong x))[j]'(by rw [Mem.length_encode_long]; exact hj) =
      .Byte (nbyte x.toNat j) := by
  simp only [encode_val, inj_bytes, encode_int, Int64.unsigned, bytes_of_int_nat]
  simp

theorem MemRel.store_word {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m : mem} (hE : EnvOk E)
    (h : MemRel E wm caps m) (a : UInt32) (x : UInt64) :
    MemRel E (wm.write64 a x) caps (Mem.stored .Mint64 m E.mem a.toNat (.Vlong x)) := by
  refine h.of_contents hE (Mem.SameExcept.of_stored _ _ _ _ _) rfl fun i hi => ?_
  rw [Mem.contents_stored_same]
  by_cases hin : a.toNat ≤ i ∧ i < a.toNat + 8
  · obtain ⟨j, rfl⟩ : ∃ j, i = a.toNat + j := ⟨i - a.toNat, by omega⟩
    have hj : j < 8 := by omega
    rw [show ((a.toNat + j : Nat) : _root_.Int) = (a.toNat : _root_.Int) + (j : _root_.Int) by
      push_cast; rfl, Mem.setN_at _ _ _ j (by rw [Mem.length_encode_long]; exact hj),
      encode_long_get x j hj, write64_bytes_at _ _ _ j hj]
  · rw [LeanExe.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)]
    rcases Nat.lt_or_ge i a.toNat with hlt | hge
    · rw [Mem.setN_outside _ _ _ _ (by omega)]; exact h.bytes i hi
    · rw [Mem.setN_above _ _ _ _ (by rw [Mem.length_encode_long]; push_cast; omega)]
      exact h.bytes i hi


/-! ## Expressions -/

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; exact h)

section

variable (A : Archi) (m : mem)

theorem sem_shr_const (x : UInt64) (k : Nat) (hk : k < 64) :
    sem_binary_operation A .Oshr (.Vlong x) tulong (.Vlong (UInt64.ofNat k)) tulong m =
      some (.Vlong (x >>> UInt64.ofNat k)) := by
  have hk' : (UInt64.ofNat k).toNat < 64 := by rw [toNat_ofNat64 (by omega)]; exact hk
  rw [← Int64.shru_eq _ _ hk']
  have : Int64.ltu (UInt64.ofNat k) Int64.iwordsize = true := by
    rw [Int64.ltu_eq]
    simp only [decide_eq_true_eq]
    exact UInt64.lt_iff_toNat_lt.mpr (by rw [toNat_ofNat64 (by omega)]; exact hk)
  show (if Int64.ltu (UInt64.ofNat k) Int64.iwordsize then
    some (val.Vlong (Int64.shru x (UInt64.ofNat k))) else (none : Option val)) = _
  rw [this]; rfl

theorem sem_shl_const (x : UInt64) (k : Nat) (hk : k < 64) :
    sem_binary_operation A .Oshl (.Vlong x) tulong (.Vlong (UInt64.ofNat k)) tulong m =
      some (.Vlong (x <<< UInt64.ofNat k)) := by
  have hk' : (UInt64.ofNat k).toNat < 64 := by rw [toNat_ofNat64 (by omega)]; exact hk
  rw [← Int64.shl_eq _ _ hk']
  have : Int64.ltu (UInt64.ofNat k) Int64.iwordsize = true := by
    rw [Int64.ltu_eq]
    simp only [decide_eq_true_eq]
    exact UInt64.lt_iff_toNat_lt.mpr (by rw [toNat_ofNat64 (by omega)]; exact hk)
  show (if Int64.ltu (UInt64.ofNat k) Int64.iwordsize then
    some (val.Vlong (Int64.shl x (UInt64.ofNat k))) else (none : Option val)) = _
  rw [this]; rfl

theorem sem_gt_ll (x y : UInt64) :
    sem_binary_operation A .Ogt (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vint (if y < x then 1 else 0)) := by
  show some (Val.of_bool (Int64.ltu y x)) = _
  rw [Int64.ltu_eq, of_bool_decide]

theorem sem_add_mem_word (b : block) (cap : Nat) (k : UInt64) (hk : 8 * k.toNat < 2 ^ 64) :
    sem_binary_operation A .Oadd (.Vptr b Ptrofs.zero) (memType cap) (.Vlong k) tulong m =
      some (.Vptr b (UInt64.ofNat (8 * k.toNat))) := by
  show some (val.Vptr b (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 k)))) = _
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [Ptrofs.add, Ptrofs.mul, Ptrofs.repr, Ptrofs.of_int64, Ptrofs.unsigned, Ptrofs.zero,
    Int64.unsigned, Ptrofs.modulus]
  rw [toNat_ofNat64 hk]
  simp
  omega

theorem sem_add_mem_byte (b : block) (k : UInt64) :
    sem_binary_operation A .Oadd (.Vptr b Ptrofs.zero) (.Tpointer tuchar noattr) (.Vlong k) tulong m =
      some (.Vptr b k) := by
  show some (val.Vptr b (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 k)))) = _
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [Ptrofs.add, Ptrofs.mul, Ptrofs.repr, Ptrofs.of_int64, Ptrofs.unsigned, Ptrofs.zero,
    Int64.unsigned, Ptrofs.modulus]
  have := k.toNat_lt
  simp
  omega

end

section

variable {A : Archi} {E : Env}

theorem eval_memVar (hE : EnvOk E) (le : temp_env) (m : mem) (cap : Nat) :
    eval_expr A E.ge empty_env le m (memVar cap) (.Vptr E.mem Ptrofs.zero) :=
  .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hE.mem) (.deref_loc_reference rfl)

theorem eval_addrPlus {le : temp_env} {m : mem} {t : ident} {q : UInt64}
    (ht : le[t]? = some (.Vlong q)) (k : Nat) (hk : q.toNat + k < 2 ^ 64) :
    eval_expr A E.ge empty_env le m (addrPlus t k) (.Vlong (UInt64.ofNat (q.toNat + k))) := by
  unfold addrPlus
  split
  · rename_i hk0
    subst hk0
    rw [Nat.add_zero, UInt64.ofNat_toNat]
    exact .eval_Etempvar _ _ _ ht
  · refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ ht) (.eval_Econst_long _ _) ?_
    show sem_binary_operation A .Oadd (.Vlong q) tulong (.Vlong _) tulong m = _
    rw [sem_add_ll]
    congr 2
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, toNat_ofNat64 hk, toNat_ofNat64 (by omega)]
    omega

theorem typeof_addrPlus (t : ident) (k : Nat) : typeof (addrPlus t k) = tulong := by
  unfold addrPlus; split <;> rfl

theorem eval_wordAt_lvalue (hE : EnvOk E) {le : temp_env} {m : mem} (cap : Nat) {t : ident}
    {q : UInt64} (ht : le[t]? = some (.Vlong q)) (hal : q.toNat % 8 = 0) :
    eval_lvalue A E.ge empty_env le m (wordAt cap t) E.mem q .Full := by
  have hsh : (q >>> UInt64.ofNat 3).toNat = q.toNat / 8 := by
    rw [UInt64.toNat_shiftRight, toNat_ofNat64 (by omega), Nat.shiftRight_eq_div_pow]
  have hq := q.toNat_lt
  refine .eval_Ederef _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (eval_memVar hE le m cap)
    (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ ht) (.eval_Econst_long _ _)
      (sem_shr_const A m q 3 (by omega))) ?_)
  show sem_binary_operation A .Oadd (.Vptr E.mem Ptrofs.zero) (memType cap) (.Vlong _) tulong m = _
  rw [sem_add_mem_word A m E.mem cap _ (by rw [hsh]; omega)]
  congr 2
  apply UInt64.toNat_inj.mp
  rw [toNat_ofNat64 (by rw [hsh]; omega), hsh]
  omega

theorem eval_byteAt_lvalue (hE : EnvOk E) {le : temp_env} {m : mem} (cap : Nat) {e : expr}
    {q : UInt64} (he : eval_expr A E.ge empty_env le m e (.Vlong q)) (hty : typeof e = tulong) :
    eval_lvalue A E.ge empty_env le m (byteAt cap e) E.mem q .Full := by
  refine .eval_Ederef _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _
    (.eval_Ecast _ _ _ _ (eval_memVar hE le m cap) rfl) he ?_)
  rw [hty]
  exact sem_add_mem_byte A m E.mem q

theorem loadv_mem {m : mem} {b : block} (chunk : memory_chunk) {q : UInt64}
    (hq : q.toNat + (size_chunk chunk).toNat ≤ 2 ^ 64) (hs : 0 ≤ size_chunk chunk) :
    Mem.loadv chunk m (.Vptr b q) = Mem.load chunk m b q.toNat := by
  show (if Ptrofs.unsigned q + size_chunk chunk ≤ Ptrofs.modulus then
    Mem.load chunk m b (Ptrofs.unsigned q) else none) = _
  rw [ite_eq_left (by simp only [Ptrofs.unsigned, Ptrofs.modulus]; omega)]
  rfl

theorem eval_wordAt (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {le : temp_env} (cap : Nat) {t : ident} {q : UInt64} {a : UInt32}
    (ht : le[t]? = some (.Vlong q)) (hq : q.toNat = a.toNat) (hin : a.toNat + 8 ≤ 65536 * E.cap)
    (hal : a.toNat % 8 = 0) :
    eval_expr A E.ge empty_env le m (wordAt cap t) (.Vlong (wm.read64 a)) := by
  refine .eval_Elvalue _ _ _ _ _ (eval_wordAt_lvalue hE cap ht (hq ▸ hal))
    (.deref_loc_value .Mint64 _ rfl ?_)
  have := hE.cap
  rw [loadv_mem _ (by simp [size_chunk]; omega) (by decide), hq]
  exact h.load_word a hin hal

theorem eval_loadByte (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {le : temp_env} (cap : Nat) {e : expr} {q : UInt64}
    (he : eval_expr A E.ge empty_env le m e (.Vlong q)) (hty : typeof e = tulong)
    (hin : q.toNat < 65536 * E.cap) :
    eval_expr A E.ge empty_env le m (.Ecast (byteAt cap e) tulong)
      (.Vlong (wm.bytes q.toNat).toUInt64) := by
  refine .eval_Ecast _ _ _ _ (.eval_Elvalue _ _ _ _ _ (eval_byteAt_lvalue hE cap he hty)
    (.deref_loc_value .Mint8unsigned _ rfl ?_)) (cast_byte_long _ m)
  have := hE.cap
  rw [loadv_mem _ (by simp [size_chunk]; omega) (by decide)]
  exact h.load_byte hin

/-- The value of bytes 0 to `k` from `q`, combined as `loadBytes` combines them. -/
def lbval (wm : Wasm.Mem) (q : Nat) : Nat → UInt64
  | 0 => (wm.bytes q).toUInt64
  | k + 1 => lbval wm q k ||| ((wm.bytes (q + (k + 1))).toUInt64 <<< UInt64.ofNat (8 * (k + 1)))

theorem lbval_read64 (wm : Wasm.Mem) (a : UInt32) : lbval wm a.toNat 7 = wm.read64 a := rfl

theorem typeof_loadBytes (cap : Nat) (t : ident) (k : Nat) : typeof (loadBytes cap t k) = tulong := by
  cases k <;> rfl

theorem eval_loadBytes (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {le : temp_env} (cap : Nat) {t : ident} {q : UInt64}
    (ht : le[t]? = some (.Vlong q)) :
    ∀ k, k < 8 → q.toNat + k < 65536 * E.cap →
      eval_expr A E.ge empty_env le m (loadBytes cap t k) (.Vlong (lbval wm q.toNat k)) := by
  have hcap := hE.cap
  intro k
  induction k with
  | zero =>
      intro _ hk
      have := eval_loadByte (A := A) hE h cap (eval_addrPlus ht 0 (by omega)) (typeof_addrPlus t 0)
        (by rw [toNat_ofNat64 (by omega)]; omega)
      rw [toNat_ofNat64 (by omega)] at this
      exact this
  | succ k ih =>
      intro hk8 hk
      have hb := eval_loadByte (A := A) hE h cap (eval_addrPlus ht (k + 1) (by omega))
        (typeof_addrPlus t (k + 1)) (by rw [toNat_ofNat64 (by omega)]; omega)
      rw [toNat_ofNat64 (by omega)] at hb
      exact .eval_Ebinop _ _ _ _ _ _ _ (ih (by omega) (by omega))
        (.eval_Ebinop _ _ _ _ _ _ _ hb (.eval_Econst_long _ _)
          (sem_shl_const A m _ (8 * (k + 1)) (by omega)))
        (by rw [typeof_loadBytes]; exact sem_or_ll A m _ _)

end


/-! ## Statements -/

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem typeof_byteOfVal (v : expr) (k : Nat) : typeof (byteOfVal v k) = tuchar := rfl

theorem shift_byte (x : UInt64) (k : Nat) (hk : k < 8) :
    UInt8.ofNat (x >>> UInt64.ofNat (8 * k)).toNat = nbyte x.toNat k := by
  rw [UInt64.toNat_shiftRight, toNat_ofNat64 (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ (8 * k) = 256 ^ k by rw [Nat.pow_mul]]
  rfl

theorem eval_byteOfVal {le : temp_env} {m : mem} {vid : ident} {x : UInt64}
    (hv : le[vid]? = some (.Vlong x)) (k : Nat) (hk : k < 8) :
    eval_expr A E.ge empty_env le m (byteOfVal (.Etempvar vid tulong) k)
      (.Vint (UInt32.ofNat ((x >>> UInt64.ofNat (8 * k)).toNat % 256))) := by
  unfold byteOfVal
  split
  · rename_i hk0
    subst hk0
    have e : x >>> UInt64.ofNat (8 * 0) = x := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight]
      simp
    rw [e]
    exact .eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hv) (cast_cbyte x m)
  · exact .eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hv)
      (.eval_Econst_long _ _) (sem_shr_const A m x (8 * k) (by omega))) (cast_cbyte _ m)

theorem storev_mem {m : mem} {b : block} (chunk : memory_chunk) {q : UInt64} {v : val}
    (hq : q.toNat + (size_chunk chunk).toNat ≤ 2 ^ 64) (hs : 0 ≤ size_chunk chunk) :
    Mem.storev chunk m (.Vptr b q) v = Mem.store chunk m b q.toNat v := by
  show (if Ptrofs.unsigned q + size_chunk chunk ≤ Ptrofs.modulus then
    Mem.store chunk m b (Ptrofs.unsigned q) v else none) = _
  rw [ite_eq_left (by simp only [Ptrofs.unsigned, Ptrofs.modulus]; omega)]
  rfl

/-- One byte store of `storeBytes`. -/
theorem exec_byteStore (hE : EnvOk E) {le : temp_env} (cap : Nat) {t vid : ident}
    {q x : UInt64} (ht : le[t]? = some (.Vlong q)) (hv : le[vid]? = some (.Vlong x)) (k : Nat)
    (hk : k < 8) {m : mem} (hin : q.toNat + k < 65536 * E.cap)
    (hp : ∀ i : Nat, i < 65536 * E.cap → Mem.perm m E.mem i .Cur .Writable) :
    ∃ m', exec_stmt A X E.ge empty_env le m
        (.Sassign (byteAt cap (addrPlus t k)) (byteOfVal (.Etempvar vid tulong) k)) E0 le m'
        .Out_normal ∧ Mem.SameExcept E.mem m m' ∧
      ∀ i : Nat, ZMap.get (i : _root_.Int) (Mem.contents_of m' E.mem) =
        if i = q.toNat + k then .Byte (nbyte x.toNat k)
        else ZMap.get (i : _root_.Int) (Mem.contents_of m E.mem) := by
  have hcap := hE.cap
  have ha := eval_addrPlus (A := A) (E := E) (m := m) ht k (by omega)
  have hlv := eval_byteAt_lvalue hE cap ha (typeof_addrPlus t k)
  have hva : Mem.valid_access m .Mint8unsigned E.mem (q.toNat + k : Nat) .Writable := by
    refine ⟨fun ofs h1 h2 => ?_, ⟨(q.toNat + k : Nat), by simp [align_chunk]⟩⟩
    have h2' : ofs < ((q.toNat + k : Nat) : _root_.Int) + 1 := h2
    have : ofs = ((q.toNat + k : Nat) : _root_.Int) := by omega
    subst this
    exact hp _ hin
  let y := x >>> UInt64.ofNat (8 * k)
  refine ⟨Mem.stored .Mint8unsigned m E.mem (q.toNat + k : Nat)
      (.Vint (UInt32.ofNat (y.toNat % 256))), ?_, Mem.SameExcept.of_stored _ _ _ _ _, ?_⟩
  · refine .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ hlv (eval_byteOfVal hv k hk)
      (by rw [typeof_byteOfVal]; exact cast_uchar _ m) (.assign_loc_value _ .Mint8unsigned _ rfl ?_)
    have e := storev_mem (m := m) (b := E.mem) (v := .Vint (UInt32.ofNat (y.toNat % 256)))
      .Mint8unsigned (q := UInt64.ofNat (q.toNat + k))
      (by rw [toNat_ofNat64 (by omega)]; simp [size_chunk]; omega) (by decide)
    rw [e, toNat_ofNat64 (by omega)]
    exact Mem.store_ok _ hva
  · intro i
    rw [Mem.contents_stored_same, encode_cbyte, shift_byte x k hk]
    split
    · rename_i hi
      subst hi
      have e := Mem.setN_at [.Byte (nbyte x.toNat k)] ((q.toNat + k : Nat) : _root_.Int)
        (Mem.contents_of m E.mem) 0 (by simp)
      simpa using e
    · rename_i hi
      rcases Nat.lt_or_ge i (q.toNat + k) with hlt | hge
      · exact Mem.setN_outside _ _ _ _ (by omega)
      · exact Mem.setN_above _ _ _ _ (by simp; omega)

theorem exec_storeBytes (hE : EnvOk E) {le : temp_env} (cap : Nat) {t vid : ident}
    {q x : UInt64} (ht : le[t]? = some (.Vlong q)) (hv : le[vid]? = some (.Vlong x)) :
    ∀ n k (m : mem), k + n < 8 → q.toNat + 8 ≤ 65536 * E.cap →
      (∀ i : Nat, i < 65536 * E.cap → Mem.perm m E.mem i .Cur .Writable) →
      ∃ m', exec_stmt A X E.ge empty_env le m (storeBytes cap t (.Etempvar vid tulong) k n) E0
          le m' .Out_normal ∧ Mem.SameExcept E.mem m m' ∧
        ∀ i : Nat, ZMap.get (i : _root_.Int) (Mem.contents_of m' E.mem) =
          if q.toNat + k ≤ i ∧ i ≤ q.toNat + k + n then .Byte (nbyte x.toNat (i - q.toNat))
          else ZMap.get (i : _root_.Int) (Mem.contents_of m E.mem) := by
  intro n
  induction n with
  | zero =>
      intro k m hk hin hp
      obtain ⟨m', hx, hs, hc⟩ := exec_byteStore (X := X) hE cap ht hv k (by omega) (by omega) hp
      refine ⟨m', hx, hs, fun i => ?_⟩
      rw [hc i]
      split_ifs <;> first | rfl | (congr 2; omega)
  | succ n ih =>
      intro k m hk hin hp
      obtain ⟨m1, hx1, hs1, hc1⟩ := exec_byteStore (X := X) hE cap ht hv k (by omega) (by omega) hp
      obtain ⟨m2, hx2, hs2, hc2⟩ := ih (k + 1) m1 (by omega) hin
        (fun i hi => by rw [hs1.perm_eq]; exact hp i hi)
      refine ⟨m2, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1 hx2, hs1.trans hs2, fun i => ?_⟩
      rw [hc2 i, hc1 i]
      split_ifs <;> first | rfl | (congr 2; omega)

end


theorem MemRel.store_bytes {E : Env} {wm : Wasm.Mem} {caps : List Nat} {m m' : mem}
    (hE : EnvOk E) (h : MemRel E wm caps m) (hs : Mem.SameExcept E.mem m m') {q x : UInt64}
    (hc : ∀ i : Nat, ZMap.get (i : _root_.Int) (Mem.contents_of m' E.mem) =
      if q.toNat + 0 ≤ i ∧ i ≤ q.toNat + 0 + 7 then .Byte (nbyte x.toNat (i - q.toNat))
      else ZMap.get (i : _root_.Int) (Mem.contents_of m E.mem))
    (a : UInt32) (hq : q.toNat = a.toNat) : MemRel E (wm.write64 a x) caps m' := by
  refine h.of_contents hE hs rfl fun i hi => ?_
  rw [hc i]
  split_ifs with hin
  · obtain ⟨j, rfl⟩ : ∃ j, i = a.toNat + j := ⟨i - a.toNat, by omega⟩
    rw [write64_bytes_at _ _ _ j (by omega), hq, Nat.add_sub_cancel_left]
  · rw [LeanExe.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)]
    exact h.bytes i hi

theorem trapCode_oob : trapCode "out of bounds memory access" = trapOutOfBounds := by decide

theorem pop_i64_i32 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.i64 :: .i32 :: σr) vs) :
    ∃ x a vr, vs = .i64 x :: .i32 a :: vr ∧ le[slotId (σr.length + 1) .i64]? = some (.Vlong x) ∧
      le[slotId σr.length .i32]? = some (.Vint a) ∧ StackRel le σr vr := by
  obtain ⟨v1, vs1, rfl, h1, hl1, h'⟩ := h.cons_inv
  obtain ⟨v2, vr, rfl, h2, hl2, hrest⟩ := h'.cons_inv
  obtain ⟨x, rfl⟩ := has_i64 h1
  obtain ⟨a, rfl⟩ := has_i32 h2
  exact ⟨x, a, vr, rfl, hl1, hl2, hrest⟩

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem exec_addr {le : temp_env} {m : mem} {h : Nat} {a : UInt32}
    (ha : le[slotId h .i32]? = some (.Vint a)) (t : ident) (off : UInt32) :
    exec_stmt A X E.ge empty_env le m (addrStmt t (tmp h .i32) off) E0
      (le.insert t (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m .Out_normal := by
  refine .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _
    (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ ha) (cast_uint_long m a)) (.eval_Econst_long _ _) ?_)
  show sem_binary_operation A .Oadd (.Vlong _) tulong (.Vlong _) tulong m = _
  rw [sem_add_ll]
  congr 2
  apply UInt64.toNat_inj.mp
  have := a.toNat_lt
  have := off.toNat_lt
  rw [UInt64.toNat_add, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega), UInt32.toNat_toUInt64]
  omega

theorem eval_bounds (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {le : temp_env} {t : ident} {q : UInt64}
    (ht : le[t]? = some (.Vlong q)) (hq : q.toNat < 2 ^ 33) :
    ∃ v, eval_expr A E.ge empty_env le m
      (.Ebinop .Ogt (.Ebinop .Oadd (.Etempvar t tulong) (clong 8) tulong)
        (.Ebinop .Omul (.Ecast pagesVar tulong) (clong 65536) tulong) tint) v ∧
      bool_val v tint m = some (decide (wm.pages * 65536 < q.toNat + 8)) := by
  have hcap := hE.cap
  have hp := h.le_cap
  refine ⟨_, .eval_Ebinop _ _ _ _ _ _ _
    (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ ht) (.eval_Econst_long _ _)
      (sem_add_ll A m _ _))
    (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Ecast _ _ _ _ (eval_global_int hE.pages h.pages)
      (cast_uint_long m _)) (.eval_Econst_long _ _) (sem_mul_ll A m _ _))
    (sem_gt_ll A m _ _), ?_⟩
  have e : (UInt64.ofNat (UInt32.ofNat wm.pages).toNat * UInt64.ofNat 65536 < q + UInt64.ofNat 8) ↔
      wm.pages * 65536 < q.toNat + 8 := by
    have hP : (UInt32.ofNat wm.pages).toNat = wm.pages := by
      rw [UInt32.toNat_ofNat']; omega
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, UInt64.toNat_add, hP,
      toNat_ofNat64 (by omega), toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  by_cases hc : wm.pages * 65536 < q.toNat + 8
  · rw [ite_eq_left (e.mpr hc), decide_eq_true hc]; exact bool_int m 1
  · rw [ite_eq_right (fun x => hc (e.mp x)), decide_eq_false hc]; exact bool_int m 0

theorem eval_aligned {le : temp_env} {m : mem} {t : ident} {q : UInt64}
    (ht : le[t]? = some (.Vlong q)) :
    ∃ v, eval_expr A E.ge empty_env le m (aligned t) v ∧
      bool_val v tint m = some (decide (q.toNat % 8 = 0)) := by
  refine ⟨_, .eval_Ebinop _ _ _ _ _ _ _
    (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ ht) (.eval_Econst_long _ _) (sem_and_ll A m _ _))
    (.eval_Econst_long _ _) (sem_eq_ll A m _ _), ?_⟩
  have e : (q &&& UInt64.ofNat 7 = UInt64.ofNat 0) ↔ q.toNat % 8 = 0 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_and, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega),
      show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  by_cases hc : q.toNat % 8 = 0
  · rw [ite_eq_left (e.mpr hc), decide_eq_true hc]; exact bool_int m 1
  · rw [ite_eq_right (fun x => hc (e.mp x)), decide_eq_false hc]; exact bool_int m 0

end


/-! ## The memory instructions -/

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- The address of an access whose eight bytes lie in memory is below `2 ^ 32` and does not wrap
in Talos's 32-bit sum. -/
theorem addr_fits (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) {a off : UInt32}
    (hin : ¬ a.toNat + off.toNat + 8 > wm.pages * 65536) :
    (a + off).toNat = a.toNat + off.toNat ∧ a.toNat + off.toNat + 8 ≤ 65536 * E.cap := by
  have := hE.cap
  have := h.le_cap
  refine ⟨?_, by omega⟩
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

theorem sim_load64 (hE : EnvOk E) (F : Nat) (off : UInt32) :
    InstrSim A X E mod c F (.load64 off) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a0, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  have hb : curBase L ≤ σr.length := by simp at hbase; omega
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨a, vr, hvs, ha, hrest⟩ := pop1_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      have hmr := hinv.store.2
      have hcapE := hE.cap
      have hpg := hmr.le_cap
      have h32a := a.toNat_lt
      have h32o := off.toNat_lt
      have hq : (UInt64.ofNat (a.toNat + off.toNat)).toNat = a.toNat + off.toNat :=
        toNat_ofNat64 (by omega)
      have hx1 := exec_addr (A := A) (X := X) (E := E) (m := m) ha (slotId σr.length .i64) off
      have ht1 : (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))[
          slotId σr.length .i64]? = some (.Vlong (UInt64.ofNat (a.toNat + off.toNat))) :=
        te_insert_same _ _ _
      obtain ⟨vb, hvb, hbb⟩ := eval_bounds (A := A) hE hmr ht1 (by rw [hq]; omega)
      by_cases hob : a.toNat + off.toNat + 8 > st.mem.pages * 65536
      · rw [ite_eq_left hob]
        obtain ⟨m', hxt, hg, hs⟩ := trap_exec (A := A) (X := X)
          (le := le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))
          hE hinv.store hinv.status trapOutOfBounds c.result
        refine ⟨E0 ++ E0,
          le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))), m', ?_,
          hg, by rw [trapCode_oob]; exact hs, by rw [trapCode_oob]; decide⟩
        refine .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1
          (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ ?_ (trapOut_ne_normal _))
        refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hvb ?_ hxt
        show bool_val vb tint m = some true
        rw [hbb, hq]; simp; omega
      · rw [ite_eq_right hob]
        obtain ⟨hfit, hin⟩ := addr_fits hE hmr hob
        obtain ⟨va, hva, hba⟩ := eval_aligned (A := A) (E := E) (m := m) ht1
        have hval : exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (.Sifthenelse (aligned (slotId σr.length .i64))
              (.Sset (slotId σr.length .i64) (wordAt c.cap (slotId σr.length .i64)))
              (.Sset (slotId σr.length .i64) (loadBytes c.cap (slotId σr.length .i64) 7))) E0
            ((le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))).insert
              (slotId σr.length .i64) (.Vlong (st.mem.read64 (a + off)))) m .Out_normal := by
          by_cases hal : (a.toNat + off.toNat) % 8 = 0
          · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hva
              (by show bool_val va tint m = some true; rw [hba, hq]; simp [hal]) ?_
            exact .exec_Sset _ _ _ _ _ _ (eval_wordAt hE hmr c.cap ht1 (by rw [hq, hfit])
              (by rw [hfit]; exact hin) (by rw [hfit]; exact hal))
          · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hva
              (by show bool_val va tint m = some false; rw [hba, hq]; simp [hal]) ?_
            have e := eval_loadBytes (A := A) hE hmr c.cap ht1 7 (by omega) (by rw [hq]; omega)
            have e' : lbval st.mem (a.toNat + off.toNat) 7 = st.mem.read64 (a + off) := by
              rw [← hfit]; exact lbval_read64 _ _
            rw [hq, e'] at e
            exact .exec_Sset _ _ _ _ _ _ e
        have hbo : exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (boundsCheck c.result (slotId σr.length .i64)) E0
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            .Out_normal := by
          refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hvb ?_ (.exec_Sskip _ _ _)
          show bool_val vb tint m = some false
          rw [hbb, hq]; simp; omega
        have hfr : Frame σr.length le
            ((le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))).insert
              (slotId σr.length .i64) (.Vlong (st.mem.read64 (a + off)))) :=
          (Frame.insert_slot _ _ _ _ (Nat.le_refl _)).trans
            (Frame.insert_slot _ _ _ _ (Nat.le_refl _))
        refine ⟨.i64 :: σr, rfl, by simp; omega, E0 ++ (E0 ++ E0),
          (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))).insert
            (slotId σr.length .i64) (.Vlong (st.mem.read64 (a + off))), m,
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hbo hval),
          ?_, hfr.mono hb⟩
        exact { stack := ⟨rfl, te_insert_same _ _ _, hrest.frame hfr⟩
                locals := (hinv.locals.insert_other _ (fun i => slotId_ne_localId _ _ i)).insert_other _
                  (fun i => slotId_ne_localId _ _ i)
                store := hinv.store
                status := hinv.status
                brk := brk_insert_slot _ _ _ (brk_insert_slot _ _ _ hinv.brk) }


theorem sim_store64 (hE : EnvOk E) (F : Nat) (off : UInt32) :
    InstrSim A X E mod c F (.store64 off) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a0, _ | ⟨b0, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, a, vr, hvs, hx, ha, hrest⟩ := pop_i64_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      have hmr := hinv.store.2
      have hcapE := hE.cap
      have hpg := hmr.le_cap
      have h32a := a.toNat_lt
      have h32o := off.toNat_lt
      have hq : (UInt64.ofNat (a.toNat + off.toNat)).toNat = a.toNat + off.toNat :=
        toNat_ofNat64 (by omega)
      have hx1 := exec_addr (A := A) (X := X) (E := E) (m := m) ha (slotId σr.length .i64) off
      have ht1 : (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))[
          slotId σr.length .i64]? = some (.Vlong (UInt64.ofNat (a.toNat + off.toNat))) :=
        te_insert_same _ _ _
      have hx' : (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))[
          slotId (σr.length + 1) .i64]? = some (.Vlong x) := by
        rw [te_insert_ne _ (slotId_ne_of_height _ _ (by omega))]; exact hx
      obtain ⟨vb, hvb, hbb⟩ := eval_bounds (A := A) hE hmr ht1 (by rw [hq]; omega)
      have hfr : Frame σr.length le
          (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) :=
        Frame.insert_slot _ _ _ _ (Nat.le_refl _)
      by_cases hob : a.toNat + off.toNat + 8 > st.mem.pages * 65536
      · rw [ite_eq_left hob]
        obtain ⟨m', hxt, hg, hs⟩ := trap_exec (A := A) (X := X)
          (le := le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))))
          hE hinv.store hinv.status trapOutOfBounds c.result
        refine ⟨E0 ++ E0,
          le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))), m', ?_,
          hg, by rw [trapCode_oob]; exact hs, by rw [trapCode_oob]; decide⟩
        refine .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1
          (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ ?_ (trapOut_ne_normal _))
        refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hvb ?_ hxt
        show bool_val vb tint m = some true
        rw [hbb, hq]; simp; omega
      · rw [ite_eq_right hob]
        obtain ⟨hfit, hin⟩ := addr_fits hE hmr hob
        obtain ⟨va, hva, hba⟩ := eval_aligned (A := A) (E := E) (m := m) ht1
        have hbo : exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (boundsCheck c.result (slotId σr.length .i64)) E0
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            .Out_normal := by
          refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hvb ?_ (.exec_Sskip _ _ _)
          show bool_val vb tint m = some false
          rw [hbb, hq]; simp; omega
        have hst : ∃ m', exec_stmt A X E.ge empty_env
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m
            (.Sifthenelse (aligned (slotId σr.length .i64))
              (.Sassign (wordAt c.cap (slotId σr.length .i64)) (tmp (σr.length + 1) .i64))
              (storeBytes c.cap (slotId σr.length .i64) (tmp (σr.length + 1) .i64) 0 7)) E0
            (le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat)))) m'
            .Out_normal ∧ Mem.SameExcept E.mem m m' ∧
            MemRel E (st.mem.write64 (a + off) x) st.memoryCaps m' := by
          by_cases hal : (a.toNat + off.toNat) % 8 = 0
          · have hvw := hmr.valid_word (i := (a + off).toNat) (by rw [hfit]; exact hin)
              (by rw [hfit]; exact hal)
            refine ⟨Mem.stored .Mint64 m E.mem (a + off).toNat (.Vlong x), ?_,
              Mem.SameExcept.of_stored _ _ _ _ _, hmr.store_word hE (a + off) x⟩
            refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hva
              (by show bool_val va tint m = some true; rw [hba, hq]; simp [hal]) ?_
            refine .exec_Sassign _ _ _ _ _ _ _ _ _ _ _
              (eval_wordAt_lvalue hE c.cap ht1 (by rw [hq]; exact hal)) (.eval_Etempvar _ _ _ hx')
              (cast_ll m x) (.assign_loc_value _ .Mint64 _ rfl ?_)
            rw [storev_mem _ (by rw [hq]; simp [size_chunk]; omega) (by decide), hq, ← hfit]
            exact Mem.store_ok _ hvw
          · obtain ⟨m', hxs, hss, hcs⟩ := exec_storeBytes (A := A) (X := X) hE c.cap ht1 hx' 7 0 m
              (by omega) (by rw [hq]; omega) (fun i hi => hmr.perm i hi)
            refine ⟨m', ?_, hss, hmr.store_bytes hE hss hcs (a + off) (by rw [hq, hfit])⟩
            exact .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hva
              (by show bool_val va tint m = some false; rw [hba, hq]; simp [hal]) hxs
        obtain ⟨m', hx2, hs', hmr'⟩ := hst
        refine ⟨σr, rfl, hb, E0 ++ (E0 ++ E0),
          le.insert (slotId σr.length .i64) (.Vlong (UInt64.ofNat (a.toNat + off.toNat))), m',
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hbo hx2),
          ?_, hfr.mono hb⟩
        exact { stack := hrest.frame hfr
                locals := hinv.locals.insert_other _ (fun i => slotId_ne_localId _ _ i)
                store := ⟨GlobalsRel.sameExcept hinv.store.1 hs' hE.mem_not, hmr'⟩
                status := hinv.status.sameExcept hs' (Ne.symm hE.mem_status)
                brk := brk_insert_slot _ _ _ hinv.brk }

theorem sim_memorySize (hE : EnvOk E) (h64 : mod.memIs64 = false) (F : Nat) :
    InstrSim A X E mod c F .memorySize := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      simp only [execOne.eq_def, h64, sizeValue_false]
      exact push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk
        (eval_global_int hE.pages hinv.store.2.pages) rfl hbase

theorem memoryCap_eq {E : Env} {α : Type} {st : Store α} {m : mem}
    (h : MemRel E st.mem st.memoryCaps m) (mod : Module) : st.memoryCap mod 0 = E.cap := by
  unfold Store.memoryCap
  rw [h.memCap]
  rfl

theorem sim_memoryGrow (hE : EnvOk E) (hcap : c.cap = E.cap) (F : Nat) :
    InstrSim A X E mod c F .memoryGrow := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a0, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  have hb : curBase L ≤ σr.length := by simp at hbase; omega
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨d, vr, hvs, hd, hrest⟩ := pop1_i32 hinv.stack
      have hmr := hinv.store.2
      have hcapE := hE.cap
      have hpg := hmr.le_cap
      have h32 := d.toNat_lt
      simp only [execOne.eq_def, hvs, memoryCap_eq hmr]
      have hT : (UInt64.ofNat (UInt32.ofNat st.mem.pages).toNat + UInt64.ofNat d.toNat).toNat =
          st.mem.pages + d.toNat := by
        have hP : (UInt32.ofNat st.mem.pages).toNat = st.mem.pages := by
          rw [UInt32.toNat_ofNat']; omega
        rw [UInt64.toNat_add, hP, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega)]
        omega
      let T := UInt64.ofNat (UInt32.ofNat st.mem.pages).toNat + UInt64.ofNat d.toNat
      let t := slotId σr.length .i64
      let r := slotId σr.length .i32
      have hx1 : exec_stmt A X E.ge empty_env le m
          (.Sset t (.Ebinop .Oadd (.Ecast pagesVar tulong) (.Ecast (tmp σr.length .i32) tulong)
            tulong)) E0 (le.insert t (.Vlong T)) m .Out_normal :=
        .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _
          (.eval_Ecast _ _ _ _ (eval_global_int hE.pages hmr.pages) (cast_uint_long m _))
          (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hd) (cast_uint_long m _)) (sem_add_ll A m _ _))
      have ht1 : (le.insert t (.Vlong T))[t]? = some (.Vlong T) := te_insert_same _ _ _
      have hcond : eval_expr A E.ge empty_env (le.insert t (.Vlong T)) m
          (.Ebinop .Ole (.Etempvar t tulong) (clong c.cap) tint)
          (.Vint (if T ≤ UInt64.ofNat c.cap then 1 else 0)) :=
        .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ ht1) (.eval_Econst_long _ _)
          (sem_le_ll A m _ _)
      have hle : T ≤ UInt64.ofNat c.cap ↔ st.mem.pages + d.toNat ≤ E.cap := by
        rw [UInt64.le_iff_toNat_le, hT, hcap, toNat_ofNat64 (by omega)]
      have hfr : ∀ v, Frame σr.length le ((le.insert t (.Vlong T)).insert r v) := fun v =>
        (Frame.insert_slot _ _ _ _ (Nat.le_refl _)).trans (Frame.insert_slot _ _ _ _ (Nat.le_refl _))
      have hinv' : ∀ (st' : Store α) (m' : mem) (w : UInt32), StoreRel E st' m' → StatusRel E m' 0 →
          Inv E c (.i32 :: σr) st' { params := sl.params, locals := sl.locals, values := .i32 w :: vr }
            ((le.insert t (.Vlong T)).insert r (.Vint w)) m' := fun st' m' w hst hs =>
        { stack := ⟨rfl, te_insert_same _ _ _, hrest.frame (hfr _)⟩
          locals := (hinv.locals.insert_other _ (fun i => slotId_ne_localId _ _ i)).insert_other _
            (fun i => slotId_ne_localId _ _ i)
          store := hst
          status := hs
          brk := brk_insert_slot _ _ _ (brk_insert_slot _ _ _ hinv.brk) }
      by_cases hg : st.mem.pages + d.toNat ≤ E.cap
      · have hgrow : st.mem.grow d E.cap = some ({ st.mem with pages := st.mem.pages + d.toNat },
            st.mem.pages) := by
          simp [Wasm.Mem.grow, hg]
        rw [hgrow]
        have hval : exec_stmt A X E.ge empty_env (le.insert t (.Vlong T)) m
            (.Ssequence (.Sset r pagesVar) (.Sassign pagesVar (.Ecast (.Etempvar t tulong) tuint)))
            (E0 ++ E0) ((le.insert t (.Vlong T)).insert r (.Vint (UInt32.ofNat st.mem.pages)))
            (Mem.stored .Mint32 m E.pages 0 (.Vint (UInt32.ofNat (st.mem.pages + d.toNat)))) .Out_normal := by
          refine .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
            (.exec_Sset _ _ _ _ _ _ (eval_global_int hE.pages hmr.pages)) ?_
          have hc := cast_long_uint m T
          rw [hT] at hc
          rw [show (st.mem.pages + d.toNat) % 2 ^ 32 = st.mem.pages + d.toNat from
            Nat.mod_eq_of_lt (by omega)] at hc
          exact exec_assign_int hE.pages (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _
            (by rw [te_insert_ne _ (slotId_ne_of_type _ (by decide))]; exact ht1)) hc) rfl hmr.pagesW
        refine ⟨.i32 :: σr, rfl, by simp; omega, E0 ++ (E0 ++ E0), _, _,
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1
            (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond
              (by rw [ite_eq_left (hle.mpr hg)]; exact bool_int m 1) hval),
          hinv' _ _ _ ⟨GlobalsRel.sameExcept hinv.store.1 (Mem.SameExcept.of_stored _ _ _ _ _)
              hE.pages_not, hmr.grow hE _ hg⟩
            (hinv.status.sameExcept (Mem.SameExcept.of_stored _ _ _ _ _) (Ne.symm hE.pages_status)),
          (hfr _).mono hb⟩
      · have hgrow : st.mem.grow d E.cap = none := by
          simp [Wasm.Mem.grow, hg]
        rw [hgrow]
        refine ⟨.i32 :: σr, rfl, by simp; omega, E0 ++ E0, _, _,
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1
            (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond
              (by rw [ite_eq_right (fun x => hg (hle.mp x))]; exact bool_int m 0)
              (.exec_Sset _ _ _ _ _ _ (.eval_Econst_int _ _))),
          hinv' _ _ _ hinv.store hinv.status, (hfr _).mono hb⟩

end

end LeanExe.Native
