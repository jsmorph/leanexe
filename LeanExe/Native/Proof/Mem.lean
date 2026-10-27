import LeanExe.Native.Proof.Basics

/-!
Loads after stores in the Lean copy of CompCert's memory model, for the chunks `Mint32` and
`Mint64` that hold the translator's globals: a store succeeds where the access is writable, a
load of the stored chunk returns the stored integer, and a store leaves the loads from other
blocks and every permission unchanged.
-/

namespace LClight

namespace Mem

theorem zget_zset (p q : _root_.Int) (v : memval) (c : contents) :
    ZMap.get q (ZMap.set p v c) = if p = q then v else ZMap.get q c := by
  simp only [ZMap.get, ZMap.set, Std.TreeMap.getD_insert]
  by_cases h : p = q
  · simp [h]
  · have : compare p q ≠ .eq := fun e => h (Int.compare_eq_eq.mp e)
    simp [h, this]

theorem setN_outside (vl : List memval) (p q : _root_.Int) (c : contents) (h : q < p) :
    ZMap.get q (setN vl p c) = ZMap.get q c := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v vl ih =>
      simp only [setN]
      rw [ih (p + 1) _ (by omega), zget_zset, if_neg (by omega)]

theorem getN_setN (vl : List memval) (p : _root_.Int) (c : contents) :
    getN vl.length p (setN vl p c) = vl := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v vl ih =>
      simp only [List.length_cons, getN, setN]
      rw [ih, setN_outside _ _ _ _ (by omega), zget_zset, if_pos rfl]

theorem proj_inj_bytes (bl : List byte) : proj_bytes (inj_bytes bl) = some bl := by
  induction bl with
  | nil => rfl
  | cons b bl ih => simp [inj_bytes, proj_bytes] at ih ⊢; simp [ih]

theorem int_of_bytes_of_int (k a : Nat) :
    int_of_bytes (bytes_of_int k (a : _root_.Int)) = ((a % 256 ^ k : Nat) : _root_.Int) := by
  induction k generalizing a with
  | zero => simp [bytes_of_int, int_of_bytes]
  | succ k ih =>
      simp only [bytes_of_int, int_of_bytes]
      have e : (a : _root_.Int) / 256 = ((a / 256 : Nat) : _root_.Int) :=
        (Int.natCast_ediv a 256).symm
      rw [e, ih]
      have hb : Byte.unsigned (Byte.repr (a : _root_.Int)) = ((a % 256 : Nat) : _root_.Int) := by
        simp only [Byte.unsigned, Byte.repr, Byte.modulus, UInt8.toNat_ofNat']
        omega
      rw [hb, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
      generalize a / 256 % 256 ^ k = r
      rw [Int.natCast_add, Int.natCast_mul]
      omega

theorem decode_encode_long (n : UInt64) :
    decode_val .Mint64 (encode_val .Mint64 (.Vlong n)) = .Vlong n := by
  simp only [encode_val, decode_val, proj_inj_bytes, decode_int, encode_int, Int64.unsigned,
    int_of_bytes_of_int]
  rw [Nat.mod_eq_of_lt n.toNat_lt, Int64.repr_toNat]

theorem decode_encode_int (n : UInt32) :
    decode_val .Mint32 (encode_val .Mint32 (.Vint n)) = .Vint n := by
  simp only [encode_val, decode_val, proj_inj_bytes, decode_int, encode_int, Int.unsigned,
    int_of_bytes_of_int]
  rw [Nat.mod_eq_of_lt n.toNat_lt, Int.repr_toNat]

theorem length_encode_long (n : UInt64) : (encode_val .Mint64 (.Vlong n)).length = 8 := by
  simp [encode_val, inj_bytes, encode_int, bytes_of_int]

theorem length_encode_int (n : UInt32) : (encode_val .Mint32 (.Vint n)).length = 4 := by
  simp [encode_val, inj_bytes, encode_int, bytes_of_int]

/-- The memory after a store whose access is writable. -/
def stored (chunk : memory_chunk) (m : mem) (b : block) (ofs : _root_.Int) (v : val) : mem :=
  { m with
    mem_contents := m.mem_contents.insert b (setN (encode_val chunk v) ofs (contents_of m b)) }

theorem store_ok {chunk : memory_chunk} {m : mem} {b : block} {ofs : _root_.Int} (v : val)
    (h : valid_access m chunk b ofs .Writable) : store chunk m b ofs v = some (stored chunk m b ofs v) := by
  simp only [store, h, ite_true, stored]

theorem store_inv {chunk : memory_chunk} {m m' : mem} {b : block} {ofs : _root_.Int} {v : val}
    (h : store chunk m b ofs v = some m') :
    valid_access m chunk b ofs .Writable ∧ m' = stored chunk m b ofs v := by
  unfold store at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem valid_access_stored (chunk chunk' : memory_chunk) (m : mem) (b b' : block)
    (ofs ofs' : _root_.Int) (v : val) (p : permission) :
    valid_access (stored chunk m b ofs v) chunk' b' ofs' p ↔ valid_access m chunk' b' ofs' p :=
  Iff.rfl

theorem perm_order_writable {p : permission} (h : perm_order p .Writable) :
    perm_order p .Readable := by
  cases h with
  | perm_refl => exact .perm_W_R
  | perm_F_any => exact .perm_F_any _

theorem valid_access_readable {m : mem} {chunk : memory_chunk} {b : block} {ofs : _root_.Int}
    (h : valid_access m chunk b ofs .Writable) : valid_access m chunk b ofs .Readable := by
  refine ⟨fun o h1 h2 => ?_, h.2⟩
  have := h.1 o h1 h2
  unfold perm perm_order' at this ⊢
  split at this
  · exact perm_order_writable this
  · exact this

theorem contents_stored_same (chunk : memory_chunk) (m : mem) (b : block) (ofs : _root_.Int)
    (v : val) :
    contents_of (stored chunk m b ofs v) b = setN (encode_val chunk v) ofs (contents_of m b) := by
  simp [contents_of, stored, Std.TreeMap.getD_insert_self]

theorem contents_stored_other (chunk : memory_chunk) (m : mem) (b b' : block)
    (ofs : _root_.Int) (v : val) (h : b ≠ b') :
    contents_of (stored chunk m b ofs v) b' = contents_of m b' := by
  have : compare b b' ≠ .eq := fun e => h (Nat.compare_eq_eq.mp e)
  simp [contents_of, stored, Std.TreeMap.getD_insert, this]

theorem load_stored_long (m : mem) (b : block) (ofs : _root_.Int) (n : UInt64)
    (h : valid_access m .Mint64 b ofs .Writable) :
    load .Mint64 (stored .Mint64 m b ofs (.Vlong n)) b ofs = some (.Vlong n) := by
  unfold load
  rw [ite_eq_left ((valid_access_stored _ _ _ _ _ _ _ _ _).mpr (valid_access_readable h)),
    contents_stored_same]
  have : size_chunk_nat .Mint64 = (encode_val .Mint64 (.Vlong n)).length := by
    rw [length_encode_long]; rfl
  rw [this, getN_setN, decode_encode_long]

theorem load_stored_int (m : mem) (b : block) (ofs : _root_.Int) (n : UInt32)
    (h : valid_access m .Mint32 b ofs .Writable) :
    load .Mint32 (stored .Mint32 m b ofs (.Vint n)) b ofs = some (.Vint n) := by
  unfold load
  rw [ite_eq_left ((valid_access_stored _ _ _ _ _ _ _ _ _).mpr (valid_access_readable h)),
    contents_stored_same]
  have : size_chunk_nat .Mint32 = (encode_val .Mint32 (.Vint n)).length := by
    rw [length_encode_int]; rfl
  rw [this, getN_setN, decode_encode_int]

theorem load_stored_other (chunk chunk' : memory_chunk) (m : mem) (b b' : block)
    (ofs ofs' : _root_.Int) (v : val) (h : b ≠ b') :
    load chunk' (stored chunk m b ofs v) b' ofs' = load chunk' m b' ofs' := by
  unfold load
  rw [contents_stored_other _ _ _ _ _ _ h]
  rfl

end Mem

end LClight
