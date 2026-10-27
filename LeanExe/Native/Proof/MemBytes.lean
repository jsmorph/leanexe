import LeanExe.Native.Proof.Ops
import LeanExe.ProofKit.Memory

/-!
Bytes in the two memories.  `nbyte x j` is byte `j` of the number `x`, little-endian.  On Talos's
side, `Mem.write64` writes the bytes `nbyte x.toNat j` of the word `x`, and eight bytes read with
`Mem.read64` are the word whose bytes they are (`read64_of_nbytes`, `read64_eq_word`).  On the
side of the Lean copy of CompCert, `encode_val` writes the same bytes, `decode_val` reads them
back, and the casts between `unsigned char` and the integer types keep the low byte.  The copy's
`setN` and `getN` read and write runs of bytes, and `SameExcept b m m'` says that `m'` differs
from `m` at most in the contents of block `b`, so that loads from other blocks and every
permission stay the same.
-/

namespace LeanExe.Native

open Wasm LClight

/-- Byte `j` of `x`, little-endian. -/
def nbyte (x j : Nat) : UInt8 := UInt8.ofNat (x / 256 ^ j)

theorem nbyte_toNat (x j : Nat) : (nbyte x j).toNat = x / 256 ^ j % 256 := by
  simp [nbyte]

theorem nbyte_succ (x j : Nat) : nbyte x (j + 1) = nbyte (x / 256) j := by
  show UInt8.ofNat (x / 256 ^ (j + 1)) = UInt8.ofNat (x / 256 / 256 ^ j)
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem byte_repr_nat (x : Nat) : Byte.repr (x : _root_.Int) = nbyte x 0 := by
  apply UInt8.toNat_inj.mp
  rw [nbyte_toNat]
  simp only [Byte.repr, Byte.modulus]
  have : ((x : _root_.Int) % 2 ^ 8) = ((x % 256 : Nat) : _root_.Int) := by
    rw [Int.natCast_emod]; rfl
  rw [this, Int.toNat_natCast]
  simp

theorem bytes_of_int_nat (k x : Nat) :
    bytes_of_int k (x : _root_.Int) = (List.range k).map (nbyte x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [bytes_of_int]
      have e : (x : _root_.Int) / 256 = ((x / 256 : Nat) : _root_.Int) :=
        (Int.natCast_ediv x 256).symm
      rw [e, ih, byte_repr_nat]
      congr 1
      apply List.map_congr_left
      intro j _
      exact (nbyte_succ x j).symm

theorem int_of_bytes_bounds (bl : List byte) :
    0 ≤ int_of_bytes bl ∧ int_of_bytes bl < 256 ^ bl.length := by
  induction bl with
  | nil => simp [int_of_bytes]
  | cons b bl ih =>
      simp only [int_of_bytes, Byte.unsigned, List.length_cons]
      have hb := b.toNat_lt
      have : (256 : _root_.Int) ^ (bl.length + 1) = 256 ^ bl.length * 256 := pow_succ _ _
      rw [this]
      constructor <;> nlinarith [ih.1, ih.2]

theorem bytes_of_int_of_bytes (bl : List byte) :
    bytes_of_int bl.length (int_of_bytes bl) = bl := by
  induction bl with
  | nil => rfl
  | cons b bl ih =>
      simp only [List.length_cons, bytes_of_int, int_of_bytes, Byte.unsigned]
      have hb := b.toNat_lt
      have e1 : ((b.toNat : _root_.Int) + int_of_bytes bl * 256) / 256 = int_of_bytes bl := by
        omega
      rw [e1, ih]
      congr 1
      apply UInt8.toNat_inj.mp
      simp only [Byte.repr, Byte.modulus]
      have e2 : ((b.toNat : _root_.Int) + int_of_bytes bl * 256) % 2 ^ 8 = (b.toNat : _root_.Int) := by
        omega
      rw [e2, Int.toNat_natCast]
      simp

/-- The bytes that `Mem.write64` writes. -/
theorem write64_byte (x : UInt64) (j : Nat) (hj : j < 8) :
    ((x >>> UInt64.ofNat (8 * j)) &&& 0xFF).toUInt8 = nbyte x.toNat j := by
  apply UInt8.toNat_inj.mp
  rw [nbyte_toNat, UInt64.toNat_toUInt8, UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h8 : (UInt64.ofNat (8 * j)).toNat % 64 = 8 * j := by
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
    omega
  rw [h8, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul]]
  rw [show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem write64_bytes_at (wm : Wasm.Mem) (a : UInt32) (x : UInt64) (j : Nat) (hj : j < 8) :
    (wm.write64 a x).bytes (a.toNat + j) = nbyte x.toNat j := by
  rw [← write64_byte x j hj]
  unfold Wasm.Mem.write64
  dsimp only
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [UInt64.shiftRight_zero]
  all_goals first | omega | simp

theorem read64_of_nbytes (wm : Wasm.Mem) (a : UInt32) (x : UInt64)
    (h : ∀ j < 8, wm.bytes (a.toNat + j) = nbyte x.toNat j) : wm.read64 a = x := by
  rw [LeanExe.ProofKit.Memory.read64_congr a (m2 := wm.write64 a x) fun j hj => by
    rw [h j hj, write64_bytes_at _ _ _ j hj], LeanExe.ProofKit.Memory.read64_write64]

theorem uint8_toUInt64 (b : UInt8) : b.toUInt64 = UInt64.ofNat b.toNat := by
  apply UInt64.toNat_inj.mp
  have := b.toNat_lt
  rw [UInt8.toNat_toUInt64, UInt64.toNat_ofNat_of_lt'
    (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]


theorem read64_eq_word (wm : Wasm.Mem) (a : UInt32) :
    Int64.repr (int_of_bytes ((List.range 8).map fun j => wm.bytes (a.toNat + j))) =
      wm.read64 a := by
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
  symm
  apply read64_of_nbytes
  intro j hj
  have e := bytes_of_int_of_bytes ((List.range 8).map fun j => wm.bytes (a.toNat + j))
  rw [hlen, ← hx, bytes_of_int_nat] at e
  have e' := congrArg (fun l => l[j]?) e
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some] at e'
  exact (Option.some.inj e').symm

theorem cast_cbyte (y : UInt64) (m : mem) :
    sem_cast (.Vlong y) tulong tuchar m = some (.Vint (UInt32.ofNat (y.toNat % 256))) := by
  show some (val.Vint (cast_int_int .I8 .Unsigned (LClight.Int.repr (Int64.unsigned y)))) = _
  congr 2
  apply UInt32.toNat_inj.mp
  simp only [cast_int_int, LClight.Int.zero_ext, LClight.Int.repr, LClight.Int.unsigned,
    Int64.unsigned, LClight.Int.modulus]
  simp
  omega

theorem cast_uchar (n : Nat) (m : mem) :
    sem_cast (.Vint (UInt32.ofNat (n % 256))) tuchar tuchar m =
      some (.Vint (UInt32.ofNat (n % 256))) := by
  show some (val.Vint (cast_int_int .I8 .Unsigned (UInt32.ofNat (n % 256)))) = _
  congr 2
  apply UInt32.toNat_inj.mp
  simp only [cast_int_int, LClight.Int.zero_ext, LClight.Int.repr, LClight.Int.unsigned,
    LClight.Int.modulus]
  simp
  omega

theorem encode_cbyte (n : Nat) :
    encode_val .Mint8unsigned (.Vint (UInt32.ofNat (n % 256))) = [.Byte (UInt8.ofNat n)] := by
  simp only [encode_val, inj_bytes, encode_int, bytes_of_int, List.map]
  congr 2
  apply UInt8.toNat_inj.mp
  simp only [Byte.repr, Byte.modulus, LClight.Int.unsigned]
  simp
  omega

theorem decode_byte (b : UInt8) :
    decode_val .Mint8unsigned [.Byte b] = .Vint (UInt32.ofNat b.toNat) := by
  simp only [decode_val, proj_bytes, decode_int, int_of_bytes, Byte.unsigned]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [LClight.Int.zero_ext, LClight.Int.repr, LClight.Int.unsigned, LClight.Int.modulus]
  have := b.toNat_lt
  simp
  omega

theorem cast_byte_long (b : UInt8) (m : mem) :
    sem_cast (.Vint (UInt32.ofNat b.toNat)) tuchar tulong m = some (.Vlong b.toUInt64) := by
  show some (val.Vlong (cast_int_long .Unsigned (UInt32.ofNat b.toNat))) = _
  rw [uint8_toUInt64]
  congr 2
  simp only [cast_int_long, LClight.Int.unsigned, Int64.repr_natCast]
  congr 1
  simp

end LeanExe.Native

namespace LClight.Mem

theorem getN_map (n : Nat) (p : _root_.Int) (c : contents) :
    getN n p c = (List.range n).map fun (j : Nat) => ZMap.get (p + (j : _root_.Int)) c := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [getN, ih]
      congr 1
      · simp
      · apply List.map_congr_left
        intro j _
        simp only [Function.comp]
        congr 1
        omega

theorem setN_at (vl : List memval) (p : _root_.Int) (c : contents) (i : Nat)
    (hi : i < vl.length) : ZMap.get (p + i) (setN vl p c) = vl[i] := by
  induction vl generalizing p c i with
  | nil => simp at hi
  | cons v vl ih =>
      simp only [setN]
      cases i with
      | zero =>
          simp only [Nat.cast_zero, Int.add_zero, List.getElem_cons_zero]
          rw [setN_outside _ _ _ _ (by omega), zget_zset, ite_eq_left rfl]
      | succ i =>
          simp only [List.getElem_cons_succ]
          rw [show p + ((i + 1 : Nat) : _root_.Int) = (p + 1) + (i : _root_.Int) by omega]
          exact ih (p + 1) _ i (by simp at hi; omega)

theorem setN_above (vl : List memval) (p q : _root_.Int) (c : contents)
    (h : p + vl.length ≤ q) : ZMap.get q (setN vl p c) = ZMap.get q c := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v vl ih =>
      simp only [setN]
      simp only [List.length_cons] at h
      rw [ih (p + 1) _ (by omega), zget_zset, ite_eq_right (by omega)]

/-- `m'` differs from `m` at most in the contents of block `b`. -/
structure SameExcept (b : block) (m m' : mem) : Prop where
  access : m'.mem_access = m.mem_access
  other : ∀ b', b' ≠ b → contents_of m' b' = contents_of m b'

theorem SameExcept.refl (b : block) (m : mem) : SameExcept b m m := ⟨rfl, fun _ _ => rfl⟩

theorem SameExcept.trans {b : block} {m1 m2 m3 : mem} (h1 : SameExcept b m1 m2)
    (h2 : SameExcept b m2 m3) : SameExcept b m1 m3 :=
  ⟨h2.access.trans h1.access, fun b' hb => (h2.other b' hb).trans (h1.other b' hb)⟩

theorem SameExcept.of_stored (chunk : memory_chunk) (m : mem) (b : block) (ofs : _root_.Int)
    (v : val) : SameExcept b m (stored chunk m b ofs v) :=
  ⟨rfl, fun _ hb => contents_stored_other _ _ _ _ _ _ (Ne.symm hb)⟩

theorem SameExcept.perm_eq {b : block} {m m' : mem} (h : SameExcept b m m') :
    perm m' = perm m := by
  funext b' ofs k p
  simp only [perm, h.access]

theorem SameExcept.valid_access_eq {b : block} {m m' : mem} (h : SameExcept b m m') :
    valid_access m' = valid_access m := by
  funext chunk b' ofs p
  simp only [valid_access, range_perm, h.perm_eq]

theorem SameExcept.load_eq {b b' : block} {m m' : mem} (h : SameExcept b m m') (hb : b' ≠ b)
    (chunk : memory_chunk) (ofs : _root_.Int) : load chunk m' b' ofs = load chunk m b' ofs := by
  unfold load
  rw [h.other b' hb]
  by_cases hva : valid_access m chunk b' ofs .Readable
  · rw [ite_eq_left (by rw [h.valid_access_eq]; exact hva), ite_eq_left hva]
  · rw [ite_eq_right (by rw [h.valid_access_eq]; exact hva), ite_eq_right hva]

theorem perm_readable {m : mem} {b : block} {ofs : _root_.Int} (h : perm m b ofs .Cur .Writable) :
    perm m b ofs .Cur .Readable := by
  unfold perm perm_order' at h ⊢
  split at h
  · exact perm_order_writable h
  · exact h

end LClight.Mem
