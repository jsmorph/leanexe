import LeanExe.Native.ClightN.Leaf
import LeanExe.Native.Proof.Whole
import LeanExe.Native.Proof.MemBytes

/-!
The bytes of N's arrays (`clightn/N.nsx`) in the memory of the Lean copy of Clight.
`ArrHolds m b sz bs` states that the block `b` of `m` holds the bytes `bs 0` to `bs (sz - 1)` and
has permissions at no other offset.  A load from such a block reads the little-endian number of
its bytes and stays within `sz` (`loadv_arr` and the lemmas after it), and a store writes the
bytes of the stored number and changes nothing outside the block (`storev_arr`).  The memory of
`init_mem` gives each variable permissions only within the size of its initialization data
(`init_extent`), which bounds the accesses that a successful load or store makes.
-/

namespace ClightN.Proof

open LClight ClightN.Base ClightN.Spec

/-! ## Numbers of bytes -/

/-- The four and the eight bytes of `f` from `o`, little-endian, as N's `le4` and `le8` state
them. -/
def le4L (f : Int → Int) (o : Int) : Int :=
  f o + (256 * f (o + 1) + (65536 * f (o + 2) + 16777216 * f (o + 3)))

def le8L (f : Int → Int) (o : Int) : Int := le4L f o + 4294967296 * le4L f (o + 4)

/-- N's `woff k`, the offset of the word at the index `k`. -/
def woffL (k : UInt64) : Int := zmod (8 * u64 k) 18446744073709551616

/-- `mb` with the `c` bytes of `x` from `o` set to those of `w`, as N's `setbytes` states. -/
def setm (mb : ident → Int → Int) (x : ident) (o c w : Int) : ident → Int → Int :=
  fun y j => if y = x ∧ o ≤ j ∧ j < o + c then zmod (zdiv w (pow2 (8 * (j - o)))) 256
    else mb y j

theorem setm_spec (mb : ident → Int → Int) (x : ident) (o c w : Int) :
    ∀ y j, (y = x ∧ o ≤ j ∧ j < o + c →
        setm mb x o c w y j = zmod (zdiv w (pow2 (8 * (j - o)))) 256) ∧
      (¬ (y = x ∧ o ≤ j ∧ j < o + c) → setm mb x o c w y j = mb y j) :=
  fun _ _ => ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩

theorem byte_unsigned_repr {z : Int} (h0 : 0 ≤ z) (h1 : z < 256) :
    Byte.unsigned (Byte.repr z) = z := by
  simp only [Byte.unsigned, Byte.repr, Byte.modulus]
  have : z % 2 ^ 8 = z := Int.emod_eq_of_lt h0 (by simpa using h1)
  rw [this]
  simp
  omega

theorem byte_of_nat (w j : Nat) (hj : j < 8) :
    Byte.repr (zmod (zdiv (w : Int) (pow2 (8 * (j : Int)))) 256) = LeanExe.Native.nbyte w j := by
  apply UInt8.toNat_inj.mp
  rw [LeanExe.Native.nbyte_toNat]
  simp only [Byte.repr, Byte.modulus, zmod, zdiv, pow2]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega)
    with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-! ## Arrays in memory -/

/-- The block `b` of `m` holds the bytes `bs` from offset 0 to `sz - 1` and has permissions at no
other offset. -/
structure ArrHolds (m : mem) (b : block) (sz : Int) (bs : Int → Int) : Prop where
  exact : ∀ i k p, Mem.perm m b i k p → 0 ≤ i ∧ i < sz
  range : ∀ i, 0 ≤ i → i < sz → 0 ≤ bs i ∧ bs i < 256
  cont : ∀ i, 0 ≤ i → i < sz → ZMap.get i (Mem.contents_of m b) = .Byte (Byte.repr (bs i))

theorem ArrHolds.same {m m' : mem} {b b' : block} {sz : Int} {bs : Int → Int}
    (h : ArrHolds m b sz bs) (hs : Mem.SameExcept b' m m') (hb : b ≠ b') : ArrHolds m' b sz bs :=
  ⟨fun i k p hp => h.exact i k p (by rw [hs.perm_eq] at hp; exact hp), h.range,
    fun i h0 h1 => by rw [hs.other b hb]; exact h.cont i h0 h1⟩

theorem size_chunk_pos (chunk : memory_chunk) : 1 ≤ size_chunk chunk := by
  cases chunk <;> simp [size_chunk]

theorem size_chunk_nat_eq (chunk : memory_chunk) :
    (size_chunk_nat chunk : Int) = size_chunk chunk := by
  have := size_chunk_pos chunk
  simp only [size_chunk_nat]
  omega

/-- A load from an array reads the bytes from its offset and stays within the array. -/
theorem loadv_arr {A : Archi} {m : mem} {b : block} {sz : Int} {bs : Int → Int}
    {chunk : memory_chunk} {ofs : ptrofs} {v : val} (h : ArrHolds m b sz bs)
    (hl : Mem.loadv A chunk m (.Vptr b ofs) = some v) :
    Ptrofs.unsigned ofs + size_chunk chunk ≤ sz ∧
      v = decode_val A chunk ((List.range (size_chunk_nat chunk)).map fun (j : Nat) =>
        .Byte (Byte.repr (bs (Ptrofs.unsigned ofs + j)))) := by
  simp only [Mem.loadv] at hl
  split at hl
  · unfold Mem.load at hl
    split at hl
    · rename_i hva
      cases hl
      have hs := size_chunk_pos chunk
      have h0 : 0 ≤ Ptrofs.unsigned ofs := by simp [Ptrofs.unsigned]
      have hp := hva.1 (Ptrofs.unsigned ofs + size_chunk chunk - 1) (by omega) (by omega)
      have hb := (h.exact _ _ _ hp).2
      refine ⟨by omega, ?_⟩
      congr 1
      rw [Mem.getN_map]
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      have := size_chunk_nat_eq chunk
      exact h.cont _ (by omega) (by omega)
    · cases hl
  · cases hl

theorem decode_arr8 {A : Archi} (f : Int → Int) (o : Int)
    (hr : ∀ j : Int, 0 ≤ j → j < 8 → 0 ≤ f (o + j) ∧ f (o + j) < 256) :
    decode_val A .Mint64 ((List.range 8).map fun (j : Nat) => .Byte (Byte.repr (f (o + j)))) =
      .Vlong (r64 (le8L f o)) := by
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  have u : ∀ j : Int, 0 ≤ j → j < 8 → Byte.unsigned (Byte.repr (f (o + j))) = f (o + j) :=
    fun j h0 h1 => byte_unsigned_repr (hr j h0 h1).1 (hr j h0 h1).2
  simp only [List.map_cons, List.map_nil, decode_val, proj_bytes, decode_int, int_of_bytes,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  rw [u 0 (by omega) (by omega), u 1 (by omega) (by omega), u 2 (by omega) (by omega),
    u 3 (by omega) (by omega), u 4 (by omega) (by omega), u 5 (by omega) (by omega),
    u 6 (by omega) (by omega), u 7 (by omega) (by omega)]
  simp only [le8L, le4L, r64]
  rw [show o + 4 + 1 = o + 5 by omega, show o + 4 + 2 = o + 6 by omega,
    show o + 4 + 3 = o + 7 by omega, Int.add_zero]
  congr 2
  omega

theorem decode_arr4 {A : Archi} (f : Int → Int) (o : Int)
    (hr : ∀ j : Int, 0 ≤ j → j < 4 → 0 ≤ f (o + j) ∧ f (o + j) < 256) :
    decode_val A .Mint32 ((List.range 4).map fun (j : Nat) => .Byte (Byte.repr (f (o + j)))) =
      .Vint (r32 (le4L f o)) := by
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  have u : ∀ j : Int, 0 ≤ j → j < 4 → Byte.unsigned (Byte.repr (f (o + j))) = f (o + j) :=
    fun j h0 h1 => byte_unsigned_repr (hr j h0 h1).1 (hr j h0 h1).2
  simp only [List.map_cons, List.map_nil, decode_val, proj_bytes, decode_int, int_of_bytes,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  rw [u 0 (by omega) (by omega), u 1 (by omega) (by omega), u 2 (by omega) (by omega),
    u 3 (by omega) (by omega)]
  simp only [le4L, r32, Int.add_zero]
  congr 2
  omega

theorem decode_arr1 {A : Archi} (f : Int → Int) (o : Int) (hr : 0 ≤ f o ∧ f o < 256) :
    decode_val A .Mint8unsigned ((List.range 1).map fun (j : Nat) => .Byte (Byte.repr (f (o + j))))
      = .Vint (r32 (f o)) := by
  rw [show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil, Nat.cast_zero, Int.add_zero]
  rw [LeanExe.Native.decode_byte]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [r32, LClight.Int.repr, LClight.Int.modulus, Byte.repr, Byte.modulus]
  have := hr.1
  have := hr.2
  simp
  omega

/-- A store to an array writes the bytes of the stored number, from the store's offset within
the array, and leaves the rest of memory as it was. -/
theorem storev_arr {A : Archi} {m m' : mem} {b : block} {sz : Int} {bs : Int → Int}
    {chunk : memory_chunk} {ofs : ptrofs} {v : val} {w : Nat} (h : ArrHolds m b sz bs)
    (he : encode_val A chunk v = inj_bytes (bytes_of_int (size_chunk_nat chunk) (w : Int)))
    (hc : size_chunk_nat chunk ≤ 8)
    (hs : Mem.storev A chunk m (.Vptr b ofs) v = some m') :
    Ptrofs.unsigned ofs + size_chunk chunk ≤ sz ∧ Mem.SameExcept b m m' ∧
      ArrHolds m' b sz (fun j => if Ptrofs.unsigned ofs ≤ j ∧ j < Ptrofs.unsigned ofs +
        size_chunk chunk then zmod (zdiv (w : Int) (pow2 (8 * (j - Ptrofs.unsigned ofs)))) 256
        else bs j) := by
  simp only [Mem.storev] at hs
  split at hs
  · obtain ⟨hva, rfl⟩ := Mem.store_inv hs
    have hsz := size_chunk_pos chunk
    have hn := size_chunk_nat_eq chunk
    have h0 : 0 ≤ Ptrofs.unsigned ofs := by simp [Ptrofs.unsigned]
    have hp := hva.1 (Ptrofs.unsigned ofs + size_chunk chunk - 1) (by omega) (by omega)
    have hb := (h.exact _ _ _ hp).2
    have hse := Mem.SameExcept.of_stored (A := A) chunk m b (Ptrofs.unsigned ofs) v
    refine ⟨by omega, hse, fun i k p hp' => h.exact i k p (by rw [hse.perm_eq] at hp'; exact hp'),
      fun i h0 h1 => ?_, fun i h0 h1 => ?_⟩
    · split
      · simp only [zmod]; omega
      · exact h.range i h0 h1
    · rw [Mem.contents_stored_same]
      split
      · rename_i hin
        obtain ⟨j, rfl⟩ : ∃ j : Nat, i = Ptrofs.unsigned ofs + j :=
          ⟨(i - Ptrofs.unsigned ofs).toNat, by omega⟩
        have hj : j < size_chunk_nat chunk := by omega
        rw [he, LeanExe.Native.bytes_of_int_nat, Mem.setN_at _ _ _ j (by simp [inj_bytes]; omega)]
        simp only [inj_bytes, List.getElem_map, List.getElem_range]
        rw [show Ptrofs.unsigned ofs + (j : Int) - Ptrofs.unsigned ofs = (j : Int) by omega,
          byte_of_nat w j (by omega)]
      · rename_i hout
        by_cases hlt : i < Ptrofs.unsigned ofs
        · rw [Mem.setN_outside _ _ _ _ hlt]; exact h.cont i h0 h1
        · rw [Mem.setN_above _ _ _ _ (by
            rw [he]; simp [inj_bytes, LeanExe.Native.bytes_of_int_nat]; omega)]
          exact h.cont i h0 h1
  · cases hs

/-! ## Offsets -/

theorem unsigned_repr (z : Int) :
    Ptrofs.unsigned (Ptrofs.repr Archi.aarch64 z) = z % 18446744073709551616 :=
  uptr_rptr z

theorem off_eq (sz : Int) (k : UInt64) (h0 : 0 ≤ sz) (h1 : sz ≤ 8) :
    Ptrofs.add Archi.aarch64 Ptrofs.zero (Ptrofs.mul Archi.aarch64
      (Ptrofs.repr Archi.aarch64 sz) (Ptrofs.of_int64 Archi.aarch64 k)) = rptr (sz * u64 k) := by
  have hk := u64_range k
  simp only [u64] at hk
  simp only [Ptrofs.add, Ptrofs.mul, Ptrofs.of_int64, unsigned_repr]
  rw [Int.emod_eq_of_lt h0 (by omega), Int.emod_eq_of_lt hk.1 hk.2]
  have hz : Ptrofs.unsigned Ptrofs.zero = 0 := rfl
  rw [hz, Int.zero_add]
  simp only [rptr, u64, Ptrofs.repr, modulusPtr, Int.emod_emod]

theorem unsigned_rptr (z : Int) : Ptrofs.unsigned (rptr z) = zmod z 18446744073709551616 :=
  uptr_rptr z

/-! ## The permissions of initialized variables -/

section

variable {A : Archi} {F V : Type}

theorem store_access {chunk : memory_chunk} {m m' : mem} {b : block} {ofs : Int} {v : val}
    (h : Mem.store A chunk m b ofs v = some m') :
    m'.mem_access = m.mem_access ∧ m'.nextblock = m.nextblock := by
  obtain ⟨_, rfl⟩ := Mem.store_inv h
  exact ⟨rfl, rfl⟩

theorem store_zeros_access (b : block) : ∀ (n : Nat) (m : mem) (p : Int) (m' : mem),
    Genv.store_zeros.go A b n m p = some m' →
      m'.mem_access = m.mem_access ∧ m'.nextblock = m.nextblock
  | 0, m, p, m', h => by cases h; exact ⟨rfl, rfl⟩
  | n + 1, m, p, m', h => by
      simp only [Genv.store_zeros.go] at h
      split at h
      · rename_i m1 h1
        obtain ⟨a1, n1⟩ := store_access h1
        obtain ⟨a2, n2⟩ := store_zeros_access b n m1 (p + 1) m' h
        exact ⟨a2.trans a1, n2.trans n1⟩
      · cases h

theorem store_init_data_list_access (ge : Genv.t F V) (b : block) :
    ∀ (l : List init_data) (m : mem) (p : Int) (m' : mem),
      Genv.store_init_data_list A ge m b p l = some m' →
        m'.mem_access = m.mem_access ∧ m'.nextblock = m.nextblock
  | [], m, p, m', h => by cases h; exact ⟨rfl, rfl⟩
  | d :: l, m, p, m', h => by
      simp only [Genv.store_init_data_list] at h
      split at h
      · cases h
      · rename_i m1 h1
        obtain ⟨a2, n2⟩ := store_init_data_list_access ge b l m1 _ m' h
        have : m1.mem_access = m.mem_access ∧ m1.nextblock = m.nextblock := by
          cases d with
          | Init_space _ => cases h1; exact ⟨rfl, rfl⟩
          | Init_addrof s o =>
              simp only [Genv.store_init_data] at h1
              split at h1
              · cases h1
              · exact store_access h1
          | _ => exact store_access h1
        exact ⟨a2.trans this.1, n2.trans this.2⟩

/-- The block of a variable that `alloc_global` allocates has permissions only within the size of
the variable's initialization data, and no other block changes its permissions. -/
theorem alloc_global_access (ge : Genv.t F V) (m m' : mem) (g : ident × globdef F V)
    (h : Genv.alloc_global A ge m g = some m') :
    m'.nextblock = m.nextblock + 1 ∧
      (∀ b, b ≠ m.nextblock → ∀ ofs k, m'.mem_access b ofs k = m.mem_access b ofs k) ∧
      ∀ v, g.2 = .Gvar v → ∀ ofs k, m'.mem_access m.nextblock ofs k ≠ none →
        0 ≤ ofs ∧ ofs < init_data_list_size A v.gvar_init := by
  obtain ⟨id, d⟩ := g
  cases d with
  | Gfun f =>
      change Mem.drop_perm (Mem.alloc m 0 1).1 m.nextblock 0 1 .Nonempty = some m' at h
      simp only [Mem.drop_perm] at h
      split at h
      · cases h
        refine ⟨rfl, fun b hb ofs k => ?_, fun v hv => by cases hv⟩
        simp [Mem.alloc, hb]
      · cases h
  | Gvar v =>
      change (match Genv.store_zeros A (Mem.alloc m 0 (init_data_list_size A v.gvar_init)).1
          m.nextblock 0 (init_data_list_size A v.gvar_init) with
        | none => none
        | some m2 =>
          match Genv.store_init_data_list A ge m2 m.nextblock 0 v.gvar_init with
          | none => none
          | some m3 => Mem.drop_perm m3 m.nextblock 0 (init_data_list_size A v.gvar_init)
              (Genv.perm_globvar v)) = some m' at h
      split at h
      · cases h
      · rename_i m2 h2
        split at h
        · cases h
        · rename_i m3 h3
          obtain ⟨a2, n2⟩ := store_zeros_access m.nextblock _ _ _ _ h2
          obtain ⟨a3, n3⟩ := store_init_data_list_access ge m.nextblock _ _ _ _ h3
          simp only [Mem.drop_perm] at h
          split at h
          · cases h
            refine ⟨?_, fun b hb ofs k => ?_, fun v' hv' ofs k hne => ?_⟩
            · simp only [n3, n2, Mem.alloc]
            · simp only [hb, false_and, ite_false, a3, a2, Mem.alloc]
            · injection hv' with e
              subst e
              by_cases hin : 0 ≤ ofs ∧ ofs < init_data_list_size A v.gvar_init
              · exact hin
              · simp only [hin, and_false, ite_false, a3, a2, Mem.alloc, ite_true] at hne
                exact absurd rfl hne
          · cases h

theorem alloc_globals_access (ge : Genv.t F V) :
    ∀ (gl : List (ident × globdef F V)) (m m' : mem),
    Genv.alloc_globals A ge m gl = some m' →
      m'.nextblock = m.nextblock + gl.length ∧
      (∀ b, b < m.nextblock → ∀ ofs k, m'.mem_access b ofs k = m.mem_access b ofs k) ∧
      ∀ k (hk : k < gl.length) v, gl[k].2 = .Gvar v → ∀ ofs kd,
        m'.mem_access (m.nextblock + k) ofs kd ≠ none →
          0 ≤ ofs ∧ ofs < init_data_list_size A v.gvar_init
  | [], m, m', h => by
      cases h
      exact ⟨rfl, fun _ _ _ _ => rfl, fun k hk => absurd hk (by simp)⟩
  | g :: gl, m, m', h => by
      simp only [Genv.alloc_globals] at h
      split at h
      · cases h
      · rename_i m1 h1
        obtain ⟨n1, o1, e1⟩ := alloc_global_access ge m m1 g h1
        obtain ⟨n2, o2, e2⟩ := alloc_globals_access ge gl m1 m' h
        have hlen : (g :: gl).length = gl.length + 1 := List.length_cons
        refine ⟨?_, ?_, ?_⟩
        · rw [n2, n1, hlen, Nat.add_assoc, Nat.add_comm 1]
        · intro b hb ofs k
          have hb1 : b < m1.nextblock := by rw [n1]; exact Nat.lt_succ_of_lt hb
          exact (o2 b hb1 ofs k).trans (o1 b (Nat.ne_of_lt hb) ofs k)
        · intro k hk v hv ofs kd hne
          cases k with
          | zero =>
              have hb1 : m.nextblock + 0 < m1.nextblock := by
                rw [n1, Nat.add_zero]; exact Nat.lt_succ_self _
              rw [o2 _ hb1] at hne
              exact e1 v hv ofs kd hne
          | succ k =>
              have hne' : m'.mem_access (m1.nextblock + k) ofs kd ≠ none := by
                rw [n1, Nat.add_assoc, Nat.add_comm 1 k]
                exact hne
              have hk' : k < gl.length := by
                rw [hlen] at hk; exact Nat.lt_of_succ_lt_succ hk
              exact e2 k hk' v hv ofs kd hne'

end

end ClightN.Proof
