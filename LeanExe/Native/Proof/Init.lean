import LeanExe.Native.Proof.Correct

/-!
The initial state of a translated program.  `init_spec` follows `Genv.init_mem` through the
program's definitions, which `translate` lays out as `lx_status`, the Wasm globals, `lx_pages`,
`lx_mem`, `lx_pun`, the built-in `__builtin_fsqrt`, the result globals, the functions, and
`lx_init`: each takes the next block, and each variable holds its initializer, so that `envOf` names the blocks and the memory relates to the module's initial
globals, an `lx_status` of 0, and a zero memory of the initial pages.  `lx_init_correct` runs
`lx_init`, whose stores `exec_initStores` and `exec_segments` follow, and relates the memory it
leaves to `nativeStore`, Talos's initial store with the memory's cap set to the number of pages
of `lx_mem`.  `funcs_found` finds the program's functions in its own global environment.

The allocation lemmas of the first part hold for the definitions that the translator emits
(`Genv.InitShape`): `Genv.InitFact` states what a block holds after its allocation, and later
allocations, which touch only later blocks, keep it (`Mem.SameBlock`).
-/

namespace LClight

namespace Mem

/-- `m'` holds what `m` holds in block `b`: the same contents and permissions. -/
def SameBlock (b : block) (m m' : mem) : Prop :=
  contents_of m' b = contents_of m b ∧ ∀ ofs k, m'.mem_access b ofs k = m.mem_access b ofs k

theorem SameBlock.refl (b : block) (m : mem) : SameBlock b m m := ⟨rfl, fun _ _ => rfl⟩

theorem SameBlock.trans {b : block} {m1 m2 m3 : mem} (h1 : SameBlock b m1 m2)
    (h2 : SameBlock b m2 m3) : SameBlock b m1 m3 :=
  ⟨h2.1.trans h1.1, fun ofs k => (h2.2 ofs k).trans (h1.2 ofs k)⟩

theorem SameBlock.perm_eq {b : block} {m m' : mem} (h : SameBlock b m m') (ofs : _root_.Int)
    (k : perm_kind) (p : permission) : perm m' b ofs k p ↔ perm m b ofs k p := by
  simp only [perm, h.2 ofs k]

theorem SameBlock.valid_access_iff {b : block} {m m' : mem} (h : SameBlock b m m')
    (chunk : memory_chunk) (ofs : _root_.Int) (p : permission) :
    valid_access m' chunk b ofs p ↔ valid_access m chunk b ofs p := by
  simp only [valid_access, range_perm, h.perm_eq]

theorem SameBlock.load_eq {b : block} {m m' : mem} (h : SameBlock b m m') (chunk : memory_chunk)
    (ofs : _root_.Int) : load chunk m' b ofs = load chunk m b ofs := by
  unfold load
  rw [h.1]
  by_cases hva : valid_access m chunk b ofs .Readable
  · rw [ite_eq_left ((h.valid_access_iff _ _ _).mpr hva), ite_eq_left hva]
  · rw [ite_eq_right (fun x => hva ((h.valid_access_iff _ _ _).mp x)), ite_eq_right hva]

theorem SameBlock.of_stored {b b' : block} (chunk : memory_chunk) (m : mem) (ofs : _root_.Int)
    (v : val) (h : b' ≠ b) : SameBlock b m (stored chunk m b' ofs v) :=
  ⟨contents_stored_other _ _ _ _ _ _ h, fun _ _ => rfl⟩

theorem alloc_other (m : mem) (lo hi : _root_.Int) {b : block} (h : b ≠ m.nextblock) :
    SameBlock b m (alloc m lo hi).1 := by
  refine ⟨?_, fun ofs k => ?_⟩
  · have : compare m.nextblock b ≠ .eq := fun e => h (Nat.compare_eq_eq.mp e).symm
    simp [contents_of, alloc, Std.TreeMap.getD_insert, this]
  · simp [alloc, h]

theorem alloc_contents (m : mem) (lo hi : _root_.Int) :
    contents_of (alloc m lo hi).1 m.nextblock = ZMap.init := by
  simp [contents_of, alloc, Std.TreeMap.getD_insert_self]

theorem alloc_perm (m : mem) (lo hi : _root_.Int) {ofs : _root_.Int} (h1 : lo ≤ ofs) (h2 : ofs < hi)
    (k : perm_kind) (p : permission) : perm (alloc m lo hi).1 m.nextblock ofs k p := by
  simp only [perm, alloc, ite_true, h1, h2, and_self, ite_true, perm_order']
  exact .perm_F_any p

/-- `store_zeros` writes zero bytes from `p` on, when they can be written. -/
theorem store_zeros_go (b : block) : ∀ (n : Nat) (m : mem) (p : _root_.Int),
    (∀ ofs, p ≤ ofs → ofs < p + n → perm m b ofs .Cur .Writable) →
    ∃ m', Genv.store_zeros.go b n m p = some m' ∧ m'.nextblock = m.nextblock ∧
      m'.mem_access = m.mem_access ∧ (∀ b', b' ≠ b → contents_of m' b' = contents_of m b') ∧
      ∀ ofs, ZMap.get ofs (contents_of m' b) =
        if p ≤ ofs ∧ ofs < p + n then .Byte 0 else ZMap.get ofs (contents_of m b)
  | 0, m, p, _ => ⟨m, rfl, rfl, rfl, fun _ _ => rfl, fun ofs => by rw [ite_eq_right (by omega)]⟩
  | n + 1, m, p, hp => by
      have hva : valid_access m .Mint8unsigned b p .Writable :=
        ⟨fun ofs h1 h2 => by
          have h2' : ofs < p + 1 := h2
          exact hp ofs h1 (by omega), ⟨p, by simp [align_chunk]⟩⟩
      obtain ⟨m', hgo, hnext, hacc, hother, hc⟩ := store_zeros_go b n
        (stored .Mint8unsigned m b p Vzero) (p + 1) (fun ofs h1 h2 => hp ofs (by omega) (by omega))
      refine ⟨m', ?_, hnext, hacc, fun b' hb' => (hother b' hb').trans
        (contents_stored_other _ _ _ _ _ _ (Ne.symm hb')), fun ofs => ?_⟩
      · simp only [Genv.store_zeros.go, store_ok _ hva]
        exact hgo
      · rw [hc ofs, contents_stored_same]
        show (if p + 1 ≤ ofs ∧ ofs < p + 1 + n then _ else
          ZMap.get ofs (setN [.Byte (Byte.repr (Int.unsigned Int.zero))] p _)) = _
        by_cases h1 : p + 1 ≤ ofs ∧ ofs < p + 1 + n
        · rw [ite_eq_left h1, ite_eq_left (by push_cast; omega)]
        · rw [ite_eq_right h1]
          by_cases h2 : ofs = p
          · subst h2
            rw [ite_eq_left (by push_cast; omega)]
            have := setN_at [memval.Byte (Byte.repr (Int.unsigned Int.zero))] ofs
              (contents_of m b) 0 (by simp)
            simp only [Nat.cast_zero, Int.add_zero] at this
            rw [this]
            rfl
          · rw [ite_eq_right (by push_cast; omega)]
            rcases lt_or_gt_of_ne h2 with hlt | hgt
            · exact setN_outside _ _ _ _ hlt
            · exact setN_above _ _ _ _ (by simp; omega)

theorem drop_perm_ok {m : mem} {b : block} {lo hi : _root_.Int}
    (h : range_perm m b lo hi .Cur .Freeable) (p : permission) :
    drop_perm m b lo hi p = some { m with
      mem_access := fun b' ofs k =>
        if b' = b ∧ lo ≤ ofs ∧ ofs < hi then some p else m.mem_access b' ofs k } := by
  simp only [drop_perm, h, ite_true]

end Mem

namespace Genv

open Mem

variable {F V : Type}

/-- The definitions that the translator emits: functions, and writable variables initialized by
one `Init_int32`, `Init_int64`, or `Init_space`. -/
def InitShape : globdef F V → Prop
  | .Gfun _ => True
  | .Gvar v => v.gvar_readonly = false ∧ v.gvar_volatile = false ∧
      ((∃ n, v.gvar_init = [.Init_int32 n]) ∨ (∃ n, v.gvar_init = [.Init_int64 n]) ∨
        (∃ n : Nat, v.gvar_init = [.Init_space n]))

/-- What the block `b` of a definition holds after its allocation. -/
def InitFact (m : mem) (b : block) (g : globdef F V) : Prop :=
  ∀ v, g = .Gvar v →
    (∀ n, v.gvar_init = [.Init_int32 n] →
      load .Mint32 m b 0 = some (.Vint n) ∧ valid_access m .Mint32 b 0 .Writable) ∧
    (∀ n, v.gvar_init = [.Init_int64 n] →
      load .Mint64 m b 0 = some (.Vlong n) ∧ valid_access m .Mint64 b 0 .Writable) ∧
    (∀ n : _root_.Int, v.gvar_init = [.Init_space n] → ∀ i : Nat, (i : _root_.Int) < n →
      ZMap.get (i : _root_.Int) (contents_of m b) = .Byte 0 ∧
        perm m b (i : _root_.Int) .Cur .Writable)

theorem InitFact.same {m m' : mem} {b : block} {g : globdef F V} (h : InitFact m b g)
    (hs : SameBlock b m m') : InitFact m' b g := by
  intro v hv
  obtain ⟨h1, h2, h3⟩ := h v hv
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn i hi => ?_⟩
  · exact ⟨by rw [hs.load_eq]; exact (h1 n hn).1, (hs.valid_access_iff _ _ _).mpr (h1 n hn).2⟩
  · exact ⟨by rw [hs.load_eq]; exact (h2 n hn).1, (hs.valid_access_iff _ _ _).mpr (h2 n hn).2⟩
  · exact ⟨by rw [hs.1]; exact (h3 n hn i hi).1, (hs.perm_eq _ _ _).mpr (h3 n hn i hi).2⟩

/-- The memory after `drop_perm` of a range of a fresh block. -/
def dropped (m : mem) (b : block) (lo hi : _root_.Int) (p : permission) : mem :=
  { m with mem_access := fun b' ofs k =>
      if b' = b ∧ lo ≤ ofs ∧ ofs < hi then some p else m.mem_access b' ofs k }

theorem dropped_perm {m : mem} {b : block} {lo hi ofs : _root_.Int} {p : permission}
    (h1 : lo ≤ ofs) (h2 : ofs < hi) (k : perm_kind) {p' : permission} (hp : perm_order p p') :
    perm (dropped m b lo hi p) b ofs k p' := by
  simp only [perm, dropped, h1, h2, and_self, ite_true, perm_order']
  exact hp

theorem dropped_other {m : mem} {b b' : block} {lo hi : _root_.Int} {p : permission}
    (h : b' ≠ b) : SameBlock b' m (dropped m b lo hi p) :=
  ⟨rfl, fun ofs k => by simp [dropped, h]⟩

theorem load_of_contents {m m' : mem} {b : block} {chunk : memory_chunk} {ofs : _root_.Int}
    (hc : contents_of m' b = contents_of m b) (hv' : valid_access m' chunk b ofs .Readable)
    (hv : valid_access m chunk b ofs .Readable) : load chunk m' b ofs = load chunk m b ofs := by
  unfold load
  rw [ite_eq_left hv', ite_eq_left hv, hc]

theorem alloc_global_spec (ge : t F V) (m : mem) (g : ident × globdef F V)
    (hg : InitShape g.2) :
    ∃ m', alloc_global ge m g = some m' ∧ m'.nextblock = m.nextblock + 1 ∧
      (∀ b, b ≠ m.nextblock → SameBlock b m m') ∧ InitFact m' m.nextblock g.2 := by
  obtain ⟨id, g⟩ := g
  cases g with
  | Gfun f =>
      have hr : range_perm (alloc m 0 1).1 m.nextblock 0 1 .Cur .Freeable :=
        fun ofs h1 h2 => alloc_perm m 0 1 h1 h2 _ _
      refine ⟨dropped (alloc m 0 1).1 m.nextblock 0 1 .Nonempty, ?_, rfl, fun b hb => ?_,
        fun v hv => by cases hv⟩
      · show drop_perm (alloc m 0 1).1 (alloc m 0 1).2 0 1 .Nonempty = _
        exact drop_perm_ok hr _
      · refine (alloc_other m 0 1 hb).trans ⟨rfl, fun ofs k => ?_⟩
        simp [dropped, hb]
  | Gvar v =>
      obtain ⟨hro, hvol, hinit⟩ := hg
      have hperm : perm_globvar v = .Writable := by simp [perm_globvar, hro, hvol]
      -- The block, zeroed: the steps that every variable takes.
      have hsz0 : 0 ≤ init_data_list_size v.gvar_init := by
        rcases hinit with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ <;> rw [hn] <;>
          simp [init_data_list_size, init_data_size]
      obtain ⟨m2, hgo, hnext2, hacc2, hoth2, hc2⟩ := store_zeros_go m.nextblock
        (init_data_list_size v.gvar_init).toNat (alloc m 0 (init_data_list_size v.gvar_init)).1 0
        (fun ofs h1 h2 => by
          have := alloc_perm m 0 (init_data_list_size v.gvar_init) h1 (by omega) .Cur .Writable
          exact this)
      have hzero : Genv.store_zeros (alloc m 0 (init_data_list_size v.gvar_init)).1 m.nextblock 0
          (init_data_list_size v.gvar_init) = some m2 := hgo
      have hperm2 : ∀ ofs, 0 ≤ ofs → ofs < init_data_list_size v.gvar_init →
          ∀ k p, perm m2 m.nextblock ofs k p := fun ofs h1 h2 k p => by
        simp only [perm, hacc2]
        exact alloc_perm m 0 _ h1 h2 k p
      have hcont2 : ∀ ofs, ZMap.get ofs (contents_of m2 m.nextblock) =
          if 0 ≤ ofs ∧ ofs < init_data_list_size v.gvar_init then .Byte 0 else .Undef := by
        intro ofs
        rw [hc2 ofs, alloc_contents]
        split_ifs <;> first | rfl | omega
      have hother2 : ∀ b, b ≠ m.nextblock → SameBlock b m m2 := fun b hb =>
        (alloc_other m 0 _ hb).trans ⟨hoth2 b hb, fun ofs k => by rw [hacc2]⟩
      have hnext2' : m2.nextblock = m.nextblock + 1 := hnext2
      -- The allocation, for the memory `m3` after the initializers.
      have hfinish : ∀ m3, store_init_data_list ge m2 m.nextblock 0 v.gvar_init = some m3 →
          m3.mem_access = m2.mem_access → m3.nextblock = m2.nextblock →
          (∀ b, b ≠ m.nextblock → contents_of m3 b = contents_of m2 b) →
          alloc_global ge m (id, .Gvar v) =
            some (dropped m3 m.nextblock 0 (init_data_list_size v.gvar_init) .Writable) ∧
          (dropped m3 m.nextblock 0 (init_data_list_size v.gvar_init) .Writable).nextblock =
            m.nextblock + 1 ∧
          ∀ b, b ≠ m.nextblock →
            SameBlock b m (dropped m3 m.nextblock 0 (init_data_list_size v.gvar_init) .Writable) := by
        intro m3 hsi hacc3 hnext3 hc3
        have hrp : range_perm m3 m.nextblock 0 (init_data_list_size v.gvar_init) .Cur .Freeable :=
          fun ofs h1 h2 => by
            have := hperm2 ofs h1 h2 .Cur .Freeable
            simp only [perm, hacc3] at this ⊢
            exact this
        refine ⟨?_, by simp only [dropped]; rw [hnext3]; exact hnext2', fun b hb =>
          ((hother2 b hb).trans ⟨hc3 b hb, fun ofs k => by rw [hacc3]⟩).trans (dropped_other hb)⟩
        show (match Genv.store_zeros (alloc m 0 (init_data_list_size v.gvar_init)).1 m.nextblock 0
            (init_data_list_size v.gvar_init) with
          | none => none
          | some m2 =>
            match store_init_data_list ge m2 m.nextblock 0 v.gvar_init with
            | none => none
            | some m3 => drop_perm m3 m.nextblock 0 (init_data_list_size v.gvar_init)
                (perm_globvar v)) = _
        rw [hzero]
        dsimp only
        rw [hsi]
        dsimp only
        rw [hperm]
        exact drop_perm_ok hrp _
      rcases hinit with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨N, hn⟩
      · have hsz : init_data_list_size v.gvar_init = 4 := by rw [hn]; rfl
        have hva : valid_access m2 .Mint32 m.nextblock 0 .Writable :=
          ⟨fun ofs h1 h2 => hperm2 ofs h1 (by rw [hsz]; exact h2) _ _, ⟨0, rfl⟩⟩
        have hsi : store_init_data_list ge m2 m.nextblock 0 v.gvar_init =
            some (stored .Mint32 m2 m.nextblock 0 (.Vint n)) := by
          rw [hn]
          simp only [store_init_data_list, store_init_data, store_ok _ hva]
        obtain ⟨h1, h2, h3⟩ := hfinish _ hsi rfl rfl
          (fun b hb => contents_stored_other _ _ _ _ _ _ (Ne.symm hb))
        refine ⟨_, h1, h2, h3, fun v' hv' => ?_⟩
        injection hv' with e
        subst e
        refine ⟨?_, ?_, ?_⟩
        rotate_left
        · intro n' hn'; rw [hn] at hn'; cases hn'
        · intro n' hn'; rw [hn] at hn'; cases hn'
        intro n' hn'
        rw [hn] at hn'
        injection hn' with e
        injection e with e
        subst e
        have hvd : valid_access (dropped (stored .Mint32 m2 m.nextblock 0 (.Vint n)) m.nextblock 0
            (init_data_list_size v.gvar_init) .Writable) .Mint32 m.nextblock 0 .Writable :=
          ⟨fun ofs h1 h2 => dropped_perm h1 (by rw [hsz]; exact h2) _ (.perm_refl _), ⟨0, rfl⟩⟩
        refine ⟨?_, hvd⟩
        rw [load_of_contents (m := stored .Mint32 m2 m.nextblock 0 (.Vint n))
          (m' := dropped (stored .Mint32 m2 m.nextblock 0 (.Vint n)) m.nextblock 0
            (init_data_list_size v.gvar_init) .Writable) rfl
          (valid_access_readable hvd) (valid_access_readable hva)]
        exact load_stored_int _ _ _ _ hva
      · have hsz : init_data_list_size v.gvar_init = 8 := by rw [hn]; rfl
        have hva : valid_access m2 .Mint64 m.nextblock 0 .Writable :=
          ⟨fun ofs h1 h2 => hperm2 ofs h1 (by rw [hsz]; exact h2) _ _, ⟨0, rfl⟩⟩
        have hsi : store_init_data_list ge m2 m.nextblock 0 v.gvar_init =
            some (stored .Mint64 m2 m.nextblock 0 (.Vlong n)) := by
          rw [hn]
          simp only [store_init_data_list, store_init_data, store_ok _ hva]
        obtain ⟨h1, h2, h3⟩ := hfinish _ hsi rfl rfl
          (fun b hb => contents_stored_other _ _ _ _ _ _ (Ne.symm hb))
        refine ⟨_, h1, h2, h3, fun v' hv' => ?_⟩
        injection hv' with e
        subst e
        refine ⟨?_, ?_, ?_⟩
        · intro n' hn'; rw [hn] at hn'; cases hn'
        rotate_left
        · intro n' hn'; rw [hn] at hn'; cases hn'
        intro n' hn'
        rw [hn] at hn'
        injection hn' with e
        injection e with e
        subst e
        have hvd : valid_access (dropped (stored .Mint64 m2 m.nextblock 0 (.Vlong n)) m.nextblock 0
            (init_data_list_size v.gvar_init) .Writable) .Mint64 m.nextblock 0 .Writable :=
          ⟨fun ofs h1 h2 => dropped_perm h1 (by rw [hsz]; exact h2) _ (.perm_refl _), ⟨0, rfl⟩⟩
        refine ⟨?_, hvd⟩
        rw [load_of_contents (m := stored .Mint64 m2 m.nextblock 0 (.Vlong n))
          (m' := dropped (stored .Mint64 m2 m.nextblock 0 (.Vlong n)) m.nextblock 0
            (init_data_list_size v.gvar_init) .Writable) rfl
          (valid_access_readable hvd) (valid_access_readable hva)]
        exact load_stored_long _ _ _ _ hva
      · have hsz : init_data_list_size v.gvar_init = N := by
          rw [hn]; simp [init_data_list_size, init_data_size]
        have hsi : store_init_data_list ge m2 m.nextblock 0 v.gvar_init = some m2 := by
          rw [hn]; rfl
        obtain ⟨h1, h2, h3⟩ := hfinish _ hsi rfl rfl (fun _ _ => rfl)
        refine ⟨_, h1, h2, h3, fun v' hv' => ?_⟩
        injection hv' with e
        subst e
        refine ⟨?_, ?_, ?_⟩
        · intro n' hn'; rw [hn] at hn'; cases hn'
        · intro n' hn'; rw [hn] at hn'; cases hn'
        intro n' hn' i hi
        rw [hn] at hn'
        injection hn' with e
        injection e with e
        subst e
        refine ⟨?_, dropped_perm (by omega) (by rw [hsz]; exact hi) _ (.perm_refl _)⟩
        show ZMap.get (i : _root_.Int) (contents_of m2 m.nextblock) = _
        rw [hcont2, ite_eq_left (by rw [hsz]; omega)]


theorem alloc_globals_spec (ge : t F V) : ∀ (gl : List (ident × globdef F V)) (m : mem),
    (∀ g ∈ gl, InitShape g.2) →
    ∃ m', alloc_globals ge m gl = some m' ∧ m'.nextblock = m.nextblock + gl.length ∧
      (∀ b, b < m.nextblock → SameBlock b m m') ∧
      ∀ k (hk : k < gl.length), InitFact m' (m.nextblock + k) gl[k].2
  | [], m, _ => ⟨m, rfl, rfl, fun _ _ => SameBlock.refl _ _, fun k hk => absurd hk (by simp)⟩
  | g :: gl, m, h => by
      obtain ⟨m1, h1, hn1, hs1, hf1⟩ := alloc_global_spec ge m g (h g (by simp))
      obtain ⟨m', h', hn', hs', hf'⟩ := alloc_globals_spec ge gl m1
        (fun g hg => h g (by simp [hg]))
      refine ⟨m', by simp only [alloc_globals, h1]; exact h',
        by rw [hn', hn1, List.length_cons, Nat.add_assoc, Nat.add_comm 1 gl.length],
        fun b hb => (hs1 b (Nat.ne_of_lt hb)).trans (hs' b (by rw [hn1]; exact Nat.lt_succ_of_lt hb)),
        fun k hk => ?_⟩
      cases k with
      | zero => exact hf1.same (hs' _ (by rw [hn1]; exact Nat.lt_succ_self _))
      | succ k =>
          have := hf' k (Nat.lt_of_succ_lt_succ hk)
          rw [hn1, Nat.add_assoc, Nat.add_comm 1 k] at this
          exact this

theorem find_add_globals_idx (ge : t F V) (gl : List (ident × globdef F V))
    (hnodup : (gl.map (·.1)).Nodup) : ∀ k (hk : k < gl.length),
      find_symbol (add_globals ge gl) gl[k].1 = some (ge.genv_next + k) ∧
        find_def (add_globals ge gl) (ge.genv_next + k) = some gl[k].2 := by
  induction gl generalizing ge with
  | nil => intro k hk; simp at hk
  | cons x gl ih =>
      intro k hk
      simp only [List.map_cons, List.nodup_cons] at hnodup
      cases k with
      | zero =>
          obtain ⟨h1, h2⟩ := add_globals_keep (add_global ge x) gl
          refine ⟨?_, ?_⟩
          · show find_symbol _ x.1 = _
            rw [add_globals_cons, h1 x.1 hnodup.1]
            exact Std.TreeMap.getElem?_insert_self
          · show find_def _ ge.genv_next = some x.2
            rw [add_globals_cons, h2 _ (Nat.lt_succ_self _)]
            exact Std.TreeMap.getElem?_insert_self
      | succ k =>
          obtain ⟨h1, h2⟩ := ih (add_global ge x) hnodup.2 k (by simpa using hk)
          rw [add_globals_cons]
          have e : (add_global ge x).genv_next + k = ge.genv_next + (k + 1) := by
            show ge.genv_next + 1 + k = _
            rw [Nat.add_assoc, Nat.add_comm 1 k]
          rw [e] at h1 h2
          exact ⟨h1, h2⟩

end Genv

end LClight

namespace LeanExe.Native

open Wasm LClight

/-! ## The definitions of a translation -/

/-- The definitions of a translated program. -/
def progDefs (cap : Nat) (decl : MemDecl) (gdefs : List (globvar type)) (nres : Nat)
    (funs : List (ident × globdef (fundef function) type)) :
    List (ident × globdef (fundef function) type) :=
  (statusId, .Gvar statusVar) ::
    (gdefs.zipIdx.map (fun x => (globalId x.2, globdef.Gvar x.1)) ++
      (pagesId, .Gvar (pagesDef decl.pagesMin.toNat)) :: (memId, .Gvar (memDef cap)) ::
        (punId, .Gvar punDef) :: (sqrtId, sqrtDef) ::
          (resDefs nres ++ (funs ++ [(initId, .Gfun (.Internal (initFunction cap decl.data)))])))

theorem translate_defs {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T) :
    ∃ decl gdefs funs, m.memory = some decl ∧ violation m = none ∧
      decl.pagesMin.toNat ≤ cap ∧ cap ≤ 65535 ∧ m.globals.mapM globalDef = some gdefs ∧
      (includedOf cap m).mapM (funDef cap m) = some funs ∧
      T.cprogram.prog_defs = progDefs cap decl gdefs T.nres funs := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨hv, decl, hdecl, ⟨hc1, hc2⟩, gdefs, hg, -, funs, hfuns, rfl⟩ := h
  exact ⟨decl, gdefs, funs, hdecl, hv, hc1, hc2, hg, hfuns, rfl⟩

/-- The identifiers of the result globals. -/
def resIds (nres : Nat) : List Nat :=
  (List.range nres).flatMap fun i => resTypes.map (resId i)

theorem resDefs_ids (nres : Nat) : (resDefs nres).map (·.1) = resIds nres := by
  simp [resDefs, resIds, List.map_flatMap, Function.comp_def]

theorem resIds_succ (n : Nat) :
    resIds (n + 1) = resIds n ++ [resId n .i32, resId n .i64, resId n .f64, resId n .f32] := by
  simp [resIds, List.range_succ, List.flatMap_append, resTypes]

theorem mem_resIds {n x : Nat} (h : x ∈ resIds n) :
    x % 4 = 0 ∧ 36 ≤ x ∧ x < 32 * n + 36 := by
  induction n with
  | zero => simp [resIds] at h
  | succ n ih =>
      rw [resIds_succ] at h
      rcases List.mem_append.mp h with h | h
      · have := ih h; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp [resId, VT.code] <;> omega

theorem resIds_nodup (n : Nat) : List.Nodup (α := Nat) (resIds n) := by
  induction n with
  | zero => simp [resIds]
  | succ n ih =>
      rw [resIds_succ]
      unfold List.Nodup at *
      refine List.pairwise_append.mpr ⟨ih, ?_, fun a ha b hb => ?_⟩
      · simp [resId, VT.code]
      · have := mem_resIds ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> simp [resId, VT.code] <;> omega

theorem resDefs_succ (n : Nat) : resDefs (n + 1) = resDefs n ++
    [(resId n .i32, .Gvar (resDef .i32)), (resId n .i64, .Gvar (resDef .i64)),
      (resId n .f64, .Gvar (resDef .f64)), (resId n .f32, .Gvar (resDef .f32))] := by
  simp [resDefs, List.range_succ, List.flatMap_append, resTypes]

theorem resDefs_length (n : Nat) : (resDefs n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resDefs_succ]; simp [ih]; omega

/-- The place of a type among the result globals of a position. -/
def VT.resIdx : VT → Nat
  | .i32 => 0
  | .i64 => 1
  | .f64 => 2
  | .f32 => 3

/-- The offset of result global `(i, t)` among the result globals. -/
def resOfs (i : Nat) (t : VT) : Nat := 4 * i + t.resIdx

theorem resIdx_lt {t : VT} (ht : t.isRes = true) : t.resIdx < 4 := by
  rcases VT.isRes_cases ht with rfl | rfl | rfl | rfl <;> decide

theorem resDefs_get (n i : Nat) (hi : i < n) (t : VT) (ht : t.isRes = true) :
    (resDefs n)[resOfs i t]? = some (resId i t, .Gvar (resDef t)) := by
  unfold resOfs
  have h3 := resIdx_lt ht
  induction n with
  | zero => omega
  | succ n ih =>
      have hlen := resDefs_length n
      rw [resDefs_succ]
      by_cases hin : i < n
      · rw [List.getElem?_append_left (by omega)]
        exact ih hin
      · have : i = n := by omega
        subst this
        rw [List.getElem?_append_right (by omega), hlen]
        rcases VT.isRes_cases ht with rfl | rfl | rfl | rfl <;> simp [VT.resIdx]

theorem closeUnderCalls_sublist (calls : Nat → List Nat) :
    ∀ (fuel : Nat) (ks : List Nat), (closeUnderCalls calls fuel ks).Sublist ks
  | 0, _ => List.Sublist.refl _
  | fuel + 1, ks => by
      unfold closeUnderCalls
      dsimp only
      split
      · exact List.Sublist.refl _
      · exact (closeUnderCalls_sublist calls fuel _).trans List.filter_sublist

theorem includedOf_nodup (cap : Nat) (m : Module) : (includedOf cap m).Nodup :=
  ((closeUnderCalls_sublist _ _ _).trans List.filter_sublist).nodup List.nodup_range

theorem funDef_ids {cap : Nat} {m : Module} : ∀ {ks : List Nat}
    {funs : List (ident × globdef (fundef function) type)},
    ks.mapM (funDef cap m) = some funs → funs.map (·.1) = ks.map funId ∧
      ∀ d ∈ funs, ∃ fd, d.2 = .Gfun (.Internal fd)
  | [], funs, h => by simp at h; subst h; simp
  | k :: ks, funs, h => by
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨d, gd, hd, rest, hrest, rfl⟩ := h
      obtain ⟨h1, h2⟩ := funDef_ids hrest
      cases hfd : (fdefsOf cap m)[k]?.join with
      | none => simp [funDef, hfd] at hd
      | some fd =>
          simp [funDef, hfd] at hd
          obtain ⟨rfl, rfl⟩ := hd
          refine ⟨by simp [h1], fun d hd' => ?_⟩
          rcases List.mem_cons.mp hd' with rfl | hd'
          · exact ⟨fd, rfl⟩
          · exact h2 d hd'

theorem globalDef_shape {g : GlobalDecl} {gv : globvar type} (h : globalDef g = some gv) :
    ∃ n, g.init = .i64 n ∧ gv.gvar_init = [.Init_int64 n] ∧ gv.gvar_readonly = false ∧
      gv.gvar_volatile = false := by
  unfold globalDef at h
  split at h
  · rename_i n hn
    cases h
    exact ⟨n, hn, rfl, rfl, rfl⟩
  · cases h

theorem zipIdx_ids (gdefs : List (globvar type)) :
    (gdefs.zipIdx.map (fun x => (globalId x.2, globdef.Gvar (F := fundef function) x.1))).map (·.1) =
      (List.range gdefs.length).map globalId := by
  rw [List.map_map, List.range_eq_range']
  have : ((fun (x : ident × globdef (fundef function) type) => x.1) ∘
      fun (x : globvar type × Nat) => (globalId x.2, globdef.Gvar (F := fundef function) x.1)) =
      globalId ∘ Prod.snd := rfl
  rw [this, ← List.map_map, List.zipIdx_map_snd]

theorem ids_nodup (G nres : Nat) (ks : List Nat) (hks : ks.Nodup) :
    List.Nodup (α := Nat)
      (statusId :: ((List.range G).map globalId ++ pagesId :: memId :: punId :: sqrtId ::
        (resIds nres ++ (ks.map funId ++ [initId])))) := by
  have hg : List.Nodup (α := Nat) ((List.range G).map globalId) :=
    List.Nodup.map (fun a b h => by
      have h' : 4 * a + 2 = 4 * b + 2 := h
      omega) List.nodup_range
  have hf : List.Nodup (α := Nat) (ks.map funId) := List.Nodup.map (fun a b h => funId_inj h) hks
  have hmg : ∀ x : Nat, x ∈ (List.range G).map globalId → x % 4 = 2 := by
    intro x hx
    obtain ⟨i, -, hi⟩ := List.mem_map.mp hx
    have : x = 4 * i + 2 := hi.symm
    omega
  have hmf : ∀ x : Nat, x ∈ ks.map funId → x % 4 = 3 := by
    intro x hx
    obtain ⟨i, -, hi⟩ := List.mem_map.mp hx
    have : x = 4 * i + 3 := hi.symm
    omega
  unfold List.Nodup at *
  have h3 : List.Pairwise (α := Nat) (· ≠ ·) (ks.map funId ++ [initId]) :=
    List.pairwise_append.mpr ⟨hf, List.pairwise_singleton _ _, fun a ha b hb => by
      rw [List.mem_singleton] at hb
      subst hb
      have := hmf a ha
      unfold initId; omega⟩
  have hr := resIds_nodup nres
  unfold List.Nodup at hr
  have h4 : List.Pairwise (α := Nat) (· ≠ ·) (resIds nres ++ (ks.map funId ++ [initId])) := by
    refine List.pairwise_append.mpr ⟨hr, h3, fun a ha b hb => ?_⟩
    have := mem_resIds ha
    rcases List.mem_append.mp hb with hb | hb
    · have := hmf b hb; omega
    · rw [List.mem_singleton] at hb; subst hb; unfold initId; omega
  -- Membership in the tail after `__builtin_fsqrt`: residues and bounds.
  have htail : ∀ a : Nat, a ∈ resIds nres ++ (ks.map funId ++ [initId]) →
      (a % 4 = 0 ∧ (a = 16 ∨ 36 ≤ a)) ∨ a % 4 = 3 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have := mem_resIds ha; omega
    rcases List.mem_append.mp ha with ha | ha
    · have := hmf a ha; omega
    · rw [List.mem_singleton] at ha; subst ha; unfold initId; omega
  have h5 : List.Pairwise (α := Nat) (· ≠ ·)
      (punId :: sqrtId :: (resIds nres ++ (ks.map funId ++ [initId]))) := by
    refine List.pairwise_cons.mpr ⟨fun a ha => ?_, List.pairwise_cons.mpr ⟨fun a ha => ?_, h4⟩⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · decide
      · have := htail a ha; unfold punId; omega
    · have := htail a ha; unfold sqrtId; omega
  -- Membership after `lx_mem`.
  have htail2 : ∀ a : Nat, a ∈ punId :: sqrtId :: (resIds nres ++ (ks.map funId ++ [initId])) →
      (a % 4 = 0 ∧ 16 ≤ a) ∨ a % 4 = 3 := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · left; decide
    rcases List.mem_cons.mp ha with rfl | ha
    · left; decide
    have := htail a ha; omega
  have h2 : List.Pairwise (α := Nat) (· ≠ ·)
      (pagesId :: memId :: punId :: sqrtId :: (resIds nres ++ (ks.map funId ++ [initId]))) := by
    refine List.pairwise_cons.mpr ⟨fun a ha => ?_, List.pairwise_cons.mpr ⟨fun a ha => ?_, h5⟩⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · decide
      · have := htail2 a ha; unfold pagesId; omega
    · have := htail2 a ha; unfold memId; omega
  have h1 : List.Pairwise (α := Nat) (· ≠ ·)
      ((List.range G).map globalId ++ pagesId :: memId :: punId :: sqrtId ::
        (resIds nres ++ (ks.map funId ++ [initId]))) := by
    refine List.pairwise_append.mpr ⟨hg, h2, fun a ha b hb => ?_⟩
    have := hmg a ha
    rcases List.mem_cons.mp hb with rfl | hb
    · unfold pagesId; omega
    rcases List.mem_cons.mp hb with rfl | hb
    · unfold memId; omega
    have := htail2 b hb; omega
  refine List.pairwise_cons.mpr ⟨fun a ha => ?_, h1⟩
  rcases List.mem_append.mp ha with ha | ha
  · have := hmg a ha; unfold statusId; omega
  rcases List.mem_cons.mp ha with rfl | ha
  · decide
  rcases List.mem_cons.mp ha with rfl | ha
  · decide
  have := htail2 a ha; unfold statusId; omega

theorem progDefs_ids (cap : Nat) (decl : MemDecl) (gdefs : List (globvar type)) (nres : Nat)
    (funs : List (ident × globdef (fundef function) type)) :
    (progDefs cap decl gdefs nres funs).map (·.1) =
      statusId :: ((List.range gdefs.length).map globalId ++
        pagesId :: memId :: punId :: sqrtId :: (resIds nres ++ (funs.map (·.1) ++ [initId]))) := by
  simp only [progDefs, List.map_cons, List.map_append, zipIdx_ids, List.map_nil, resDefs_ids]

theorem progDefs_nodup {cap : Nat} {m : Module} {decl : MemDecl} {gdefs : List (globvar type)}
    {nres : Nat} {funs : List (ident × globdef (fundef function) type)}
    (hfuns : (includedOf cap m).mapM (funDef cap m) = some funs) :
    ((progDefs cap decl gdefs nres funs).map (·.1)).Nodup := by
  rw [progDefs_ids, (funDef_ids hfuns).1]
  exact ids_nodup _ _ _ (includedOf_nodup cap m)

theorem progDefs_shape {cap : Nat} {m : Module} {decl : MemDecl} {gdefs : List (globvar type)}
    {nres : Nat} {funs : List (ident × globdef (fundef function) type)}
    (hg : m.globals.mapM globalDef = some gdefs)
    (hfuns : (includedOf cap m).mapM (funDef cap m) = some funs) :
    ∀ g ∈ progDefs cap decl gdefs nres funs, Genv.InitShape g.2 := by
  intro g hg'
  simp only [progDefs, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hg'
  rcases hg' with rfl | ⟨⟨gv, i⟩, hi, rfl⟩ | rfl | rfl | rfl | rfl | hg' | hg' | rfl
  · exact ⟨rfl, rfl, .inl ⟨0, rfl⟩⟩
  · have hmem : gv ∈ gdefs := by
      have := List.mem_map_of_mem (f := Prod.fst) hi
      rwa [List.zipIdx_map_fst] at this
    obtain ⟨g0, -, hg0⟩ := mapM_mem' hg gv hmem
    obtain ⟨n, -, hn, hro, hvol⟩ := globalDef_shape hg0
    exact ⟨hro, hvol, .inr (.inl ⟨n, hn⟩)⟩
  · exact ⟨rfl, rfl, .inl ⟨_, rfl⟩⟩
  · exact ⟨rfl, rfl, .inr (.inr ⟨_, rfl⟩)⟩
  · exact ⟨rfl, rfl, .inr (.inr ⟨8, rfl⟩)⟩
  · trivial
  · simp only [resDefs, resTypes, List.mem_flatMap, List.mem_range, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hg'
    obtain ⟨i, -, rfl | rfl | rfl | rfl⟩ := hg'
    · exact ⟨rfl, rfl, .inl ⟨0, rfl⟩⟩
    · exact ⟨rfl, rfl, .inr (.inl ⟨0, rfl⟩)⟩
    · exact ⟨rfl, rfl, .inr (.inr ⟨8, rfl⟩)⟩
    · exact ⟨rfl, rfl, .inr (.inr ⟨4, rfl⟩)⟩
  · obtain ⟨fd, hfd⟩ := (funDef_ids hfuns).2 g hg'
    rw [hfd]; trivial
  · trivial

section Indices

variable (cap : Nat) (decl : MemDecl) (gdefs : List (globvar type)) (nres : Nat)
  (funs : List (ident × globdef (fundef function) type))

theorem progDefs_status : (progDefs cap decl gdefs nres funs)[0]? = some (statusId, .Gvar statusVar) :=
  rfl

theorem progDefs_global (i : Nat) (hi : i < gdefs.length) :
    (progDefs cap decl gdefs nres funs)[1 + i]? = some (globalId i, .Gvar gdefs[i]) := by
  rw [Nat.add_comm, progDefs, List.getElem?_cons_succ,
    List.getElem?_append_left (by simp; exact hi), List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem hi]
  simp

theorem progDefs_pages :
    (progDefs cap decl gdefs nres funs)[1 + gdefs.length]? =
      some (pagesId, .Gvar (pagesDef decl.pagesMin.toNat)) := by
  rw [Nat.add_comm, progDefs, List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
  simp

theorem progDefs_mem :
    (progDefs cap decl gdefs nres funs)[2 + gdefs.length]? = some (memId, .Gvar (memDef cap)) := by
  rw [show 2 + gdefs.length = gdefs.length + 1 + 1 by omega, progDefs, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp

theorem progDefs_pun :
    (progDefs cap decl gdefs nres funs)[3 + gdefs.length]? = some (punId, .Gvar punDef) := by
  rw [show 3 + gdefs.length = gdefs.length + 2 + 1 by omega, progDefs, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp

theorem progDefs_sqrt :
    (progDefs cap decl gdefs nres funs)[4 + gdefs.length]? = some (sqrtId, sqrtDef) := by
  rw [show 4 + gdefs.length = gdefs.length + 3 + 1 by omega, progDefs, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp

theorem progDefs_res (i : Nat) (hi : i < nres) (t : VT) (ht : t.isRes = true) :
    (progDefs cap decl gdefs nres funs)[5 + gdefs.length + resOfs i t]? =
      some (resId i t, .Gvar (resDef t)) := by
  have hk : resOfs i t < (resDefs nres).length := by
    have := resIdx_lt ht
    rw [resDefs_length]; unfold resOfs; omega
  rw [show 5 + gdefs.length + resOfs i t = gdefs.length + (resOfs i t + 4) + 1 by omega, progDefs,
    List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
  simp only [List.length_map, List.length_zipIdx, Nat.add_sub_cancel_left, List.getElem?_cons_succ]
  rw [List.getElem?_append_left hk]
  exact resDefs_get nres i hi t ht

end Indices

/-- The environment of a translated program in its own global environment: `lx_status` is block
1, the Wasm global `i` block `i + 2`, `lx_pages` block `G + 2`, `lx_mem` block `G + 3`, `lx_pun`
block `G + 4`, `__builtin_fsqrt` block `G + 5`, and the result global of position `i` and type `t`
block `G + 6 + resOfs i t`, for `G` globals. -/
def envOf (T : Translation) (G cap : Nat) : Env :=
  { ge := globalenv T.cprogram, status := 1, globals := (List.range G).map (· + 2),
    pages := G + 2, mem := G + 3, cap := cap, res := fun i t => G + 6 + resOfs i t,
    nres := T.nres, pun := G + 4, sqrt := G + 5 }

/-- A writable access at offset 0 from writable bytes. -/
theorem valid_access_of_bytes {m : mem} {b : block} {chunk : memory_chunk}
    (hsz : size_chunk chunk ≤ 8) (hal : align_chunk chunk ∣ 0)
    (hp : ∀ i : Nat, (i : _root_.Int) < 8 → Mem.perm m b (i : _root_.Int) .Cur .Writable) :
    Mem.valid_access m chunk b 0 .Writable := by
  refine ⟨fun ofs h1 h2 => ?_, hal⟩
  have e : ofs = ((ofs.toNat : Nat) : _root_.Int) := by omega
  rw [e]
  exact hp _ (by omega)

theorem valid_access_of_bytes4 {m : mem} {b : block} {chunk : memory_chunk}
    (hsz : size_chunk chunk ≤ 4) (hal : align_chunk chunk ∣ 0)
    (hp : ∀ i : Nat, (i : _root_.Int) < 4 → Mem.perm m b (i : _root_.Int) .Cur .Writable) :
    Mem.valid_access m chunk b 0 .Writable := by
  refine ⟨fun ofs h1 h2 => ?_, hal⟩
  have e : ofs = ((ofs.toNat : Nat) : _root_.Int) := by omega
  rw [e]
  exact hp _ (by omega)

/-- The initial memory of a translated program: its blocks are those of `envOf`, `lx_status` is
0, the C globals hold the module's initial globals, `lx_pages` holds the initial pages, and
`lx_mem` is zero. -/
theorem init_spec {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T) :
    ∃ decl m0, m.memory = some decl ∧ init_mem T.cprogram = some m0 ∧
      EnvOk (envOf T m.globals.length cap) ∧ StatusRel (envOf T m.globals.length cap) m0 0 ∧
      GlobalsRel (envOf T m.globals.length cap) (m.globals.map (·.init)) m0 ∧
      MemRel (envOf T m.globals.length cap) (Wasm.Mem.empty decl.pagesMin.toNat) [cap] m0 := by
  obtain ⟨decl, gdefs, funs, hdecl, -, hc1, hc2, hg, hfuns, hdefs⟩ := translate_defs h
  have hG : gdefs.length = m.globals.length := mapM_length hg
  have hnd := progDefs_nodup (decl := decl) (gdefs := gdefs) (nres := T.nres) hfuns
  have hsh := progDefs_shape (decl := decl) (nres := T.nres) hg hfuns
  obtain ⟨m0, hm0, -, -, hfact⟩ := Genv.alloc_globals_spec (globalenv T.cprogram)
    (progDefs cap decl gdefs T.nres funs) Mem.empty hsh
  have hsym := Genv.find_add_globals_idx (Genv.empty_genv T.cprogram.prog_public)
    (progDefs cap decl gdefs T.nres funs) hnd
  have hge : globalenv T.cprogram = Genv.add_globals (Genv.empty_genv T.cprogram.prog_public)
      (progDefs cap decl gdefs T.nres funs) := by
    unfold globalenv; rw [hdefs]
  have at_idx : ∀ k x, (progDefs cap decl gdefs T.nres funs)[k]? = some x →
      Genv.find_symbol (globalenv T.cprogram) x.1 = some (1 + k) ∧ Genv.InitFact m0 (1 + k) x.2 := by
    intro k x hk
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨h1, -⟩ := hsym k hlt
    have h2 := hfact k hlt
    rw [heq] at h1 h2
    exact ⟨by rw [hge]; exact h1, h2⟩
  obtain ⟨hs1, hs2⟩ := at_idx 0 _ (progDefs_status cap decl gdefs T.nres funs)
  obtain ⟨hp1, hp2⟩ := at_idx _ _ (progDefs_pages cap decl gdefs T.nres funs)
  obtain ⟨hm1, hm2⟩ := at_idx _ _ (progDefs_mem cap decl gdefs T.nres funs)
  have hr : ∀ i < T.nres, ∀ t : VT, t.isRes = true →
      Genv.find_symbol (globalenv T.cprogram) (resId i t) = some (m.globals.length + 6 + resOfs i t) ∧
        Mem.valid_access m0 t.chunk (m.globals.length + 6 + resOfs i t) 0 .Writable := by
    intro i hi t ht
    obtain ⟨h1, h2⟩ := at_idx _ _ (progDefs_res cap decl gdefs T.nres funs i hi t ht)
    rw [show 1 + (5 + gdefs.length + resOfs i t) = m.globals.length + 6 + resOfs i t by omega]
      at h1 h2
    refine ⟨h1, ?_⟩
    rcases VT.isRes_cases ht with rfl | rfl | rfl | rfl
    · exact ((h2 _ rfl).1 0 (by simp [resDef])).2
    · exact ((h2 _ rfl).2.1 0 (by simp [resDef])).2
    · exact valid_access_of_bytes (by decide) (by decide)
        (fun j hj => ((h2 _ rfl).2.2 8 (by simp [resDef]) j hj).2)
    · exact valid_access_of_bytes4 (by decide) (by decide)
        (fun j hj => ((h2 _ rfl).2.2 4 (by simp [resDef]) j hj).2)
  obtain ⟨hpun1, hpun2⟩ := at_idx _ _ (progDefs_pun cap decl gdefs T.nres funs)
  obtain ⟨hsq1, -⟩ := at_idx _ _ (progDefs_sqrt cap decl gdefs T.nres funs)
  rw [show 1 + (3 + gdefs.length) = m.globals.length + 4 by omega] at hpun1 hpun2
  rw [show 1 + (4 + gdefs.length) = m.globals.length + 5 by omega] at hsq1
  have hsqf : Genv.find_funct_ptr (globalenv T.cprogram) (m.globals.length + 5) = some sqrtFun := by
    obtain ⟨b, hb1, hb2⟩ := Genv.find_add_globals (Genv.empty_genv T.cprogram.prog_public)
      (progDefs cap decl gdefs T.nres funs) hnd (id := sqrtId) (d := sqrtDef)
      (by simp [progDefs])
    rw [← hge] at hb1 hb2
    rw [hsq1] at hb1
    cases hb1
    exact Genv.find_funct_ptr_of_def hb2
  have hpunW : Mem.valid_access m0 .Mint64 (m.globals.length + 4) 0 .Writable :=
    valid_access_of_bytes (by decide) (by decide)
      (fun j hj => ((hpun2 _ rfl).2.2 8 rfl j hj).2)
  have hpg : 1 + (1 + gdefs.length) = m.globals.length + 2 := by omega
  have hmb : 1 + (2 + gdefs.length) = m.globals.length + 3 := by omega
  rw [hpg] at hp1 hp2
  rw [hmb] at hm1 hm2
  refine ⟨decl, m0, hdecl, ?_, ?_, ?_, ?_, ?_⟩
  · show Genv.alloc_globals (globalenv T.cprogram) Mem.empty T.cprogram.prog_defs = some m0
    rw [hdefs]; exact hm0
  · refine { status := hs1, globals := fun i hi => ?_, nodup := ?_, status_not := ?_, pages := hp1,
             mem := hm1, pages_not := ?_, mem_not := ?_, pages_status := ?_, mem_status := ?_,
             mem_pages := ?_, cap := hc2, res := fun i hi t ht => (hr i hi t ht).1,
             res_inj := fun i j t u _ _ ht hu he => ?_, res_other := fun i _ t ht => ?_,
             pun := hpun1, pun_other := ?_, sqrt := hsq1, sqrt_fun := hsqf }
    · simp only [envOf, List.length_map, List.length_range] at hi
      have := (at_idx _ _ (progDefs_global cap decl gdefs T.nres funs i (by omega))).1
      simp only [envOf, List.getElem_map, List.getElem_range]
      rw [show i + 2 = 1 + (1 + i) by omega]
      exact this
    · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
    · simp [envOf]
    · simp [envOf]
    · simp [envOf]
    · simp [envOf]
    · simp [envOf]
    · simp [envOf]
    · have he' : m.globals.length + 6 + resOfs i t = (m.globals.length + 6 + resOfs j u : Nat) :=
        he
      unfold resOfs at he'
      rcases VT.isRes_cases ht with rfl | rfl | rfl | rfl <;>
        rcases VT.isRes_cases hu with rfl | rfl | rfl | rfl <;>
        simp [VT.resIdx] at he' <;> first | exact ⟨by omega, rfl⟩ | omega
    · have hlt : ∀ x : Nat, x ∈ (List.range m.globals.length).map (· + 2) →
          x < m.globals.length + 2 := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        omega
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun hmem => ?_, fun h => ?_⟩
      · have h' : m.globals.length + 6 + resOfs i t = (1 : Nat) := h; omega
      · have h' : m.globals.length + 6 + resOfs i t = (m.globals.length + 2 : Nat) := h; omega
      · have h' : m.globals.length + 6 + resOfs i t = (m.globals.length + 3 : Nat) := h; omega
      · have h2 : m.globals.length + 6 + resOfs i t < (m.globals.length + 2 : Nat) := hlt _ hmem
        omega
      · have h' : m.globals.length + 6 + resOfs i t = (m.globals.length + 4 : Nat) := h; omega
    · have hlt : ∀ x : Nat, x ∈ (List.range m.globals.length).map (· + 2) →
          x < m.globals.length + 2 := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        omega
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun hmem => ?_⟩
      · have h' : m.globals.length + 4 = (1 : Nat) := h; omega
      · have h' : m.globals.length + 4 = (m.globals.length + 2 : Nat) := h; omega
      · have h' : m.globals.length + 4 = (m.globals.length + 3 : Nat) := h; omega
      · have h2 : m.globals.length + 4 < (m.globals.length + 2 : Nat) := hlt _ hmem
        omega
  · exact (hs2 _ rfl).1 0 rfl
  · refine ⟨by simp [envOf], fun i hi => ?_⟩
    simp only [envOf, List.length_map, List.length_range] at hi
    obtain ⟨gv, hgv, hgi⟩ := mapM_get hg i hi
    obtain ⟨n, hinit, hn, -, -⟩ := globalDef_shape hgv
    have hgi' : gdefs[i]'(by omega) = gv := (List.getElem?_eq_some_iff.mp hgi).2
    have h2 := (at_idx _ _ (progDefs_global cap decl gdefs T.nres funs i (by omega))).2
    rw [hgi'] at h2
    obtain ⟨hl, hva⟩ := (h2 _ rfl).2.1 n hn
    refine ⟨n, by simp only [List.getElem?_map]; rw [List.getElem?_eq_getElem hi]; simp [hinit], ?_, ?_⟩
    · simp only [envOf, List.getElem_map, List.getElem_range]
      rw [show i + 2 = 1 + (1 + i) by omega]; exact hl
    · simp only [envOf, List.getElem_map, List.getElem_range]
      rw [show i + 2 = 1 + (1 + i) by omega]; exact hva
  · obtain ⟨hl, hva⟩ := (hp2 _ rfl).1 _ rfl
    obtain hz := (hm2 _ rfl).2.2 _ rfl
    exact { pages := hl, pagesW := hva, le_cap := hc1, memCap := rfl
            bytes := fun i hi => (hz i (by simp [envOf] at hi ⊢; omega)).1
            perm := fun i hi => (hz i (by simp [envOf] at hi ⊢; omega)).2
            resW := fun i hi t ht => (hr i hi t ht).2
            punW := hpunW }

/-! ## The data segments -/

theorem writeBytes_bytes (wm : Wasm.Mem) (a : Nat) (bs : List UInt8) (i : Nat) :
    (wm.writeBytes a bs).bytes i =
      if a ≤ i ∧ i < a + bs.length then bs.getD (i - a) 0 else wm.bytes i := by
  unfold Wasm.Mem.writeBytes
  dsimp only
  split
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  · rfl

theorem MemRel.congr {E : Env} {wm wm' : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) (hp : wm'.pages = wm.pages)
    (hb : ∀ i, i < 65536 * E.cap → wm'.bytes i = wm.bytes i) : MemRel E wm' caps m where
  pages := by rw [hp]; exact h.pages
  pagesW := h.pagesW
  le_cap := hp ▸ h.le_cap
  memCap := h.memCap
  bytes := fun i hi => by rw [hb i hi]; exact h.bytes i hi
  perm := h.perm
  resW := h.resW
  punW := h.punW

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n :=
  UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 2 ^ 32 from rfl]; exact h)

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem exec_wordStore (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) (le : temp_env) (cap a : Nat) (ha : a % 8 = 0)
    (hin : a + 8 ≤ 65536 * E.cap) (ws : List UInt8) :
    ∃ m', exec_stmt A X E.ge empty_env le m (wordStore cap a ws) E0 le m' .Out_normal ∧
      Mem.SameExcept E.mem m m' ∧ MemRel E (wm.write64 (UInt32.ofNat a) (wordOfBytes ws)) caps m' := by
  have hcap := hE.cap
  have ha32 : (UInt32.ofNat a).toNat = a := toNat_ofNat32 (by omega)
  have hk : (UInt64.ofNat (a / 8)).toNat = a / 8 := toNat_ofNat64 (by omega)
  have hptr : UInt64.ofNat (8 * (UInt64.ofNat (a / 8)).toNat) = UInt64.ofNat a := by
    rw [hk]; congr 1; omega
  have hva := h.valid_word (i := a) hin ha
  refine ⟨Mem.stored .Mint64 m E.mem a (.Vlong (wordOfBytes ws)), ?_,
    Mem.SameExcept.of_stored _ _ _ _ _, ?_⟩
  · refine .exec_Sassign _ _ _ _ _ E.mem (UInt64.ofNat a) _ _ _ _
      (.eval_Ederef _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (eval_memVar hE le m cap)
        (.eval_Econst_long _ _) ?_)) (.eval_Econst_long _ _) (cast_ll m _)
      (.assign_loc_value _ .Mint64 _ rfl ?_)
    · show sem_binary_operation A .Oadd (.Vptr E.mem Ptrofs.zero) (memType cap) (.Vlong _) tulong m = _
      rw [sem_add_mem_word A m E.mem cap _ (by rw [hk]; omega), hptr]
    · rw [storev_mem _ (by rw [toNat_ofNat64 (by omega)]; simp [size_chunk]; omega) (by decide),
        toNat_ofNat64 (by omega)]
      exact Mem.store_ok _ hva
  · have := h.store_word hE (UInt32.ofNat a) (wordOfBytes ws)
    rw [ha32] at this
    exact this

theorem exec_byteStore' (hE : EnvOk E) {wm : Wasm.Mem} {caps : List Nat} {m : mem}
    (h : MemRel E wm caps m) (le : temp_env) (cap a : Nat) (hin : a < 65536 * E.cap) (b : UInt8) :
    ∃ m', exec_stmt A X E.ge empty_env le m (byteStore cap a b) E0 le m' .Out_normal ∧
      Mem.SameExcept E.mem m m' ∧ MemRel E (wm.write8 (UInt32.ofNat a) b) caps m' := by
  have hcap := hE.cap
  have ha32 : (UInt32.ofNat a).toNat = a := toNat_ofNat32 (by omega)
  have hva := h.valid_byte hin
  refine ⟨Mem.stored .Mint8unsigned m E.mem a (.Vint (UInt32.ofNat (b.toNat % 256))), ?_,
    Mem.SameExcept.of_stored _ _ _ _ _, ?_⟩
  · have hcast : sem_cast (.Vint b.toUInt32) tuint tuchar m =
        some (.Vint (UInt32.ofNat (b.toNat % 256))) := by
      show some (val.Vint (cast_int_int .I8 .Unsigned b.toUInt32)) = _
      congr 2
      apply UInt32.toNat_inj.mp
      simp only [cast_int_int, LClight.Int.zero_ext, LClight.Int.repr, LClight.Int.unsigned,
        LClight.Int.modulus]
      have := b.toNat_lt
      simp; omega
    refine .exec_Sassign _ _ _ _ _ E.mem (UInt64.ofNat a) _ _ _ _
      (eval_byteAt_lvalue hE cap (.eval_Econst_long _ _) rfl)
      (.eval_Ecast _ _ _ _ (.eval_Econst_int _ _) hcast)
      (cast_uchar _ m) (.assign_loc_value _ .Mint8unsigned _ rfl ?_)
    rw [storev_mem _ (by rw [toNat_ofNat64 (by omega)]; simp [size_chunk]; omega) (by decide),
      toNat_ofNat64 (by omega)]
    exact Mem.store_ok _ hva
  · have := h.store_byte hE (UInt32.ofNat a) b
    rw [ha32] at this
    exact this

end

/-! ## Lists of statements -/

section

variable {A : Archi} {X : ExtSem} {ge : genv}

/-- `seqList L` runs to completion from `le` and `m` to `le'` and `m'`. -/
def ExecList (A : Archi) (X : ExtSem) (ge : genv) (le : temp_env) (m : mem) (L : List statement)
    (le' : temp_env) (m' : mem) : Prop :=
  exec_stmt A X ge empty_env le m (seqList L) E0 le' m' .Out_normal

theorem ExecList.nil (le : temp_env) (m : mem) : ExecList A X ge le m [] le m := .exec_Sskip _ _ _

theorem ExecList.cons {le le1 le2 : temp_env} {m m1 m2 : mem} {s : statement}
    {L : List statement} (h1 : exec_stmt A X ge empty_env le m s E0 le1 m1 .Out_normal)
    (h2 : ExecList A X ge le1 m1 L le2 m2) : ExecList A X ge le m (s :: L) le2 m2 := by
  cases L with
  | nil =>
      obtain ⟨rfl, rfl, -, -⟩ := exec_skip_inv h2
      exact h1
  | cons s' L => exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2

theorem ExecList.append : ∀ (L1 : List statement) {L2 : List statement} {le le1 le2 : temp_env}
    {m m1 m2 : mem}, ExecList A X ge le m L1 le1 m1 → ExecList A X ge le1 m1 L2 le2 m2 →
    ExecList A X ge le m (L1 ++ L2) le2 m2
  | [], _, _, _, _, _, _, _, h1, h2 => by
      obtain ⟨rfl, rfl, -, -⟩ := exec_skip_inv h1
      exact h2
  | [s], _, _, _, _, _, _, _, h1, h2 => ExecList.cons h1 h2
  | s :: s' :: L1, _, _, _, _, _, _, _, h1, h2 => by
      have h1' : exec_stmt A X ge empty_env _ _ (.Ssequence s (seqList (s' :: L1))) E0 _ _
          .Out_normal := h1
      generalize ht : E0 = t at h1'
      generalize ho : outcome.Out_normal = o at h1'
      cases h1' with
      | exec_Sseq_1 _ _ _ _ _ t1 le3 m3 t2 _ _ _ ha hb =>
          subst ho
          have ht' : t1 = [] ∧ t2 = [] := List.append_eq_nil_iff.mp ht.symm
          obtain ⟨rfl, rfl⟩ := ht'
          exact ExecList.cons ha (ExecList.append (s' :: L1) hb h2)
      | exec_Sseq_2 _ _ _ _ _ _ _ _ _ _ hne => exact absurd ho.symm hne

end

theorem nbyte_wordOfBytes (bs : List UInt8) (hlen : bs.length = 8) (j : Nat) (hj : j < 8) :
    nbyte (wordOfBytes bs).toNat j = bs.getD j 0 := by
  obtain ⟨h0, h1⟩ := int_of_bytes_bounds bs
  rw [hlen] at h1
  have hx : ((wordOfBytes bs).toNat : _root_.Int) = int_of_bytes bs := by
    simp only [wordOfBytes, Int64.repr, Int64.modulus]
    rw [UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; norm_num at h1 ⊢; omega)]
    norm_num at h1 ⊢
    omega
  have e := bytes_of_int_of_bytes bs
  rw [hlen, ← hx, bytes_of_int_nat] at e
  have e' := congrArg (fun l => l.getD j 0) e
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some] at e'
  rw [e', List.getD_eq_getElem?_getD]

theorem byte_step (wm : Wasm.Mem) (a : Nat) (b0 : UInt8) (rest : List UInt8) (ha : a < 2 ^ 32)
    (i : Nat) : ((wm.write8 (UInt32.ofNat a) b0).writeBytes (a + 1) rest).bytes i =
      (wm.writeBytes a (b0 :: rest)).bytes i := by
  have ha32 : (UInt32.ofNat a).toNat = a := toNat_ofNat32 ha
  rw [writeBytes_bytes, writeBytes_bytes]
  simp only [List.length_cons]
  by_cases h1 : a + 1 ≤ i ∧ i < a + 1 + rest.length
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = a + 1 + j := ⟨i - (a + 1), by omega⟩
    rw [show a + 1 + j - a = j + 1 by omega, show a + 1 + j - (a + 1) = j by omega]
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right h1]
    by_cases h2 : i = a
    · subst h2
      rw [ite_eq_left (by omega), Nat.sub_self]
      have := write8_same wm (UInt32.ofNat i) b0
      rw [ha32] at this
      rw [this]
      rfl
    · rw [ite_eq_right (by omega), write8_ne _ _ _ (by rw [ha32]; exact h2)]

theorem word_step (wm : Wasm.Mem) (a : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (rest : List UInt8)
    (ha : a + 8 ≤ 2 ^ 32) (i : Nat) :
    ((wm.write64 (UInt32.ofNat a) (wordOfBytes [b0, b1, b2, b3, b4, b5, b6, b7])).writeBytes
        (a + 8) rest).bytes i =
      (wm.writeBytes a (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)).bytes i := by
  have ha32 : (UInt32.ofNat a).toNat = a := toNat_ofNat32 (by omega)
  rw [writeBytes_bytes, writeBytes_bytes]
  simp only [List.length_cons]
  by_cases h1 : a + 8 ≤ i ∧ i < a + 8 + rest.length
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = a + 8 + j := ⟨i - (a + 8), by omega⟩
    rw [show a + 8 + j - a = j + 8 by omega, show a + 8 + j - (a + 8) = j by omega]
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right h1]
    by_cases h2 : a ≤ i ∧ i < a + 8
    · rw [ite_eq_left (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
      have hj : j < 8 := by omega
      have := write64_bytes_at wm (UInt32.ofNat a) (wordOfBytes [b0, b1, b2, b3, b4, b5, b6, b7]) j hj
      rw [ha32] at this
      rw [this, nbyte_wordOfBytes _ rfl j hj, Nat.add_sub_cancel_left]
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
      all_goals first | rfl | omega
    · rw [ite_eq_right (by omega),
        LeanExe.ProofKit.Memory.write64_bytes_outside _ _ _ (by rw [ha32]; omega)]

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem exec_initStores (hE : EnvOk E) {caps : List Nat} (le : temp_env) (cap : Nat) :
    ∀ (a : Nat) (bs : List UInt8) (wm : Wasm.Mem) (m : mem), a + bs.length ≤ 65536 * E.cap →
      MemRel E wm caps m →
      ∃ m', ExecList A X E.ge le m (initStores cap a bs) le m' ∧ Mem.SameExcept E.mem m m' ∧
        MemRel E (wm.writeBytes a bs) caps m' := by
  have hcap := hE.cap
  intro a bs
  induction a, bs using initStores.induct with
  | case1 a b0 b1 b2 b3 b4 b5 b6 b7 rest' ha ih =>
      intro wm m hin h
      simp only [List.length_cons] at hin
      obtain ⟨m1, hx1, hs1, h1⟩ := exec_wordStore (A := A) (X := X) hE h le cap a ha (by omega)
        [b0, b1, b2, b3, b4, b5, b6, b7]
      obtain ⟨m2, hx2, hs2, h2⟩ := ih _ m1 (by omega) h1
      refine ⟨m2, ?_, hs1.trans hs2, h2.congr rfl (fun i _ => (word_step _ _ _ _ _ _ _ _ _ _ _
        (by omega) i).symm)⟩
      rw [initStores.eq_1, ite_eq_left ha]
      exact ExecList.cons hx1 hx2
  | case2 a b0 b1 b2 b3 b4 b5 b6 b7 rest' ha ih =>
      intro wm m hin h
      simp only [List.length_cons] at hin
      obtain ⟨m1, hx1, hs1, h1⟩ := exec_byteStore' (A := A) (X := X) hE h le cap a (by omega) b0
      obtain ⟨m2, hx2, hs2, h2⟩ := ih _ m1 (by simp; omega) h1
      refine ⟨m2, ?_, hs1.trans hs2, h2.congr rfl (fun i _ => (byte_step _ _ _ _ (by omega) i).symm)⟩
      rw [initStores.eq_1, ite_eq_right ha]
      exact ExecList.cons hx1 hx2
  | case3 a b0 rest hshort ih =>
      intro wm m hin h
      simp only [List.length_cons] at hin
      obtain ⟨m1, hx1, hs1, h1⟩ := exec_byteStore' (A := A) (X := X) hE h le cap a (by omega) b0
      obtain ⟨m2, hx2, hs2, h2⟩ := ih _ m1 (by omega) h1
      refine ⟨m2, ?_, hs1.trans hs2, h2.congr rfl (fun i _ => (byte_step _ _ _ _ (by omega) i).symm)⟩
      rw [initStores.eq_2 _ _ _ _ hshort]
      exact ExecList.cons hx1 hx2
  | case4 a =>
      intro wm m _ h
      refine ⟨m, ?_, Mem.SameExcept.refl _ _, h.congr rfl (fun i _ => ?_)⟩
      · rw [initStores.eq_3]; exact ExecList.nil le m
      · rw [writeBytes_bytes]; simp

/-- Talos's step of `Module.initialStore` for a data segment of memory 0. -/
def segApply (acc : Wasm.Mem) (seg : DataSegment) : Wasm.Mem :=
  match seg.offset with
  | some off =>
      if seg.memIdx = 0 && seg.offsetExpr.isEmpty then
        if off.toNat + seg.bytes.length ≤ acc.pages * 65536 then acc.writeBytes off.toNat seg.bytes
        else acc
      else acc
  | none => acc

theorem initialStore_mem {m : Module} {decl : MemDecl} (h : m.memory = some decl) :
    (m.initialStore : Store Unit).mem =
      decl.data.foldl segApply (Wasm.Mem.empty decl.pagesMin.toNat) := by
  simp only [Module.initialStore, h]
  rfl

theorem exec_segments (hE : EnvOk E) {caps : List Nat} (le : temp_env) (cap pages : Nat)
    (hp : pages * 65536 ≤ 65536 * E.cap) :
    ∀ (segs : List DataSegment) (wm : Wasm.Mem) (m : mem), segs.all (segmentOk pages) = true →
      wm.pages = pages → MemRel E wm caps m →
      ∃ m', ExecList A X E.ge le m (segs.flatMap (segmentStores cap)) le m' ∧
        Mem.SameExcept E.mem m m' ∧ MemRel E (segs.foldl segApply wm) caps m'
  | [], wm, m, _, _, h => ⟨m, ExecList.nil le m, Mem.SameExcept.refl _ _, h⟩
  | seg :: segs, wm, m, hall, hpg, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hseg, hall⟩ := hall
      unfold segmentOk at hseg
      split at hseg
      · rename_i off hoff
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff] at hseg
        obtain ⟨⟨hidx, hexpr⟩, hfit⟩ := hseg
        obtain ⟨m1, hx1, hs1, h1⟩ := exec_initStores (A := A) (X := X) hE le cap off.toNat seg.bytes
          wm m (by omega) h
        have happ : segApply wm seg = wm.writeBytes off.toNat seg.bytes := by
          simp [segApply, hoff, hidx, hexpr, hpg, hfit]
        obtain ⟨m2, hx2, hs2, h2⟩ := exec_segments hE le cap pages hp segs _ m1 hall
          (by rw [← hpg]; rfl) h1
        refine ⟨m2, ?_, hs1.trans hs2, ?_⟩
        · rw [List.flatMap_cons]
          have : segmentStores cap seg = initStores cap off.toNat seg.bytes := by
            simp [segmentStores, hoff]
          rw [this]
          exact ExecList.append _ hx1 hx2
        · rw [List.foldl_cons, happ]; exact h2
      · cases hseg

end

theorem violation_segments {m : Module} {decl : MemDecl} (hv : violation m = none)
    (hd : m.memory = some decl) : decl.data.all (segmentOk decl.pagesMin.toNat) = true := by
  unfold violation at hv
  cases hs : shapeViolation m with
  | some r => simp [hs] at hv
  | none =>
      cases hm : memoryViolation m.memory with
      | some r => simp [hs, hm] at hv
      | none =>
          rw [hd] at hm
          by_cases h64 : decl.is64
          · simp [memoryViolation, h64] at hm
          · by_cases hall : decl.data.all (segmentOk decl.pagesMin.toNat) = true
            · exact hall
            · simp [memoryViolation, h64, hall] at hm

/-- The store in which a translated module starts: Talos's initial store with the memory's cap
set to `cap`. -/
def nativeStore (m : Module) (cap : Nat) : Store Unit :=
  { (m.initialStore : Store Unit) with memoryCaps := [cap] }

/-- `lx_init` from the program's initial memory gives a memory related to `nativeStore`. -/
theorem lx_init_correct {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T) :
    ∃ decl m0, m.memory = some decl ∧ init_mem T.cprogram = some m0 ∧
      EnvOk (envOf T m.globals.length cap) ∧
      (initId, globdef.Gfun (.Internal (initFunction cap decl.data))) ∈ T.cprogram.prog_defs ∧
      ∀ (A : Archi) (X : ExtSem), ∃ m1,
        eval_funcall A X (globalenv T.cprogram) m0 (.Internal (initFunction cap decl.data)) [] E0
          m1 .Vundef ∧
        StoreRel (envOf T m.globals.length cap) (nativeStore m cap) m1 ∧
        StatusRel (envOf T m.globals.length cap) m1 0 := by
  obtain ⟨decl, m0, hdecl, hinit, hE, hs, hg, hmr⟩ := init_spec h
  obtain ⟨decl', gdefs, funs, hdecl', hv, hc1, -, -, -, hdefs⟩ := translate_defs h
  rw [hdecl] at hdecl'
  cases hdecl'
  refine ⟨decl, m0, hdecl, hinit, hE, by rw [hdefs]; simp [progDefs], fun A X => ?_⟩
  obtain ⟨m1, hx, hsame, hmr1⟩ := exec_segments (A := A) (X := X) hE (create_undef_temps [])
    cap decl.pagesMin.toNat (by simp [envOf]; omega) decl.data _ m0
    (violation_segments hv hdecl) rfl hmr
  refine ⟨m1, ?_, ⟨?_, ?_⟩, hs.sameExcept hsame (Ne.symm hE.mem_status)⟩
  · refine .eval_funcall_internal _ _ _ _ _ _ _ _ _ _ _ _
      (.intro (create_undef_temps []) rfl List.nodup_nil
        (fun _ hx => by simp [var_names, initFunction] at hx) rfl)
      hx rfl ?_
    rfl
  · exact GlobalsRel.sameExcept hg hsame hE.mem_not
  · show MemRel _ (m.initialStore : Store Unit).mem [cap] m1
    rw [initialStore_mem hdecl]
    exact hmr1

/-- The functions of a translated program are found in its own global environment. -/
theorem funcs_found {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T) :
    ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol (globalenv T.cprogram) (funId k) = some b ∧
        Genv.find_funct_ptr (globalenv T.cprogram) b = some (.Internal fd) := by
  obtain ⟨decl, gdefs, funs, -, -, -, -, -, hfuns, hdefs⟩ := translate_defs h
  intro k fd hk
  have hnd : (T.cprogram.prog_defs.map (·.1)).Nodup := by rw [hdefs]; exact progDefs_nodup hfuns
  obtain ⟨b, hs, hd⟩ := Genv.find_add_globals _ _ hnd hk
  exact ⟨b, hs, Genv.find_funct_ptr_of_def hd⟩

end LeanExe.Native
