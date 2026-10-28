import LeanExe.Native.Proof.Init
import LeanExe.Native.Bare

/-!
The whole program that `ccomp` compiles for a translation (`docs/native-bare-metal.md`):
CompCert's declarations of its built-in and run-time functions `pre`, the translation's
definitions in the order of the C text, and further definitions `post`, such as the `main` and
the volatile global `lx_out` of a bare-metal program.  `clightgen` puts its declarations first,
among them `__builtin_fsqrt`, which the translation places between `lx_pun` and the result
globals, so `wholeDefs` takes that declaration from `pre` and leaves it out of the translation's
part.  The program's `main` is `mainId`.

`WholeOk pre post T` asks that `pre` declare `__builtin_fsqrt` as the translation does, that
every definition be a function or a variable whose allocation `init_mem` can do, and that the
identifiers be distinct.  Under it, `init_whole` follows `init_mem` of the whole program, each
definition at the block one more than its position, and `start_whole` runs `lx_init` and states
every premise that `NativeA` puts on the environment, for `envWhole`, whose blocks are those
positions.  These theorems hold for every `pre` and `post` that meet `WholeOk`, so they cover
every list of declarations that a version of CompCert prints.  `wholeOk_of` derives `WholeOk`
from conditions on identifiers that the per-build check confirms for the program `clightgen`
reads.  `bareProgram` is the whole program of a bare-metal build, whose `post` declares `lx_out`
and defines `main`, in the order in which `clightgen` lists them after the translation's
definitions.
-/

namespace LClight

namespace Genv

open Mem

variable {F V : Type}

/-- The definitions whose allocation `alloc_global_spec_w` follows: those of `InitShape`, and
variables without initialization data, such as an `extern` declaration. -/
def InitShapeW (g : globdef F V) : Prop := InitShape g ∨ ∃ v, g = .Gvar v ∧ v.gvar_init = []

theorem alloc_global_spec_w (ge : t F V) (m : mem) (g : ident × globdef F V)
    (hg : InitShapeW g.2) :
    ∃ m', alloc_global ge m g = some m' ∧ m'.nextblock = m.nextblock + 1 ∧
      (∀ b, b ≠ m.nextblock → SameBlock b m m') ∧ InitFact m' m.nextblock g.2 := by
  rcases hg with hg | ⟨v, hv, hinit⟩
  · exact alloc_global_spec ge m g hg
  · obtain ⟨id, d⟩ := g
    simp only at hv
    subst hv
    have hrp : range_perm (alloc m 0 0).1 m.nextblock 0 0 .Cur .Freeable :=
      fun ofs h1 h2 => absurd h2 (by omega)
    refine ⟨dropped (alloc m 0 0).1 m.nextblock 0 0 (perm_globvar v), ?_, rfl, fun b hb => ?_, ?_⟩
    · show (match Genv.store_zeros (alloc m 0 (init_data_list_size v.gvar_init)).1 m.nextblock 0
            (init_data_list_size v.gvar_init) with
          | none => none
          | some m2 =>
            match store_init_data_list ge m2 m.nextblock 0 v.gvar_init with
            | none => none
            | some m3 => drop_perm m3 m.nextblock 0 (init_data_list_size v.gvar_init)
                (perm_globvar v)) = _
      rw [hinit]
      exact drop_perm_ok hrp _
    · exact (alloc_other m 0 0 hb).trans (dropped_other hb)
    · intro v' hv'
      injection hv' with e
      subst e
      refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩ <;> rw [hinit] at hn <;> cases hn

theorem alloc_globals_spec_w (ge : t F V) : ∀ (gl : List (ident × globdef F V)) (m : mem),
    (∀ g ∈ gl, InitShapeW g.2) →
    ∃ m', alloc_globals ge m gl = some m' ∧ m'.nextblock = m.nextblock + gl.length ∧
      (∀ b, b < m.nextblock → SameBlock b m m') ∧
      ∀ k (hk : k < gl.length), InitFact m' (m.nextblock + k) gl[k].2
  | [], m, _ => ⟨m, rfl, rfl, fun _ _ => SameBlock.refl _ _, fun k hk => absurd hk (by simp)⟩
  | g :: gl, m, h => by
      obtain ⟨m1, h1, hn1, hs1, hf1⟩ := alloc_global_spec_w ge m g (h g (by simp))
      obtain ⟨m', h', hn', hs', hf'⟩ := alloc_globals_spec_w ge gl m1
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

end Genv

end LClight

namespace LeanExe.Native

open Wasm LClight

/-! ## The whole program -/

/-- The definitions of the whole program: `pre`, the translation's definitions but
`__builtin_fsqrt`, and `post`. -/
def wholeDefs (pre post : List (ident × globdef (fundef function) type)) (T : Translation) :
    List (ident × globdef (fundef function) type) :=
  pre ++ T.cprogram.prog_defs.filter (fun d => d.1 != sqrtId) ++ post

def wholeProgram (pre post : List (ident × globdef (fundef function) type)) (T : Translation) :
    program function :=
  { prog_defs := wholeDefs pre post T, prog_public := [], prog_main := mainId }

/-- The conditions on `pre` and `post` under which the theorems of this file hold. -/
structure WholeOk (pre post : List (ident × globdef (fundef function) type)) (T : Translation) :
    Prop where
  sqrt : (sqrtId, sqrtDef) ∈ pre
  pre_shape : ∀ d ∈ pre, Genv.InitShapeW d.2
  post_shape : ∀ d ∈ post, Genv.InitShapeW d.2
  nodup : ((wholeDefs pre post T).map (·.1)).Nodup

/-- The block of the identifier `id` among the definitions `defs`: one more than its position. -/
def blockOf (defs : List (ident × globdef (fundef function) type)) (id : ident) : block :=
  1 + defs.findIdx (fun d => d.1 == id)

theorem findIdx_of_mem {defs : List (ident × globdef (fundef function) type)}
    (hnd : (defs.map (·.1)).Nodup) {k : Nat} (hk : k < defs.length) :
    defs.findIdx (fun d => d.1 == defs[k].1) = k := by
  rw [List.findIdx_eq hk]
  refine ⟨by simp, fun j hjk => ?_⟩
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro hj
  have hj' : (defs.map (·.1))[j]'(by simp; omega) = (defs.map (·.1))[k]'(by simp; omega) := by
    simpa using hj
  have := (List.Nodup.getElem_inj_iff hnd).mp hj'
  omega

/-- A definition of a list with distinct identifiers is at the block of its identifier. -/
theorem blockOf_mem {defs : List (ident × globdef (fundef function) type)}
    (hnd : (defs.map (·.1)).Nodup) {id : ident} {d : globdef (fundef function) type}
    (hmem : (id, d) ∈ defs) :
    ∃ k, ∃ hk : k < defs.length, defs[k] = (id, d) ∧ blockOf defs id = 1 + k := by
  obtain ⟨k, hk, hkd⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨k, hk, hkd, ?_⟩
  unfold blockOf
  have := findIdx_of_mem hnd hk
  rw [hkd] at this
  rw [this]

theorem blockOf_inj {defs : List (ident × globdef (fundef function) type)}
    (hnd : (defs.map (·.1)).Nodup) {id1 id2 : ident} {d1 d2 : globdef (fundef function) type}
    (h1 : (id1, d1) ∈ defs) (h2 : (id2, d2) ∈ defs) (h : blockOf defs id1 = blockOf defs id2) :
    id1 = id2 := by
  obtain ⟨k1, hk1, he1, hb1⟩ := blockOf_mem hnd h1
  obtain ⟨k2, hk2, he2, hb2⟩ := blockOf_mem hnd h2
  have e : 1 + k1 = 1 + k2 := by rw [← hb1, ← hb2]; exact h
  have : k1 = k2 := by omega
  subst this
  rw [he1] at he2
  exact (Prod.mk.inj he2).1

/-- The environment of the whole program: each global of the translation at the block of its
identifier. -/
def envWhole (pre post : List (ident × globdef (fundef function) type)) (T : Translation)
    (G cap : Nat) : Env :=
  let D := wholeDefs pre post T
  { ge := globalenv (wholeProgram pre post T), status := blockOf D statusId,
    globals := (List.range G).map fun i => blockOf D (globalId i), pages := blockOf D pagesId,
    mem := blockOf D memId, cap := cap, res := fun i t => blockOf D (resId i t), nres := T.nres,
    pun := blockOf D punId, sqrt := blockOf D sqrtId }

theorem mem_wholeDefs_of_mem {pre post : List (ident × globdef (fundef function) type)}
    {T : Translation} {id : ident} {d : globdef (fundef function) type}
    (h : (id, d) ∈ T.cprogram.prog_defs) (hne : id ≠ sqrtId) : (id, d) ∈ wholeDefs pre post T := by
  simp only [wholeDefs, List.mem_append, List.mem_filter]
  exact .inl (.inr ⟨h, by simpa using hne⟩)

theorem resId_inj {i j : Nat} {t u : VT} (ht : t.isRes = true) (hu : u.isRes = true)
    (h : resId i t = resId j u) : i = j ∧ t = u := by
  have h' : 32 * (i + 1) + 4 * t.code = 32 * (j + 1) + 4 * u.code := h
  rcases VT.isRes_cases ht with rfl | rfl | rfl <;> rcases VT.isRes_cases hu with rfl | rfl | rfl <;>
    simp only [VT.code] at h' <;> first | exact ⟨by omega, rfl⟩ | (exfalso; omega)

/-- The identifiers of a translation: `statusId`, the constant identifiers 8 to 24, those of the
globals and functions, which leave the remainder 2 or 3 modulo 4, and those of the result
globals, multiples of 4 from 36. -/
theorem translation_ids {m : Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) :
    ∀ x : Nat, x ∈ T.cprogram.prog_defs.map (·.1) →
      x = 1 ∨ x = 8 ∨ x = 12 ∨ x = 16 ∨ x = 20 ∨ x = 24 ∨ x % 4 = 2 ∨ x % 4 = 3 ∨
        (36 ≤ x ∧ x % 4 = 0) := by
  obtain ⟨decl, gdefs, funs, -, -, -, -, -, hfuns, hdefs⟩ := translate_defs h
  intro x hx
  rw [hdefs, progDefs_ids, (funDef_ids hfuns).1] at hx
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with hx | ⟨i, -, hi⟩ | hx | hx | hx | hx | hx | ⟨k, -, hk⟩ | hx
  · have : x = 1 := hx; omega
  · have : x = 4 * i + 2 := hi.symm; omega
  · have : x = 8 := hx; omega
  · have : x = 12 := hx; omega
  · have : x = 20 := hx; omega
  · have : x = 24 := hx; omega
  · have := mem_resIds hx; omega
  · have : x = 4 * k + 3 := hk.symm; omega
  · have : x = 16 := hx; omega

/-- `WholeOk` from conditions that the per-build check confirms: `pre` declares functions with
distinct identifiers, `sqrtId` or numbers other than 1 that leave the remainder 1 modulo 4, among
them `__builtin_fsqrt`, and `post` has distinct identifiers among `mainId` and 28. -/
theorem wholeOk_of {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {pre post : List (ident × globdef (fundef function) type)} (hsq : (sqrtId, sqrtDef) ∈ pre)
    (hfun : ∀ d ∈ pre, ∃ f, d.2 = .Gfun f) (hpost : ∀ d ∈ post, Genv.InitShapeW d.2)
    (hnd : (pre.map (·.1)).Nodup) (hndp : (post.map (·.1)).Nodup)
    (hids : ∀ x : Nat, x ∈ pre.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1))
    (hidp : ∀ x : Nat, x ∈ post.map (·.1) → x = 4 ∨ x = 28) :
    WholeOk pre post T := by
  obtain ⟨decl, gdefs, funs, -, -, -, -, -, hfuns, hdefs⟩ := translate_defs h
  have hT : (T.cprogram.prog_defs.map (·.1)).Nodup := by
    rw [hdefs]; exact progDefs_nodup hfuns
  have hF : ((T.cprogram.prog_defs.filter fun d => d.1 != sqrtId).map (·.1)).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup hT
  have hmid : ∀ x : Nat,
      x ∈ (T.cprogram.prog_defs.filter (fun d => d.1 != sqrtId)).map (·.1) →
      x ≠ 24 ∧ (x = 1 ∨ x = 8 ∨ x = 12 ∨ x = 16 ∨ x = 20 ∨ x = 24 ∨ x % 4 = 2 ∨ x % 4 = 3 ∨
        (36 ≤ x ∧ x % 4 = 0)) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_filter] at hq
    have hqs : q.1 ≠ sqrtId := by simpa using hq.2
    exact ⟨hqs, translation_ids h q.1 (List.mem_map_of_mem hq.1)⟩
  refine ⟨hsq, fun d hd => ?_, hpost, ?_⟩
  · obtain ⟨f, hf⟩ := hfun d hd
    rw [hf]
    exact .inl trivial
  · simp only [wholeDefs, List.map_append]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hnd, hF, fun a ha b hb hab => ?_⟩,
      hndp, fun a ha b hb hab => ?_⟩
    · have h1 := hids a ha
      have h2 := hmid b hb
      have hab' : @Eq Nat a b := hab
      omega
    · have h3 := hidp b hb
      have hab' : @Eq Nat a b := hab
      rcases List.mem_append.mp ha with ha | ha
      · have := hids a ha; omega
      · have := hmid a ha; omega

/-- The bare-metal program of a translation with the function `main`. -/
def bareProgram (pre : List (ident × globdef (fundef function) type)) (T : Translation)
    (main : function) : program function :=
  wholeProgram pre (bareTail main) T

theorem wholeOk_bare {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {pre : List (ident × globdef (fundef function) type)} (hsq : (sqrtId, sqrtDef) ∈ pre)
    (hfun : ∀ d ∈ pre, ∃ f, d.2 = .Gfun f) (hnd : (pre.map (·.1)).Nodup)
    (hids : ∀ x : Nat, x ∈ pre.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1)) (main : function) :
    WholeOk pre (bareTail main) T := by
  refine wholeOk_of h hsq hfun (fun d hd => ?_) hnd (by simp [bareTail, outId, mainId]) hids
    (fun x hx => ?_)
  · simp only [bareTail, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact .inr ⟨outVar, rfl, rfl⟩
    · exact .inl trivial
  · simp only [bareTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx
    · have : x = 28 := hx; omega
    · have : x = 4 := hx; omega

/-! ## The initial memory -/

theorem init_whole {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {pre post : List (ident × globdef (fundef function) type)} (hw : WholeOk pre post T) :
    ∃ decl m0, m.memory = some decl ∧ init_mem (wholeProgram pre post T) = some m0 ∧
      EnvOk (envWhole pre post T m.globals.length cap) ∧
      StatusRel (envWhole pre post T m.globals.length cap) m0 0 ∧
      GlobalsRel (envWhole pre post T m.globals.length cap) (m.globals.map (·.init)) m0 ∧
      MemRel (envWhole pre post T m.globals.length cap) (Wasm.Mem.empty decl.pagesMin.toNat) [cap]
        m0 := by
  obtain ⟨decl, gdefs, funs, hdecl, -, hc1, hc2, hg, hfuns, hdefs⟩ := translate_defs h
  have hG : gdefs.length = m.globals.length := mapM_length hg
  set D := wholeDefs pre post T with hD
  have hnd : (D.map (·.1)).Nodup := hw.nodup
  have hshT := progDefs_shape (cap := cap) (decl := decl) (nres := T.nres) hg hfuns
  have hsh : ∀ g ∈ D, Genv.InitShapeW g.2 := by
    intro g hgD
    simp only [hD, wholeDefs, List.mem_append, List.mem_filter] at hgD
    rcases hgD with (hp | ⟨hT, -⟩) | hq
    · exact hw.pre_shape g hp
    · rw [hdefs] at hT
      exact .inl (hshT g hT)
    · exact hw.post_shape g hq
  obtain ⟨m0, hm0, -, -, hfact⟩ := Genv.alloc_globals_spec_w (globalenv (wholeProgram pre post T))
    D Mem.empty hsh
  have hsym := Genv.find_add_globals_idx (Genv.empty_genv (wholeProgram pre post T).prog_public)
    D hnd
  have hge : globalenv (wholeProgram pre post T) =
      Genv.add_globals (Genv.empty_genv (wholeProgram pre post T).prog_public) D := rfl
  -- Each definition of the whole program: its symbol, its definition, and its initial contents.
  have at_mem : ∀ id d, (id, d) ∈ D →
      Genv.find_symbol (globalenv (wholeProgram pre post T)) id = some (blockOf D id) ∧
        Genv.find_def (globalenv (wholeProgram pre post T)) (blockOf D id) = some d ∧
        Genv.InitFact m0 (blockOf D id) d := by
    intro id d hmem
    obtain ⟨k, hk, hkd, hb⟩ := blockOf_mem hnd hmem
    obtain ⟨h1, h2⟩ := hsym k hk
    have h3 := hfact k hk
    rw [hkd] at h1 h2 h3
    rw [hb, hge]
    exact ⟨h1, h2, h3⟩
  -- The definitions of the translation that the environment names.
  have mT : ∀ (id : Nat × ident) d, (progDefs cap decl gdefs T.nres funs)[id.1]? = some (id.2, d) →
      id.2 ≠ sqrtId → (id.2, d) ∈ D := by
    intro id d hk hne
    exact mem_wholeDefs_of_mem (by rw [hdefs]; exact List.mem_of_getElem? hk) hne
  have memS : (statusId, globdef.Gvar statusVar) ∈ D :=
    mT (0, statusId) _ (progDefs_status cap decl gdefs T.nres funs) (by show (1 : Nat) ≠ 24; decide)
  have memG : ∀ i (hi : i < gdefs.length), (globalId i, globdef.Gvar gdefs[i]) ∈ D := fun i hi =>
    mT (1 + i, globalId i) _ (progDefs_global cap decl gdefs T.nres funs i hi)
      (by show 4 * i + 2 ≠ 24; omega)
  have memP : (pagesId, globdef.Gvar (pagesDef decl.pagesMin.toNat)) ∈ D :=
    mT (1 + gdefs.length, pagesId) _ (progDefs_pages cap decl gdefs T.nres funs) (by show (8 : Nat) ≠ 24; decide)
  have memM : (memId, globdef.Gvar (memDef cap)) ∈ D :=
    mT (2 + gdefs.length, memId) _ (progDefs_mem cap decl gdefs T.nres funs) (by show (12 : Nat) ≠ 24; decide)
  have memU : (punId, globdef.Gvar punDef) ∈ D :=
    mT (3 + gdefs.length, punId) _ (progDefs_pun cap decl gdefs T.nres funs) (by show (20 : Nat) ≠ 24; decide)
  have hres : ∀ (i : Nat) (t : VT), t.isRes = true →
      36 ≤ 32 * (i + 1) + 4 * t.code ∧ (32 * (i + 1) + 4 * t.code) % 4 = 0 := by
    intro i t ht
    rcases VT.isRes_cases ht with rfl | rfl | rfl <;> simp only [VT.code] <;> omega
  have memR : ∀ i < T.nres, ∀ t : VT, t.isRes = true → (resId i t, globdef.Gvar (resDef t)) ∈ D :=
    fun i hi t ht => mT (5 + gdefs.length + resOfs i t, resId i t) _
      (progDefs_res cap decl gdefs T.nres funs i hi t ht)
      (by show 32 * (i + 1) + 4 * t.code ≠ 24; have := hres i t ht; omega)
  have memQ : (sqrtId, sqrtDef) ∈ D := by
    simp only [hD, wholeDefs, List.mem_append]
    exact .inl (.inl hw.sqrt)
  -- Distinct identifiers have distinct blocks.
  have bne : ∀ {id1 id2 : ident} {d1 d2 : globdef (fundef function) type}, (id1, d1) ∈ D →
      (id2, d2) ∈ D → id1 ≠ id2 → blockOf D id1 ≠ blockOf D id2 :=
    fun h1 h2 hne he => hne (blockOf_inj hnd h1 h2 he)
  have gmem : ∀ x ∈ (List.range m.globals.length).map (fun i => blockOf D (globalId i)),
      ∃ i, i < gdefs.length ∧ x = blockOf D (globalId i) := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, by omega, rfl⟩
  have hr : ∀ i < T.nres, ∀ t : VT, t.isRes = true →
      Mem.valid_access m0 t.chunk (blockOf D (resId i t)) 0 .Writable := by
    intro i hi t ht
    have h2 := (at_mem _ _ (memR i hi t ht)).2.2
    rcases VT.isRes_cases ht with rfl | rfl | rfl
    · exact ((h2 _ rfl).1 0 (by simp [resDef])).2
    · exact ((h2 _ rfl).2.1 0 (by simp [resDef])).2
    · exact valid_access_of_bytes (by decide) (by decide)
        (fun j hj => ((h2 _ rfl).2.2 8 (by simp [resDef]) j hj).2)
  obtain ⟨hs1, -, hs2⟩ := at_mem _ _ memS
  obtain ⟨hp1, -, hp2⟩ := at_mem _ _ memP
  obtain ⟨hm1, -, hm2⟩ := at_mem _ _ memM
  obtain ⟨hpun1, -, hpun2⟩ := at_mem _ _ memU
  obtain ⟨hsq1, hsq2, -⟩ := at_mem _ _ memQ
  have hpunW : Mem.valid_access m0 .Mint64 (blockOf D punId) 0 .Writable :=
    valid_access_of_bytes (by decide) (by decide)
      (fun j hj => ((hpun2 _ rfl).2.2 8 rfl j hj).2)
  refine ⟨decl, m0, hdecl, hm0, ?_, ?_, ?_, ?_⟩
  · refine { status := hs1, globals := fun i hi => ?_, nodup := ?_, status_not := ?_,
             pages := hp1, mem := hm1, pages_not := ?_, mem_not := ?_,
             pages_status := bne memP memS (by show (8 : Nat) ≠ 1; decide),
             mem_status := bne memM memS (by show (12 : Nat) ≠ 1; decide),
             mem_pages := bne memM memP (by show (12 : Nat) ≠ 8; decide), cap := hc2,
             res := fun i hi t ht => (at_mem _ _ (memR i hi t ht)).1,
             res_inj := fun i j t u hi hj ht hu he => ?_, res_other := fun i hi t ht => ?_,
             pun := hpun1, pun_other := ?_, sqrt := hsq1,
             sqrt_fun := Genv.find_funct_ptr_of_def (by simpa [sqrtDef, envWhole] using hsq2) }
    · simp only [envWhole, List.length_map, List.length_range] at hi
      simp only [envWhole, List.getElem_map, List.getElem_range]
      exact (at_mem _ _ (memG i (by omega))).1
    · simp only [envWhole]
      refine List.nodup_map_iff_inj_on (List.nodup_range) |>.mpr ?_
      intro a ha b hb hab
      simp only [List.mem_range] at ha hb
      have := blockOf_inj hnd (memG a (by omega)) (memG b (by omega)) hab
      have h' : 4 * a + 2 = 4 * b + 2 := this
      omega
    · intro hx
      obtain ⟨i, hi, he⟩ := gmem _ hx
      exact bne memS (memG i hi) (by show 1 ≠ 4 * i + 2; omega) he
    · intro hx
      obtain ⟨i, hi, he⟩ := gmem _ hx
      exact bne memP (memG i hi) (by show 8 ≠ 4 * i + 2; omega) he
    · intro hx
      obtain ⟨i, hi, he⟩ := gmem _ hx
      exact bne memM (memG i hi) (by show 12 ≠ 4 * i + 2; omega) he
    · exact resId_inj ht hu (blockOf_inj hnd (memR i hi t ht) (memR j hj u hu) he)
    · have hR := memR i hi t ht
      obtain ⟨hc36, hc4⟩ := hres i t ht
      refine ⟨bne hR memS (by show 32 * (i + 1) + 4 * t.code ≠ 1; omega),
        bne hR memP (by show 32 * (i + 1) + 4 * t.code ≠ 8; omega),
        bne hR memM (by show 32 * (i + 1) + 4 * t.code ≠ 12; omega), fun hx => ?_,
        bne hR memU (by show 32 * (i + 1) + 4 * t.code ≠ 20; omega)⟩
      obtain ⟨i', hi', he⟩ := gmem _ hx
      exact bne hR (memG i' hi') (by show 32 * (i + 1) + 4 * t.code ≠ 4 * i' + 2; omega) he
    · refine ⟨bne memU memS (by show (20 : Nat) ≠ 1; decide), bne memU memP (by show (20 : Nat) ≠ 8; decide),
        bne memU memM (by show (20 : Nat) ≠ 12; decide),
        fun hx => ?_⟩
      obtain ⟨i, hi, he⟩ := gmem _ hx
      exact bne memU (memG i hi) (by show 20 ≠ 4 * i + 2; omega) he
  · exact (hs2 _ rfl).1 0 rfl
  · refine ⟨by simp [envWhole], fun i hi => ?_⟩
    simp only [envWhole, List.length_map, List.length_range] at hi
    obtain ⟨gv, hgv, hgi⟩ := mapM_get hg i hi
    obtain ⟨n, hinit, hn, -, -⟩ := globalDef_shape hgv
    have hgi' : gdefs[i]'(by omega) = gv := (List.getElem?_eq_some_iff.mp hgi).2
    have h2 := (at_mem _ _ (memG i (by omega))).2.2
    rw [hgi'] at h2
    obtain ⟨hl, hva⟩ := (h2 _ rfl).2.1 n hn
    refine ⟨n, by simp only [List.getElem?_map]; rw [List.getElem?_eq_getElem hi]; simp [hinit], ?_, ?_⟩
    · simp only [envWhole, List.getElem_map, List.getElem_range]; exact hl
    · simp only [envWhole, List.getElem_map, List.getElem_range]; exact hva
  · obtain ⟨hl, hva⟩ := (hp2 _ rfl).1 _ rfl
    obtain hz := (hm2 _ rfl).2.2 _ rfl
    exact { pages := hl, pagesW := hva, le_cap := hc1, memCap := rfl
            bytes := fun i hi => (hz i (by simp [envWhole] at hi ⊢; omega)).1
            perm := fun i hi => (hz i (by simp [envWhole] at hi ⊢; omega)).2
            resW := fun i hi t ht => hr i hi t ht
            punW := hpunW }

/-! ## `lx_init` and the functions -/

theorem lx_init_whole {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {pre post : List (ident × globdef (fundef function) type)} (hw : WholeOk pre post T) :
    ∃ decl m0, m.memory = some decl ∧ init_mem (wholeProgram pre post T) = some m0 ∧
      EnvOk (envWhole pre post T m.globals.length cap) ∧
      (initId, globdef.Gfun (.Internal (initFunction cap decl.data))) ∈
        (wholeProgram pre post T).prog_defs ∧
      ∀ (A : Archi) (X : ExtSem), ∃ m1,
        eval_funcall A X (globalenv (wholeProgram pre post T)) m0
          (.Internal (initFunction cap decl.data)) [] E0 m1 .Vundef ∧
        StoreRel (envWhole pre post T m.globals.length cap) (nativeStore m cap) m1 ∧
        StatusRel (envWhole pre post T m.globals.length cap) m1 0 := by
  obtain ⟨decl, m0, hdecl, hinit, hE, hs, hg, hmr⟩ := init_whole h hw
  obtain ⟨decl', gdefs, funs, hdecl', hv, hc1, -, -, -, hdefs⟩ := translate_defs h
  rw [hdecl] at hdecl'
  cases hdecl'
  refine ⟨decl, m0, hdecl, hinit, hE,
    mem_wholeDefs_of_mem (by rw [hdefs]; simp [progDefs]) (by decide), fun A X => ?_⟩
  obtain ⟨m1, hx, hsame, hmr1⟩ := exec_segments (A := A) (X := X) hE (create_undef_temps [])
    cap decl.pagesMin.toNat (by simp [envWhole]; omega) decl.data _ m0
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

/-- The functions of the translation are found in the whole program's global environment. -/
theorem funcs_whole {T : Translation}
    {pre post : List (ident × globdef (fundef function) type)} (hw : WholeOk pre post T) :
    ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol (globalenv (wholeProgram pre post T)) (funId k) = some b ∧
        Genv.find_funct_ptr (globalenv (wholeProgram pre post T)) b = some (.Internal fd) := by
  intro k fd hk
  have hmem := mem_wholeDefs_of_mem (pre := pre) (post := post) hk
    (by simp [funId, sqrtId]; omega)
  obtain ⟨b, hs, hd⟩ := Genv.find_add_globals (Genv.empty_genv []) (wholeDefs pre post T) hw.nodup hmem
  exact ⟨b, hs, Genv.find_funct_ptr_of_def hd⟩

/-- The state from which the functions of the translation are called in the whole program:
`init_mem` gives `m0`, and `lx_init` from `m0` gives `m1`, which `envWhole`, which meets the
hypotheses on the environment of `NativeA`, relates to `nativeStore` with `lx_status` 0. -/
theorem start_whole {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {pre post : List (ident × globdef (fundef function) type)} (hw : WholeOk pre post T)
    (A : Archi) (X : ExtSem) :
    ∃ decl m0 m1, m.memory = some decl ∧ init_mem (wholeProgram pre post T) = some m0 ∧
      (initId, globdef.Gfun (.Internal (initFunction cap decl.data))) ∈
        (wholeProgram pre post T).prog_defs ∧
      eval_funcall A X (globalenv (wholeProgram pre post T)) m0
        (.Internal (initFunction cap decl.data)) [] E0 m1 .Vundef ∧
      StoreRel (envWhole pre post T m.globals.length cap) (nativeStore m cap) m1 ∧
      StatusRel (envWhole pre post T m.globals.length cap) m1 0 ∧
      EnvOk (envWhole pre post T m.globals.length cap) ∧
      (envWhole pre post T m.globals.length cap).globals.length = m.globals.length ∧
      (envWhole pre post T m.globals.length cap).cap = cap ∧
      T.nres ≤ (envWhole pre post T m.globals.length cap).nres ∧
      (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
        ∃ b, Genv.find_symbol (envWhole pre post T m.globals.length cap).ge (funId k) = some b ∧
          Genv.find_funct_ptr (envWhole pre post T m.globals.length cap).ge b =
            some (.Internal fd)) := by
  obtain ⟨decl, m0, hdecl, hinit, hE, hmem, hrun⟩ := lx_init_whole h hw
  obtain ⟨m1, hcall, hst, hs⟩ := hrun A X
  exact ⟨decl, m0, m1, hdecl, hinit, hmem, hcall, hst, hs, hE, by simp [envWhole], rfl,
    Nat.le_refl _, funcs_whole hw⟩

end LeanExe.Native
