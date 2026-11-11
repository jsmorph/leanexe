import LeanExe.Native.ClightN.Leaf
import LeanExe.Native.Proof.Whole

/-!
The executions of the Lean copy of Clight are executions of N (`clightn/N.nsx`), for the
programs that the translator's forms make up.  `progOk` decides, for a program's definitions, its
`main`, and a list `S` of functions that contains `main` and the functions they call, that the
bodies of those functions use only the forms that N's relations cover: the leaf operators and
casts, temporaries, constants, the scalar globals, calls of functions of `S`, the volatile store
to a global of type `volatile unsigned int`, and the statements of the translation.  It also
decides the conditions that N's program judgment places on the definitions.  `program_to_n`
carries the copy's `bigstep_program_terminates` at `Archi.aarch64` to `nprog`.

The proof follows the copy's derivation.  It relates the copy's temporaries to N's by
`TempsRel` and its memory to N's scalar globals by `GRel`, and carries the invariants that no
temporary holds a pointer (`NoPtr`) and that a `return` gives a value of a leaf cast to the
function's result type (`RetOk`).  Rocq proves in `clightn/rocq/NExec.v` that each derivation of
N is one of CompCert's.
-/

namespace ClightN.Proof

open LClight ClightN.Base ClightN.Spec

/-! ## Leaf forms -/

/-- The operator forms of `binop_ok`. -/
def binForms : List (binary_operation × type × type) :=
  [(.Oadd, tul, tul), (.Osub, tul, tul), (.Omul, tul, tul), (.Odiv, tul, tul),
   (.Omod, tul, tul), (.Oand, tul, tul), (.Oor, tul, tul), (.Oxor, tul, tul),
   (.Oshl, tul, tul), (.Oshr, tul, tul), (.Oeq, tul, tul), (.One, tul, tul),
   (.Olt, tul, tul), (.Ole, tul, tul), (.Ogt, tul, tul), (.Oge, tul, tul),
   (.Olt, tsl, tsl), (.Ole, tsl, tsl), (.Oshr, tsl, tul),
   (.Oadd, tui, tui), (.Osub, tui, tui), (.Oand, tui, tui), (.Oshl, tui, tui),
   (.Oshr, tui, tui), (.Oeq, tui, tui), (.One, tui, tui), (.Olt, tui, tui),
   (.Ogt, tui, tui), (.Oge, tui, tui)]

/-- The cast forms of `cast_ok`. -/
def castForms : List (type × type) :=
  [(tsi, tui), (tui, tsi), (tul, tui), (tui, tul), (tul, tsl), (tsl, tul), (tuc, tul),
   (tuc, tui), (tul, tuc), (tui, tuc), (tvuc, tul), (tvui, tul), (tui, tvui), (tul, tul),
   (tui, tui), (tuc, tuc), (tsi, tsi)]

theorem binop_leaf {op : binary_operation} {t1 t2 : type} {v1 v2 v : val} {m : mem}
    (hf : (op, t1, t2) ∈ binForms)
    (h : sem_binary_operation Archi.aarch64 op v1 t1 v2 t2 m = some v) :
    binop_ok op t1 t2 v1 v2 v := by
  simp only [binForms, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact (add_ul_ul () v1 v2 v m).1 h
  · exact (sub_ul_ul () v1 v2 v m).1 h
  · exact (mul_ul_ul () v1 v2 v m).1 h
  · exact (div_ul_ul () v1 v2 v m).1 h
  · exact (mod_ul_ul () v1 v2 v m).1 h
  · exact (and_ul_ul () v1 v2 v m).1 h
  · exact (or_ul_ul () v1 v2 v m).1 h
  · exact (xor_ul_ul () v1 v2 v m).1 h
  · exact (shl_ul_ul () v1 v2 v m).1 h
  · exact (shr_ul_ul () v1 v2 v m).1 h
  · exact (eq_ul_ul () v1 v2 v m).1 h
  · exact (ne_ul_ul () v1 v2 v m).1 h
  · exact (lt_ul_ul () v1 v2 v m).1 h
  · exact (le_ul_ul () v1 v2 v m).1 h
  · exact (gt_ul_ul () v1 v2 v m).1 h
  · exact (ge_ul_ul () v1 v2 v m).1 h
  · exact (lt_sl_sl () v1 v2 v m).1 h
  · exact (le_sl_sl () v1 v2 v m).1 h
  · exact (shr_sl_ul () v1 v2 v m).1 h
  · exact (add_ui_ui () v1 v2 v m).1 h
  · exact (sub_ui_ui () v1 v2 v m).1 h
  · exact (and_ui_ui () v1 v2 v m).1 h
  · exact (shl_ui_ui () v1 v2 v m).1 h
  · exact (shr_ui_ui () v1 v2 v m).1 h
  · exact (eq_ui_ui () v1 v2 v m).1 h
  · exact (ne_ui_ui () v1 v2 v m).1 h
  · exact (lt_ui_ui () v1 v2 v m).1 h
  · exact (gt_ui_ui () v1 v2 v m).1 h
  · exact (ge_ui_ui () v1 v2 v m).1 h

theorem cast_leaf {t1 t2 : type} {v1 v : val} {m : mem} (hf : (t1, t2) ∈ castForms)
    (h : sem_cast Archi.aarch64 v1 t1 t2 m = some v) : cast_ok t1 t2 v1 v := by
  simp only [castForms, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (cast_si_ui v1 v m).1 h
  · exact (cast_ui_si v1 v m).1 h
  · exact (cast_ul_ui v1 v m).1 h
  · exact (cast_ui_ul v1 v m).1 h
  · exact (cast_ul_sl v1 v m).1 h
  · exact (cast_sl_ul v1 v m).1 h
  · exact (cast_uc_ul v1 v m).1 h
  · exact (cast_uc_ui v1 v m).1 h
  · exact (cast_ul_uc v1 v m).1 h
  · exact (cast_ui_uc v1 v m).1 h
  · exact (cast_vuc_ul v1 v m).1 h
  · exact (cast_vui_ul v1 v m).1 h
  · exact (cast_ui_vui v1 v m).1 h
  · exact (cast_ul_ul v1 v m).1 h
  · exact (cast_ui_ui v1 v m).1 h
  · exact (cast_uc_uc v1 v m).1 h
  · exact (cast_si_si v1 v m).1 h

theorem bool_leaf {t : type} {v : val} {b : Bool} {m : mem} (ht : t = tsi ∨ t = tui)
    (h : bool_val Archi.aarch64 v t m = some b) : bool_ok t v b := by
  rcases ht with rfl | rfl
  · exact (bool_si v b m).1 h
  · exact (bool_ui v b m).1 h

/-! ## Values without pointers -/

def NoPtrV (v : val) : Prop := ∀ b o, v ≠ .Vptr b o

theorem binop_ok_noptr {op : binary_operation} {t1 t2 : type} {v1 v2 v : val}
    (h : binop_ok op t1 t2 v1 v2 v) : NoPtrV v := by
  intro b o e
  subst e
  cases h

theorem cast_ok_noptr {t1 t2 : type} {v1 v : val} (h : cast_ok t1 t2 v1 v) (hp : NoPtrV v1) :
    NoPtrV v := by
  intro b o e
  subst e
  cases h with
  | co_ul_sl_ptr => exact hp _ _ rfl
  | co_sl_ul_ptr => exact hp _ _ rfl
  | co_ul_ul_ptr => exact hp _ _ rfl

/-! ## The forms that N covers -/

def scalarTy (t : type) : Bool := t == tui || t == tul

/-- The definition `d` of `x` is a writable, non-volatile variable of the scalar type `ty`. -/
def scalarDef (x : ident) (ty : type) (d : ident × globdef (fundef function) type) : Bool :=
  d.1 == x && match d.2 with
    | .Gvar v => v.gvar_info == ty && !v.gvar_readonly && !v.gvar_volatile
    | .Gfun _ => false

/-- The definition `d` of `x` is a writable variable of type `volatile unsigned int`. -/
def volDef (x : ident) (d : ident × globdef (fundef function) type) : Bool :=
  d.1 == x && match d.2 with
    | .Gvar v => v.gvar_info == tvui && !v.gvar_readonly && v.gvar_volatile
    | .Gfun _ => false

abbrev Defs := List (ident × globdef (fundef function) type)

def exprOk (defs : Defs) : expr → Bool
  | .Econst_int _ _ | .Econst_long _ _ | .Econst_float _ _ | .Econst_single _ _
  | .Etempvar _ _ => true
  | .Evar x ty => scalarTy ty && defs.any (scalarDef x ty)
  | .Ebinop op a1 a2 _ =>
      exprOk defs a1 && exprOk defs a2 && decide ((op, typeof a1, typeof a2) ∈ binForms)
  | .Ecast a ty => exprOk defs a && decide ((typeof a, ty) ∈ castForms)
  | _ => false

def argsOk (defs : Defs) : List expr → List type → Bool
  | [], [] => true
  | a :: al, ty :: tys =>
      exprOk defs a && decide ((typeof a, ty) ∈ castForms) && argsOk defs al tys
  | _, _ => false

def ptrVui : type := .Tpointer tvui (attr.mk false none)

def stmtOk (defs : Defs) (S : List ident) (ret : type) : statement → Bool
  | .Sskip | .Sbreak | .Scontinue | .Sreturn none => true
  | .Sset _ a => exprOk defs a
  | .Sassign (.Evar x ty) a =>
      scalarTy ty && defs.any (scalarDef x ty) && exprOk defs a &&
        decide ((typeof a, ty) ∈ castForms)
  | .Scall _ (.Evar x (.Tfunction tys _ _)) al => S.contains x && argsOk defs al tys
  | .Sbuiltin none (.EF_vstore .Mint32) [p1, p2] [.Eaddrof (.Evar x t1) p3, a] =>
      p1 == ptrVui && p2 == tvui && t1 == tvui && p3 == ptrVui && defs.any (volDef x) &&
        exprOk defs a && decide ((typeof a, tvui) ∈ castForms)
  | .Ssequence s1 s2 => stmtOk defs S ret s1 && stmtOk defs S ret s2
  | .Sloop s1 s2 => stmtOk defs S ret s1 && stmtOk defs S ret s2
  | .Sifthenelse a s1 s2 =>
      exprOk defs a && (typeof a == tsi || typeof a == tui) && stmtOk defs S ret s1 &&
        stmtOk defs S ret s2
  | .Sreturn (some a) => exprOk defs a && ret != .Tvoid && decide ((typeof a, ret) ∈ castForms)
  | _ => false

/-- The variables whose initialization data N accepts: a scalar global is initialized by one
datum of its type, and another variable has none or one `Init_space` of a size not negative. -/
def varOk (v : globvar type) : Bool :=
  match v.gvar_init with
  | [] => !(scalarTy v.gvar_info && !v.gvar_readonly && !v.gvar_volatile)
  | [.Init_int32 _] => !v.gvar_readonly && !v.gvar_volatile && v.gvar_info == tui
  | [.Init_int64 _] => !v.gvar_readonly && !v.gvar_volatile && v.gvar_info == tul
  | [.Init_space n] =>
      !v.gvar_readonly && !v.gvar_volatile && decide (0 ≤ n) && !scalarTy v.gvar_info
  | _ => false

def defOk : globdef (fundef function) type → Bool
  | .Gvar v => varOk v
  | .Gfun _ => true

/-- The function `x` of `defs` uses only the forms of `stmtOk` and declares no local variable in
memory. -/
def funOk (defs : Defs) (S : List ident) (x : ident) : Bool :=
  defs.any fun d => d.1 == x && match d.2 with
    | .Gfun (.Internal f) => f.fn_vars.isEmpty && stmtOk defs S f.fn_return f.fn_body
    | _ => false

def progOk (defs : Defs) (main : ident) (S : List ident) : Bool :=
  decide (defs.map (·.1)).Nodup && defs.all (fun d => defOk d.2) && S.contains main &&
    S.all (funOk defs S)

/-! ## N's lists -/

theorem in_defs_of_mem {defs : Defs} {x : ident} {g : globdef (fundef function) type}
    (h : (x, g) ∈ defs) : in_defs defs x g := by
  induction defs with
  | nil => cases h
  | cons d rest ih =>
      rcases List.mem_cons.mp h with e | h
      · subst e
        exact .in_here x g rest
      · exact .in_there d rest x g (ih h)

theorem out_defs_of {x : ident} : ∀ {defs : Defs}, x ∉ defs.map (·.1) → out_defs x defs
  | [], _ => .od_nil x
  | (y, g) :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      exact .od_cons x y g rest (fun e => h.1 e) (out_defs_of h.2)

theorem norepet_defs_of : ∀ {defs : Defs}, (defs.map (·.1)).Nodup → norepet_defs defs
  | [], _ => .nd_nil
  | (x, g) :: rest, h => by
      simp only [List.map_cons, List.nodup_cons] at h
      exact .nd_cons x g rest (out_defs_of h.1) (norepet_defs_of h.2)

theorem out_names_of {x : ident} :
    ∀ {l : List (ident × type)}, x ∉ var_names l → out_names x l
  | [], _ => .on_nil x
  | (y, t) :: rest, h => by
      simp only [var_names, List.map_cons, List.mem_cons, not_or] at h
      exact .on_cons x y t rest (fun e => h.1 e) (out_names_of h.2)

theorem norepet_names_of : ∀ {l : List (ident × type)}, (var_names l).Nodup → norepet_names l
  | [], _ => .nn_nil
  | (x, t) :: rest, h => by
      simp only [var_names, List.map_cons, List.nodup_cons] at h
      exact .nn_cons x t rest (out_names_of h.1) (norepet_names_of h.2)

theorem disjoint_names_of {l2 : List (ident × type)} :
    ∀ {l1 : List (ident × type)}, (∀ x ∈ var_names l1, ∀ y ∈ var_names l2, x ≠ y) →
      disjoint_names l1 l2
  | [], _ => .dn_nil l2
  | (x, t) :: rest, h => by
      refine .dn_cons x t rest l2 (out_names_of fun hx => h x (by simp [var_names]) x hx rfl)
        (disjoint_names_of fun a ha b hb => h a ?_ b hb)
      simp only [var_names, List.map_cons, List.mem_cons] at ha ⊢
      exact .inr ha

theorem params_types_of : ∀ l : List (ident × type), params_types l (type_of_params l)
  | [] => .pt_nil
  | (x, t) :: rest => .pt_cons x t rest _ (params_types_of rest)

/-! ## Temporaries -/

def TempsRel (le : temp_env) (ln : ident → Option val) : Prop := ∀ x, le[x]? = ln x

def NoPtr (ln : ident → Option val) : Prop := ∀ x v, ln x = some v → NoPtrV v

def NoPtrs (vs : List val) : Prop := ∀ v ∈ vs, NoPtrV v

theorem upd_insert (le : temp_env) (x : ident) (v : val) :
    ∀ y, (y = x → (le.insert x v)[y]? = some v) ∧ (¬ y = x → (le.insert x v)[y]? = le[y]?) :=
  fun y => ⟨fun e => by subst e; exact te_insert_same le y v,
    fun ne => te_insert_ne v (Ne.symm ne)⟩

theorem noptr_insert {le : temp_env} {x : ident} {v : val} (hp : NoPtr fun y => le[y]?)
    (hv : NoPtrV v) : NoPtr fun y => (le.insert x v)[y]? := by
  intro y w hw
  change (le.insert x v)[y]? = some w at hw
  by_cases e : y = x
  · subst e
    rw [te_insert_same] at hw
    cases hw
    exact hv
  · rw [te_insert_ne v (Ne.symm e)] at hw
    exact hp y w hw

theorem undef_temps_of :
    ∀ temps : List (ident × type), undef_temps temps fun y => (create_undef_temps temps)[y]?
  | [] => .ut_nil _ fun _ => rfl
  | (x, t) :: rest =>
      .ut_cons x t rest _ _ (undef_temps_of rest) (upd_insert (create_undef_temps rest) x .Vundef)

theorem noptr_undef : ∀ temps : List (ident × type),
    NoPtr fun y => (create_undef_temps temps)[y]?
  | [] => fun _ _ h => by cases h
  | (x, _) :: rest => noptr_insert (noptr_undef rest) (fun _ _ e => by cases e)

theorem bind_params_of : ∀ (params : List (ident × type)) (vs : List val) (le le' : temp_env),
    bind_parameter_temps params vs le = some le' →
      bind_params params vs (fun y => le[y]?) (fun y => le'[y]?)
  | [], [], le, le', h => by
      cases h
      exact .bp_nil _
  | (x, t) :: rest, v :: vs, le, le', h =>
      .bp_cons x t rest v vs _ _ _ (upd_insert le x v) (bind_params_of rest vs _ le' h)
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

theorem noptr_bind : ∀ (params : List (ident × type)) (vs : List val) (le le' : temp_env),
    bind_parameter_temps params vs le = some le' → NoPtrs vs → (NoPtr fun y => le[y]?) →
      NoPtr fun y => le'[y]?
  | [], [], le, le', h, _, hp => by
      cases h
      exact hp
  | (x, _) :: rest, v :: vs, le, le', h, hvs, hp =>
      noptr_bind rest vs _ le' h (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
        (noptr_insert hp (hvs v List.mem_cons_self))
  | [], _ :: _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, h, _, _ => by cases h

/-! ## Global environments and scalar globals -/

/-- What the proof uses of the global environment `ge` of a program with the definitions
`defs`. -/
structure GenvOk (ge : genv) (defs : Defs) : Prop where
  nodup : (defs.map (·.1)).Nodup
  sym_def : ∀ x g, (x, g) ∈ defs →
    ∃ b, Genv.find_symbol ge x = some b ∧ Genv.find_def ge b = some g
  def_sym : ∀ x b, Genv.find_symbol ge x = some b →
    ∃ g, (x, g) ∈ defs ∧ Genv.find_def ge b = some g
  inj : ∀ x y b, Genv.find_symbol ge x = some b → Genv.find_symbol ge y = some b → x = y

theorem mem_unique {defs : Defs} (hn : (defs.map (·.1)).Nodup) {x : ident}
    {g1 g2 : globdef (fundef function) type} (h1 : (x, g1) ∈ defs) (h2 : (x, g2) ∈ defs) :
    g1 = g2 := by
  induction defs with
  | nil => cases h1
  | cons d rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hn
      have hx : ∀ g, (x, g) ∈ rest → d.1 ≠ x := fun g hg e =>
        hn.1 (e ▸ List.mem_map_of_mem (f := (·.1)) hg)
      rcases List.mem_cons.mp h1 with e1 | r1 <;> rcases List.mem_cons.mp h2 with e2 | r2
      · rw [← e1] at e2
        injection e2 with _ e
        exact e.symm
      · exact absurd (by rw [← e1]) (hx g2 r2)
      · exact absurd (by rw [← e2]) (hx g1 r1)
      · exact ih hn.2 r1 r2

theorem genvOk_globalenv (p : program function) (hn : (p.prog_defs.map (·.1)).Nodup) :
    GenvOk (globalenv p) p.prog_defs := by
  have hsd : ∀ x g, (x, g) ∈ p.prog_defs →
      ∃ b, Genv.find_symbol (globalenv p) x = some b ∧ Genv.find_def (globalenv p) b = some g :=
    fun x g h => Genv.find_add_globals _ _ hn h
  have hidx : ∀ z c, Genv.find_symbol (globalenv p) z = some c →
      ∃ k, ∃ hk : k < p.prog_defs.length, p.prog_defs[k].1 = z ∧ c = 1 + k := by
    intro z c hz
    by_cases hm : z ∈ p.prog_defs.map (·.1)
    · obtain ⟨k, hk, e⟩ := List.getElem_of_mem hm
      simp only [List.getElem_map, List.length_map] at e hk
      have := (Genv.find_add_globals_idx (Genv.empty_genv p.prog_public) p.prog_defs hn k hk).1
      rw [e] at this
      simp only [globalenv] at hz
      rw [this] at hz
      cases hz
      exact ⟨k, hk, e, rfl⟩
    · have := (Genv.add_globals_keep (Genv.empty_genv p.prog_public) p.prog_defs).1 z hm
      simp only [globalenv] at hz
      rw [this] at hz
      cases hz
  refine ⟨hn, hsd, fun x b h => ?_, fun x y b hx hy => ?_⟩
  · obtain ⟨k, hk, e, rfl⟩ := hidx x b h
    obtain ⟨b', h1, h2⟩ := hsd x p.prog_defs[k].2 (by rw [← e]; exact List.getElem_mem hk)
    rw [h] at h1
    cases h1
    exact ⟨p.prog_defs[k].2, by rw [← e]; exact List.getElem_mem hk, h2⟩
  · obtain ⟨k1, hk1, e1, rfl⟩ := hidx x b hx
    obtain ⟨k2, hk2, e2, e⟩ := hidx y _ hy
    have : k1 = k2 := Nat.add_left_cancel e
    subst this
    rw [← e1, ← e2]

def chunkOf (ty : type) : memory_chunk := if ty = tui then .Mint32 else .Mint64

/-- The memory `m` holds the values `gv` of the scalar globals. -/
def GRel (ge : genv) (defs : Defs) (m : mem) (gv : ident → Option val) : Prop :=
  ∀ x ty init b, (x, .Gvar ⟨ty, init, false, false⟩) ∈ defs → scalar ty →
    Genv.find_symbol ge x = some b →
    ∃ v, gv x = some v ∧ gval ty v ∧ Mem.load Archi.aarch64 (chunkOf ty) m b 0 = some v ∧
      Mem.valid_access m (chunkOf ty) b 0 .Writable

theorem gval_noptr {ty : type} {v : val} (h : gval ty v) : NoPtrV v := by
  intro b o e
  subst e
  cases h

theorem scalar_of {ty : type} (h : scalarTy ty = true) : scalar ty := by
  simp only [scalarTy, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact .sc_ui
  · exact .sc_ul

theorem scalarDef_mem {defs : Defs} {x : ident} {ty : type}
    (h : defs.any (scalarDef x ty) = true) :
    ∃ init, (x, .Gvar ⟨ty, init, false, false⟩) ∈ defs := by
  obtain ⟨⟨y, g⟩, hd, hs⟩ := List.any_eq_true.mp h
  simp only [scalarDef, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨rfl, hs⟩ := hs
  cases g with
  | Gfun _ => simp at hs
  | Gvar v =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
      obtain ⟨⟨e1, e2⟩, e3⟩ := hs
      obtain ⟨info, init, ro, vol⟩ := v
      simp only at e1 e2 e3
      subst e1 e2 e3
      exact ⟨init, hd⟩

theorem volDef_mem {defs : Defs} {x : ident} (h : defs.any (volDef x) = true) :
    ∃ init, (x, .Gvar ⟨tvui, init, false, true⟩) ∈ defs := by
  obtain ⟨⟨y, g⟩, hd, hs⟩ := List.any_eq_true.mp h
  simp only [volDef, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨rfl, hs⟩ := hs
  cases g with
  | Gfun _ => simp at hs
  | Gvar v =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
      obtain ⟨⟨e1, e2⟩, e3⟩ := hs
      obtain ⟨info, init, ro, vol⟩ := v
      simp only at e1 e2 e3
      subst e1 e2 e3
      exact ⟨init, hd⟩

theorem access_scalar {ty : type} (h : scalar ty) :
    access_mode Archi.aarch64 ty = .By_value (chunkOf ty) := by
  cases h <;> rfl

/-! ## Expressions -/

section

variable {ge : genv} {defs : Defs}

theorem eval_to_n {le : temp_env} {m : mem} {ln gv : ident → Option val}
    (htr : TempsRel le ln) (hp : NoPtr ln) (hg : GRel ge defs m gv) :
    ∀ {a : expr} {v : val}, exprOk defs a = true →
      eval_expr Archi.aarch64 ge empty_env le m a v →
      neval defs ln gv a v ∧ has_type a (typeof a) ∧ NoPtrV v := by
  intro a
  induction a with
  | Econst_int i ty =>
      intro v _ h
      cases h with
      | eval_Econst_int => exact ⟨.nv_int i ty, .ht_int i ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | Econst_long i ty =>
      intro v _ h
      cases h with
      | eval_Econst_long => exact ⟨.nv_long i ty, .ht_long i ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | Econst_float f ty =>
      intro v _ h
      cases h with
      | eval_Econst_float => exact ⟨.nv_float f ty, .ht_float f ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | Econst_single f ty =>
      intro v _ h
      cases h with
      | eval_Econst_single =>
          exact ⟨.nv_single f ty, .ht_single f ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | Etempvar x ty =>
      intro v _ h
      cases h with
      | eval_Etempvar _ _ _ hv =>
          have hv' : ln x = some v := (htr x).symm.trans hv
          exact ⟨.nv_temp x ty v hv', .ht_temp x ty, hp x v hv'⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | Evar x ty =>
      intro v hok h
      simp only [exprOk, Bool.and_eq_true] at hok
      have hsc := scalar_of hok.1
      obtain ⟨init, hd⟩ := scalarDef_mem hok.2
      cases h with
      | eval_Elvalue _ l ofs bf _ hl hdr =>
          cases hl with
          | eval_Evar_local _ _ _ he => simp [empty_env] at he
          | eval_Evar_global _ _ _ _ hs =>
              obtain ⟨w, hw, hgv, hload, _⟩ := hg x ty init l hd hsc hs
              cases hdr with
              | deref_loc_value chunk _ hac hlv =>
                  change access_mode _ ty = _ at hac
                  rw [access_scalar hsc] at hac
                  cases hac
                  have : v = w := by
                    have hz : Ptrofs.unsigned Ptrofs.zero = 0 := rfl
                    simp only [Mem.loadv, hz] at hlv
                    rw [ite_eq_left (by cases hsc <;> decide), hload] at hlv
                    cases hlv
                    rfl
                  subst this
                  exact ⟨.nv_global x ty init v (in_defs_of_mem hd) hsc hw, .ht_var x ty,
                    gval_noptr hgv⟩
              | deref_loc_reference hac =>
                  change access_mode _ ty = _ at hac
                  rw [access_scalar hsc] at hac
                  cases hac
  | Ebinop op a1 a2 ty ih1 ih2 =>
      intro v hok h
      simp only [exprOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      cases h with
      | eval_Ebinop _ _ _ _ v1 v2 _ h1 h2 hs =>
          obtain ⟨n1, t1, _⟩ := ih1 hok.1.1 h1
          obtain ⟨n2, t2, _⟩ := ih2 hok.1.2 h2
          have hb := binop_leaf hok.2 hs
          exact ⟨.nv_binop op a1 a2 ty _ _ v1 v2 v n1 t1 n2 t2 hb, .ht_binop op a1 a2 ty,
            binop_ok_noptr hb⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | Ecast a ty ih =>
      intro v hok h
      simp only [exprOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      cases h with
      | eval_Ecast _ _ v1 _ h1 hc =>
          obtain ⟨n1, t1, p1⟩ := ih hok.1 h1
          have hc' := cast_leaf hok.2 hc
          exact ⟨.nv_cast a ty _ v1 v n1 t1 hc', .ht_cast a ty, cast_ok_noptr hc' p1⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | _ => intro v hok _; simp [exprOk] at hok

theorem evallist_to_n {le : temp_env} {m : mem}
    {ln gv : ident → Option val} (htr : TempsRel le ln) (hp : NoPtr ln) (hg : GRel ge defs m gv) :
    ∀ {al : List expr} {tys : List type} {vs : List val}, argsOk defs al tys = true →
      eval_exprlist Archi.aarch64 ge empty_env le m al tys vs →
      neval_list defs ln gv al tys vs ∧ NoPtrs vs := by
  intro al tys vs hok h
  induction h with
  | eval_Enil => exact ⟨.nl_nil, fun _ h => by cases h⟩
  | eval_Econs a bl ty tyl v1 v2 vl ha hc _ ih =>
      simp only [argsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨na, ta, pa⟩ := eval_to_n htr hp hg hok.1.1 ha
      have hc' := cast_leaf hok.1.2 hc
      obtain ⟨nl, pl⟩ := ih hok.2
      refine ⟨.nl_cons a bl ty tyl _ v1 v2 vl na ta hc' nl, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact cast_ok_noptr hc' pa
      · exact pl w hw

end

/-! ## Statements -/

/-- `ln` with `x` set to `v`, as N's rules state an update. -/
def upd (ln : ident → Option val) (x : ident) (v : val) : ident → Option val :=
  fun y => if y = x then some v else ln y

theorem upd_spec (ln : ident → Option val) (x : ident) (v : val) :
    ∀ y, (y = x → upd ln x v y = some v) ∧ (¬ y = x → upd ln x v y = ln y) :=
  fun y => ⟨fun e => by simp [upd, e], fun e => by simp [upd, e]⟩

theorem temps_upd {le : temp_env} {ln : ident → Option val} (htr : TempsRel le ln) (x : ident)
    (v : val) : TempsRel (le.insert x v) (upd ln x v) := by
  intro y
  by_cases e : y = x
  · subst e
    simp [upd]
  · simp only [upd, e, ite_false]
    rw [te_insert_ne v (Ne.symm e)]
    exact htr y

theorem noptr_upd {ln : ident → Option val} (hp : NoPtr ln) (x : ident) {v : val}
    (hv : NoPtrV v) : NoPtr (upd ln x v) := by
  intro y w hw
  by_cases e : y = x
  · simp only [upd, e, ite_true] at hw
    cases hw
    exact hv
  · simp only [upd, e, ite_false] at hw
    exact hp y w hw

theorem set_opt_of (optid : Option ident) {v : val} {le : temp_env} {ln : ident → Option val}
    (htr : TempsRel le ln) (hp : NoPtr ln) (hv : NoPtrV v) :
    ∃ ln', set_opt optid v ln ln' ∧ TempsRel (set_opttemp optid v le) ln' ∧ NoPtr ln' := by
  cases optid with
  | none => exact ⟨ln, .so_none v ln, htr, hp⟩
  | some x => exact ⟨upd ln x v, .so_some x v ln _ (upd_spec ln x v), temps_upd htr x v,
      noptr_upd hp x hv⟩

theorem gval_of_cast {t ty : type} {v1 v : val} (hsc : scalar ty) (h : cast_ok t ty v1 v)
    (hp : NoPtrV v1) : gval ty v := by
  cases hsc <;> cases h <;> first | exact .gv_ui _ | exact .gv_ul _ | exact absurd rfl (hp _ _)

/-- A `return` gives a value without a pointer, of a type with a leaf cast to the result type
`ret`, which is not `void`. -/
def RetOk (ret : type) (out : outcome) : Prop :=
  ∀ v t, out = .Out_return (some (v, t)) → (t, ret) ∈ castForms ∧ ret ≠ .Tvoid ∧ NoPtrV v

theorem retOk_normal (ret : type) : RetOk ret .Out_normal := fun _ _ e => by cases e

theorem cast_vui {t : type} {v1 v : val} (h : cast_ok t tvui v1 v) : ∃ i, v = .Vint i := by
  cases h
  exact ⟨_, rfl⟩

/-- The statements that `stmtOk` accepts, by their forms. -/
inductive SOk (defs : Defs) (S : List ident) (ret : type) : statement → Prop
  | skip : SOk defs S ret .Sskip
  | brk : SOk defs S ret .Sbreak
  | cont : SOk defs S ret .Scontinue
  | ret_none : SOk defs S ret (.Sreturn none)
  | ret_some (a : expr) : exprOk defs a = true → ret ≠ .Tvoid → (typeof a, ret) ∈ castForms →
      SOk defs S ret (.Sreturn (some a))
  | set (x : ident) (a : expr) : exprOk defs a = true → SOk defs S ret (.Sset x a)
  | store (x : ident) (ty : type) (a : expr) : scalarTy ty = true →
      defs.any (scalarDef x ty) = true → exprOk defs a = true → (typeof a, ty) ∈ castForms →
      SOk defs S ret (.Sassign (.Evar x ty) a)
  | call (optid : Option ident) (x : ident) (tys : List type) (rty : type)
      (cc : calling_convention) (al : List expr) : S.contains x = true →
      argsOk defs al tys = true → SOk defs S ret (.Scall optid (.Evar x (.Tfunction tys rty cc)) al)
  | out (x : ident) (a : expr) : defs.any (volDef x) = true → exprOk defs a = true →
      (typeof a, tvui) ∈ castForms →
      SOk defs S ret (.Sbuiltin none (.EF_vstore .Mint32) [ptrVui, tvui]
        [.Eaddrof (.Evar x tvui) ptrVui, a])
  | seq (s1 s2 : statement) : SOk defs S ret s1 → SOk defs S ret s2 →
      SOk defs S ret (.Ssequence s1 s2)
  | loop (s1 s2 : statement) : SOk defs S ret s1 → SOk defs S ret s2 →
      SOk defs S ret (.Sloop s1 s2)
  | ite (a : expr) (s1 s2 : statement) : exprOk defs a = true →
      (typeof a = tsi ∨ typeof a = tui) → SOk defs S ret s1 → SOk defs S ret s2 →
      SOk defs S ret (.Sifthenelse a s1 s2)

theorem sok_of {defs : Defs} {S : List ident} {ret : type} :
    (s : statement) → stmtOk defs S ret s = true → SOk defs S ret s
  | .Sskip, _ => .skip
  | .Sbreak, _ => .brk
  | .Scontinue, _ => .cont
  | .Sreturn none, _ => .ret_none
  | .Sreturn (some a), h => by
      simp only [stmtOk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      exact .ret_some a h.1.1 h.1.2 h.2
  | .Sset x a, h => .set x a (by simpa [stmtOk] using h)
  | .Sassign a1 a2, h => by
      cases a1 with
      | Evar x ty =>
          simp only [stmtOk, Bool.and_eq_true, decide_eq_true_eq] at h
          exact .store x ty a2 h.1.1.1 h.1.1.2 h.1.2 h.2
      | _ => simp [stmtOk] at h
  | .Scall optid f al, h => by
      cases f with
      | Evar x fty =>
          cases fty with
          | Tfunction tys rty cc =>
              simp only [stmtOk, Bool.and_eq_true] at h
              exact .call optid x tys rty cc al h.1 h.2
          | _ => simp [stmtOk] at h
      | _ => simp [stmtOk] at h
  | .Sbuiltin optid ef tys al, h => by
      unfold stmtOk at h
      split at h
      case h_8 p1 p2 x t1 p3 a heq =>
        injection heq with e1 e2 e3 e4
        subst e1 e2 e3 e4
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hv⟩, ha⟩, hc⟩ := h
        exact .out _ _ hv ha hc
      all_goals first | (rename_i heq; injection heq) | simp at h
  | .Ssequence s1 s2, h => by
      simp only [stmtOk, Bool.and_eq_true] at h
      exact .seq s1 s2 (sok_of s1 h.1) (sok_of s2 h.2)
  | .Sloop s1 s2, h => by
      simp only [stmtOk, Bool.and_eq_true] at h
      exact .loop s1 s2 (sok_of s1 h.1) (sok_of s2 h.2)
  | .Sifthenelse a s1 s2, h => by
      simp only [stmtOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      exact .ite a s1 s2 h.1.1.1 h.1.1.2 (sok_of s1 h.1.2) (sok_of s2 h.2)
  | .Sswitch _ _, h => by simp [stmtOk] at h
  | .Slabel _ _, h => by simp [stmtOk] at h
  | .Sgoto _, h => by simp [stmtOk] at h

/-- The functions of `S` are internal functions of `defs` that declare no local variable in
memory and whose bodies use the forms of `stmtOk`. -/
def FunsOk (defs : Defs) (S : List ident) : Prop :=
  ∀ x, S.contains x = true → ∃ f, (x, .Gfun (.Internal f)) ∈ defs ∧ f.fn_vars = [] ∧
    SOk defs S f.fn_return f.fn_body

section

variable {X : ExtSem} {ge : genv} {defs : Defs} {S : List ident}

theorem grel_store (hge : GenvOk ge defs) {m m' : mem} {gv : ident → Option val} {x : ident}
    {ty : type} {init : List init_data} {b : block} {v : val} (hg : GRel ge defs m gv)
    (hd : (x, .Gvar ⟨ty, init, false, false⟩) ∈ defs) (hs : Genv.find_symbol ge x = some b)
    (hv : gval ty v) (hst : Mem.store Archi.aarch64 (chunkOf ty) m b 0 v = some m') :
    GRel ge defs m' (upd gv x v) := by
  obtain ⟨hva, rfl⟩ := Mem.store_inv hst
  intro y ty' init' b' hd' hsc' hs'
  by_cases e : y = x
  · subst e
    have hdd := mem_unique hge.nodup hd hd'
    injection hdd with hdd
    injection hdd with e1 e2
    subst e1 e2
    rw [hs] at hs'
    cases hs'
    refine ⟨v, by simp [upd], hv, ?_, (Mem.valid_access_stored _ _ _ _ _ _ _ _ _).mpr hva⟩
    cases hv with
    | gv_ui i => exact Mem.load_stored_int m b 0 i hva
    | gv_ul i => exact Mem.load_stored_long m b 0 i hva
  · obtain ⟨w, hw, hgw, hl, hvw⟩ := hg y ty' init' b' hd' hsc' hs'
    have hb : b ≠ b' := fun e' => e (hge.inj y x b' hs' (e' ▸ hs))
    refine ⟨w, by simp [upd, e, hw], hgw, ?_, (Mem.valid_access_stored _ _ _ _ _ _ _ _ _).mpr hvw⟩
    rw [Mem.load_stored_other _ _ _ _ _ _ _ _ hb]
    exact hl

theorem storev_zero {chunk : memory_chunk} {m m' : mem} {b : block} {v : val}
    (h : Mem.storev Archi.aarch64 chunk m (.Vptr b Ptrofs.zero) v = some m') :
    Mem.store Archi.aarch64 chunk m b 0 v = some m' := by
  have hz : Ptrofs.unsigned Ptrofs.zero = 0 := rfl
  simp only [Mem.storev, hz] at h
  split at h
  · exact h
  · cases h

theorem result_of {out : outcome} {ret : type} {v : val} {m : mem} (hr : RetOk ret out)
    (h : outcome_result_value Archi.aarch64 out ret v m) : result_ok out ret v ∧ NoPtrV v := by
  cases out with
  | Out_break => simp [outcome_result_value] at h
  | Out_continue => simp [outcome_result_value] at h
  | Out_normal =>
      cases ret <;> simp [outcome_result_value] at h
      subst h
      exact ⟨.rs_normal, fun _ _ e => by cases e⟩
  | Out_return r =>
      cases r with
      | none =>
          cases ret <;> simp [outcome_result_value] at h
          subst h
          exact ⟨.rs_none, fun _ _ e => by cases e⟩
      | some p =>
          obtain ⟨v', t'⟩ := p
          obtain ⟨hne, hc⟩ := h
          obtain ⟨hcf, _, pv⟩ := hr v' t' rfl
          have hco := cast_leaf hcf hc
          exact ⟨.rs_some v' t' ret v hne hco, cast_ok_noptr hco pv⟩

theorem entry_facts {f : function} {vargs : List val} {m : mem} {e : env} {le : temp_env}
    {m1 : mem} (h : function_entry2 f vargs m e le m1) :
    e = empty_env ∧ m1 = m ∧ (var_names f.fn_params).Nodup ∧
      (∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y) ∧
      bind_parameter_temps f.fn_params vargs (create_undef_temps f.fn_temps) = some le := by
  cases h with
  | intro _ _ hnd hdj hb => exact ⟨rfl, rfl, hnd, hdj, hb⟩

theorem blocks_empty : blocks_of_env Archi.aarch64 empty_env = [] := rfl

theorem fun_eta (f : function) (h : f.fn_vars = []) :
    f = ⟨f.fn_return, f.fn_callconv, f.fn_params, [], f.fn_temps, f.fn_body⟩ := by
  cases f
  simp_all

theorem ptrofs_zero : Ptrofs.zero = rptr 0 := rfl

mutual

theorem exec_to_n (hge : GenvOk ge defs) (hS : FunsOk defs S) {e : env} {le : temp_env}
    {m : mem} {s : statement} {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
    (h : exec_stmt Archi.aarch64 X ge e le m s t le' m' out) :
    ∀ {ret : type} {ln gv : ident → Option val}, e = empty_env → SOk defs S ret s →
      TempsRel le ln → NoPtr ln → GRel ge defs m gv →
      ∃ ln' gv', nexec defs ln gv s t ln' gv' out ∧ TempsRel le' ln' ∧ NoPtr ln' ∧
        GRel ge defs m' gv' ∧ RetOk ret out := by
  match h with
  | .exec_Sskip _ _ _ =>
      intro ret ln gv _ _ htr hp hg
      exact ⟨ln, gv, .nx_skip ln gv, htr, hp, hg, retOk_normal ret⟩
  | .exec_Sset _ _ _ x a v hv =>
      intro ret ln gv he hok htr hp hg
      subst he
      cases hok with
      | set _ _ ha =>
          obtain ⟨n, _, pv⟩ := eval_to_n htr hp hg ha hv
          exact ⟨upd ln x v, gv, .nx_set ln gv x a v _ n (upd_spec ln x v), temps_upd htr x v,
            noptr_upd hp x pv, hg, retOk_normal ret⟩
  | .exec_Sassign _ _ _ a1 a2 loc ofs bf v2 v m1 hl ha2 hc hasg =>
      intro ret ln gv he hok htr hp hg
      subst he
      cases hok with
      | store x ty _ hsty hdef ha hcf =>
          have hsc := scalar_of hsty
          obtain ⟨init, hd⟩ := scalarDef_mem hdef
          obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg ha ha2
          have hco := cast_leaf hcf hc
          have hgv := gval_of_cast hsc hco p2
          cases hl with
          | eval_Evar_local _ _ _ hle => simp [empty_env] at hle
          | eval_Evar_global _ b _ _ hs =>
              cases hasg with
              | assign_loc_value _ chunk _ hac hst =>
                  change access_mode _ ty = _ at hac
                  rw [access_scalar hsc] at hac
                  cases hac
                  exact ⟨ln, upd gv x v, .nx_store ln gv x ty init a2 _ v2 v _ (in_defs_of_mem hd)
                    hsc n2 t2 hco hgv (upd_spec gv x v), htr, hp,
                    grel_store hge hg hd hs hgv (storev_zero hst), retOk_normal ret⟩
  | .exec_Scall _ _ _ optid a al tyargs tyres cconv vf vargs fd t1 m1 vres hcls hvf hargs
      hfind hty hcall =>
      intro ret ln gv he hok htr hp hg
      subst he
      cases hok with
      | call _ x tys rty cc _ hxS hargsok =>
          simp only [typeof, classify_fun] at hcls
          injection hcls with e1 e2 e3
          subst e1 e2 e3
          cases hvf with
          | eval_Elvalue _ l ofs bf _ hl hdr =>
              cases hl with
              | eval_Evar_local _ _ _ hle => simp [empty_env] at hle
              | eval_Evar_global _ _ _ _ hs =>
                  cases hdr with
                  | deref_loc_value _ _ hac _ => cases hac
                  | deref_loc_reference _ =>
                      obtain ⟨f, hdf, hvars, hbody⟩ := hS x hxS
                      obtain ⟨b', hsb, hdb⟩ := hge.sym_def _ _ hdf
                      rw [hs] at hsb
                      cases hsb
                      have hfd : fd = .Internal f := by
                        simp only [Genv.find_funct, Genv.find_funct_ptr, hdb] at hfind
                        simp at hfind
                        exact hfind.symm
                      obtain ⟨nl, pl⟩ := evallist_to_n htr hp hg hargsok hargs
                      obtain ⟨ln0, ln1, ln2, gv2, out2, hu, hb, hnr, hdj, hx, hres, hg2, pres⟩ :=
                        call_to_n hge hS hcall hfd hvars hbody pl hg
                      rw [hfd] at hty
                      simp only [type_of_fundef, type_of_function] at hty
                      injection hty with e1 e2 e3
                      subst e1 e2 e3
                      obtain ⟨ln3, hso, htr3, hp3⟩ := set_opt_of optid htr hp pres
                      rw [fun_eta f hvars] at hdf
                      exact ⟨ln3, gv2, .nx_call ln gv optid x _ f.fn_return f.fn_callconv al vargs
                        f.fn_params f.fn_temps f.fn_body ln0 ln1 t1 ln2 gv2 out2 vres ln3
                        (in_defs_of_mem hdf) (params_types_of _) nl hnr hdj hu hb hx hres hso,
                        htr3, hp3, hg2, retOk_normal ret⟩
  | .exec_Sbuiltin _ _ _ optid ef al tyargs vargs t1 m1 vres hargs hext =>
      intro ret ln gv he hok htr hp hg
      subst he
      cases hok with
      | out x a hvol ha hcf =>
          obtain ⟨init, hd⟩ := volDef_mem hvol
          cases hargs with
          | eval_Econs _ _ _ _ w1 w1' _ ha1 hc1 hrest =>
              cases hrest with
              | eval_Econs _ _ _ _ w2 w2' _ ha2 hc2 hnil =>
                  cases hnil
                  obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg ha ha2
                  have hco := cast_leaf hcf hc2
                  obtain ⟨i, rfl⟩ := cast_vui hco
                  obtain ⟨b, hs, hdb⟩ := hge.sym_def _ _ hd
                  cases ha1 with
                  | eval_Elvalue _ _ _ _ _ hl _ => cases hl
                  | eval_Eaddrof _ _ l o hl =>
                      cases hl with
                      | eval_Evar_local _ _ _ hle => simp [empty_env] at hle
                      | eval_Evar_global _ _ _ _ hs1 =>
                          rw [hs] at hs1
                          cases hs1
                          have hw1 : some (val.Vptr b Ptrofs.zero) = some w1' := hc1
                          cases hw1
                          simp only [external_call] at hext
                          cases hext with
                          | volatile_store_sem_intro _ _ _ _ _ _ hvs =>
                              cases hvs with
                              | volatile_store_vol y ev _ _ hsy hev =>
                                  have hy := hge.inj y x b hsy hs
                                  subst hy
                                  cases hev
                                  refine ⟨ln, gv, ?_, htr, hp, hg, retOk_normal ret⟩
                                  rw [ptrofs_zero]
                                  exact .nx_out ln gv y init a _ w2 i (in_defs_of_mem hd) n2 t2 hco
                              | volatile_store_nonvol _ _ hnv _ =>
                                  simp [Genv.block_is_volatile, Genv.find_var_info, hdb] at hnv
  | .exec_Sseq_1 _ _ _ s1 s2 t1 le1 m1 t2 le2 m2 out h1 h2 =>
      intro ret ln gv he hok htr hp hg
      cases hok with
      | seq _ _ hok1 hok2 =>
          obtain ⟨ln1, gv1, n1, htr1, hp1, hg1, _⟩ := exec_to_n hge hS h1 he hok1 htr hp hg
          obtain ⟨ln2, gv2, n2, htr2, hp2, hg2, hr2⟩ := exec_to_n hge hS h2 he hok2 htr1 hp1 hg1
          exact ⟨ln2, gv2, .nx_seq1 ln gv s1 s2 t1 ln1 gv1 t2 ln2 gv2 out n1 n2, htr2, hp2, hg2,
            hr2⟩
  | .exec_Sseq_2 _ _ _ s1 s2 t1 le1 m1 out h1 hne =>
      intro ret ln gv he hok htr hp hg
      cases hok with
      | seq _ _ hok1 _ =>
          obtain ⟨ln1, gv1, n1, htr1, hp1, hg1, hr1⟩ := exec_to_n hge hS h1 he hok1 htr hp hg
          exact ⟨ln1, gv1, .nx_seq2 ln gv s1 s2 t1 ln1 gv1 out n1 hne, htr1, hp1, hg1, hr1⟩
  | .exec_Sifthenelse _ _ _ a s1 s2 v1 b t1 le1 m1 out hv hb hs =>
      intro ret ln gv he hok htr hp hg
      cases hok with
      | ite _ _ _ ha hty hok1 hok2 =>
          have hokb : SOk defs S ret (if b then s1 else s2) := by cases b <;> assumption
          obtain ⟨ln1, gv1, n1, htr1, hp1, hg1, hr1⟩ := exec_to_n hge hS hs he hokb htr hp hg
          subst he
          obtain ⟨na, ta, _⟩ := eval_to_n htr hp hg ha hv
          have hbo := bool_leaf hty hb
          refine ⟨ln1, gv1, ?_, htr1, hp1, hg1, hr1⟩
          cases b with
          | true => exact .nx_if_true ln gv a s1 s2 v1 _ t1 ln1 gv1 out na ta hbo n1
          | false => exact .nx_if_false ln gv a s1 s2 v1 _ t1 ln1 gv1 out na ta hbo n1
  | .exec_Sreturn_none _ _ _ =>
      intro ret ln gv _ _ htr hp hg
      exact ⟨ln, gv, .nx_return_none ln gv, htr, hp, hg, fun _ _ e => by cases e⟩
  | .exec_Sreturn_some _ _ _ a v hv =>
      intro ret ln gv he hok htr hp hg
      subst he
      cases hok with
      | ret_some _ ha hne hcf =>
          obtain ⟨na, ta, pv⟩ := eval_to_n htr hp hg ha hv
          refine ⟨ln, gv, .nx_return_some ln gv a v _ na ta, htr, hp, hg, ?_⟩
          intro w t' e
          injection e with e
          injection e with e
          injection e with e1 e2
          subst e1 e2
          exact ⟨hcf, hne, pv⟩
  | .exec_Sbreak _ _ _ =>
      intro ret ln gv _ _ htr hp hg
      exact ⟨ln, gv, .nx_break ln gv, htr, hp, hg, fun _ _ e => by cases e⟩
  | .exec_Scontinue _ _ _ =>
      intro ret ln gv _ _ htr hp hg
      exact ⟨ln, gv, .nx_continue ln gv, htr, hp, hg, fun _ _ e => by cases e⟩
  | .exec_Sloop_stop1 _ _ _ s1 s2 t1 le1 m1 out1 out h1 hbr =>
      intro ret ln gv he hok htr hp hg
      cases hok with
      | loop _ _ hok1 _ =>
          obtain ⟨ln1, gv1, n1, htr1, hp1, hg1, hr1⟩ := exec_to_n hge hS h1 he hok1 htr hp hg
          refine ⟨ln1, gv1, .nx_loop_stop1 ln gv s1 s2 t1 ln1 gv1 out1 out n1 ?_, htr1, hp1, hg1,
            ?_⟩
          · cases hbr with
            | Out_break_or_return_B => exact .inl ⟨rfl, rfl⟩
            | Out_break_or_return_R r => exact .inr ⟨r, rfl, rfl⟩
          · cases hbr with
            | Out_break_or_return_B => exact fun _ _ e => by cases e
            | Out_break_or_return_R r => exact hr1
  | .exec_Sloop_stop2 _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out h1 hnc h2 hbr =>
      intro ret ln gv he hok htr hp hg
      have hok' := hok
      cases hok with
      | loop _ _ hok1 hok2 =>
          obtain ⟨ln1, gv1, n1, htr1, hp1, hg1, _⟩ := exec_to_n hge hS h1 he hok1 htr hp hg
          obtain ⟨ln2, gv2, n2, htr2, hp2, hg2, hr2⟩ := exec_to_n hge hS h2 he hok2 htr1 hp1 hg1
          refine ⟨ln2, gv2, .nx_loop_stop2 ln gv s1 s2 t1 ln1 gv1 out1 t2 ln2 gv2 out2 out n1 ?_ n2
            ?_, htr2, hp2, hg2, ?_⟩
          · cases hnc with
            | Out_normal_or_continue_N => exact .inl rfl
            | Out_normal_or_continue_C => exact .inr rfl
          · cases hbr with
            | Out_break_or_return_B => exact .inl ⟨rfl, rfl⟩
            | Out_break_or_return_R r => exact .inr ⟨r, rfl, rfl⟩
          · cases hbr with
            | Out_break_or_return_B => exact fun _ _ e => by cases e
            | Out_break_or_return_R r => exact hr2
  | .exec_Sloop_loop _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out h1 hnc h2 h3 =>
      intro ret ln gv he hok htr hp hg
      have hok' := hok
      cases hok with
      | loop _ _ hok1 hok2 =>
          obtain ⟨ln1, gv1, n1, htr1, hp1, hg1, _⟩ := exec_to_n hge hS h1 he hok1 htr hp hg
          obtain ⟨ln2, gv2, n2, htr2, hp2, hg2, _⟩ := exec_to_n hge hS h2 he hok2 htr1 hp1 hg1
          obtain ⟨ln3, gv3, n3, htr3, hp3, hg3, hr3⟩ :=
            exec_to_n hge hS h3 he hok' htr2 hp2 hg2
          refine ⟨ln3, gv3, ?_, htr3, hp3, hg3, hr3⟩
          rw [List.append_assoc]
          refine .nx_loop ln gv s1 s2 t1 ln1 gv1 out1 t2 ln2 gv2 t3 ln3 gv3 out n1 ?_ n2 n3
          cases hnc with
          | Out_normal_or_continue_N => exact .inl rfl
          | Out_normal_or_continue_C => exact .inr rfl
termination_by structural h

theorem call_to_n (hge : GenvOk ge defs) (hS : FunsOk defs S) {m : mem} {fd : fundef function}
    {vargs : List val} {t : trace} {m' : mem} {vres : val}
    (h : eval_funcall Archi.aarch64 X ge m fd vargs t m' vres) :
    ∀ {f : function} {gv : ident → Option val}, fd = .Internal f → f.fn_vars = [] →
      SOk defs S f.fn_return f.fn_body → NoPtrs vargs → GRel ge defs m gv →
      ∃ ln0 ln1 ln2 gv2 out, undef_temps f.fn_temps ln0 ∧ bind_params f.fn_params vargs ln0 ln1 ∧
        norepet_names f.fn_params ∧ disjoint_names f.fn_params f.fn_temps ∧
        nexec defs ln1 gv f.fn_body t ln2 gv2 out ∧ result_ok out f.fn_return vres ∧
        GRel ge defs m' gv2 ∧ NoPtrV vres := by
  match h with
  | .eval_funcall_internal _ f _ _ e le1 le2 m1 m2 out _ m3 hentry hbody hres hfree =>
      intro f2 gv hfd _ hok hpv hg
      injection hfd with hfd
      subst hfd
      obtain ⟨he, hm, hnd, hdj, hbind⟩ := entry_facts hentry
      have hp1 : NoPtr fun y => le1[y]? := noptr_bind _ _ _ _ hbind hpv (noptr_undef _)
      obtain ⟨ln2, gv2, hx, _, _, hg2, hret⟩ :=
        exec_to_n hge hS hbody he hok (fun _ => rfl) hp1 (hm ▸ hg)
      obtain ⟨hres', pv⟩ := result_of hret hres
      subst he
      rw [blocks_empty] at hfree
      cases hfree
      exact ⟨_, _, ln2, gv2, out, undef_temps_of f.fn_temps,
        bind_params_of _ _ _ _ hbind, norepet_names_of hnd, disjoint_names_of hdj, hx, hres',
        hg2, pv⟩
  | .eval_funcall_external .. =>
      intro f gv hfd
      cases hfd
termination_by structural h

end

end

/-! ## Programs -/

theorem mem_of_in_defs {defs : Defs} {x : ident} {g : globdef (fundef function) type}
    (h : in_defs defs x g) : (x, g) ∈ defs := by
  induction h with
  | in_here => exact List.mem_cons_self
  | in_there d rest _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem lookup_of_mem {defs : Defs} (hn : (defs.map (·.1)).Nodup) {x : ident}
    {g : globdef (fundef function) type} (h : (x, g) ∈ defs) : defs.lookup x = some g := by
  induction defs with
  | nil => cases h
  | cons d rest ih =>
      obtain ⟨y, g'⟩ := d
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h with e | h
      · injection e with e1 e2
        subst e1 e2
        simp [List.lookup]
      · have hne : x ≠ y := fun e => hn.1 (e ▸ List.mem_map_of_mem (f := (·.1)) h)
        have hb : (x == y) = false := beq_false_of_ne hne
        simp [List.lookup, hb, ih hn.2 h]

/-- The initial value of a scalar global, from its initialization data. -/
def initVal (defs : Defs) (x : ident) : Option val :=
  match defs.lookup x with
  | some (.Gvar v) =>
      match v.gvar_init with
      | [.Init_int32 n] => some (.Vint n)
      | [.Init_int64 n] => some (.Vlong n)
      | _ => none
  | _ => none

theorem scalarTy_of {ty : type} (h : scalar ty) : scalarTy ty = true := by
  cases h <;> rfl

theorem varOk_scalar {ty : type} {init : List init_data}
    (h : varOk ⟨ty, init, false, false⟩ = true) (hsc : scalar ty) :
    (ty = tui ∧ ∃ n, init = [.Init_int32 n]) ∨ (ty = tul ∧ ∃ n, init = [.Init_int64 n]) := by
  have hs := scalarTy_of hsc
  unfold varOk at h
  split at h
  · simp_all
  · rename_i n heq
    simp only [Bool.not_false, Bool.true_and, beq_iff_eq] at h
    exact .inl ⟨h, n, heq⟩
  · rename_i n heq
    simp only [Bool.not_false, Bool.true_and, beq_iff_eq] at h
    exact .inr ⟨h, n, heq⟩
  · simp_all
  · simp at h

theorem varOk_init {v : globvar type} (h : varOk v = true) : init_ok v.gvar_init := by
  unfold varOk at h
  split at h
  · rename_i heq
    rw [heq]
    exact .io_nil
  · rename_i n heq
    rw [heq]
    exact .io_int32 n
  · rename_i n heq
    rw [heq]
    exact .io_int64 n
  · rename_i n heq
    rw [heq]
    exact .io_space n
  · simp at h

theorem defOk_shape {g : globdef (fundef function) type} (h : defOk g = true) :
    Genv.InitShapeW g := by
  cases g with
  | Gfun _ => exact .inl trivial
  | Gvar v =>
      simp only [defOk] at h
      unfold varOk at h
      split at h
      · rename_i heq
        exact .inr ⟨v, rfl, heq⟩
      · rename_i n heq
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        exact .inl ⟨h.1.1, h.1.2, .inl ⟨n, heq⟩⟩
      · rename_i n heq
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        exact .inl ⟨h.1.1, h.1.2, .inr (.inl ⟨n, heq⟩)⟩
      · rename_i n heq
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
        refine .inl ⟨h.1.1.1, h.1.1.2, .inr (.inr ⟨n.toNat, ?_⟩)⟩
        rw [heq, Int.toNat_of_nonneg h.1.2]
      · simp at h

theorem funOk_spec {defs : Defs} {S : List ident} {x : ident} (h : funOk defs S x = true) :
    ∃ f, (x, .Gfun (.Internal f)) ∈ defs ∧ f.fn_vars = [] ∧ SOk defs S f.fn_return f.fn_body := by
  obtain ⟨⟨y, g⟩, hd, hs⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨rfl, hs⟩ := hs
  match g, hd, hs with
  | .Gfun (.Internal f), hd, hs =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hs
      exact ⟨f, hd, hs.1, sok_of _ hs.2⟩
  | .Gfun (.External ..), _, hs => simp at hs
  | .Gvar _, _, hs => simp at hs

/-- The initial memory of a program whose definitions `progOk` accepts holds the initial values
of its scalar globals. -/
theorem grel_init {p : program function} {m0 : mem} (hn : (p.prog_defs.map (·.1)).Nodup)
    (hdefs : ∀ d ∈ p.prog_defs, defOk d.2 = true) (h : init_mem Archi.aarch64 p = some m0) :
    GRel (globalenv p) p.prog_defs m0 (initVal p.prog_defs) := by
  obtain ⟨m', ha, _, _, hf⟩ := Genv.alloc_globals_spec_w (A := Archi.aarch64) (globalenv p)
    p.prog_defs Mem.empty (fun g hg => defOk_shape (hdefs g hg))
  have : m0 = m' := by
    simp only [init_mem] at h
    rw [ha] at h
    cases h
    rfl
  subst this
  intro x ty init b hd hsc hs
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hd
  have hsk := (Genv.find_add_globals_idx (Genv.empty_genv p.prog_public) p.prog_defs hn k hk).1
  rw [e] at hsk
  simp only [globalenv] at hs
  rw [hsk] at hs
  cases hs
  have hif := hf k hk ⟨ty, init, false, false⟩ (by rw [e])
  have hok := hdefs _ hd
  simp only [defOk] at hok
  have hlk := lookup_of_mem hn hd
  rcases varOk_scalar hok hsc with ⟨rfl, n, rfl⟩ | ⟨rfl, n, rfl⟩
  · obtain ⟨hl, hv⟩ := hif.1 n rfl
    exact ⟨.Vint n, by simp [initVal, hlk], .gv_ui n, hl, hv⟩
  · obtain ⟨hl, hv⟩ := hif.2.1 n rfl
    exact ⟨.Vlong n, by simp [initVal, hlk], .gv_ul n, hl, hv⟩

/-- The copy's execution of a program whose definitions, `main`, and functions `S` `progOk`
accepts is an execution of N. -/
theorem program_to_n {X : ExtSem} {p : program function} {t : trace} {r : int} (S : List ident)
    (hok : progOk p.prog_defs p.prog_main S = true)
    (h : bigstep_program_terminates Archi.aarch64 X p t r) : nprog p.prog_defs p.prog_main t r := by
  obtain ⟨b, fd, m0, m1, t, r, hinit, hs, hf, hty, hcall⟩ := h
  simp only [progOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hnd, hdefs⟩, hmain⟩, hfuns⟩ := hok
  have hge := genvOk_globalenv p hnd
  have hS : FunsOk p.prog_defs S := fun x hx => funOk_spec (hfuns x (List.contains_iff_mem.mp hx))
  obtain ⟨f, hdf, hvars, hbody⟩ := hS _ hmain
  obtain ⟨b', hsb, hdb⟩ := hge.sym_def _ _ hdf
  rw [hs] at hsb
  cases hsb
  have hfd : fd = .Internal f := by
    simp only [Genv.find_funct_ptr, hdb] at hf
    simp at hf
    exact hf.symm
  obtain ⟨ln0, ln1, ln2, gv2, out, hu, hb, _, _, hx, hres, _, _⟩ :=
    call_to_n hge hS hcall hfd hvars hbody (fun _ h => by cases h)
      (grel_init hnd hdefs hinit)
  rw [hfd] at hty
  simp only [type_of_fundef, type_of_function] at hty
  injection hty with hpar hret hcc
  have hpn : f.fn_params = [] := by
    cases h' : f.fn_params with
    | nil => rfl
    | cons _ _ => simp [h', type_of_params] at hpar
  rw [hpn] at hb
  cases hb
  rw [hret] at hres
  rw [fun_eta f hvars, hpn, hret, hcc] at hdf
  refine .np_intro p.prog_defs p.prog_main f.fn_temps f.fn_body (initVal p.prog_defs) ln0 t ln2
    gv2 out r (norepet_defs_of hnd) ?_ ?_ (in_defs_of_mem hdf) hu hx hres
  · intro x ty init ro vol hd
    exact varOk_init (v := ⟨ty, init, ro, vol⟩) (hdefs _ (mem_of_in_defs hd))
  · intro x ty init hd hsc
    have hd := mem_of_in_defs hd
    have hlk := lookup_of_mem hnd hd
    rcases varOk_scalar (hdefs _ hd) hsc with ⟨rfl, n, rfl⟩ | ⟨rfl, n, rfl⟩
    · exact ⟨.Vint n, .gi_ui n, by simp [initVal, hlk]⟩
    · exact ⟨.Vlong n, .gi_ul n, by simp [initVal, hlk]⟩

end ClightN.Proof
