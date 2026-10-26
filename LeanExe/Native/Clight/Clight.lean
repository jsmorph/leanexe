import LeanExe.Native.Clight.Cop
import LeanExe.Native.Clight.Events

/-!
The syntax of Clight and the evaluation of its expressions, from CompCert 3.18's
`cfrontend/Clight.v`.  The syntax is complete.  The semantics is that of `step2`, in which
function parameters are temporaries, the form `clightgen` produces.

The copy omits these rules of `Clight.v`, so the constructs they cover have no outcome:
`eval_Esizeof`, `eval_Ealignof`, `eval_Efield_struct`, `eval_Efield_union`, `deref_loc_copy`,
`deref_loc_bitfield`, `assign_loc_copy`, and `assign_loc_bitfield`.  `function_entry2` admits a
function only when it declares no local variable in memory (`fn_vars = []`), so the local
environment is always empty and `alloc_variables` and the frees at return do nothing.
-/

namespace LClight

inductive expr where
  | Econst_int (i : int) (ty : type)
  | Econst_float (f : float) (ty : type)
  | Econst_single (f : float32) (ty : type)
  | Econst_long (i : int64) (ty : type)
  | Evar (id : ident) (ty : type)
  | Etempvar (id : ident) (ty : type)
  | Ederef (a : expr) (ty : type)
  | Eaddrof (a : expr) (ty : type)
  | Eunop (op : unary_operation) (a : expr) (ty : type)
  | Ebinop (op : binary_operation) (a1 a2 : expr) (ty : type)
  | Ecast (a : expr) (ty : type)
  | Efield (a : expr) (f : ident) (ty : type)
  | Esizeof (ty1 ty : type)
  | Ealignof (ty1 ty : type)
  deriving Repr, Inhabited

def typeof : expr → type
  | .Econst_int _ ty => ty
  | .Econst_float _ ty => ty
  | .Econst_single _ ty => ty
  | .Econst_long _ ty => ty
  | .Evar _ ty => ty
  | .Etempvar _ ty => ty
  | .Ederef _ ty => ty
  | .Eaddrof _ ty => ty
  | .Eunop _ _ ty => ty
  | .Ebinop _ _ _ ty => ty
  | .Ecast _ ty => ty
  | .Efield _ _ ty => ty
  | .Esizeof _ ty => ty
  | .Ealignof _ ty => ty

abbrev label := ident

mutual
  inductive statement where
    | Sskip
    | Sassign (a1 a2 : expr)
    | Sset (id : ident) (a : expr)
    | Scall (optid : Option ident) (a : expr) (al : List expr)
    | Sbuiltin (optid : Option ident) (ef : external_function) (tyargs : List type)
        (al : List expr)
    | Ssequence (s1 s2 : statement)
    | Sifthenelse (a : expr) (s1 s2 : statement)
    | Sloop (s1 s2 : statement)
    | Sbreak
    | Scontinue
    | Sreturn (a : Option expr)
    | Sswitch (a : expr) (sl : labeled_statements)
    | Slabel (lbl : label) (s : statement)
    | Sgoto (lbl : label)

  inductive labeled_statements where
    | LSnil
    | LScons (c : Option _root_.Int) (s : statement) (sl : labeled_statements)
end

structure function where
  fn_return : type
  fn_callconv : calling_convention
  fn_params : List (ident × type)
  fn_vars : List (ident × type)
  fn_temps : List (ident × type)
  fn_body : statement

def type_of_function (f : function) : type :=
  .Tfunction (type_of_params f.fn_params) f.fn_return f.fn_callconv

def type_of_fundef : fundef function → type
  | .Internal fd => type_of_function fd
  | .External _ args res cc => .Tfunction args res cc

/-- `Clight.genv` without its composite environment, which is empty. -/
abbrev genv := Genv.t (fundef function) type

def globalenv (p : program function) : genv :=
  Genv.add_globals (Genv.empty_genv p.prog_public) p.prog_defs

/-- `Genv.init_mem`. -/
def init_mem (p : program function) : Option mem :=
  Genv.alloc_globals (globalenv p) Mem.empty p.prog_defs

abbrev env := Std.TreeMap ident (block × type)

def empty_env : env := ∅

abbrev temp_env := Std.TreeMap ident val

/-- `deref_loc` without the copy and bit-field cases. -/
inductive deref_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs) : bitfield → val → Prop
  | deref_loc_value (chunk : memory_chunk) (v : val) :
      access_mode ty = .By_value chunk →
      Mem.loadv chunk m (.Vptr b ofs) = some v →
      deref_loc ty m b ofs .Full v
  | deref_loc_reference :
      access_mode ty = .By_reference →
      deref_loc ty m b ofs .Full (.Vptr b ofs)

/-- `assign_loc` without the copy and bit-field cases. -/
inductive assign_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs) :
    bitfield → val → mem → Prop
  | assign_loc_value (v : val) (chunk : memory_chunk) (m' : mem) :
      access_mode ty = .By_value chunk →
      Mem.storev chunk m (.Vptr b ofs) v = some m' →
      assign_loc ty m b ofs .Full v m'

def var_names (vars : List (ident × type)) : List ident := vars.map (·.1)

def create_undef_temps : List (ident × type) → temp_env
  | [] => ∅
  | (id, _) :: temps' => (create_undef_temps temps').insert id .Vundef

def bind_parameter_temps : List (ident × type) → List val → temp_env → Option temp_env
  | [], [], le => some le
  | (id, _) :: xl, v :: vl, le => bind_parameter_temps xl vl (le.insert id v)
  | _, _, _ => none

def block_of_binding (id_b_ty : ident × (block × type)) : block × _root_.Int × _root_.Int :=
  (id_b_ty.2.1, 0, sizeof id_b_ty.2.2)

def blocks_of_env (e : env) : List (block × _root_.Int × _root_.Int) :=
  e.toList.map block_of_binding

def set_opttemp (optid : Option ident) (v : val) (le : temp_env) : temp_env :=
  match optid with
  | none => le
  | some id => le.insert id v

mutual
  inductive eval_expr (A : Archi) (ge : genv) (e : env) (le : temp_env) (m : mem) :
      expr → val → Prop
    | eval_Econst_int (i : int) (ty : type) :
        eval_expr A ge e le m (.Econst_int i ty) (.Vint i)
    | eval_Econst_float (f : float) (ty : type) :
        eval_expr A ge e le m (.Econst_float f ty) (.Vfloat f)
    | eval_Econst_single (f : float32) (ty : type) :
        eval_expr A ge e le m (.Econst_single f ty) (.Vsingle f)
    | eval_Econst_long (i : int64) (ty : type) :
        eval_expr A ge e le m (.Econst_long i ty) (.Vlong i)
    | eval_Etempvar (id : ident) (ty : type) (v : val) :
        le[id]? = some v →
        eval_expr A ge e le m (.Etempvar id ty) v
    | eval_Eaddrof (a : expr) (ty : type) (loc : block) (ofs : ptrofs) :
        eval_lvalue A ge e le m a loc ofs .Full →
        eval_expr A ge e le m (.Eaddrof a ty) (.Vptr loc ofs)
    | eval_Eunop (op : unary_operation) (a : expr) (ty : type) (v1 v : val) :
        eval_expr A ge e le m a v1 →
        sem_unary_operation op v1 (typeof a) m = some v →
        eval_expr A ge e le m (.Eunop op a ty) v
    | eval_Ebinop (op : binary_operation) (a1 a2 : expr) (ty : type) (v1 v2 v : val) :
        eval_expr A ge e le m a1 v1 →
        eval_expr A ge e le m a2 v2 →
        sem_binary_operation A op v1 (typeof a1) v2 (typeof a2) m = some v →
        eval_expr A ge e le m (.Ebinop op a1 a2 ty) v
    | eval_Ecast (a : expr) (ty : type) (v1 v : val) :
        eval_expr A ge e le m a v1 →
        sem_cast v1 (typeof a) ty m = some v →
        eval_expr A ge e le m (.Ecast a ty) v
    | eval_Elvalue (a : expr) (loc : block) (ofs : ptrofs) (bf : bitfield) (v : val) :
        eval_lvalue A ge e le m a loc ofs bf →
        deref_loc (typeof a) m loc ofs bf v →
        eval_expr A ge e le m a v

  inductive eval_lvalue (A : Archi) (ge : genv) (e : env) (le : temp_env) (m : mem) :
      expr → block → ptrofs → bitfield → Prop
    | eval_Evar_local (id : ident) (l : block) (ty : type) :
        e[id]? = some (l, ty) →
        eval_lvalue A ge e le m (.Evar id ty) l Ptrofs.zero .Full
    | eval_Evar_global (id : ident) (l : block) (ty : type) :
        e[id]? = none →
        Genv.find_symbol ge id = some l →
        eval_lvalue A ge e le m (.Evar id ty) l Ptrofs.zero .Full
    | eval_Ederef (a : expr) (ty : type) (l : block) (ofs : ptrofs) :
        eval_expr A ge e le m a (.Vptr l ofs) →
        eval_lvalue A ge e le m (.Ederef a ty) l ofs .Full
end

inductive eval_exprlist (A : Archi) (ge : genv) (e : env) (le : temp_env) (m : mem) :
    List expr → List type → List val → Prop
  | eval_Enil : eval_exprlist A ge e le m [] [] []
  | eval_Econs (a : expr) (bl : List expr) (ty : type) (tyl : List type) (v1 v2 : val)
      (vl : List val) :
      eval_expr A ge e le m a v1 →
      sem_cast v1 (typeof a) ty m = some v2 →
      eval_exprlist A ge e le m bl tyl vl →
      eval_exprlist A ge e le m (a :: bl) (ty :: tyl) (v2 :: vl)

/-- `function_entry2` for a function without local variables in memory: CompCert's
`list_norepet` of the empty `fn_vars` holds, and `alloc_variables` leaves the empty environment
and the memory unchanged. -/
inductive function_entry2 (f : function) (vargs : List val) (m : mem) :
    env → temp_env → mem → Prop
  | intro (le : temp_env) :
      f.fn_vars = [] →
      (var_names f.fn_params).Nodup →
      (∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y) →
      bind_parameter_temps f.fn_params vargs (create_undef_temps f.fn_temps) = some le →
      function_entry2 f vargs m empty_env le m

end LClight
