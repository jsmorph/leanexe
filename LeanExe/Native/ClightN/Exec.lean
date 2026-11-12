import LeanExe.Native.ClightN.Arrays
import LeanExe.Native.Proof.Reacts

/-!
The executions of the Lean copy of Clight are executions of N (`clightn/N.nsx`), for the
programs that the translator's forms make up.  `progOk` decides, for a program's definitions, its
`main`, and a list `S` of functions that contains `main` and the functions they call, that the
bodies of those functions use only the forms that N's relations cover: the leaf operators, unary
operators, and casts, temporaries, constants, the scalar globals, the words, bytes, and cells of
the arrays, calls of functions of `S` and of `__builtin_fsqrt`, the volatile store to a global of
type `volatile unsigned int`, the volatile loads from and stores to the elements of volatile
arrays, and the statements of the translation.  It also decides the conditions that N's
judgments of whole programs place on the definitions.  `program_to_n` carries the copy's
`bigstep_program_terminates` at `Archi.aarch64` to `nprog`, and `reacts_to_n` carries
`LoopReacts` to `nreacts`.

The proof follows the copy's derivation.  It relates the copy's temporaries to N's by
`TempsRel`, its memory to N's scalar globals by `GRel` and to the bytes of N's arrays by `MRel`,
and carries the invariants that no temporary holds a pointer (`NoPtr`), that a `return` gives a
value of a leaf cast to the function's result type (`RetOk`), and that each array's block has
permissions only within its bytes (`ArrHolds.exact`), which bounds the offset of every access
that succeeds.  Rocq proves in `clightn/rocq/NExec.v` that each derivation of N is one of
CompCert's.
-/

namespace ClightN.Proof

open LClight ClightN.Base ClightN.Spec
open LeanExe.Native (sqrtSig sqrtFun)

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
   (.Ogt, tui, tui), (.Oge, tui, tui),
   (.Oadd, tdbl, tdbl), (.Osub, tdbl, tdbl), (.Omul, tdbl, tdbl), (.Odiv, tdbl, tdbl),
   (.Oeq, tdbl, tdbl), (.One, tdbl, tdbl), (.Olt, tdbl, tdbl), (.Ole, tdbl, tdbl),
   (.Oge, tdbl, tdbl), (.Oadd, tflt, tflt), (.Osub, tflt, tflt), (.Omul, tflt, tflt),
   (.Odiv, tflt, tflt), (.Oeq, tflt, tflt), (.One, tflt, tflt), (.Olt, tflt, tflt),
   (.Ole, tflt, tflt), (.Oge, tflt, tflt)]

/-- The cast forms of `cast_ok`. -/
def castForms : List (type × type) :=
  [(tsi, tui), (tui, tsi), (tul, tui), (tui, tul), (tul, tsl), (tsl, tul), (tuc, tul),
   (tuc, tui), (tul, tuc), (tui, tuc), (tvuc, tul), (tvui, tul), (tui, tvui), (tul, tul),
   (tui, tui), (tuc, tuc), (tsi, tsi), (tdbl, tdbl), (tflt, tflt), (tul, tdbl), (tdbl, tul),
   (tflt, tdbl), (tdbl, tflt), (tsi, tflt), (tui, tflt), (tul, tflt), (tflt, tsi), (tflt, tul)]

/-- The unary operator forms of `unop_ok`. -/
def unopForms : List (unary_operation × type) :=
  [(.Oneg, tdbl), (.Oabsfloat, tdbl), (.Oneg, tflt)]

theorem binop_leaf {op : binary_operation} {t1 t2 : type} {v1 v2 v : val} {m : mem}
    (hf : (op, t1, t2) ∈ binForms)
    (h : sem_binary_operation Archi.aarch64 op v1 t1 v2 t2 m = some v) :
    binop_ok op t1 t2 v1 v2 v := by
  simp only [binForms, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
  · exact (add_d_d () v1 v2 v m).1 h
  · exact (sub_d_d () v1 v2 v m).1 h
  · exact (mul_d_d () v1 v2 v m).1 h
  · exact (div_d_d () v1 v2 v m).1 h
  · exact (eq_d_d () v1 v2 v m).1 h
  · exact (ne_d_d () v1 v2 v m).1 h
  · exact (lt_d_d () v1 v2 v m).1 h
  · exact (le_d_d () v1 v2 v m).1 h
  · exact (ge_d_d () v1 v2 v m).1 h
  · exact (add_f_f () v1 v2 v m).1 h
  · exact (sub_f_f () v1 v2 v m).1 h
  · exact (mul_f_f () v1 v2 v m).1 h
  · exact (div_f_f () v1 v2 v m).1 h
  · exact (eq_f_f () v1 v2 v m).1 h
  · exact (ne_f_f () v1 v2 v m).1 h
  · exact (lt_f_f () v1 v2 v m).1 h
  · exact (le_f_f () v1 v2 v m).1 h
  · exact (ge_f_f () v1 v2 v m).1 h

theorem cast_leaf {t1 t2 : type} {v1 v : val} {m : mem} (hf : (t1, t2) ∈ castForms)
    (h : sem_cast Archi.aarch64 v1 t1 t2 m = some v) : cast_ok t1 t2 v1 v := by
  simp only [castForms, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
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
  · exact (cast_d_d v1 v m).1 h
  · exact (cast_f_f v1 v m).1 h
  · exact (cast_ul_d v1 v m).1 h
  · exact (cast_d_ul v1 v m).1 h
  · exact (cast_f_d v1 v m).1 h
  · exact (cast_d_f v1 v m).1 h
  · exact (cast_si_f v1 v m).1 h
  · exact (cast_ui_f v1 v m).1 h
  · exact (cast_ul_f v1 v m).1 h
  · exact (cast_f_si v1 v m).1 h
  · exact (cast_f_ul v1 v m).1 h

theorem unop_leaf {op : unary_operation} {t : type} {v1 v : val} {m : mem}
    (hf : (op, t) ∈ unopForms) (h : sem_unary_operation Archi.aarch64 op v1 t m = some v) :
    unop_ok op t v1 v := by
  simp only [unopForms, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (neg_d v1 v m).1 h
  · exact (abs_d v1 v m).1 h
  · exact (neg_f v1 v m).1 h

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

theorem unop_ok_noptr {op : unary_operation} {t : type} {v1 v : val} (h : unop_ok op t v1 v) :
    NoPtrV v := by
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

def scalarTy (t : type) : Bool := t == tui || t == tul || t == tdbl || t == tflt

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

abbrev noattrL : attr := attr.mk false none
abbrev tarrL (n : Int) : type := .Tarray tul n noattrL
abbrev ptul : type := .Tpointer tul noattrL
abbrev ptuc : type := .Tpointer tuc noattrL

/-- The definition `d` of `x` is an array of `n` words, writable and not volatile, initialized by
one `Init_space` of its `8 n` bytes. -/
def arrDef (x : ident) (n : Int) (d : ident × globdef (fundef function) type) : Bool :=
  d.1 == x && match d.2 with
    | .Gvar v => v.gvar_info == tarrL n && v.gvar_init == [.Init_space (8 * n)] &&
        !v.gvar_readonly && !v.gvar_volatile
    | .Gfun _ => false

/-- The definition `d` of `x` is a writable, volatile array of `n` elements of type `ty`. -/
def volArr (x : ident) (ty : type) (n : Int) (d : ident × globdef (fundef function) type) :
    Bool :=
  d.1 == x && match d.2 with
    | .Gvar v => v.gvar_info == .Tarray ty n noattrL && !v.gvar_readonly && v.gvar_volatile
    | .Gfun _ => false

/-- The base of an access to a word or a byte of an array: `x` of a word, of pointer type `pt`
and element type `ty`, and `(unsigned char *) x` of a byte. -/
def baseOk (defs : Defs) : expr → type → type → Bool
  | .Evar x (.Tarray t n a), pt, ty =>
      t == tul && a == noattrL && pt == ptul && ty == tul && defs.any (arrDef x n)
  | .Ecast (.Evar x (.Tarray t n a)) ct, pt, ty =>
      t == tul && a == noattrL && ct == ptuc && pt == ptuc && ty == tuc && defs.any (arrDef x n)
  | _, _, _ => false

/-- The array of a cell `*(ty *) x` of type `unsigned long long`, `unsigned int`, `double`, or
`float`. -/
def cellOk (defs : Defs) : expr → type → type → Bool
  | .Evar x (.Tarray t n a), pt, ty =>
      t == tul && a == noattrL && pt == .Tpointer ty noattrL &&
        (ty == tul || ty == tui || ty == tdbl || ty == tflt) && decide (1 ≤ n) &&
        defs.any (arrDef x n)
  | _, _, _ => false

def exprOk (defs : Defs) : expr → Bool
  | .Econst_int _ _ | .Econst_long _ _ | .Econst_float _ _ | .Econst_single _ _
  | .Etempvar _ _ => true
  | .Evar x ty => scalarTy ty && defs.any (scalarDef x ty)
  | .Ebinop op a1 a2 _ =>
      exprOk defs a1 && exprOk defs a2 && decide ((op, typeof a1, typeof a2) ∈ binForms)
  | .Ecast a ty => exprOk defs a && decide ((typeof a, ty) ∈ castForms)
  | .Ederef (.Ebinop op b i pt) ty =>
      op == .Oadd && exprOk defs i && typeof i == tul && baseOk defs b pt ty
  | .Ederef (.Ecast c pt) ty => cellOk defs c pt ty
  | .Eunop op a _ => exprOk defs a && decide ((op, typeof a) ∈ unopForms)
  | _ => false

def argsOk (defs : Defs) : List expr → List type → Bool
  | [], [] => true
  | a :: al, ty :: tys =>
      exprOk defs a && decide ((typeof a, ty) ∈ castForms) && argsOk defs al tys
  | _, _ => false

def ptrVui : type := .Tpointer tvui (attr.mk false none)

/-- The definition `d` of `x` is the built-in `__builtin_fsqrt` of type `double (double)`. -/
def sqrtDefOf (x : ident) (d : ident × globdef (fundef function) type) : Bool :=
  d.1 == x && match d.2 with
    | .Gfun (.External (.EF_builtin name sg) targs tres cc) =>
        name == "__builtin_fsqrt" && sg == sqrtSig && targs == [tdbl] && tres == tdbl &&
          cc == cc_default
    | _ => false

/-- The left side `lhs` of an assignment of `a`: a scalar global, a word or a byte of an array,
or a cell. -/
def assignOk (defs : Defs) : expr → expr → Bool
  | .Evar x ty, a =>
      scalarTy ty && defs.any (scalarDef x ty) && exprOk defs a &&
        decide ((typeof a, ty) ∈ castForms)
  | .Ederef (.Ebinop op b i pt) ty, a =>
      op == .Oadd && exprOk defs i && typeof i == tul && baseOk defs b pt ty && exprOk defs a &&
        decide ((typeof a, ty) ∈ castForms)
  | .Ederef (.Ecast c pt) ty, a =>
      cellOk defs c pt ty && exprOk defs a && decide ((typeof a, ty) ∈ castForms)
  | _, _ => false

/-- The chunk of a volatile load from an element of type `ty`. -/
def vchunk : memory_chunk → type → Bool
  | .Mint8unsigned, ty => ty == tvuc
  | .Mint32, ty => ty == tvui
  | _, _ => false

/-- The volatile accesses of the bare-metal `main`: the store to `lx_out`, the store to and the
load from an element of a volatile array. -/
def builtinOk (defs : Defs) : Option ident → external_function → List type → List expr → Bool
  | none, .EF_vstore .Mint32, [p1, p2], [.Eaddrof (.Evar x t1) p3, a] =>
      p1 == ptrVui && p2 == tvui && t1 == tvui && p3 == ptrVui && defs.any (volDef x) &&
        exprOk defs a && decide ((typeof a, tvui) ∈ castForms)
  | none, .EF_vstore .Mint32, [p1, p2],
      [.Eaddrof (.Ederef (.Ebinop op (.Evar x (.Tarray t n aa)) i p4) t2) p3, a] =>
      op == .Oadd && p1 == ptrVui && p2 == tvui && t == tvui && aa == noattrL && p4 == ptrVui &&
        t2 == tvui && p3 == ptrVui && defs.any (volArr x tvui n) && exprOk defs i &&
        typeof i == tul && exprOk defs a && decide ((typeof a, tvui) ∈ castForms)
  | some _, .EF_vload ch, [p1],
      [.Eaddrof (.Ederef (.Ebinop op (.Evar x (.Tarray t n aa)) i p2) t2) p3] =>
      op == .Oadd && vchunk ch t && aa == noattrL && p1 == .Tpointer t noattrL && p2 == p1 &&
        t2 == t && p3 == p1 && defs.any (volArr x t n) && exprOk defs i && typeof i == tul
  | _, _, _, _ => false

def stmtOk (defs : Defs) (S : List ident) (ret : type) : statement → Bool
  | .Sskip | .Sbreak | .Scontinue | .Sreturn none => true
  | .Sset _ a => exprOk defs a
  | .Sassign lhs a => assignOk defs lhs a
  | .Scall _ (.Evar x (.Tfunction tys rty cc)) al =>
      (S.contains x || (tys == [tdbl] && rty == tdbl && cc == cc_default &&
        defs.any (sqrtDefOf x))) && argsOk defs al tys
  | .Sbuiltin optid ef tys al => builtinOk defs optid ef tys al
  | .Ssequence s1 s2 => stmtOk defs S ret s1 && stmtOk defs S ret s2
  | .Sloop s1 s2 => stmtOk defs S ret s1 && stmtOk defs S ret s2
  | .Sifthenelse a s1 s2 =>
      exprOk defs a && (typeof a == tsi || typeof a == tui) && stmtOk defs S ret s1 &&
        stmtOk defs S ret s2
  | .Sreturn (some a) => exprOk defs a && ret != .Tvoid && decide ((typeof a, ret) ∈ castForms)
  | _ => false

/-- The variables whose initialization data N accepts: a scalar global is initialized by one
datum of its type, or one `Init_space` of its size for a `double` or a `float`, and another
variable has none or one `Init_space` of a size not negative. -/
def varOk (v : globvar type) : Bool :=
  match v.gvar_init with
  | [] => !(scalarTy v.gvar_info && !v.gvar_readonly && !v.gvar_volatile)
  | [.Init_int32 _] => !v.gvar_readonly && !v.gvar_volatile && v.gvar_info == tui
  | [.Init_int64 _] => !v.gvar_readonly && !v.gvar_volatile && v.gvar_info == tul
  | [.Init_space n] =>
      !v.gvar_readonly && !v.gvar_volatile && decide (0 ≤ n) &&
        (!scalarTy v.gvar_info || (v.gvar_info == tdbl && n == 8) ||
          (v.gvar_info == tflt && n == 4))
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

/-- The internal functions of `defs`, a list of functions that `progOk` can take for every
program whose functions use only N's forms. -/
def internals (defs : Defs) : List ident :=
  defs.filterMap fun d => match d.2 with
    | .Gfun (.Internal _) => some d.1
    | _ => none

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

def chunkOf (ty : type) : memory_chunk :=
  if ty = tui then .Mint32 else if ty = tdbl then .Mfloat64 else if ty = tflt then .Mfloat32
  else .Mint64

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
  rcases h with ((rfl | rfl) | rfl) | rfl
  · exact .sc_ui
  · exact .sc_ul
  · exact .sc_d
  · exact .sc_f

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


/-! ## Arrays and volatile arrays -/

/-- The memory `m` holds the bytes `mb` of the arrays of `defs`. -/
def MRel (ge : genv) (defs : Defs) (m : mem) (mb : ident → Int → Int) : Prop :=
  ∀ x n b, (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs →
    Genv.find_symbol ge x = some b → ArrHolds m b (8 * n) (mb x)

theorem arrDef_mem {defs : Defs} {x : ident} {n : Int} (h : defs.any (arrDef x n) = true) :
    (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs := by
  obtain ⟨⟨y, g⟩, hd, hs⟩ := List.any_eq_true.mp h
  simp only [arrDef, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨rfl, hs⟩ := hs
  cases g with
  | Gfun _ => simp at hs
  | Gvar v =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
      obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := hs
      obtain ⟨info, init, ro, vol⟩ := v
      simp only at e1 e2 e3 e4
      subst e1 e2 e3 e4
      exact hd

theorem volArr_mem {defs : Defs} {x : ident} {ty : type} {n : Int}
    (h : defs.any (volArr x ty n) = true) :
    ∃ init, (x, .Gvar ⟨.Tarray ty n noattrL, init, false, true⟩) ∈ defs := by
  obtain ⟨⟨y, g⟩, hd, hs⟩ := List.any_eq_true.mp h
  simp only [volArr, Bool.and_eq_true, beq_iff_eq] at hs
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

theorem baseOk_spec {defs : Defs} {b : expr} {pt ty : type} (h : baseOk defs b pt ty = true) :
    ∃ x n, (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs ∧
      ((b = .Evar x (tarrL n) ∧ pt = ptul ∧ ty = tul) ∨
        (b = .Ecast (.Evar x (tarrL n)) ptuc ∧ pt = ptuc ∧ ty = tuc)) := by
  cases b with
  | Evar x t =>
      cases t with
      | Tarray t n a =>
          simp only [baseOk, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
          obtain ⟨rfl, rfl, rfl, rfl, hd⟩ := h
          exact ⟨x, n, arrDef_mem hd, .inl ⟨rfl, rfl, rfl⟩⟩
      | _ => simp [baseOk] at h
  | Ecast c ct =>
      cases c with
      | Evar x t =>
          cases t with
          | Tarray t n a =>
              simp only [baseOk, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl, hd⟩ := h
              exact ⟨x, n, arrDef_mem hd, .inr ⟨rfl, rfl, rfl⟩⟩
          | _ => simp [baseOk] at h
      | _ => simp [baseOk] at h
  | _ => simp [baseOk] at h

theorem cellOk_spec {defs : Defs} {c : expr} {pt ty : type} (h : cellOk defs c pt ty = true) :
    ∃ x n, (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs ∧
      c = .Evar x (tarrL n) ∧ pt = .Tpointer ty noattrL ∧
        (ty = tul ∨ ty = tui ∨ ty = tdbl ∨ ty = tflt) ∧ 1 ≤ n := by
  cases c with
  | Evar x t =>
      cases t with
      | Tarray t n a =>
          simp only [cellOk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
            and_assoc, or_assoc] at h
          obtain ⟨rfl, rfl, rfl, hty, h1, hd⟩ := h
          exact ⟨x, n, arrDef_mem hd, rfl, rfl, hty, h1⟩
      | _ => simp [cellOk] at h
  | _ => simp [cellOk] at h

theorem vchunk_spec {ch : memory_chunk} {ty : type} (h : vchunk ch ty = true) :
    (ch = .Mint8unsigned ∧ ty = tvuc) ∨ (ch = .Mint32 ∧ ty = tvui) := by
  cases ch <;> simp [vchunk] at h
  · exact .inl ⟨rfl, h⟩
  · exact .inr ⟨rfl, h⟩

/-! ## Expressions -/

theorem has_type_of_ok {defs : Defs} : ∀ {a : expr}, exprOk defs a = true →
    has_type a (typeof a)
  | .Econst_int i ty, _ => .ht_int i ty
  | .Econst_long i ty, _ => .ht_long i ty
  | .Econst_float f ty, _ => .ht_float f ty
  | .Econst_single f ty, _ => .ht_single f ty
  | .Etempvar x ty, _ => .ht_temp x ty
  | .Evar x ty, _ => .ht_var x ty
  | .Ebinop op a1 a2 ty, _ => .ht_binop op a1 a2 ty
  | .Ecast a ty, _ => .ht_cast a ty
  | .Ederef a ty, _ => .ht_deref a ty
  | .Eunop op a ty, _ => .ht_unop op a ty
  | .Eaddrof _ _, h => by simp [exprOk] at h
  | .Efield _ _ _, h => by simp [exprOk] at h
  | .Esizeof _ _, h => by simp [exprOk] at h
  | .Ealignof _ _, h => by simp [exprOk] at h


section

variable {ge : genv} {defs : Defs}

theorem eval_arr_var {le : temp_env} {m : mem} {x : ident} {t : type} {n : Int} {a : attr}
    {v : val} (h : eval_expr Archi.aarch64 ge empty_env le m (.Evar x (.Tarray t n a)) v) :
    ∃ b, Genv.find_symbol ge x = some b ∧ v = .Vptr b Ptrofs.zero := by
  cases h with
  | eval_Elvalue _ l ofs bf _ hl hd =>
      cases hl with
      | eval_Evar_local _ _ _ he => simp [empty_env] at he
      | eval_Evar_global _ _ _ _ hs =>
          cases hd with
          | deref_loc_value _ _ hac _ => cases hac
          | deref_loc_reference _ => exact ⟨_, hs, rfl⟩

theorem eval_arr_cast {le : temp_env} {m : mem} {x : ident} {t : type} {n : Int} {a : attr}
    {pt : type} {pa : attr} {v : val}
    (h : eval_expr Archi.aarch64 ge empty_env le m (.Ecast (.Evar x (.Tarray t n a))
      (.Tpointer pt pa)) v) :
    ∃ b, Genv.find_symbol ge x = some b ∧ v = .Vptr b Ptrofs.zero := by
  cases h with
  | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | eval_Ecast _ _ v1 _ h1 hc =>
      obtain ⟨b, hs, rfl⟩ := eval_arr_var h1
      have e : sem_cast Archi.aarch64 (.Vptr b Ptrofs.zero) (.Tarray t n a) (.Tpointer pt pa) m =
          some (.Vptr b Ptrofs.zero) := rfl
      change sem_cast Archi.aarch64 _ (.Tarray t n a) _ m = _ at hc
      rw [e] at hc
      cases hc
      exact ⟨b, hs, rfl⟩

/-- The address `x + i` of an element of the array `x`, whose base is `x` or a cast of `x`. -/
theorem eval_elem_addr {le : temp_env} {m : mem} {ln gv : ident → Option val}
    {mb : ident → Int → Int} {base i : expr} {t pt : type} {x : ident} {l : block} {ofs : ptrofs}
    (hbase : ∀ v, eval_expr Archi.aarch64 ge empty_env le m base v →
      ∃ b, Genv.find_symbol ge x = some b ∧ v = .Vptr b Ptrofs.zero)
    (hty : typeconv (typeof base) = .Tpointer t noattrL)
    (hi : ∀ w, eval_expr Archi.aarch64 ge empty_env le m i w →
      neval defs ln gv mb i w ∧ has_type i (typeof i) ∧ NoPtrV w)
    (hti : typeof i = tul)
    (h : eval_expr Archi.aarch64 ge empty_env le m (.Ebinop .Oadd base i pt) (.Vptr l ofs)) :
    ∃ k, neval defs ln gv mb i (.Vlong k) ∧ Genv.find_symbol ge x = some l ∧
      ofs = Ptrofs.add Archi.aarch64 Ptrofs.zero (Ptrofs.mul Archi.aarch64
        (Ptrofs.repr Archi.aarch64 (sizeof Archi.aarch64 t))
        (Ptrofs.of_int64 Archi.aarch64 k)) := by
  cases h with
  | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | eval_Ebinop _ _ _ _ v1 v2 _ h1 h2 hs =>
      obtain ⟨b, hsb, rfl⟩ := hbase v1 h1
      obtain ⟨n2, _, p2⟩ := hi v2 h2
      rw [hti] at hs
      have hc : classify_add (typeof base) tul = .add_case_pl t := by
        simp only [classify_add, hty]
        rfl
      simp only [sem_binary_operation, sem_add, hc] at hs
      cases v2 with
      | Vlong k =>
          simp only [sem_add_ptr_long, Option.some.injEq, val.Vptr.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨k, n2, hsb, rfl⟩
      | Vptr b' o => exact absurd rfl (p2 b' o)
      | _ => simp [sem_add_ptr_long] at hs

theorem word_off (k : UInt64) :
    Ptrofs.unsigned (Ptrofs.add Archi.aarch64 Ptrofs.zero (Ptrofs.mul Archi.aarch64
      (Ptrofs.repr Archi.aarch64 (sizeof Archi.aarch64 tul)) (Ptrofs.of_int64 Archi.aarch64 k))) =
      woffL k := by
  rw [show sizeof Archi.aarch64 tul = 8 from rfl, off_eq 8 k (by decide) (by decide),
    unsigned_rptr]
  rfl

theorem byte_off (k : UInt64) :
    Ptrofs.unsigned (Ptrofs.add Archi.aarch64 Ptrofs.zero (Ptrofs.mul Archi.aarch64
      (Ptrofs.repr Archi.aarch64 (sizeof Archi.aarch64 tuc)) (Ptrofs.of_int64 Archi.aarch64 k))) =
      u64 k := by
  rw [show sizeof Archi.aarch64 tuc = 1 from rfl, off_eq 1 k (by decide) (by decide),
    unsigned_rptr, Int.one_mul]
  have := u64_range k
  simp only [zmod]
  omega

theorem decode_word {f : Int → Int} {o sz : Int} (h0 : 0 ≤ o) (hb : o + 8 ≤ sz)
    (hr : ∀ i, 0 ≤ i → i < sz → 0 ≤ f i ∧ f i < 256) :
    decode_val Archi.aarch64 .Mint64 ((List.range 8).map fun (j : Nat) =>
      .Byte (Byte.repr (f (o + j)))) = .Vlong (r64 (le8L f o)) :=
  decode_arr8 f o fun j h1 h2 => hr _ (by omega) (by omega)

theorem decode_cell32 {f : Int → Int} {sz : Int} (hb : 4 ≤ sz)
    (hr : ∀ i, 0 ≤ i → i < sz → 0 ≤ f i ∧ f i < 256) :
    decode_val Archi.aarch64 .Mint32 ((List.range 4).map fun (j : Nat) =>
      .Byte (Byte.repr (f (0 + j)))) = .Vint (r32 (le4L f 0)) :=
  decode_arr4 f 0 fun j h1 h2 => hr _ (by omega) (by omega)

theorem decode_cellf64 {f : Int → Int} {sz : Int} (hb : 8 ≤ sz)
    (hr : ∀ i, 0 ≤ i → i < sz → 0 ≤ f i ∧ f i < 256) :
    decode_val Archi.aarch64 .Mfloat64 ((List.range 8).map fun (j : Nat) =>
      .Byte (Byte.repr (f (0 + j)))) = .Vfloat (f64_of_bits (r64 (le8L f 0))) :=
  decode_arr8f f 0 fun j h1 h2 => hr _ (by omega) (by omega)

theorem decode_cellf32 {f : Int → Int} {sz : Int} (hb : 4 ≤ sz)
    (hr : ∀ i, 0 ≤ i → i < sz → 0 ≤ f i ∧ f i < 256) :
    decode_val Archi.aarch64 .Mfloat32 ((List.range 4).map fun (j : Nat) =>
      .Byte (Byte.repr (f (0 + j)))) = .Vsingle (f32_of_bits (r32 (le4L f 0))) :=
  decode_arr4f f 0 fun j h1 h2 => hr _ (by omega) (by omega)

theorem eval_to_n {le : temp_env} {m : mem} {ln gv : ident → Option val}
    {mb : ident → Int → Int} (htr : TempsRel le ln) (hp : NoPtr ln) (hg : GRel ge defs m gv)
    (hm : MRel ge defs m mb) :
    ∀ (a : expr) {v : val}, exprOk defs a = true →
      eval_expr Archi.aarch64 ge empty_env le m a v →
      neval defs ln gv mb a v ∧ has_type a (typeof a) ∧ NoPtrV v
  | .Econst_int i ty, v, _, h => by
      cases h with
      | eval_Econst_int => exact ⟨.nv_int i ty, .ht_int i ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Econst_long i ty, v, _, h => by
      cases h with
      | eval_Econst_long => exact ⟨.nv_long i ty, .ht_long i ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Econst_float f ty, v, _, h => by
      cases h with
      | eval_Econst_float => exact ⟨.nv_float f ty, .ht_float f ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Econst_single f ty, v, _, h => by
      cases h with
      | eval_Econst_single =>
          exact ⟨.nv_single f ty, .ht_single f ty, fun _ _ e => by cases e⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Etempvar x ty, v, _, h => by
      cases h with
      | eval_Etempvar _ _ _ hv =>
          have hv' : ln x = some v := (htr x).symm.trans hv
          exact ⟨.nv_temp x ty v hv', .ht_temp x ty, hp x v hv'⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Evar x ty, v, hok, h => by
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
  | .Ebinop op a1 a2 ty, v, hok, h => by
      simp only [exprOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      cases h with
      | eval_Ebinop _ _ _ _ v1 v2 _ h1 h2 hs =>
          obtain ⟨n1, t1, _⟩ := eval_to_n htr hp hg hm a1 hok.1.1 h1
          obtain ⟨n2, t2, _⟩ := eval_to_n htr hp hg hm a2 hok.1.2 h2
          have hb := binop_leaf hok.2 hs
          exact ⟨.nv_binop op a1 a2 ty _ _ v1 v2 v n1 t1 n2 t2 hb, .ht_binop op a1 a2 ty,
            binop_ok_noptr hb⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Ecast a ty, v, hok, h => by
      simp only [exprOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      cases h with
      | eval_Ecast _ _ v1 _ h1 hc =>
          obtain ⟨n1, t1, p1⟩ := eval_to_n htr hp hg hm a hok.1 h1
          have hc' := cast_leaf hok.2 hc
          exact ⟨.nv_cast a ty _ v1 v n1 t1 hc', .ht_cast a ty, cast_ok_noptr hc' p1⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Eunop op a ty, v, hok, h => by
      simp only [exprOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      cases h with
      | eval_Eunop _ _ _ v1 _ h1 hu =>
          obtain ⟨n1, t1, _⟩ := eval_to_n htr hp hg hm a hok.1 h1
          have hu' := unop_leaf hok.2 hu
          exact ⟨.nv_unop op a ty _ v1 v n1 t1 hu', .ht_unop op a ty, unop_ok_noptr hu'⟩
      | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  | .Ederef (.Ebinop op base i pt) ty, v, hok, h => by
      simp only [exprOk, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
      obtain ⟨rfl, hiok, hti, hbase⟩ := hok
      have ih : ∀ w, eval_expr Archi.aarch64 ge empty_env le m i w →
          neval defs ln gv mb i w ∧ has_type i (typeof i) ∧ NoPtrV w :=
        fun w hw => eval_to_n htr hp hg hm i hiok hw
      have hti' : has_type i tul := hti ▸ has_type_of_ok hiok
      obtain ⟨x, n, hd, hshape⟩ := baseOk_spec hbase
      rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases h with
        | eval_Elvalue _ l ofs bf _ hl hdr =>
            cases hl with
            | eval_Ederef _ _ _ _ ha =>
                obtain ⟨k, nk, hs, rfl⟩ := eval_elem_addr (fun w hw => eval_arr_var hw) rfl ih
                  hti ha
                cases hdr with
                | deref_loc_value chunk _ hac hlv =>
                    cases hac
                    have harr := hm x n l hd hs
                    obtain ⟨hb, rfl⟩ := loadv_arr harr hlv
                    rw [word_off k] at hb ⊢
                    have h0 : 0 ≤ woffL k := by
                      simp only [woffL, zmod]; exact Int.emod_nonneg _ (by decide)
                    refine ⟨?_, .ht_deref _ _, fun _ _ e => by cases e⟩
                    rw [show size_chunk_nat .Mint64 = 8 from rfl, decode_word h0 hb harr.range]
                    exact .nv_word x n i k (in_defs_of_mem hd) nk hti' hb
                | deref_loc_reference hac => cases hac
      · cases h with
        | eval_Elvalue _ l ofs bf _ hl hdr =>
            cases hl with
            | eval_Ederef _ _ _ _ ha =>
                obtain ⟨k, nk, hs, rfl⟩ := eval_elem_addr (fun w hw => eval_arr_cast hw) rfl ih
                  hti ha
                cases hdr with
                | deref_loc_value chunk _ hac hlv =>
                    cases hac
                    have harr := hm x n l hd hs
                    obtain ⟨hb, rfl⟩ := loadv_arr harr hlv
                    rw [byte_off k] at hb ⊢
                    have hk := u64_range k
                    have hb' : u64 k < 8 * n := by simp only [size_chunk] at hb; omega
                    refine ⟨?_, .ht_deref _ _, fun _ _ e => by cases e⟩
                    rw [show size_chunk_nat .Mint8unsigned = 1 from rfl,
                      decode_arr1 _ _ (harr.range _ hk.1 hb')]
                    exact .nv_byte x n i k (in_defs_of_mem hd) nk hti' hb'
                | deref_loc_reference hac => cases hac
  | .Ederef (.Ecast c pt) ty, v, hok, h => by
      simp only [exprOk] at hok
      obtain ⟨x, n, hd, rfl, rfl, hty, h1⟩ := cellOk_spec hok
      cases h with
      | eval_Elvalue _ l ofs bf _ hl hdr =>
          cases hl with
          | eval_Ederef _ _ _ _ ha =>
              obtain ⟨b, hs, e⟩ := eval_arr_cast ha
              injection e with e1 e2
              subst e1 e2
              have harr := hm x n l hd hs
              have hz : Ptrofs.unsigned Ptrofs.zero = 0 := rfl
              rcases hty with rfl | rfl | rfl | rfl
              · cases hdr with
                | deref_loc_value chunk _ hac hlv =>
                    cases hac
                    obtain ⟨hb, rfl⟩ := loadv_arr harr hlv
                    rw [hz] at hb ⊢
                    refine ⟨?_, .ht_deref _ _, fun _ _ e => by cases e⟩
                    rw [show size_chunk_nat .Mint64 = 8 from rfl,
                      decode_word (le_refl 0) hb harr.range]
                    exact .nv_cell64 x n (in_defs_of_mem hd) h1
                | deref_loc_reference hac => cases hac
              · cases hdr with
                | deref_loc_value chunk _ hac hlv =>
                    cases hac
                    obtain ⟨hb, rfl⟩ := loadv_arr harr hlv
                    rw [hz] at hb ⊢
                    refine ⟨?_, .ht_deref _ _, fun _ _ e => by cases e⟩
                    rw [show size_chunk_nat .Mint32 = 4 from rfl,
                      decode_cell32 (by simp only [size_chunk] at hb; omega) harr.range]
                    exact .nv_cell32 x n (in_defs_of_mem hd) h1
                | deref_loc_reference hac => cases hac
              · cases hdr with
                | deref_loc_value chunk _ hac hlv =>
                    cases hac
                    obtain ⟨hb, rfl⟩ := loadv_arr harr hlv
                    rw [hz] at hb ⊢
                    refine ⟨?_, .ht_deref _ _, fun _ _ e => by cases e⟩
                    rw [show size_chunk_nat .Mfloat64 = 8 from rfl,
                      decode_cellf64 (by simp only [size_chunk] at hb; omega) harr.range]
                    exact .nv_cellf64 x n (in_defs_of_mem hd) h1
                | deref_loc_reference hac => cases hac
              · cases hdr with
                | deref_loc_value chunk _ hac hlv =>
                    cases hac
                    obtain ⟨hb, rfl⟩ := loadv_arr harr hlv
                    rw [hz] at hb ⊢
                    refine ⟨?_, .ht_deref _ _, fun _ _ e => by cases e⟩
                    rw [show size_chunk_nat .Mfloat32 = 4 from rfl,
                      decode_cellf32 (by simp only [size_chunk] at hb; omega) harr.range]
                    exact .nv_cellf32 x n (in_defs_of_mem hd) h1
                | deref_loc_reference hac => cases hac
  | .Ederef (.Econst_int _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Econst_float _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Econst_single _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Econst_long _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Evar _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Etempvar _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Ederef _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Eaddrof _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Eunop _ _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Efield _ _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Esizeof _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Ederef (.Ealignof _ _) _, _, hok, _ => by simp [exprOk] at hok
  | .Eaddrof _ _, _, hok, _ => by simp [exprOk] at hok
  | .Efield _ _ _, _, hok, _ => by simp [exprOk] at hok
  | .Esizeof _ _, _, hok, _ => by simp [exprOk] at hok
  | .Ealignof _ _, _, hok, _ => by simp [exprOk] at hok
termination_by structural a => a

theorem evallist_to_n {le : temp_env} {m : mem} {ln gv : ident → Option val}
    {mb : ident → Int → Int} (htr : TempsRel le ln) (hp : NoPtr ln) (hg : GRel ge defs m gv)
    (hm : MRel ge defs m mb) :
    ∀ {al : List expr} {tys : List type} {vs : List val}, argsOk defs al tys = true →
      eval_exprlist Archi.aarch64 ge empty_env le m al tys vs →
      neval_list defs ln gv mb al tys vs ∧ NoPtrs vs := by
  intro al tys vs hok h
  induction h with
  | eval_Enil => exact ⟨.nl_nil, fun _ h => by cases h⟩
  | eval_Econs a bl ty tyl v1 v2 vl ha hc _ ih =>
      simp only [argsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨na, ta, pa⟩ := eval_to_n htr hp hg hm a hok.1.1 ha
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
  cases hsc <;> cases h <;>
    first | exact .gv_ui _ | exact .gv_ul _ | exact .gv_d _ | exact .gv_f _ |
      exact absurd rfl (hp _ _)

theorem cast_long {t : type} {v1 v : val} (h : cast_ok t tul v1 v) (hp : NoPtrV v1) :
    ∃ w, v = .Vlong w := by
  cases h <;> first | exact ⟨_, rfl⟩ | exact absurd rfl (hp _ _)

theorem cast_float {t : type} {v1 v : val} (h : cast_ok t tdbl v1 v) : ∃ f, v = .Vfloat f := by
  cases h <;> exact ⟨_, rfl⟩

theorem cast_single {t : type} {v1 v : val} (h : cast_ok t tflt v1 v) :
    ∃ f, v = .Vsingle f := by
  cases h <;> exact ⟨_, rfl⟩

theorem cast_vui {t : type} {v1 v : val} (h : cast_ok t tvui v1 v) : ∃ i, v = .Vint i := by
  cases h
  exact ⟨_, rfl⟩

theorem cast_int {t ty : type} {v1 v : val} (hty : ty = tuc ∨ ty = tui ∨ ty = tvui)
    (h : cast_ok t ty v1 v) : ∃ c, v = .Vint c := by
  rcases hty with rfl | rfl | rfl <;> cases h <;> exact ⟨_, rfl⟩

/-- A `return` gives a value without a pointer, of a type with a leaf cast to the result type
`ret`, which is not `void`. -/
def RetOk (ret : type) (out : outcome) : Prop :=
  ∀ v t, out = .Out_return (some (v, t)) → (t, ret) ∈ castForms ∧ ret ≠ .Tvoid ∧ NoPtrV v

theorem retOk_normal (ret : type) : RetOk ret .Out_normal := fun _ _ e => by cases e

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
  | store_word (x : ident) (n : Int) (i a : expr) :
      (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs →
      exprOk defs i = true → typeof i = tul → exprOk defs a = true → (typeof a, tul) ∈ castForms →
      SOk defs S ret (.Sassign (.Ederef (.Ebinop .Oadd (.Evar x (tarrL n)) i ptul) tul) a)
  | store_byte (x : ident) (n : Int) (i a : expr) :
      (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs →
      exprOk defs i = true → typeof i = tul → exprOk defs a = true → (typeof a, tuc) ∈ castForms →
      SOk defs S ret
        (.Sassign (.Ederef (.Ebinop .Oadd (.Ecast (.Evar x (tarrL n)) ptuc) i ptuc) tuc) a)
  | store_cell (x : ident) (n : Int) (ty : type) (a : expr) :
      (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs →
      (ty = tul ∨ ty = tui ∨ ty = tdbl ∨ ty = tflt) → 1 ≤ n → exprOk defs a = true →
      (typeof a, ty) ∈ castForms →
      SOk defs S ret (.Sassign (.Ederef (.Ecast (.Evar x (tarrL n)) (.Tpointer ty noattrL)) ty) a)
  | call (optid : Option ident) (x : ident) (tys : List type) (rty : type)
      (cc : calling_convention) (al : List expr) : S.contains x = true →
      argsOk defs al tys = true → SOk defs S ret (.Scall optid (.Evar x (.Tfunction tys rty cc)) al)
  | sqrt (optid : Option ident) (x : ident) (al : List expr) : defs.any (sqrtDefOf x) = true →
      argsOk defs al [tdbl] = true →
      SOk defs S ret (.Scall optid (.Evar x (.Tfunction [tdbl] tdbl cc_default)) al)
  | out (x : ident) (a : expr) : defs.any (volDef x) = true → exprOk defs a = true →
      (typeof a, tvui) ∈ castForms →
      SOk defs S ret (.Sbuiltin none (.EF_vstore .Mint32) [ptrVui, tvui]
        [.Eaddrof (.Evar x tvui) ptrVui, a])
  | vload (t x : ident) (ty : type) (n : Int) (init : List init_data) (ch : memory_chunk)
      (i : expr) : (x, .Gvar ⟨.Tarray ty n noattrL, init, false, true⟩) ∈ defs →
      ((ch = .Mint8unsigned ∧ ty = tvuc) ∨ (ch = .Mint32 ∧ ty = tvui)) →
      exprOk defs i = true → typeof i = tul →
      SOk defs S ret (.Sbuiltin (some t) (.EF_vload ch) [.Tpointer ty noattrL]
        [.Eaddrof (.Ederef (.Ebinop .Oadd (.Evar x (.Tarray ty n noattrL)) i
          (.Tpointer ty noattrL)) ty) (.Tpointer ty noattrL)])
  | vstore (x : ident) (n : Int) (init : List init_data) (i a : expr) :
      (x, .Gvar ⟨.Tarray tvui n noattrL, init, false, true⟩) ∈ defs →
      exprOk defs i = true → typeof i = tul → exprOk defs a = true →
      (typeof a, tvui) ∈ castForms →
      SOk defs S ret (.Sbuiltin none (.EF_vstore .Mint32) [ptrVui, tvui]
        [.Eaddrof (.Ederef (.Ebinop .Oadd (.Evar x (.Tarray tvui n noattrL)) i ptrVui) tvui)
          ptrVui, a])
  | seq (s1 s2 : statement) : SOk defs S ret s1 → SOk defs S ret s2 →
      SOk defs S ret (.Ssequence s1 s2)
  | loop (s1 s2 : statement) : SOk defs S ret s1 → SOk defs S ret s2 →
      SOk defs S ret (.Sloop s1 s2)
  | ite (a : expr) (s1 s2 : statement) : exprOk defs a = true →
      (typeof a = tsi ∨ typeof a = tui) → SOk defs S ret s1 → SOk defs S ret s2 →
      SOk defs S ret (.Sifthenelse a s1 s2)

theorem assignOk_spec {defs : Defs} {S : List ident} {ret : type} {lhs a : expr}
    (h : assignOk defs lhs a = true) : SOk defs S ret (.Sassign lhs a) := by
  cases lhs with
  | Evar x ty =>
      simp only [assignOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .store x ty a h.1.1.1 h.1.1.2 h.1.2 h.2
  | Ederef p ty =>
      cases p with
      | Ebinop op base i pt =>
          simp only [assignOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
          obtain ⟨rfl, hi, hti, hb, ha, hc⟩ := h
          obtain ⟨x, n, hd, hs⟩ := baseOk_spec hb
          rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact .store_word x n i a hd hi hti ha hc
          · exact .store_byte x n i a hd hi hti ha hc
      | Ecast c pt =>
          simp only [assignOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
          obtain ⟨hc, ha, hcf⟩ := h
          obtain ⟨x, n, hd, rfl, rfl, hty, h1⟩ := cellOk_spec hc
          exact .store_cell x n ty a hd hty h1 ha hcf
      | _ => simp [assignOk] at h
  | _ => simp [assignOk] at h

theorem builtinOk_spec {defs : Defs} {S : List ident} {ret : type} {optid : Option ident}
    {ef : external_function} {tys : List type} {al : List expr}
    (h : builtinOk defs optid ef tys al = true) : SOk defs S ret (.Sbuiltin optid ef tys al) := by
  unfold builtinOk at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    obtain ⟨rfl, rfl, rfl, rfl, hv, ha, hc⟩ := h
    exact .out _ _ hv ha hc
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hv, hi, hti, ha, hc⟩ := h
    obtain ⟨init, hd⟩ := volArr_mem hv
    exact .vstore _ _ init _ _ hd hi hti ha hc
  · simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨rfl, hch, rfl, rfl, rfl, rfl, rfl, hv, hi, hti⟩ := h
    obtain ⟨init, hd⟩ := volArr_mem hv
    exact .vload _ _ _ _ init _ _ hd (vchunk_spec hch) hi hti
  · simp at h

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
  | .Sassign lhs a, h => assignOk_spec (by simpa [stmtOk] using h)
  | .Scall optid f al, h => by
      cases f with
      | Evar x fty =>
          cases fty with
          | Tfunction tys rty cc =>
              simp only [stmtOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
              rcases h with ⟨hx | ⟨⟨⟨rfl, rfl⟩, rfl⟩, hd⟩, ha⟩
              · exact .call optid x tys rty cc al hx ha
              · exact .sqrt optid x al hd ha
          | _ => simp [stmtOk] at h
      | _ => simp [stmtOk] at h
  | .Sbuiltin optid ef tys al, h => builtinOk_spec (by simpa [stmtOk] using h)
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

theorem block_ne (hge : GenvOk ge defs) {x y : ident} {gx gy : globdef (fundef function) type}
    {bx by' : block} (hx : (x, gx) ∈ defs) (hy : (y, gy) ∈ defs) (hne : gx ≠ gy)
    (hbx : Genv.find_symbol ge x = some bx) (hby : Genv.find_symbol ge y = some by') :
    bx ≠ by' := by
  intro e
  subst e
  have hxy := hge.inj x y bx hbx hby
  subst hxy
  exact hne (mem_unique hge.nodup hx hy)

theorem scalar_ne_arr {ty : type} {init : List init_data} {n : Int} (hsc : scalar ty) :
    (globdef.Gvar ⟨ty, init, false, false⟩ : globdef (fundef function) type) ≠
      .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩ := by
  intro e
  injection e with e
  injection e with e
  cases hsc <;> cases e

theorem grel_same {m m' : mem} {gv : ident → Option val} {b : block} (hg : GRel ge defs m gv)
    (hs : Mem.SameExcept b m m')
    (hb : ∀ x ty init bx, (x, .Gvar ⟨ty, init, false, false⟩) ∈ defs → scalar ty →
      Genv.find_symbol ge x = some bx → bx ≠ b) : GRel ge defs m' gv := by
  intro x ty init bx hd hsc hsx
  obtain ⟨w, hw, hgw, hl, hva⟩ := hg x ty init bx hd hsc hsx
  refine ⟨w, hw, hgw, ?_, by rw [hs.valid_access_eq]; exact hva⟩
  rw [hs.load_eq (hb x ty init bx hd hsc hsx)]
  exact hl

theorem mrel_same {m m' : mem} {mb : ident → Int → Int} {b : block} (hm : MRel ge defs m mb)
    (hs : Mem.SameExcept b m m')
    (hb : ∀ x n bx, (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs →
      Genv.find_symbol ge x = some bx → bx ≠ b) : MRel ge defs m' mb :=
  fun x n bx hd hsx => (hm x n bx hd hsx).same hs (hb x n bx hd hsx)

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
    | gv_d f => exact Mem.load_stored_float m b 0 f hva
    | gv_f f => exact Mem.load_stored_single m b 0 f hva
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

/-- The bytes of an array after a store of the number `w` from the offset `o` within it. -/
theorem mrel_store (hge : GenvOk ge defs) {m m' : mem} {mb : ident → Int → Int} {x : ident}
    {n : Int} {b : block} {w : Nat} {gv : ident → Option val} (hm : MRel ge defs m mb)
    (hgs : GRel ge defs m gv)
    (hd : (x, .Gvar ⟨tarrL n, [.Init_space (8 * n)], false, false⟩) ∈ defs)
    (hs : Genv.find_symbol ge x = some b) (hse : Mem.SameExcept b m m') {o c : Int}
    (harr : ArrHolds m' b (8 * n) (fun j => if o ≤ j ∧ j < o + c then
      zmod (zdiv (w : Int) (pow2 (8 * (j - o)))) 256 else mb x j)) :
    MRel ge defs m' (setm mb x o c w) ∧ GRel ge defs m' gv := by
  refine ⟨fun y n' by' hd' hsy => ?_, grel_same hgs hse fun z ty init bz hz hsc hsz =>
    block_ne hge hz hd (scalar_ne_arr hsc) hsz hs⟩
  by_cases e : y = x
  · subst e
    rw [hs] at hsy
    cases hsy
    have hdd := mem_unique hge.nodup hd hd'
    injection hdd with hdd
    injection hdd with e1 e2
    injection e1 with _ e1
    subst e1
    have : setm mb y o c w y = fun j => if o ≤ j ∧ j < o + c then
        zmod (zdiv (w : Int) (pow2 (8 * (j - o)))) 256 else mb y j := by
      funext j
      simp [setm]
    rw [this]
    exact harr
  · have hb : by' ≠ b := fun e' => e (hge.inj y x by' hsy (e' ▸ hs))
    have : setm mb x o c w y = mb y := by
      funext j
      simp [setm, e]
    rw [this]
    exact (hm y n' by' hd' hsy).same hse hb

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

theorem load_result_vint {ch : memory_chunk} {ty : type} {j : int}
    (h : (ch = .Mint8unsigned ∧ ty = tvuc) ∨ (ch = .Mint32 ∧ ty = tvui)) :
    ∃ sz, sizeof Archi.aarch64 ty = sz ∧ 0 ≤ sz ∧ sz ≤ 8 ∧
      vload_ok ch ty sz j (Val.load_result Archi.aarch64 ch (.Vint j)) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨1, rfl, by decide, by decide, ?_⟩
    have : Val.load_result Archi.aarch64 .Mint8unsigned (.Vint j) =
        .Vint (r32 (zmod (u32 j) 256)) := rfl
    rw [this]
    exact .vl_uchar j
  · exact ⟨4, rfl, by decide, by decide, .vl_uint j⟩

mutual

theorem exec_to_n (hge : GenvOk ge defs) (hS : FunsOk defs S) {e : env} {le : temp_env}
    {m : mem} {s : statement} {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
    (h : exec_stmt Archi.aarch64 X ge e le m s t le' m' out) :
    ∀ {ret : type} {ln gv : ident → Option val} {mb : ident → Int → Int}, e = empty_env →
      SOk defs S ret s → TempsRel le ln → NoPtr ln → GRel ge defs m gv → MRel ge defs m mb →
      ∃ ln' gv' mb', nexec defs ln gv mb s t ln' gv' mb' out ∧ TempsRel le' ln' ∧ NoPtr ln' ∧
        GRel ge defs m' gv' ∧ MRel ge defs m' mb' ∧ RetOk ret out := by
  match h with
  | .exec_Sskip _ _ _ =>
      intro ret ln gv mb _ _ htr hp hg hm
      exact ⟨ln, gv, mb, .nx_skip ln gv mb, htr, hp, hg, hm, retOk_normal ret⟩
  | .exec_Sset _ _ _ x a v hv =>
      intro ret ln gv mb he hok htr hp hg hm
      subst he
      cases hok with
      | set _ _ ha =>
          obtain ⟨n, _, pv⟩ := eval_to_n htr hp hg hm a ha hv
          exact ⟨upd ln x v, gv, mb, .nx_set ln gv mb x a v _ n (upd_spec ln x v),
            temps_upd htr x v, noptr_upd hp x pv, hg, hm, retOk_normal ret⟩
  | .exec_Sassign _ _ _ a1 a2 loc ofs bf v2 v m1 hl ha2 hc hasg =>
      intro ret ln gv mb he hok htr hp hg hm
      subst he
      cases hok with
      | store x ty _ hsty hdef ha hcf =>
          have hsc := scalar_of hsty
          obtain ⟨init, hd⟩ := scalarDef_mem hdef
          obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg hm a2 ha ha2
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
                  have hst' := storev_zero hst
                  obtain ⟨_, hm1⟩ := Mem.store_inv hst'
                  have hse : Mem.SameExcept loc m m1 := by
                    rw [hm1]; exact Mem.SameExcept.of_stored _ _ _ _ _
                  exact ⟨ln, upd gv x v, mb, .nx_store ln gv mb x ty init a2 _ v2 v _
                    (in_defs_of_mem hd) hsc n2 t2 hco hgv (upd_spec gv x v), htr, hp,
                    grel_store hge hg hd hs hgv hst',
                    mrel_same hm hse fun y n by' hy hsy =>
                      block_ne hge hy hd (scalar_ne_arr hsc).symm hsy hs,
                    retOk_normal ret⟩
      | store_word x n i _ hd hiok hti ha hcf =>
          obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg hm a2 ha ha2
          have hco := cast_leaf hcf hc
          obtain ⟨w, rfl⟩ := cast_long hco p2
          have hti' : has_type i tul := hti ▸ has_type_of_ok hiok
          cases hl with
          | eval_Ederef _ _ _ _ ha1 =>
              obtain ⟨k, nk, hs, rfl⟩ := eval_elem_addr (fun w hw => eval_arr_var hw) rfl
                (fun w hw => eval_to_n htr hp hg hm i hiok hw) hti ha1
              cases hasg with
              | assign_loc_value _ chunk _ hac hst =>
                  cases hac
                  obtain ⟨hb, hse, harr⟩ := storev_arr (w := w.toNat) (hm x n loc hd hs) rfl
                    (by decide) hst
                  rw [word_off k] at hb harr
                  obtain ⟨hm', hg'⟩ := mrel_store hge hm hg hd hs hse harr
                  exact ⟨ln, gv, setm mb x (woffL k) 8 (u64 w),
                    .nx_store_word ln gv mb x n i k a2 _ v2 w _ (in_defs_of_mem hd) nk hti' hb n2
                      t2 hco (setm_spec mb x (woffL k) 8 (u64 w)),
                    htr, hp, hg', hm', retOk_normal ret⟩
      | store_byte x n i _ hd hiok hti ha hcf =>
          obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg hm a2 ha ha2
          have hco := cast_leaf hcf hc
          obtain ⟨c, rfl⟩ := cast_int (.inl rfl) hco
          have hti' : has_type i tul := hti ▸ has_type_of_ok hiok
          cases hl with
          | eval_Ederef _ _ _ _ ha1 =>
              obtain ⟨k, nk, hs, rfl⟩ := eval_elem_addr (fun w hw => eval_arr_cast hw) rfl
                (fun w hw => eval_to_n htr hp hg hm i hiok hw) hti ha1
              cases hasg with
              | assign_loc_value _ chunk _ hac hst =>
                  cases hac
                  obtain ⟨hb, hse, harr⟩ := storev_arr (w := c.toNat) (hm x n loc hd hs) rfl
                    (by decide) hst
                  rw [byte_off k] at hb harr
                  have hb' : u64 k < 8 * n := by simp only [size_chunk] at hb; omega
                  obtain ⟨hm', hg'⟩ := mrel_store hge hm hg hd hs hse harr
                  exact ⟨ln, gv, setm mb x (u64 k) 1 (u32 c),
                    .nx_store_byte ln gv mb x n i k a2 _ v2 c _ (in_defs_of_mem hd) nk hti' hb' n2
                      t2 hco (setm_spec mb x (u64 k) 1 (u32 c)),
                    htr, hp, hg', hm', retOk_normal ret⟩
      | store_cell x n ty _ hd hty h1 ha hcf =>
          obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg hm a2 ha ha2
          have hco := cast_leaf hcf hc
          cases hl with
          | eval_Ederef _ _ _ _ ha1 =>
              obtain ⟨b, hs, e⟩ := eval_arr_cast ha1
              injection e with e1 e2
              subst e1 e2
              have hz : Ptrofs.unsigned Ptrofs.zero = 0 := rfl
              rcases hty with rfl | rfl | rfl | rfl
              · obtain ⟨w, rfl⟩ := cast_long hco p2
                cases hasg with
                | assign_loc_value _ chunk _ hac hst =>
                    cases hac
                    obtain ⟨hb, hse, harr⟩ := storev_arr (w := w.toNat) (hm x n loc hd hs) rfl
                      (by decide) hst
                    rw [hz] at hb harr
                    obtain ⟨hm', hg'⟩ := mrel_store hge hm hg hd hs hse harr
                    exact ⟨ln, gv, setm mb x 0 8 (u64 w),
                      .nx_store_cell64 ln gv mb x n a2 _ v2 w _ (in_defs_of_mem hd) h1 n2 t2 hco
                        (setm_spec mb x 0 8 (u64 w)),
                      htr, hp, hg', hm', retOk_normal ret⟩
              · obtain ⟨c, rfl⟩ := cast_int (.inr (.inl rfl)) hco
                cases hasg with
                | assign_loc_value _ chunk _ hac hst =>
                    cases hac
                    obtain ⟨hb, hse, harr⟩ := storev_arr (w := c.toNat) (hm x n loc hd hs) rfl
                      (by decide) hst
                    rw [hz] at hb harr
                    obtain ⟨hm', hg'⟩ := mrel_store hge hm hg hd hs hse harr
                    exact ⟨ln, gv, setm mb x 0 4 (u32 c),
                      .nx_store_cell32 ln gv mb x n a2 _ v2 c _ (in_defs_of_mem hd) h1 n2 t2 hco
                        (setm_spec mb x 0 4 (u32 c)),
                      htr, hp, hg', hm', retOk_normal ret⟩
              · obtain ⟨f, rfl⟩ := cast_float hco
                cases hasg with
                | assign_loc_value _ chunk _ hac hst =>
                    cases hac
                    obtain ⟨hb, hse, harr⟩ := storev_arr (w := f.toNat) (hm x n loc hd hs) rfl
                      (by decide) hst
                    rw [hz] at hb harr
                    obtain ⟨hm', hg'⟩ := mrel_store hge hm hg hd hs hse harr
                    exact ⟨ln, gv, setm mb x 0 8 (u64 (f64_bits f)),
                      .nx_store_cellf64 ln gv mb x n a2 _ v2 f _ (in_defs_of_mem hd) h1 n2 t2 hco
                        (setm_spec mb x 0 8 (u64 (f64_bits f))),
                      htr, hp, hg', hm', retOk_normal ret⟩
              · obtain ⟨f, rfl⟩ := cast_single hco
                cases hasg with
                | assign_loc_value _ chunk _ hac hst =>
                    cases hac
                    obtain ⟨hb, hse, harr⟩ := storev_arr (w := f.toNat) (hm x n loc hd hs) rfl
                      (by decide) hst
                    rw [hz] at hb harr
                    obtain ⟨hm', hg'⟩ := mrel_store hge hm hg hd hs hse harr
                    exact ⟨ln, gv, setm mb x 0 4 (u32 (f32_bits f)),
                      .nx_store_cellf32 ln gv mb x n a2 _ v2 f _ (in_defs_of_mem hd) h1 n2 t2 hco
                        (setm_spec mb x 0 4 (u32 (f32_bits f))),
                      htr, hp, hg', hm', retOk_normal ret⟩
  | .exec_Scall _ _ _ optid a al tyargs tyres cconv vf vargs fd t1 m1 vres hcls hvf hargs
      hfind hty hcall =>
      intro ret ln gv mb he hok htr hp hg hm
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
                      obtain ⟨nl, pl⟩ := evallist_to_n htr hp hg hm hargsok hargs
                      obtain ⟨ln0, ln1, ln2, gv2, mb2, out2, hu, hb, hnr, hdj, hx, hres, hg2, hm2,
                        pres⟩ := call_to_n hge hS hcall hfd hvars hbody pl hg hm
                      rw [hfd] at hty
                      simp only [type_of_fundef, type_of_function] at hty
                      injection hty with e1 e2 e3
                      subst e1 e2 e3
                      obtain ⟨ln3, hso, htr3, hp3⟩ := set_opt_of optid htr hp pres
                      rw [fun_eta f hvars] at hdf
                      exact ⟨ln3, gv2, mb2, .nx_call ln gv mb optid x _ f.fn_return f.fn_callconv al
                        vargs f.fn_params f.fn_temps f.fn_body ln0 ln1 t1 ln2 gv2 mb2 out2 vres ln3
                        (in_defs_of_mem hdf) (params_types_of _) nl hnr hdj hu hb hx hres hso,
                        htr3, hp3, hg2, hm2, retOk_normal ret⟩
      | sqrt _ x _ hd hargsok =>
          simp only [typeof, classify_fun] at hcls
          injection hcls with e1 e2 e3
          subst e1 e2 e3
          obtain ⟨d, hmem, hdef⟩ := List.any_eq_true.mp hd
          have hmem : (x, .Gfun sqrtFun) ∈ defs := by
            obtain ⟨y, g⟩ := d
            simp only [sqrtDefOf, Bool.and_eq_true, beq_iff_eq] at hdef
            obtain ⟨rfl, hdef⟩ := hdef
            match g, hdef with
            | .Gfun (.External (.EF_builtin name sg) targs tres cc), h =>
                simp only [Bool.and_eq_true, beq_iff_eq] at h
                obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
                exact hmem
          cases hvf with
          | eval_Elvalue _ l ofs bf _ hl hdr =>
              cases hl with
              | eval_Evar_local _ _ _ hle => simp [empty_env] at hle
              | eval_Evar_global _ _ _ _ hs =>
                  cases hdr with
                  | deref_loc_value _ _ hac _ => cases hac
                  | deref_loc_reference _ =>
                      obtain ⟨b', hsb, hdb⟩ := hge.sym_def _ _ hmem
                      rw [hs] at hsb
                      cases hsb
                      have hfd : fd = sqrtFun := by
                        simp only [Genv.find_funct, Genv.find_funct_ptr, hdb] at hfind
                        simp at hfind
                        exact hfind.symm
                      subst hfd
                      obtain ⟨nl, _⟩ := evallist_to_n htr hp hg hm hargsok hargs
                      obtain ⟨f, rfl⟩ : ∃ f, vargs = [.Vfloat f] := by
                        cases nl with
                        | nl_cons _ _ _ _ _ _ _ _ _ _ hc nrest =>
                            cases nrest
                            obtain ⟨f, rfl⟩ := cast_float hc
                            exact ⟨f, rfl⟩
                      cases hcall with
                      | eval_funcall_external _ _ _ _ _ _ _ _ _ hext =>
                          have hlk : lookup_builtin_function "__builtin_fsqrt" sqrtSig =
                              some .BI_fsqrt := rfl
                          simp only [external_call, hlk, known_builtin_sem] at hext
                          obtain ⟨hsem, rfl, rfl⟩ := hext
                          injection hsem with hsem
                          subst hsem
                          obtain ⟨ln3, hso, htr3, hp3⟩ :=
                            set_opt_of (v := .Vfloat (LClight.Float.sqrt Archi.aarch64 f)) optid
                              htr hp (fun _ _ e => by cases e)
                          exact ⟨ln3, gv, mb, .nx_sqrt ln gv mb optid x al f ln3
                            (in_defs_of_mem hmem) nl hso, htr3, hp3, hg, hm, retOk_normal ret⟩
  | .exec_Sbuiltin _ _ _ optid ef al tyargs vargs t1 m1 vres hargs hext =>
      intro ret ln gv mb he hok htr hp hg hm
      subst he
      cases hok with
      | out x a hvol ha hcf =>
          obtain ⟨init, hd⟩ := volDef_mem hvol
          cases hargs with
          | eval_Econs _ _ _ _ w1 w1' _ ha1 hc1 hrest =>
              cases hrest with
              | eval_Econs _ _ _ _ w2 w2' _ ha2 hc2 hnil =>
                  cases hnil
                  obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg hm a ha ha2
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
                                  refine ⟨ln, gv, mb, ?_, htr, hp, hg, hm, retOk_normal ret⟩
                                  rw [ptrofs_zero]
                                  exact .nx_out ln gv mb y init a _ w2 i (in_defs_of_mem hd) n2 t2
                                    hco
                              | volatile_store_nonvol _ _ hnv _ =>
                                  simp [Genv.block_is_volatile, Genv.find_var_info, hdb] at hnv
      | vstore x n init i a hd hiok hti ha hcf =>
          have hti' : has_type i tul := hti ▸ has_type_of_ok hiok
          cases hargs with
          | eval_Econs _ _ _ _ w1 w1' _ ha1 hc1 hrest =>
              cases hrest with
              | eval_Econs _ _ _ _ w2 w2' _ ha2 hc2 hnil =>
                  cases hnil
                  obtain ⟨n2, t2, p2⟩ := eval_to_n htr hp hg hm a ha ha2
                  have hco := cast_leaf hcf hc2
                  obtain ⟨c, rfl⟩ := cast_vui hco
                  obtain ⟨b, hs, hdb⟩ := hge.sym_def _ _ hd
                  cases ha1 with
                  | eval_Elvalue _ _ _ _ _ hl _ => cases hl
                  | eval_Eaddrof _ _ l o hl =>
                      cases hl with
                      | eval_Ederef _ _ _ _ hadr =>
                          obtain ⟨k, nk, hs1, rfl⟩ := eval_elem_addr (fun w hw => eval_arr_var hw)
                            rfl (fun w hw => eval_to_n htr hp hg hm i hiok hw) hti hadr
                          rw [hs] at hs1
                          cases hs1
                          have hofs := off_eq 4 k (by decide) (by decide)
                          have hw1 : some (val.Vptr b (rptr (4 * u64 k))) = some w1' := by
                            rw [← hofs]
                            exact hc1
                          cases hw1
                          simp only [external_call] at hext
                          cases hext with
                          | volatile_store_sem_intro _ _ _ _ _ _ hvs =>
                              cases hvs with
                              | volatile_store_vol y ev _ _ hsy hev =>
                                  have hy := hge.inj y x b hsy hs
                                  subst hy
                                  cases hev
                                  exact ⟨ln, gv, mb, .nx_vstore ln gv mb y n init i k a _ w2 c
                                    (in_defs_of_mem hd) nk hti' n2 t2 hco, htr, hp, hg, hm,
                                    retOk_normal ret⟩
                              | volatile_store_nonvol _ _ hnv _ =>
                                  simp [Genv.block_is_volatile, Genv.find_var_info, hdb] at hnv
      | vload t x ty n init ch i hd hch hiok hti =>
          have hti' : has_type i tul := hti ▸ has_type_of_ok hiok
          obtain ⟨b, hs, hdb⟩ := hge.sym_def _ _ hd
          cases hargs with
          | eval_Econs _ _ _ _ w1 w1' _ ha1 hc1 hrest =>
              cases hrest
              cases ha1 with
              | eval_Elvalue _ _ _ _ _ hl _ => cases hl
              | eval_Eaddrof _ _ l o hl =>
                  cases hl with
                  | eval_Ederef _ _ _ _ hadr =>
                      obtain ⟨k, nk, hs1, rfl⟩ := eval_elem_addr (fun w hw => eval_arr_var hw)
                        rfl (fun w hw => eval_to_n htr hp hg hm i hiok hw) hti hadr
                      rw [hs] at hs1
                      cases hs1
                      have hw1 : some (val.Vptr b (Ptrofs.add Archi.aarch64 Ptrofs.zero
                          (Ptrofs.mul Archi.aarch64 (Ptrofs.repr Archi.aarch64
                            (sizeof Archi.aarch64 ty)) (Ptrofs.of_int64 Archi.aarch64 k)))) =
                          some w1' := hc1
                      cases hw1
                      simp only [external_call] at hext
                      cases hext with
                      | volatile_load_sem_intro _ _ _ _ _ hvl =>
                          cases hvl with
                          | volatile_load_vol y ev v0 _ hsy hev =>
                              have hy := hge.inj y x b hsy hs
                              subst hy
                              have hti0 : type_of_chunk ch = .Tint := by
                                rcases hch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
                              rw [hti0] at hev
                              cases hev with
                              | ev_match_int j =>
                                  obtain ⟨sz, hsz, h0, h8, hvl⟩ := load_result_vint (j := j) hch
                                  rw [hsz, off_eq sz k h0 h8]
                                  exact ⟨upd ln t _, gv, mb, .nx_vload ln gv mb t y ty n init ch sz
                                    i k j _ _ (in_defs_of_mem hd) nk hti' hvl (upd_spec ln t _),
                                    temps_upd htr t _, noptr_upd hp t (by
                                      rcases hch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
                                        exact fun _ _ e => by cases e),
                                    hg, hm, retOk_normal ret⟩
                          | volatile_load_nonvol _ hnv _ =>
                              simp [Genv.block_is_volatile, Genv.find_var_info, hdb] at hnv
  | .exec_Sseq_1 _ _ _ s1 s2 t1 le1 m1 t2 le2 m2 out h1 h2 =>
      intro ret ln gv mb he hok htr hp hg hm
      cases hok with
      | seq _ _ hok1 hok2 =>
          obtain ⟨ln1, gv1, mb1, n1, htr1, hp1, hg1, hm1, _⟩ :=
            exec_to_n hge hS h1 he hok1 htr hp hg hm
          obtain ⟨ln2, gv2, mb2, n2, htr2, hp2, hg2, hm2, hr2⟩ :=
            exec_to_n hge hS h2 he hok2 htr1 hp1 hg1 hm1
          exact ⟨ln2, gv2, mb2,
            .nx_seq1 ln gv mb s1 s2 t1 ln1 gv1 mb1 t2 ln2 gv2 mb2 out n1 n2, htr2, hp2, hg2, hm2,
            hr2⟩
  | .exec_Sseq_2 _ _ _ s1 s2 t1 le1 m1 out h1 hne =>
      intro ret ln gv mb he hok htr hp hg hm
      cases hok with
      | seq _ _ hok1 _ =>
          obtain ⟨ln1, gv1, mb1, n1, htr1, hp1, hg1, hm1, hr1⟩ :=
            exec_to_n hge hS h1 he hok1 htr hp hg hm
          exact ⟨ln1, gv1, mb1, .nx_seq2 ln gv mb s1 s2 t1 ln1 gv1 mb1 out n1 hne, htr1, hp1, hg1,
            hm1, hr1⟩
  | .exec_Sifthenelse _ _ _ a s1 s2 v1 b t1 le1 m1 out hv hb hs =>
      intro ret ln gv mb he hok htr hp hg hm
      cases hok with
      | ite _ _ _ ha hty hok1 hok2 =>
          have hokb : SOk defs S ret (if b then s1 else s2) := by cases b <;> assumption
          obtain ⟨ln1, gv1, mb1, n1, htr1, hp1, hg1, hm1, hr1⟩ :=
            exec_to_n hge hS hs he hokb htr hp hg hm
          subst he
          obtain ⟨na, ta, _⟩ := eval_to_n htr hp hg hm a ha hv
          have hbo := bool_leaf hty hb
          refine ⟨ln1, gv1, mb1, ?_, htr1, hp1, hg1, hm1, hr1⟩
          cases b with
          | true => exact .nx_if_true ln gv mb a s1 s2 v1 _ t1 ln1 gv1 mb1 out na ta hbo n1
          | false => exact .nx_if_false ln gv mb a s1 s2 v1 _ t1 ln1 gv1 mb1 out na ta hbo n1
  | .exec_Sreturn_none _ _ _ =>
      intro ret ln gv mb _ _ htr hp hg hm
      exact ⟨ln, gv, mb, .nx_return_none ln gv mb, htr, hp, hg, hm, fun _ _ e => by cases e⟩
  | .exec_Sreturn_some _ _ _ a v hv =>
      intro ret ln gv mb he hok htr hp hg hm
      subst he
      cases hok with
      | ret_some _ ha hne hcf =>
          obtain ⟨na, ta, pv⟩ := eval_to_n htr hp hg hm a ha hv
          refine ⟨ln, gv, mb, .nx_return_some ln gv mb a v _ na ta, htr, hp, hg, hm, ?_⟩
          intro w t' e
          injection e with e
          injection e with e
          injection e with e1 e2
          subst e1 e2
          exact ⟨hcf, hne, pv⟩
  | .exec_Sbreak _ _ _ =>
      intro ret ln gv mb _ _ htr hp hg hm
      exact ⟨ln, gv, mb, .nx_break ln gv mb, htr, hp, hg, hm, fun _ _ e => by cases e⟩
  | .exec_Scontinue _ _ _ =>
      intro ret ln gv mb _ _ htr hp hg hm
      exact ⟨ln, gv, mb, .nx_continue ln gv mb, htr, hp, hg, hm, fun _ _ e => by cases e⟩
  | .exec_Sloop_stop1 _ _ _ s1 s2 t1 le1 m1 out1 out h1 hbr =>
      intro ret ln gv mb he hok htr hp hg hm
      cases hok with
      | loop _ _ hok1 _ =>
          obtain ⟨ln1, gv1, mb1, n1, htr1, hp1, hg1, hm1, hr1⟩ :=
            exec_to_n hge hS h1 he hok1 htr hp hg hm
          refine ⟨ln1, gv1, mb1, .nx_loop_stop1 ln gv mb s1 s2 t1 ln1 gv1 mb1 out1 out n1 ?_, htr1,
            hp1, hg1, hm1, ?_⟩
          · cases hbr with
            | Out_break_or_return_B => exact .inl ⟨rfl, rfl⟩
            | Out_break_or_return_R r => exact .inr ⟨r, rfl, rfl⟩
          · cases hbr with
            | Out_break_or_return_B => exact fun _ _ e => by cases e
            | Out_break_or_return_R r => exact hr1
  | .exec_Sloop_stop2 _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out h1 hnc h2 hbr =>
      intro ret ln gv mb he hok htr hp hg hm
      cases hok with
      | loop _ _ hok1 hok2 =>
          obtain ⟨ln1, gv1, mb1, n1, htr1, hp1, hg1, hm1, _⟩ :=
            exec_to_n hge hS h1 he hok1 htr hp hg hm
          obtain ⟨ln2, gv2, mb2, n2, htr2, hp2, hg2, hm2, hr2⟩ :=
            exec_to_n hge hS h2 he hok2 htr1 hp1 hg1 hm1
          refine ⟨ln2, gv2, mb2, .nx_loop_stop2 ln gv mb s1 s2 t1 ln1 gv1 mb1 out1 t2 ln2 gv2 mb2
            out2 out n1 ?_ n2 ?_, htr2, hp2, hg2, hm2, ?_⟩
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
      intro ret ln gv mb he hok htr hp hg hm
      have hok' := hok
      cases hok with
      | loop _ _ hok1 hok2 =>
          obtain ⟨ln1, gv1, mb1, n1, htr1, hp1, hg1, hm1, _⟩ :=
            exec_to_n hge hS h1 he hok1 htr hp hg hm
          obtain ⟨ln2, gv2, mb2, n2, htr2, hp2, hg2, hm2, _⟩ :=
            exec_to_n hge hS h2 he hok2 htr1 hp1 hg1 hm1
          obtain ⟨ln3, gv3, mb3, n3, htr3, hp3, hg3, hm3, hr3⟩ :=
            exec_to_n hge hS h3 he hok' htr2 hp2 hg2 hm2
          refine ⟨ln3, gv3, mb3, ?_, htr3, hp3, hg3, hm3, hr3⟩
          rw [List.append_assoc]
          refine .nx_loop ln gv mb s1 s2 t1 ln1 gv1 mb1 out1 t2 ln2 gv2 mb2 t3 ln3 gv3 mb3 out n1
            ?_ n2 n3
          cases hnc with
          | Out_normal_or_continue_N => exact .inl rfl
          | Out_normal_or_continue_C => exact .inr rfl
termination_by structural h

theorem call_to_n (hge : GenvOk ge defs) (hS : FunsOk defs S) {m : mem} {fd : fundef function}
    {vargs : List val} {t : trace} {m' : mem} {vres : val}
    (h : eval_funcall Archi.aarch64 X ge m fd vargs t m' vres) :
    ∀ {f : function} {gv : ident → Option val} {mb : ident → Int → Int}, fd = .Internal f →
      f.fn_vars = [] → SOk defs S f.fn_return f.fn_body → NoPtrs vargs → GRel ge defs m gv →
      MRel ge defs m mb →
      ∃ ln0 ln1 ln2 gv2 mb2 out, undef_temps f.fn_temps ln0 ∧
        bind_params f.fn_params vargs ln0 ln1 ∧ norepet_names f.fn_params ∧
        disjoint_names f.fn_params f.fn_temps ∧ nexec defs ln1 gv mb f.fn_body t ln2 gv2 mb2 out ∧
        result_ok out f.fn_return vres ∧ GRel ge defs m' gv2 ∧ MRel ge defs m' mb2 ∧
        NoPtrV vres := by
  match h with
  | .eval_funcall_internal _ f _ _ e le1 le2 m1 m2 out _ m3 hentry hbody hres hfree =>
      intro f2 gv mb hfd _ hok hpv hg hm
      injection hfd with hfd
      subst hfd
      obtain ⟨he, hm1, hnd, hdj, hbind⟩ := entry_facts hentry
      have hp1 : NoPtr fun y => le1[y]? := noptr_bind _ _ _ _ hbind hpv (noptr_undef _)
      obtain ⟨ln2, gv2, mb2, hx, _, _, hg2, hm2, hret⟩ :=
        exec_to_n hge hS hbody he hok (fun _ => rfl) hp1 (hm1 ▸ hg) (hm1 ▸ hm)
      obtain ⟨hres', pv⟩ := result_of hret hres
      subst he
      rw [blocks_empty] at hfree
      cases hfree
      exact ⟨_, _, ln2, gv2, mb2, out, undef_temps_of f.fn_temps,
        bind_params_of _ _ _ _ hbind, norepet_names_of hnd, disjoint_names_of hdj, hx, hres',
        hg2, hm2, pv⟩
  | .eval_funcall_external .. =>
      intro f gv mb hfd
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
      | [.Init_space _] =>
          if v.gvar_info = tdbl then some (.Vfloat (f64_of_bits (r64 0)))
          else if v.gvar_info = tflt then some (.Vsingle (f32_of_bits (r32 0))) else none
      | _ => none
  | _ => none

theorem scalarTy_of {ty : type} (h : scalar ty) : scalarTy ty = true := by
  cases h <;> rfl

theorem varOk_scalar {ty : type} {init : List init_data}
    (h : varOk ⟨ty, init, false, false⟩ = true) (hsc : scalar ty) :
    (ty = tui ∧ ∃ n, init = [.Init_int32 n]) ∨ (ty = tul ∧ ∃ n, init = [.Init_int64 n]) ∨
      (ty = tdbl ∧ init = [.Init_space 8]) ∨ (ty = tflt ∧ init = [.Init_space 4]) := by
  have hs := scalarTy_of hsc
  unfold varOk at h
  split at h
  · simp_all
  · rename_i n heq
    simp only [Bool.not_false, Bool.true_and, beq_iff_eq] at h
    exact .inl ⟨h, n, heq⟩
  · rename_i n heq
    simp only [Bool.not_false, Bool.true_and, beq_iff_eq] at h
    exact .inr (.inl ⟨h, n, heq⟩)
  · rename_i n heq
    simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq, Bool.not_eq_true', hs, Bool.true_eq_false, false_or] at h
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inr (.inr (.inl ⟨rfl, heq⟩))
    · exact .inr (.inr (.inr ⟨rfl, heq⟩))
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

/-- A block whose bytes from offset 0 are zero, with the permission to write them: a load of the
chunk at offset 0 reads the value of zero bytes. -/
theorem load_zeros {m : mem} {b : block} {chunk : memory_chunk}
    (h : ∀ i : Nat, (i : Int) < size_chunk chunk →
      ZMap.get (i : Int) (Mem.contents_of m b) = .Byte 0 ∧ Mem.perm m b (i : Int) .Cur .Writable)
    (ha : align_chunk chunk ∣ 0) :
    Mem.load Archi.aarch64 chunk m b 0 = some (decode_val Archi.aarch64 chunk
        ((List.range (size_chunk_nat chunk)).map fun _ => .Byte 0)) ∧
      Mem.valid_access m chunk b 0 .Writable := by
  have hva : Mem.valid_access m chunk b 0 .Writable := by
    refine ⟨fun ofs h0 h1 => ?_, ha⟩
    have := (h ofs.toNat (by omega)).2
    rwa [Int.toNat_of_nonneg h0] at this
  refine ⟨?_, hva⟩
  unfold Mem.load
  rw [ite_eq_left (Mem.valid_access_readable hva), Mem.getN_map]
  congr 2
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  have := size_chunk_nat_eq chunk
  have := (h j (by omega)).1
  simpa using this

theorem decode_zero64 : decode_val Archi.aarch64 .Mfloat64
    ((List.range (size_chunk_nat .Mfloat64)).map fun _ => .Byte 0) =
      .Vfloat (f64_of_bits (r64 0)) :=
  rfl

theorem decode_zero32 : decode_val Archi.aarch64 .Mfloat32
    ((List.range (size_chunk_nat .Mfloat32)).map fun _ => .Byte 0) =
      .Vsingle (f32_of_bits (r32 0)) :=
  rfl

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
  rcases varOk_scalar hok hsc with ⟨rfl, n, rfl⟩ | ⟨rfl, n, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hl, hv⟩ := hif.1 n rfl
    exact ⟨.Vint n, by simp [initVal, hlk], .gv_ui n, hl, hv⟩
  · obtain ⟨hl, hv⟩ := hif.2.1 n rfl
    exact ⟨.Vlong n, by simp [initVal, hlk], .gv_ul n, hl, hv⟩
  · obtain ⟨hl, hv⟩ := load_zeros (chunk := .Mfloat64) (fun i hi => hif.2.2 8 rfl i hi)
      (Int.dvd_zero _)
    rw [decode_zero64] at hl
    exact ⟨_, by simp [initVal, hlk], .gv_d _, hl, hv⟩
  · obtain ⟨hl, hv⟩ := load_zeros (chunk := .Mfloat32) (fun i hi => hif.2.2 4 rfl i hi)
      (Int.dvd_zero _)
    rw [decode_zero32] at hl
    exact ⟨_, by simp [initVal, hlk], .gv_f _, hl, hv⟩

/-- The initial memory of a program whose definitions `progOk` accepts holds zero in every byte of
every array, and each array's block has permissions only within its bytes. -/
theorem mrel_init {p : program function} {m0 : mem} (hn : (p.prog_defs.map (·.1)).Nodup)
    (hdefs : ∀ d ∈ p.prog_defs, defOk d.2 = true) (h : init_mem Archi.aarch64 p = some m0) :
    MRel (globalenv p) p.prog_defs m0 (fun _ _ => 0) := by
  obtain ⟨m', ha, _, _, hf⟩ := Genv.alloc_globals_spec_w (A := Archi.aarch64) (globalenv p)
    p.prog_defs Mem.empty (fun g hg => defOk_shape (hdefs g hg))
  have : m0 = m' := by
    simp only [init_mem] at h
    rw [ha] at h
    cases h
    rfl
  subst this
  obtain ⟨_, _, hext⟩ := alloc_globals_access (A := Archi.aarch64) (globalenv p) p.prog_defs
    Mem.empty m0 ha
  intro x n b hd hs
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hd
  have hsk := (Genv.find_add_globals_idx (Genv.empty_genv p.prog_public) p.prog_defs hn k hk).1
  rw [e] at hsk
  simp only [globalenv] at hs
  rw [hsk] at hs
  cases hs
  change ArrHolds m0 (Mem.empty.nextblock + k) (8 * n) _
  have hif := hf k hk ⟨tarrL n, [.Init_space (8 * n)], false, false⟩ (by rw [e])
  have hx := hext k hk ⟨tarrL n, [.Init_space (8 * n)], false, false⟩ (by rw [e])
  have hsz : init_data_list_size Archi.aarch64 [.Init_space (8 * n)] = max (8 * n) 0 := by
    simp [init_data_list_size, init_data_size]
  refine ⟨fun i kd pr hp => ?_, fun i _ _ => by simp, fun i h0 h1 => ?_⟩
  · have hne : m0.mem_access (Mem.empty.nextblock + k) i kd ≠ none := by
      intro hnone
      unfold Mem.perm Mem.perm_order' at hp
      rw [hnone] at hp
      exact hp
    have := hx i kd hne
    simp only [hsz] at this
    omega
  · have := (hif.2.2 (8 * n) rfl i.toNat (by omega)).1
    rw [Int.toNat_of_nonneg h0] at this
    rw [this]
    rfl

/-- The initial state of N for a program whose definitions `progOk` accepts. -/
theorem ninit_of {defs : Defs} (hnd : (defs.map (·.1)).Nodup)
    (hdefs : ∀ d ∈ defs, defOk d.2 = true) : ninit defs (initVal defs) (fun _ _ => 0) := by
  refine .ni_intro defs _ _ (norepet_defs_of hnd) ?_ ?_ (fun _ _ _ _ _ _ => rfl)
  · intro x ty init ro vol hd
    exact varOk_init (v := ⟨ty, init, ro, vol⟩) (hdefs _ (mem_of_in_defs hd))
  · intro x ty init hd hsc
    have hd := mem_of_in_defs hd
    have hlk := lookup_of_mem hnd hd
    rcases varOk_scalar (hdefs _ hd) hsc with
      ⟨rfl, n, rfl⟩ | ⟨rfl, n, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.Vint n, .gi_ui n, by simp [initVal, hlk]⟩
    · exact ⟨.Vlong n, .gi_ul n, by simp [initVal, hlk]⟩
    · exact ⟨_, .gi_d, by simp [initVal, hlk]⟩
    · exact ⟨_, .gi_f, by simp [initVal, hlk]⟩

/-- The function `main` of a program whose definitions `progOk` accepts, called from
`init_mem`'s memory, with the facts that N's judgments of whole programs take. -/
theorem main_facts {p : program function} {S : List ident}
    (hok : progOk p.prog_defs p.prog_main S = true) {b : block} {fd : fundef function}
    (hs : Genv.find_symbol (globalenv p) p.prog_main = some b)
    (hf : Genv.find_funct_ptr (globalenv p) b = some fd)
    (hty : type_of_fundef fd = .Tfunction [] type_int32s cc_default) :
    ∃ f, fd = .Internal f ∧ GenvOk (globalenv p) p.prog_defs ∧ FunsOk p.prog_defs S ∧
      (∀ d ∈ p.prog_defs, defOk d.2 = true) ∧ (p.prog_defs.map (·.1)).Nodup ∧
      f.fn_vars = [] ∧ f.fn_params = [] ∧ f.fn_return = tsi ∧ SOk p.prog_defs S tsi f.fn_body ∧
      in_defs p.prog_defs p.prog_main
        (.Gfun (.Internal ⟨tsi, cc_default, [], [], f.fn_temps, f.fn_body⟩)) := by
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
  subst hfd
  simp only [type_of_fundef, type_of_function] at hty
  injection hty with hpar hret hcc
  have hpn : f.fn_params = [] := by
    cases h' : f.fn_params with
    | nil => rfl
    | cons _ _ => simp [h', type_of_params] at hpar
  rw [hret] at hbody
  rw [fun_eta f hvars, hpn, hret, hcc] at hdf
  exact ⟨f, rfl, hge, hS, hdefs, hnd, hvars, hpn, hret, hbody, in_defs_of_mem hdf⟩

/-- The copy's execution of a program whose definitions, `main`, and functions `S` `progOk`
accepts is an execution of N. -/
theorem program_to_n {X : ExtSem} {p : program function} {t : trace} {r : int} (S : List ident)
    (hok : progOk p.prog_defs p.prog_main S = true)
    (h : bigstep_program_terminates Archi.aarch64 X p t r) : nprog p.prog_defs p.prog_main t r := by
  obtain ⟨b, fd, m0, m1, t, r, hinit, hs, hf, hty, hcall⟩ := h
  obtain ⟨f, rfl, hge, hS, hdefs, hnd, hvars, hpn, hret, hbody, hmain⟩ := main_facts hok hs hf hty
  obtain ⟨ln0, ln1, ln2, gv2, mb2, out, hu, hb, _, _, hx, hres, _, _, _⟩ :=
    call_to_n hge hS hcall rfl hvars (hret ▸ hbody) (fun _ h => by cases h)
      (grel_init hnd hdefs hinit) (mrel_init hnd hdefs hinit)
  rw [hpn] at hb
  cases hb
  rw [hret] at hres
  exact .np_intro p.prog_defs p.prog_main f.fn_temps f.fn_body (initVal p.prog_defs)
    (fun _ _ => 0) ln0 t ln2 gv2 mb2 out r (ninit_of hnd hdefs) hmain hu hx hres

/-! ## Programs that run forever -/

theorem loop_in_of {s init body post : statement} (h : LoopEntry s init body post) :
    loop_in s init body post := by
  induction h with
  | loop b q => exact .li_loop b q
  | seq_after rest _ ih => exact .li_after _ _ _ _ rest ih
  | seq_before pre _ ih => exact .li_before _ _ _ _ pre ih

theorem loopEntry_sok {defs : Defs} {S : List ident} {ret : type}
    {s init body post : statement} (h : LoopEntry s init body post) :
    SOk defs S ret s → SOk defs S ret init ∧ SOk defs S ret body ∧ SOk defs S ret post := by
  induction h with
  | loop b q =>
      intro hs
      cases hs with
      | loop _ _ h1 h2 => exact ⟨.skip, h1, h2⟩
  | seq_after rest _ ih =>
      intro hs
      cases hs with
      | seq _ _ h1 _ => exact ih h1
  | seq_before pre _ ih =>
      intro hs
      cases hs with
      | seq _ _ h1 h2 =>
          obtain ⟨a, b, c⟩ := ih h2
          exact ⟨.seq _ _ h1 a, b, c⟩

/-- The copy's judgment of a `main` that runs forever, for a program whose definitions, `main`,
and functions `S` `progOk` accepts, is N's. -/
theorem reacts_to_n {X : ExtSem} {p : program function} {t0 : trace} {W : Nat → trace}
    (S : List ident) (hok : progOk p.prog_defs p.prog_main S = true)
    (h : LoopReacts Archi.aarch64 X p t0 W) : nreacts p.prog_defs p.prog_main t0 W := by
  obtain ⟨hne, b, f, m0, m1, e, le0, init, body, post, Inv, hinit, hs, hf, hty, hl, hentry,
    ⟨le, m, hx0, hi0⟩, hstep⟩ := h
  obtain ⟨f', hff, hge, hS, hdefs, hnd, hvars, hpn, _, hbody, hmain⟩ :=
    main_facts (fd := .Internal f) hok hs hf hty
  injection hff with hff
  subst hff
  obtain ⟨he, hm1, _, _, hbind⟩ := entry_facts hentry
  subst he hm1
  rw [hpn] at hbind
  cases hbind
  obtain ⟨hi, hb, hp⟩ := loopEntry_sok hl hbody
  let ge := globalenv p
  let InvN : Nat → (ident → Option val) → (ident → Option val) → (ident → Int → Int) → Prop :=
    fun n ln gv mb => ∃ le m, Inv n le m ∧ TempsRel le ln ∧ NoPtr ln ∧ GRel ge p.prog_defs m gv ∧
      MRel ge p.prog_defs m mb
  obtain ⟨ln, gv, mb, nx, htr, hp1, hg, hm, _⟩ := exec_to_n hge hS hx0 rfl hi (fun _ => rfl)
    (noptr_undef _) (grel_init hnd hdefs hinit) (mrel_init hnd hdefs hinit)
  refine .nr_intro p.prog_defs p.prog_main f.fn_temps f.fn_body (initVal p.prog_defs)
    (fun _ _ => 0) _ init body post t0 W InvN (fun n hn => hne n hn) (ninit_of hnd hdefs) hmain
    (undef_temps_of f.fn_temps) (loop_in_of hl) ⟨ln, gv, mb, nx, le, m, hi0, htr, hp1, hg, hm⟩ ?_
  rintro n ln gv mb ⟨le, m, hinv, htr, hp1, hg, hm⟩
  obtain ⟨le', m', hx, hi'⟩ := hstep n le m hinv
  obtain ⟨ln', gv', mb', nx, htr', hp', hg', hm', _⟩ :=
    exec_to_n hge hS hx rfl (.seq _ _ hb hp) htr hp1 hg hm
  exact ⟨ln', gv', mb', nx, le', m', hi', htr', hp', hg', hm'⟩

end ClightN.Proof
