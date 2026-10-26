import LeanExe.Native.Clight.Memory

/-!
The C types of CompCert 3.18's `cfrontend/Ctypes.v`, the operations on them that the semantics
uses, function definitions, and programs.  The programs of this copy declare no struct or union,
so the composite environment is empty, and `sizeof` returns for a struct or union what
`Ctypes.v` returns for one the environment lacks.  `Tfunction` holds a `List type`, which makes
`type` a nested inductive type; Lean derives no decidable equality for it, so `type_beq` and its
lemma supply one.
-/

namespace LClight

inductive signedness where
  | Signed | Unsigned
  deriving Repr, DecidableEq

inductive intsize where
  | I8 | I16 | I32 | IBool
  deriving Repr, DecidableEq

inductive floatsize where
  | F32 | F64
  deriving Repr, DecidableEq

/-- `attr`: `attr_alignas` is the logarithm of the required alignment. -/
structure attr where
  attr_volatile : Bool
  attr_alignas : Option Nat
  deriving Repr, DecidableEq

def noattr : attr := { attr_volatile := false, attr_alignas := none }

inductive type where
  | Tvoid
  | Tint (sz : intsize) (sg : signedness) (a : attr)
  | Tlong (sg : signedness) (a : attr)
  | Tfloat (sz : floatsize) (a : attr)
  | Tpointer (t : type) (a : attr)
  | Tarray (t : type) (n : _root_.Int) (a : attr)
  | Tfunction (args : List type) (res : type) (cc : calling_convention)
  | Tstruct (id : ident) (a : attr)
  | Tunion (id : ident) (a : attr)
  deriving Repr, Inhabited

mutual
  def type_beq : type → type → Bool
    | .Tvoid, .Tvoid => true
    | .Tint s1 g1 a1, .Tint s2 g2 a2 => s1 == s2 && g1 == g2 && a1 == a2
    | .Tlong g1 a1, .Tlong g2 a2 => g1 == g2 && a1 == a2
    | .Tfloat s1 a1, .Tfloat s2 a2 => s1 == s2 && a1 == a2
    | .Tpointer t1 a1, .Tpointer t2 a2 => type_beq t1 t2 && a1 == a2
    | .Tarray t1 n1 a1, .Tarray t2 n2 a2 => type_beq t1 t2 && n1 == n2 && a1 == a2
    | .Tfunction l1 r1 c1, .Tfunction l2 r2 c2 => typelist_beq l1 l2 && type_beq r1 r2 && c1 == c2
    | .Tstruct i1 a1, .Tstruct i2 a2 => i1 == i2 && a1 == a2
    | .Tunion i1 a1, .Tunion i2 a2 => i1 == i2 && a1 == a2
    | _, _ => false

  def typelist_beq : List type → List type → Bool
    | [], [] => true
    | t1 :: l1, t2 :: l2 => type_beq t1 t2 && typelist_beq l1 l2
    | _, _ => false
end

mutual
  theorem type_beq_eq : (t1 t2 : type) → type_beq t1 t2 = true → t1 = t2
    | .Tvoid, t2, h => by cases t2 <;> simp_all [type_beq]
    | .Tint s1 g1 a1, t2, h => by cases t2 <;> simp_all [type_beq]
    | .Tlong g1 a1, t2, h => by cases t2 <;> simp_all [type_beq]
    | .Tfloat s1 a1, t2, h => by cases t2 <;> simp_all [type_beq]
    | .Tpointer t1 a1, t2, h => by
        cases t2 with
        | Tpointer t2 a2 =>
            simp only [type_beq, Bool.and_eq_true, beq_iff_eq] at h
            rw [type_beq_eq t1 t2 h.1, h.2]
        | _ => simp [type_beq] at h
    | .Tarray t1 n1 a1, t2, h => by
        cases t2 with
        | Tarray t2 n2 a2 =>
            simp only [type_beq, Bool.and_eq_true, beq_iff_eq] at h
            rw [type_beq_eq t1 t2 h.1.1, h.1.2, h.2]
        | _ => simp [type_beq] at h
    | .Tfunction l1 r1 c1, t2, h => by
        cases t2 with
        | Tfunction l2 r2 c2 =>
            simp only [type_beq, Bool.and_eq_true, beq_iff_eq] at h
            rw [typelist_beq_eq l1 l2 h.1.1, type_beq_eq r1 r2 h.1.2, h.2]
        | _ => simp [type_beq] at h
    | .Tstruct i1 a1, t2, h => by cases t2 <;> simp_all [type_beq]
    | .Tunion i1 a1, t2, h => by cases t2 <;> simp_all [type_beq]

  theorem typelist_beq_eq : (l1 l2 : List type) → typelist_beq l1 l2 = true → l1 = l2
    | [], [], _ => rfl
    | t1 :: l1, t2 :: l2, h => by
        simp only [typelist_beq, Bool.and_eq_true] at h
        rw [type_beq_eq t1 t2 h.1, typelist_beq_eq l1 l2 h.2]
    | [], _ :: _, h => by simp [typelist_beq] at h
    | _ :: _, [], h => by simp [typelist_beq] at h
end

mutual
  theorem type_beq_refl : (t : type) → type_beq t t = true
    | .Tvoid => rfl
    | .Tint _ _ _ => by simp [type_beq]
    | .Tlong _ _ => by simp [type_beq]
    | .Tfloat _ _ => by simp [type_beq]
    | .Tpointer t _ => by simp [type_beq, type_beq_refl t]
    | .Tarray t _ _ => by simp [type_beq, type_beq_refl t]
    | .Tfunction l r _ => by simp [type_beq, typelist_beq_refl l, type_beq_refl r]
    | .Tstruct _ _ => by simp [type_beq]
    | .Tunion _ _ => by simp [type_beq]

  theorem typelist_beq_refl : (l : List type) → typelist_beq l l = true
    | [] => rfl
    | t :: l => by simp [typelist_beq, type_beq_refl t, typelist_beq_refl l]
end

instance : DecidableEq type := fun t1 t2 =>
  if h : type_beq t1 t2 = true then isTrue (type_beq_eq t1 t2 h)
  else isFalse (fun e => by subst e; exact h (type_beq_refl t1))

def type_int32s : type := .Tint .I32 .Signed noattr

def attr_of_type : type → attr
  | .Tvoid => noattr
  | .Tint _ _ a => a
  | .Tlong _ a => a
  | .Tfloat _ a => a
  | .Tpointer _ a => a
  | .Tarray _ _ a => a
  | .Tfunction _ _ _ => noattr
  | .Tstruct _ a => a
  | .Tunion _ a => a

def change_attributes (f : attr → attr) (ty : type) : type :=
  match ty with
  | .Tvoid => ty
  | .Tint sz si a => .Tint sz si (f a)
  | .Tlong si a => .Tlong si (f a)
  | .Tfloat sz a => .Tfloat sz (f a)
  | .Tpointer elt a => .Tpointer elt (f a)
  | .Tarray elt sz a => .Tarray elt sz (f a)
  | .Tfunction _ _ _ => ty
  | .Tstruct id a => .Tstruct id (f a)
  | .Tunion id a => .Tunion id (f a)

def remove_attributes (ty : type) : type := change_attributes (fun _ => noattr) ty

/-- The usual unary conversion. -/
def typeconv (ty : type) : type :=
  match ty with
  | .Tint .I8 _ _ | .Tint .I16 _ _ | .Tint .IBool _ _ => .Tint .I32 .Signed noattr
  | .Tarray t _ _ => .Tpointer t noattr
  | .Tfunction _ _ _ => .Tpointer ty noattr
  | _ => remove_attributes ty

/-- `sizeof` with an empty composite environment and `Archi.ptr64` true. -/
def sizeof : type → _root_.Int
  | .Tvoid => 1
  | .Tint .I8 _ _ => 1
  | .Tint .I16 _ _ => 2
  | .Tint .I32 _ _ => 4
  | .Tint .IBool _ _ => 1
  | .Tlong _ _ => 8
  | .Tfloat .F32 _ => 4
  | .Tfloat .F64 _ => 8
  | .Tpointer _ _ => 8
  | .Tarray t' n _ => sizeof t' * max 0 n
  | .Tfunction _ _ _ => 1
  | .Tstruct _ _ => 0
  | .Tunion _ _ => 0

inductive mode where
  | By_value (chunk : memory_chunk)
  | By_reference
  | By_copy
  | By_nothing
  deriving Repr, DecidableEq

def access_mode : type → mode
  | .Tint .I8 .Signed _ => .By_value .Mint8signed
  | .Tint .I8 .Unsigned _ => .By_value .Mint8unsigned
  | .Tint .I16 .Signed _ => .By_value .Mint16signed
  | .Tint .I16 .Unsigned _ => .By_value .Mint16unsigned
  | .Tint .I32 _ _ => .By_value .Mint32
  | .Tint .IBool _ _ => .By_value .Mbool
  | .Tlong _ _ => .By_value .Mint64
  | .Tfloat .F32 _ => .By_value .Mfloat32
  | .Tfloat .F64 _ => .By_value .Mfloat64
  | .Tvoid => .By_nothing
  | .Tpointer _ _ => .By_value Mptr
  | .Tarray _ _ _ => .By_reference
  | .Tfunction _ _ _ => .By_reference
  | .Tstruct _ _ => .By_copy
  | .Tunion _ _ => .By_copy

/-- `bitfield`: the access mode of a struct or union member. -/
inductive bitfield where
  | Full
  | Bits (sz : intsize) (sg : signedness) (pos width : _root_.Int)
  deriving Repr, DecidableEq

def type_of_params (params : List (ident × type)) : List type := params.map (·.2)

/-- `Ctypes.fundef`. -/
inductive fundef (F : Type) where
  | Internal (f : F)
  | External (ef : external_function) (targs : List type) (tres : type)
      (cc : calling_convention)
  deriving Repr

/-- `Ctypes.program` without composite definitions: `prog_types` is empty and
`prog_comp_env` is the empty environment. -/
structure program (F : Type) where
  prog_defs : List (ident × globdef (fundef F) type)
  prog_public : List ident
  prog_main : ident
  deriving Repr

end LClight
