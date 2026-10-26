import LeanExe.Native.Clight.Ctypes

/-!
The operators of Clight, from CompCert 3.18's `cfrontend/Cop.v`, with `Archi.ptr64` true and an
empty composite environment, which `sizeof` assumes.  The floating-point operations take the NaN
parameters `A : Archi`.  The comparison of two pointers, or of a pointer and an integer, has no
result (`cmp_ptr`, which needs `Val.cmplu_bool`).  `classify_switch` and `sem_switch_arg`, which
only `Sswitch` uses, and the bit-field accesses `load_bitfield` and `store_bitfield`, which only
the members of structs and unions use, are omitted.  The rest of `Cop.v` that Clight uses is
copied.
-/

namespace LClight

inductive unary_operation where
  | Onotbool | Onotint | Oneg | Oabsfloat
  deriving Repr, DecidableEq

inductive binary_operation where
  | Oadd | Osub | Omul | Odiv | Omod | Oand | Oor | Oxor | Oshl | Oshr
  | Oeq | One | Olt | Ogt | Ole | Oge
  deriving Repr, DecidableEq

/-! ## Casts and truth values -/

inductive classify_cast_cases where
  | cast_case_pointer
  | cast_case_i2i (sz2 : intsize) (si2 : signedness)
  | cast_case_f2f
  | cast_case_s2s
  | cast_case_f2s
  | cast_case_s2f
  | cast_case_i2f (si1 : signedness)
  | cast_case_i2s (si1 : signedness)
  | cast_case_f2i (sz2 : intsize) (si2 : signedness)
  | cast_case_s2i (sz2 : intsize) (si2 : signedness)
  | cast_case_l2l
  | cast_case_i2l (si1 : signedness)
  | cast_case_l2i (sz2 : intsize) (si2 : signedness)
  | cast_case_l2f (si1 : signedness)
  | cast_case_l2s (si1 : signedness)
  | cast_case_f2l (si2 : signedness)
  | cast_case_s2l (si2 : signedness)
  | cast_case_i2bool
  | cast_case_l2bool
  | cast_case_f2bool
  | cast_case_s2bool
  | cast_case_struct (id1 id2 : ident)
  | cast_case_union (id1 id2 : ident)
  | cast_case_void
  | cast_case_default
  deriving Repr, DecidableEq

def classify_cast (tfrom tto : type) : classify_cast_cases :=
  match tto, tfrom with
  | .Tvoid, _ => .cast_case_void
  | .Tint sz2 si2 _, .Tint _ _ _ =>
      match sz2 with
      | .IBool => .cast_case_i2bool
      | _ => .cast_case_i2i sz2 si2
  | .Tint sz2 si2 _, .Tlong _ _ =>
      if sz2 = .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F64 _ =>
      if sz2 = .IBool then .cast_case_f2bool else .cast_case_f2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F32 _ =>
      if sz2 = .IBool then .cast_case_s2bool else .cast_case_s2i sz2 si2
  | .Tint sz2 si2 _, .Tpointer _ _ | .Tint sz2 si2 _, .Tarray _ _ _
  | .Tint sz2 si2 _, .Tfunction _ _ _ =>
      if sz2 = .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
  | .Tlong _ _, .Tlong _ _ => .cast_case_pointer
  | .Tlong _ _, .Tint _ si1 _ => .cast_case_i2l si1
  | .Tlong si2 _, .Tfloat .F64 _ => .cast_case_f2l si2
  | .Tlong si2 _, .Tfloat .F32 _ => .cast_case_s2l si2
  | .Tlong _ _, .Tpointer _ _ | .Tlong _ _, .Tarray _ _ _ | .Tlong _ _, .Tfunction _ _ _ =>
      .cast_case_pointer
  | .Tfloat .F64 _, .Tint _ si1 _ => .cast_case_i2f si1
  | .Tfloat .F32 _, .Tint _ si1 _ => .cast_case_i2s si1
  | .Tfloat .F64 _, .Tlong si1 _ => .cast_case_l2f si1
  | .Tfloat .F32 _, .Tlong si1 _ => .cast_case_l2s si1
  | .Tfloat .F64 _, .Tfloat .F64 _ => .cast_case_f2f
  | .Tfloat .F32 _, .Tfloat .F32 _ => .cast_case_s2s
  | .Tfloat .F64 _, .Tfloat .F32 _ => .cast_case_s2f
  | .Tfloat .F32 _, .Tfloat .F64 _ => .cast_case_f2s
  | .Tpointer _ _, .Tint _ si _ => .cast_case_i2l si
  | .Tpointer _ _, .Tlong _ _ => .cast_case_pointer
  | .Tpointer _ _, .Tpointer _ _ | .Tpointer _ _, .Tarray _ _ _
  | .Tpointer _ _, .Tfunction _ _ _ => .cast_case_pointer
  | .Tstruct id2 _, .Tstruct id1 _ => .cast_case_struct id1 id2
  | .Tunion id2 _, .Tunion id1 _ => .cast_case_union id1 id2
  | _, _ => .cast_case_default

def cast_int_int (sz : intsize) (sg : signedness) (i : int) : int :=
  match sz, sg with
  | .I8, .Signed => Int.sign_ext 8 i
  | .I8, .Unsigned => Int.zero_ext 8 i
  | .I16, .Signed => Int.sign_ext 16 i
  | .I16, .Unsigned => Int.zero_ext 16 i
  | .I32, _ => i
  | .IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one

def cast_int_float (si : signedness) (i : int) : float :=
  match si with
  | .Signed => Float.of_int i
  | .Unsigned => Float.of_intu i

def cast_float_int (si : signedness) (f : float) : Option int :=
  match si with
  | .Signed => Float.to_int f
  | .Unsigned => Float.to_intu f

def cast_int_single (si : signedness) (i : int) : float32 :=
  match si with
  | .Signed => Float32.of_int i
  | .Unsigned => Float32.of_intu i

def cast_single_int (si : signedness) (f : float32) : Option int :=
  match si with
  | .Signed => Float32.to_int f
  | .Unsigned => Float32.to_intu f

def cast_int_long (si : signedness) (i : int) : int64 :=
  match si with
  | .Signed => Int64.repr (Int.signed i)
  | .Unsigned => Int64.repr (Int.unsigned i)

def cast_long_float (si : signedness) (i : int64) : float :=
  match si with
  | .Signed => Float.of_long i
  | .Unsigned => Float.of_longu i

def cast_long_single (si : signedness) (i : int64) : float32 :=
  match si with
  | .Signed => Float32.of_long i
  | .Unsigned => Float32.of_longu i

def cast_float_long (si : signedness) (f : float) : Option int64 :=
  match si with
  | .Signed => Float.to_long f
  | .Unsigned => Float.to_longu f

def cast_single_long (si : signedness) (f : float32) : Option int64 :=
  match si with
  | .Signed => Float32.to_long f
  | .Unsigned => Float32.to_longu f

def sem_cast (v : val) (t1 t2 : type) (m : mem) : Option val :=
  match classify_cast t1 t2 with
  | .cast_case_pointer =>
      match v with
      | .Vptr _ _ => some v
      | .Vint _ => none
      | .Vlong _ => some v
      | _ => none
  | .cast_case_i2i sz2 si2 =>
      match v with
      | .Vint i => some (.Vint (cast_int_int sz2 si2 i))
      | _ => none
  | .cast_case_f2f =>
      match v with
      | .Vfloat f => some (.Vfloat f)
      | _ => none
  | .cast_case_s2s =>
      match v with
      | .Vsingle f => some (.Vsingle f)
      | _ => none
  | .cast_case_s2f =>
      match v with
      | .Vsingle f => some (.Vfloat (Float.of_single f))
      | _ => none
  | .cast_case_f2s =>
      match v with
      | .Vfloat f => some (.Vsingle (Float.to_single f))
      | _ => none
  | .cast_case_i2f si1 =>
      match v with
      | .Vint i => some (.Vfloat (cast_int_float si1 i))
      | _ => none
  | .cast_case_i2s si1 =>
      match v with
      | .Vint i => some (.Vsingle (cast_int_single si1 i))
      | _ => none
  | .cast_case_f2i sz2 si2 =>
      match v with
      | .Vfloat f =>
          match cast_float_int si2 f with
          | some i => some (.Vint (cast_int_int sz2 si2 i))
          | none => none
      | _ => none
  | .cast_case_s2i sz2 si2 =>
      match v with
      | .Vsingle f =>
          match cast_single_int si2 f with
          | some i => some (.Vint (cast_int_int sz2 si2 i))
          | none => none
      | _ => none
  | .cast_case_i2bool =>
      match v with
      | .Vint n => some (.Vint (if Int.eq n Int.zero then Int.zero else Int.one))
      | .Vptr _ _ => none
      | _ => none
  | .cast_case_l2bool =>
      match v with
      | .Vlong n => some (.Vint (if Int64.eq n Int64.zero then Int.zero else Int.one))
      | .Vptr b ofs => if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_f2bool =>
      match v with
      | .Vfloat f => some (.Vint (if Float.cmp .Ceq f Float.zero then Int.zero else Int.one))
      | _ => none
  | .cast_case_s2bool =>
      match v with
      | .Vsingle f => some (.Vint (if Float32.cmp .Ceq f Float32.zero then Int.zero else Int.one))
      | _ => none
  | .cast_case_l2l =>
      match v with
      | .Vlong n => some (.Vlong n)
      | _ => none
  | .cast_case_i2l si =>
      match v with
      | .Vint n => some (.Vlong (cast_int_long si n))
      | _ => none
  | .cast_case_l2i sz si =>
      match v with
      | .Vlong n => some (.Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => none
  | .cast_case_l2f si1 =>
      match v with
      | .Vlong i => some (.Vfloat (cast_long_float si1 i))
      | _ => none
  | .cast_case_l2s si1 =>
      match v with
      | .Vlong i => some (.Vsingle (cast_long_single si1 i))
      | _ => none
  | .cast_case_f2l si2 =>
      match v with
      | .Vfloat f =>
          match cast_float_long si2 f with
          | some i => some (.Vlong i)
          | none => none
      | _ => none
  | .cast_case_s2l si2 =>
      match v with
      | .Vsingle f =>
          match cast_single_long si2 f with
          | some i => some (.Vlong i)
          | none => none
      | _ => none
  | .cast_case_struct id1 id2 =>
      match v with
      | .Vptr _ _ => if id1 = id2 then some v else none
      | _ => none
  | .cast_case_union id1 id2 =>
      match v with
      | .Vptr _ _ => if id1 = id2 then some v else none
      | _ => none
  | .cast_case_void => some v
  | .cast_case_default => none

inductive classify_bool_cases where
  | bool_case_i | bool_case_l | bool_case_f | bool_case_s | bool_default
  deriving Repr, DecidableEq

def classify_bool (ty : type) : classify_bool_cases :=
  match typeconv ty with
  | .Tint _ _ _ => .bool_case_i
  | .Tpointer _ _ => .bool_case_l
  | .Tfloat .F64 _ => .bool_case_f
  | .Tfloat .F32 _ => .bool_case_s
  | .Tlong _ _ => .bool_case_l
  | _ => .bool_default

def bool_val (v : val) (t : type) (m : mem) : Option Bool :=
  match classify_bool t with
  | .bool_case_i =>
      match v with
      | .Vint n => some (!Int.eq n Int.zero)
      | .Vptr _ _ => none
      | _ => none
  | .bool_case_l =>
      match v with
      | .Vlong n => some (!Int64.eq n Int64.zero)
      | .Vptr b ofs => if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_f =>
      match v with
      | .Vfloat f => some (!Float.cmp .Ceq f Float.zero)
      | _ => none
  | .bool_case_s =>
      match v with
      | .Vsingle f => some (!Float32.cmp .Ceq f Float32.zero)
      | _ => none
  | .bool_default => none

/-! ## Unary operators -/

def sem_notbool (v : val) (ty : type) (m : mem) : Option val :=
  (bool_val v ty m).map fun b => Val.of_bool (!b)

inductive classify_neg_cases where
  | neg_case_i (s : signedness) | neg_case_f | neg_case_s | neg_case_l (s : signedness)
  | neg_default
  deriving Repr, DecidableEq

def classify_neg (ty : type) : classify_neg_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .neg_case_i .Unsigned
  | .Tint _ _ _ => .neg_case_i .Signed
  | .Tfloat .F64 _ => .neg_case_f
  | .Tfloat .F32 _ => .neg_case_s
  | .Tlong si _ => .neg_case_l si
  | _ => .neg_default

def sem_neg (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i _ =>
      match v with
      | .Vint n => some (.Vint (Int.neg n))
      | _ => none
  | .neg_case_f =>
      match v with
      | .Vfloat f => some (.Vfloat (Float.neg f))
      | _ => none
  | .neg_case_s =>
      match v with
      | .Vsingle f => some (.Vsingle (Float32.neg f))
      | _ => none
  | .neg_case_l _ =>
      match v with
      | .Vlong n => some (.Vlong (Int64.neg n))
      | _ => none
  | .neg_default => none

def sem_absfloat (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i sg =>
      match v with
      | .Vint n => some (.Vfloat (Float.abs (cast_int_float sg n)))
      | _ => none
  | .neg_case_f =>
      match v with
      | .Vfloat f => some (.Vfloat (Float.abs f))
      | _ => none
  | .neg_case_s =>
      match v with
      | .Vsingle f => some (.Vfloat (Float.abs (Float.of_single f)))
      | _ => none
  | .neg_case_l sg =>
      match v with
      | .Vlong n => some (.Vfloat (Float.abs (cast_long_float sg n)))
      | _ => none
  | .neg_default => none

inductive classify_notint_cases where
  | notint_case_i (s : signedness) | notint_case_l (s : signedness) | notint_default
  deriving Repr, DecidableEq

def classify_notint (ty : type) : classify_notint_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .notint_case_i .Unsigned
  | .Tint _ _ _ => .notint_case_i .Signed
  | .Tlong si _ => .notint_case_l si
  | _ => .notint_default

def sem_notint (v : val) (ty : type) : Option val :=
  match classify_notint ty with
  | .notint_case_i _ =>
      match v with
      | .Vint n => some (.Vint (Int.not n))
      | _ => none
  | .notint_case_l _ =>
      match v with
      | .Vlong n => some (.Vlong (Int64.not n))
      | _ => none
  | .notint_default => none

/-! ## Binary operators -/

inductive binarith_cases where
  | bin_case_i (s : signedness) | bin_case_l (s : signedness) | bin_case_f | bin_case_s
  | bin_default
  deriving Repr, DecidableEq

def classify_binarith (ty1 ty2 : type) : binarith_cases :=
  match ty1, ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint .I32 .Unsigned _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .bin_case_i .Signed
  | .Tlong .Signed _, .Tlong .Signed _ => .bin_case_l .Signed
  | .Tlong _ _, .Tlong _ _ => .bin_case_l .Unsigned
  | .Tlong sg _, .Tint _ _ _ => .bin_case_l sg
  | .Tint _ _ _, .Tlong sg _ => .bin_case_l sg
  | .Tfloat .F32 _, .Tfloat .F32 _ => .bin_case_s
  | .Tfloat _ _, .Tfloat _ _ => .bin_case_f
  | .Tfloat .F64 _, .Tint _ _ _ | .Tfloat .F64 _, .Tlong _ _ => .bin_case_f
  | .Tint _ _ _, .Tfloat .F64 _ | .Tlong _ _, .Tfloat .F64 _ => .bin_case_f
  | .Tfloat .F32 _, .Tint _ _ _ | .Tfloat .F32 _, .Tlong _ _ => .bin_case_s
  | .Tint _ _ _, .Tfloat .F32 _ | .Tlong _ _, .Tfloat .F32 _ => .bin_case_s
  | _, _ => .bin_default

def binarith_type (c : binarith_cases) : type :=
  match c with
  | .bin_case_i sg => .Tint .I32 sg noattr
  | .bin_case_l sg => .Tlong sg noattr
  | .bin_case_f => .Tfloat .F64 noattr
  | .bin_case_s => .Tfloat .F32 noattr
  | .bin_default => .Tvoid

def sem_binarith
    (sem_int : signedness → int → int → Option val)
    (sem_long : signedness → int64 → int64 → Option val)
    (sem_float : float → float → Option val)
    (sem_single : float32 → float32 → Option val)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  let c := classify_binarith t1 t2
  let t := binarith_type c
  match sem_cast v1 t1 t m, sem_cast v2 t2 t m with
  | some v1', some v2' =>
      match c with
      | .bin_case_i sg =>
          match v1', v2' with
          | .Vint n1, .Vint n2 => sem_int sg n1 n2
          | _, _ => none
      | .bin_case_f =>
          match v1', v2' with
          | .Vfloat n1, .Vfloat n2 => sem_float n1 n2
          | _, _ => none
      | .bin_case_s =>
          match v1', v2' with
          | .Vsingle n1, .Vsingle n2 => sem_single n1 n2
          | _, _ => none
      | .bin_case_l sg =>
          match v1', v2' with
          | .Vlong n1, .Vlong n2 => sem_long sg n1 n2
          | _, _ => none
      | .bin_default => none
  | _, _ => none

inductive classify_add_cases where
  | add_case_pi (ty : type) (si : signedness)
  | add_case_pl (ty : type)
  | add_case_ip (si : signedness) (ty : type)
  | add_case_lp (ty : type)
  | add_default

def classify_add (ty1 ty2 : type) : classify_add_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .add_case_pi ty si
  | .Tpointer ty _, .Tlong _ _ => .add_case_pl ty
  | .Tint _ si _, .Tpointer ty _ => .add_case_ip si ty
  | .Tlong _ _, .Tpointer ty _ => .add_case_lp ty
  | _, _ => .add_default

def ptrofs_of_int (si : signedness) (n : int) : ptrofs :=
  match si with
  | .Signed => Ptrofs.of_ints n
  | .Unsigned => Ptrofs.of_intu n

def sem_add_ptr_int (ty : type) (si : signedness) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vint n2 =>
      let n2 := ptrofs_of_int si n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
  | .Vint _, .Vint _ => none
  | .Vlong n1, .Vint n2 =>
      let n2 := cast_int_long si n2
      some (.Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof ty)) n2)))
  | _, _ => none

def sem_add_ptr_long (ty : type) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vlong n2 =>
      let n2 := Ptrofs.of_int64 n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
  | .Vint _, .Vlong _ => none
  | .Vlong n1, .Vlong n2 => some (.Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof ty)) n2)))
  | _, _ => none

def sem_add (A : Archi) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_add t1 t2 with
  | .add_case_pi ty si => sem_add_ptr_int ty si v1 v2
  | .add_case_pl ty => sem_add_ptr_long ty v1 v2
  | .add_case_ip si ty => sem_add_ptr_int ty si v2 v1
  | .add_case_lp ty => sem_add_ptr_long ty v2 v1
  | .add_default =>
      sem_binarith
        (fun _ n1 n2 => some (.Vint (Int.add n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Int64.add n1 n2)))
        (fun n1 n2 => some (.Vfloat (Float.add A n1 n2)))
        (fun n1 n2 => some (.Vsingle (Float32.add A n1 n2)))
        v1 t1 v2 t2 m

inductive classify_sub_cases where
  | sub_case_pi (ty : type) (si : signedness)
  | sub_case_pp (ty : type)
  | sub_case_pl (ty : type)
  | sub_default

def classify_sub (ty1 ty2 : type) : classify_sub_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .sub_case_pi ty si
  | .Tpointer ty _, .Tpointer _ _ => .sub_case_pp ty
  | .Tpointer ty _, .Tlong _ _ => .sub_case_pl ty
  | _, _ => .sub_default

def sem_sub (A : Archi) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_sub t1 t2 with
  | .sub_case_pi ty si =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vint n2 =>
          let n2 := ptrofs_of_int si n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
      | .Vint _, .Vint _ => none
      | .Vlong n1, .Vint n2 =>
          let n2 := cast_int_long si n2
          some (.Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ty)) n2)))
      | _, _ => none
  | .sub_case_pl ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
      | .Vint _, .Vlong _ => none
      | .Vlong n1, .Vlong n2 =>
          some (.Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ty)) n2)))
      | _, _ => none
  | .sub_case_pp ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
          if b1 = b2 then
            let sz := sizeof ty
            if 0 < sz ∧ sz ≤ Ptrofs.max_signed then
              some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else none
          else none
      | _, _ => none
  | .sub_default =>
      sem_binarith
        (fun _ n1 n2 => some (.Vint (Int.sub n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Int64.sub n1 n2)))
        (fun n1 n2 => some (.Vfloat (Float.sub A n1 n2)))
        (fun n1 n2 => some (.Vsingle (Float32.sub A n1 n2)))
        v1 t1 v2 t2 m

def sem_mul (A : Archi) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (Int.mul n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Int64.mul n1 n2)))
    (fun n1 n2 => some (.Vfloat (Float.mul A n1 n2)))
    (fun n1 n2 => some (.Vsingle (Float32.mul A n1 n2)))
    v1 t1 v2 t2 m

def sem_div (A : Archi) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Int.eq n2 Int.zero || (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone)
          then none else some (.Vint (Int.divs n1 n2))
      | .Unsigned =>
          if Int.eq n2 Int.zero then none else some (.Vint (Int.divu n1 n2)))
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Int64.eq n2 Int64.zero ||
              (Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone)
          then none else some (.Vlong (Int64.divs n1 n2))
      | .Unsigned =>
          if Int64.eq n2 Int64.zero then none else some (.Vlong (Int64.divu n1 n2)))
    (fun n1 n2 => some (.Vfloat (Float.div A n1 n2)))
    (fun n1 n2 => some (.Vsingle (Float32.div A n1 n2)))
    v1 t1 v2 t2 m

def sem_mod (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Int.eq n2 Int.zero || (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone)
          then none else some (.Vint (Int.mods n1 n2))
      | .Unsigned =>
          if Int.eq n2 Int.zero then none else some (.Vint (Int.modu n1 n2)))
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Int64.eq n2 Int64.zero ||
              (Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone)
          then none else some (.Vlong (Int64.mods n1 n2))
      | .Unsigned =>
          if Int64.eq n2 Int64.zero then none else some (.Vlong (Int64.modu n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

def sem_and (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (Int.and n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Int64.and n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

def sem_or (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (Int.or n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Int64.or n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

def sem_xor (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (Int.xor n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Int64.xor n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

inductive classify_shift_cases where
  | shift_case_ii (s : signedness) | shift_case_ll (s : signedness)
  | shift_case_il (s : signedness) | shift_case_li (s : signedness) | shift_default
  deriving Repr, DecidableEq

def classify_shift (ty1 ty2 : type) : classify_shift_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .shift_case_ii .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .shift_case_ii .Signed
  | .Tint .I32 .Unsigned _, .Tlong _ _ => .shift_case_il .Unsigned
  | .Tint _ _ _, .Tlong _ _ => .shift_case_il .Signed
  | .Tlong s _, .Tint _ _ _ => .shift_case_li s
  | .Tlong s _, .Tlong _ _ => .shift_case_ll s
  | _, _ => .shift_default

def sem_shift
    (sem_int : signedness → int → int → int)
    (sem_long : signedness → int64 → int64 → int64)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  match classify_shift t1 t2 with
  | .shift_case_ii sg =>
      match v1, v2 with
      | .Vint n1, .Vint n2 =>
          if Int.ltu n2 Int.iwordsize then some (.Vint (sem_int sg n1 n2)) else none
      | _, _ => none
  | .shift_case_il sg =>
      match v1, v2 with
      | .Vint n1, .Vlong n2 =>
          if Int64.ltu n2 (Int64.repr 32) then some (.Vint (sem_int sg n1 (Int64.loword n2)))
          else none
      | _, _ => none
  | .shift_case_li sg =>
      match v1, v2 with
      | .Vlong n1, .Vint n2 =>
          if Int.ltu n2 Int64.iwordsize' then
            some (.Vlong (sem_long sg n1 (Int64.repr (Int.unsigned n2))))
          else none
      | _, _ => none
  | .shift_case_ll sg =>
      match v1, v2 with
      | .Vlong n1, .Vlong n2 =>
          if Int64.ltu n2 Int64.iwordsize then some (.Vlong (sem_long sg n1 n2)) else none
      | _, _ => none
  | .shift_default => none

def sem_shl (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift (fun _ n1 n2 => Int.shl n1 n2) (fun _ n1 n2 => Int64.shl n1 n2) v1 t1 v2 t2

def sem_shr (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift
    (fun sg n1 n2 =>
      match sg with
      | .Signed => Int.shr n1 n2
      | .Unsigned => Int.shru n1 n2)
    (fun sg n1 n2 =>
      match sg with
      | .Signed => Int64.shr n1 n2
      | .Unsigned => Int64.shru n1 n2)
    v1 t1 v2 t2

inductive classify_cmp_cases where
  | cmp_case_pp | cmp_case_pi (si : signedness) | cmp_case_ip (si : signedness) | cmp_case_pl
  | cmp_case_lp | cmp_default
  deriving Repr, DecidableEq

def classify_cmp (ty1 ty2 : type) : classify_cmp_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer _ _, .Tpointer _ _ => .cmp_case_pp
  | .Tpointer _ _, .Tint _ si _ => .cmp_case_pi si
  | .Tint _ si _, .Tpointer _ _ => .cmp_case_ip si
  | .Tpointer _ _, .Tlong _ _ => .cmp_case_pl
  | .Tlong _ _, .Tpointer _ _ => .cmp_case_lp
  | _, _ => .cmp_default

/-- `sem_cmp`.  The five pointer cases call `cmp_ptr`, which the copy omits. -/
def sem_cmp (c : comparison) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) :
    Option val :=
  match classify_cmp t1 t2 with
  | .cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
          some (Val.of_bool (match sg with
            | .Signed => Int.cmp c n1 n2
            | .Unsigned => Int.cmpu c n1 n2)))
        (fun sg n1 n2 =>
          some (Val.of_bool (match sg with
            | .Signed => Int64.cmp c n1 n2
            | .Unsigned => Int64.cmpu c n1 n2)))
        (fun n1 n2 => some (Val.of_bool (Float.cmp c n1 n2)))
        (fun n1 n2 => some (Val.of_bool (Float32.cmp c n1 n2)))
        v1 t1 v2 t2 m
  | _ => none

inductive classify_fun_cases where
  | fun_case_f (targs : List type) (tres : type) (cc : calling_convention)
  | fun_default

def classify_fun (ty : type) : classify_fun_cases :=
  match ty with
  | .Tfunction args res cc => .fun_case_f args res cc
  | .Tpointer (.Tfunction args res cc) _ => .fun_case_f args res cc
  | _ => .fun_default

def sem_unary_operation (op : unary_operation) (v : val) (ty : type) (m : mem) : Option val :=
  match op with
  | .Onotbool => sem_notbool v ty m
  | .Onotint => sem_notint v ty
  | .Oneg => sem_neg v ty
  | .Oabsfloat => sem_absfloat v ty

def sem_binary_operation (A : Archi) (op : binary_operation) (v1 : val) (t1 : type) (v2 : val)
    (t2 : type) (m : mem) : Option val :=
  match op with
  | .Oadd => sem_add A v1 t1 v2 t2 m
  | .Osub => sem_sub A v1 t1 v2 t2 m
  | .Omul => sem_mul A v1 t1 v2 t2 m
  | .Omod => sem_mod v1 t1 v2 t2 m
  | .Odiv => sem_div A v1 t1 v2 t2 m
  | .Oand => sem_and v1 t1 v2 t2 m
  | .Oor => sem_or v1 t1 v2 t2 m
  | .Oxor => sem_xor v1 t1 v2 t2 m
  | .Oshl => sem_shl v1 t1 v2 t2
  | .Oshr => sem_shr v1 t1 v2 t2
  | .Oeq => sem_cmp .Ceq v1 t1 v2 t2 m
  | .One => sem_cmp .Cne v1 t1 v2 t2 m
  | .Olt => sem_cmp .Clt v1 t1 v2 t2 m
  | .Ogt => sem_cmp .Cgt v1 t1 v2 t2 m
  | .Ole => sem_cmp .Cle v1 t1 v2 t2 m
  | .Oge => sem_cmp .Cge v1 t1 v2 t2 m

end LClight
