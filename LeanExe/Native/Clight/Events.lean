/-
Derived from CompCert 3.18, the files `common/Events.v`, `common/Builtins0.v`, and
`common/Builtins.v`.  CompCert is Copyright Institut National de Recherche en Informatique et en
Automatique (INRIA) and AbsInt Angewandte Informatik GmbH, and its source files carry INRIA's
copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26 and 2026-10-27: transcribed from Coq into Lean, with the
changes that `LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import LeanExe.Native.Clight.Globalenvs

/-!
Events, traces, and the semantics of external calls, from CompCert 3.18's `common/Events.v`,
`common/Builtins0.v`, and `common/Builtins.v`.

CompCert leaves the semantics of an `EF_external` function to the parameter
`external_functions_sem`, and proves its compiler for every semantics that satisfies
`extcall_properties`.  `ExtSem` is that parameter here, without the hypothesis
`external_functions_properties` that CompCert states of it, so a theorem about the copy
corresponds to CompCert's compiler theorem only when it holds for every `ExtSem`, as the
theorems in this directory do.  `builtin_function` lists the three functions directly, where
`Builtins.v` nests them under `BI_standard`.  Of the built-in functions, the copy
gives meaning to `__builtin_fsqrt` and its alias `__builtin_sqrt`, `__builtin_fabs`, and
`__builtin_fabsf`, each at the signature of CompCert's table.  `EF_vstore` has the semantics of
`volatile_store_sem`, so a store to a volatile global is an output event, as in CompCert, and
`EF_vload` has the semantics of `volatile_load_sem`, so a load from a volatile global is an input
event whose value is any value of the access's type.  `eventval_match` omits the case
`ev_match_ptr`, so a volatile store of a pointer has no rule, and a volatile load returns no
pointer.  `external_call` takes the global environment, where CompCert takes a `Senv.t`, and
passes its symbol map to `ExtSem`.  Every other built-in, run-time function, `malloc`, `free`,
`memcpy`, annotation, inline assembly, and debug information has no rule.
-/

namespace LClight

inductive eventval where
  | EVint (i : int)
  | EVlong (i : int64)
  | EVfloat (f : float)
  | EVsingle (f : float32)
  | EVptr_global (id : ident) (ofs : ptrofs)
  deriving Repr, DecidableEq

inductive event where
  | Event_syscall (name : String) (args : List eventval) (res : eventval)
  | Event_vload (chunk : memory_chunk) (id : ident) (ofs : ptrofs) (v : eventval)
  | Event_vstore (chunk : memory_chunk) (id : ident) (ofs : ptrofs) (v : eventval)
  | Event_annot (text : String) (args : List eventval)
  deriving Repr, DecidableEq

abbrev trace := List event

def E0 : trace := []

/-- `external_functions_sem`: a relation from the symbol table, the arguments, and the memory to
a trace, a result, and a memory.  CompCert passes a `Senv.t`; the copy passes the map from
names to blocks, `genv_symb`. -/
structure ExtSem where
  external_functions_sem :
    String → signature → Std.TreeMap ident block → List val → mem → trace → val → mem → Prop

/-- The built-in functions that the copy gives meaning to. -/
inductive builtin_function where
  | BI_fabs | BI_fabsf | BI_fsqrt
  deriving Repr, DecidableEq

def builtin_function_sig : builtin_function → signature
  | .BI_fabs | .BI_fsqrt => { sig_args := [.Xfloat], sig_res := .Xfloat, sig_cc := cc_default }
  | .BI_fabsf => { sig_args := [.Xsingle], sig_res := .Xsingle, sig_cc := cc_default }

/-- The entries of `standard_builtin_table` for these functions, in the table's order. -/
def builtin_table : List (String × builtin_function) :=
  [("__builtin_fabs", .BI_fabs), ("__builtin_fabsf", .BI_fabsf),
   ("__builtin_fsqrt", .BI_fsqrt), ("__builtin_sqrt", .BI_fsqrt)]

/-- `lookup_builtin_function`, over the entries of `builtin_table`.  CompCert also searches the
rest of the standard table and the platform table; a name found there has no rule here. -/
def lookup_builtin_function (name : String) (sg : signature) : Option builtin_function :=
  (builtin_table.find? fun e => e.1 == name && builtin_function_sig e.2 == sg).map (·.2)

/-- `builtin_function_sem`, as `mkbuiltin_n1t` builds it: one argument, and `Vundef` when the
argument is not of the expected kind. -/
def builtin_function_sem (A : Archi) (bf : builtin_function) (vargs : List val) : Option val :=
  match bf, vargs with
  | .BI_fabs, [v] =>
      some (match v with
        | .Vfloat f => .Vfloat (Float.abs f)
        | _ => .Vundef)
  | .BI_fabsf, [v] =>
      some (match v with
        | .Vsingle f => .Vsingle (Float32.abs f)
        | _ => .Vundef)
  | .BI_fsqrt, [v] =>
      some (match v with
        | .Vfloat f => .Vfloat (Float.sqrt A f)
        | _ => .Vundef)
  | _, _ => none

/-- `known_builtin_sem`: no event, and the memory unchanged. -/
def known_builtin_sem (A : Archi) (bf : builtin_function) (vargs : List val) (m : mem)
    (t : trace) (vres : val) (m' : mem) : Prop :=
  builtin_function_sem A bf vargs = some vres ∧ t = E0 ∧ m' = m

/-- `eventval_match` (`Events.v`, lines 270 to 283) without `ev_match_ptr`. -/
inductive eventval_match : eventval → typ → val → Prop
  | ev_match_int (i : int) : eventval_match (.EVint i) .Tint (.Vint i)
  | ev_match_long (i : int64) : eventval_match (.EVlong i) .Tlong (.Vlong i)
  | ev_match_float (f : float) : eventval_match (.EVfloat f) .Tfloat (.Vfloat f)
  | ev_match_single (f : float32) : eventval_match (.EVsingle f) .Tsingle (.Vsingle f)

/-- `volatile_load` (`Events.v`, lines 557 to 569), with `Senv.block_is_volatile` and
`Senv.find_symbol` of the global environment `ge`. -/
inductive volatile_load {F V : Type} (ge : Genv.t F V) :
    memory_chunk → mem → block → ptrofs → trace → val → Prop
  | volatile_load_vol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs) (id : ident)
      (ev : eventval) (v : val) :
      Genv.block_is_volatile ge b = true →
      Genv.find_symbol ge id = some b →
      eventval_match ev (type_of_chunk chunk) v →
      volatile_load ge chunk m b ofs [.Event_vload chunk id ofs ev] (Val.load_result chunk v)
  | volatile_load_nonvol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs) (v : val) :
      Genv.block_is_volatile ge b = false →
      Mem.loadv chunk m (.Vptr b ofs) = some v →
      volatile_load ge chunk m b ofs E0 v

/-- `volatile_store` (`Events.v`, lines 571 to 583), with `Senv.block_is_volatile` and
`Senv.find_symbol` of the global environment `ge`. -/
inductive volatile_store {F V : Type} (ge : Genv.t F V) :
    memory_chunk → mem → block → ptrofs → val → trace → mem → Prop
  | volatile_store_vol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs) (id : ident)
      (ev : eventval) (v : val) :
      Genv.block_is_volatile ge b = true →
      Genv.find_symbol ge id = some b →
      eventval_match ev (type_of_chunk chunk) (Val.load_result chunk v) →
      volatile_store ge chunk m b ofs v [.Event_vstore chunk id ofs ev] m
  | volatile_store_nonvol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs) (v : val)
      (m' : mem) :
      Genv.block_is_volatile ge b = false →
      Mem.storev chunk m (.Vptr b ofs) v = some m' →
      volatile_store ge chunk m b ofs v E0 m'

/-- `volatile_store_sem` (`Events.v`, lines 820 to 824). -/
inductive volatile_store_sem {F V : Type} (chunk : memory_chunk) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop
  | volatile_store_sem_intro (b : block) (ofs : ptrofs) (m1 : mem) (v : val) (t : trace)
      (m2 : mem) :
      volatile_store ge chunk m1 b ofs v t m2 →
      volatile_store_sem chunk ge [.Vptr b ofs, v] m1 t .Vundef m2

/-- `volatile_load_sem` (`Events.v`, lines 709 to 713). -/
inductive volatile_load_sem {F V : Type} (chunk : memory_chunk) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop
  | volatile_load_sem_intro (b : block) (ofs : ptrofs) (m : mem) (t : trace) (v : val) :
      volatile_load ge chunk m b ofs t v →
      volatile_load_sem chunk ge [.Vptr b ofs] m t v m

/-- `external_call` (`Events.v`, lines 1524 to 1538) for `EF_external`, the built-in functions
of `builtin_table`, `EF_vload`, and `EF_vstore`. -/
def external_call {F V : Type} (A : Archi) (X : ExtSem) (ef : external_function)
    (ge : Genv.t F V) (vargs : List val) (m : mem) (t : trace) (vres : val) (m' : mem) : Prop :=
  match ef with
  | .EF_external name sg => X.external_functions_sem name sg ge.genv_symb vargs m t vres m'
  | .EF_vload chunk => volatile_load_sem chunk ge vargs m t vres m'
  | .EF_vstore chunk => volatile_store_sem chunk ge vargs m t vres m'
  | .EF_builtin name sg =>
      match lookup_builtin_function name sg with
      | some bf => known_builtin_sem A bf vargs m t vres m'
      | none => False
  | _ => False

end LClight
