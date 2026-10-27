/-
Derived from CompCert 3.18, the file `common/AST.v`.  CompCert is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and AbsInt Angewandte Informatik GmbH, and its
source files carry INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26 and 2026-10-27: transcribed from Coq into Lean, with the
changes that `LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import LeanExe.Native.Clight.Floats

/-!
The syntax shared by CompCert's languages, from CompCert 3.18's `common/AST.v`: identifiers, the
back-end types and signatures, memory chunks, the initialization data of globals, global
definitions, and external functions.  Identifiers and blocks are natural numbers, where Coq
uses `positive`, so 0 is an identifier and a block with no counterpart in CompCert; `globalenv`
and `Mem.empty` number blocks from 1.  The constructors are those of `AST.v`, so that the output of `clightgen` has a
representation; the semantics gives meaning to some of them only.
-/

namespace LClight

/-- `ident`, a positive number in CompCert. -/
abbrev ident := Nat

/-- `typ`. -/
inductive typ where
  | Tint | Tfloat | Tlong | Tsingle | Tany32 | Tany64
  deriving Repr, DecidableEq

/-- `xtype`. -/
inductive xtype where
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned | Xint | Xfloat | Xlong
  | Xsingle | Xptr | Xany32 | Xany64 | Xvoid
  deriving Repr, DecidableEq

/-- `calling_convention`. -/
structure calling_convention where
  cc_vararg : Option _root_.Int
  cc_unproto : Bool
  cc_structret : Bool
  deriving Repr, DecidableEq

def cc_default : calling_convention :=
  { cc_vararg := none, cc_unproto := false, cc_structret := false }

/-- `signature`. -/
structure signature where
  sig_args : List xtype
  sig_res : xtype
  sig_cc : calling_convention
  deriving Repr, DecidableEq

/-- `memory_chunk`. -/
inductive memory_chunk where
  | Mbool | Mint8signed | Mint8unsigned | Mint16signed | Mint16unsigned | Mint32 | Mint64
  | Mfloat32 | Mfloat64 | Many32 | Many64
  deriving Repr, DecidableEq

/-- `Mptr` on a 64-bit target. -/
def Mptr : memory_chunk := .Mint64

/-- `type_of_chunk` (`AST.v`, lines 219 to 232). -/
def type_of_chunk : memory_chunk → typ
  | .Mbool | .Mint8signed | .Mint8unsigned | .Mint16signed | .Mint16unsigned | .Mint32 => .Tint
  | .Mint64 => .Tlong
  | .Mfloat32 => .Tsingle
  | .Mfloat64 => .Tfloat
  | .Many32 => .Tany32
  | .Many64 => .Tany64

/-- `init_data`. -/
inductive init_data where
  | Init_int8 (n : int)
  | Init_int16 (n : int)
  | Init_int32 (n : int)
  | Init_int64 (n : int64)
  | Init_float32 (f : float32)
  | Init_float64 (f : float)
  | Init_space (n : _root_.Int)
  | Init_addrof (id : ident) (ofs : ptrofs)
  deriving Repr, DecidableEq

def init_data_size : init_data → _root_.Int
  | .Init_int8 _ => 1
  | .Init_int16 _ => 2
  | .Init_int32 _ => 4
  | .Init_int64 _ => 8
  | .Init_float32 _ => 4
  | .Init_float64 _ => 8
  | .Init_addrof _ _ => 8
  | .Init_space n => max n 0

def init_data_list_size : List init_data → _root_.Int
  | [] => 0
  | i :: il => init_data_size i + init_data_list_size il

/-- `globvar`. -/
structure globvar (V : Type) where
  gvar_info : V
  gvar_init : List init_data
  gvar_readonly : Bool
  gvar_volatile : Bool
  deriving Repr

/-- `globdef`. -/
inductive globdef (F V : Type) where
  | Gfun (f : F)
  | Gvar (v : globvar V)
  deriving Repr

/-- `external_function`. -/
inductive external_function where
  | EF_external (name : String) (sg : signature)
  | EF_builtin (name : String) (sg : signature)
  | EF_runtime (name : String) (sg : signature)
  | EF_vload (chunk : memory_chunk)
  | EF_vstore (chunk : memory_chunk)
  | EF_malloc
  | EF_free
  | EF_memcpy (sz al : _root_.Int)
  | EF_annot (kind : Nat) (text : String) (targs : List typ)
  | EF_annot_val (kind : Nat) (text : String) (targ : typ)
  | EF_inline_asm (text : String) (sg : signature) (clobbers : List String)
  | EF_debug (kind : Nat) (text : ident) (targs : List typ)
  deriving Repr, DecidableEq

end LClight
