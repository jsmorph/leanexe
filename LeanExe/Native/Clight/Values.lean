/-
Derived from CompCert 3.18, the file `common/Values.v`.  CompCert is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and AbsInt Angewandte Informatik GmbH, and its
source files carry INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26: transcribed from Coq into Lean, with the changes that
`LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import LeanExe.Native.Clight.AST

/-!
The values of CompCert 3.18's `common/Values.v` and the few operations on them that the memory
model and the operators use, on a 64-bit target.
-/

namespace LClight

/-- `block`, a positive number in CompCert. -/
abbrev block := Nat

/-- `val`. -/
inductive val where
  | Vundef
  | Vint (i : int)
  | Vlong (i : int64)
  | Vfloat (f : float)
  | Vsingle (f : float32)
  | Vptr (b : block) (ofs : ptrofs)
  deriving Repr, DecidableEq, Inhabited

def Vzero : val := .Vint Int.zero
def Vone : val := .Vint Int.one
def Vtrue : val := .Vint Int.one
def Vfalse : val := .Vint Int.zero

/-- `Vptrofs` with `Archi.ptr64` true. -/
def Vptrofs (n : ptrofs) : val := .Vlong (Ptrofs.to_int64 n)

namespace Val

def of_bool (b : Bool) : val := if b then Vtrue else Vfalse

def is_bool (v : val) : Bool := v == Vtrue || v == Vfalse

def norm_bool (v : val) : val := if is_bool v then v else .Vundef

/-- `Val.load_result` with `Archi.ptr64` true. -/
def load_result (chunk : memory_chunk) (v : val) : val :=
  match chunk, v with
  | .Mbool, .Vint n => norm_bool (.Vint (Int.zero_ext 8 n))
  | .Mint8signed, .Vint n => .Vint (Int.sign_ext 8 n)
  | .Mint8unsigned, .Vint n => .Vint (Int.zero_ext 8 n)
  | .Mint16signed, .Vint n => .Vint (Int.sign_ext 16 n)
  | .Mint16unsigned, .Vint n => .Vint (Int.zero_ext 16 n)
  | .Mint32, .Vint n => .Vint n
  | .Mint64, .Vlong n => .Vlong n
  | .Mint64, .Vptr b ofs => .Vptr b ofs
  | .Mfloat32, .Vsingle f => .Vsingle f
  | .Mfloat64, .Vfloat f => .Vfloat f
  | .Many32, .Vint _ => v
  | .Many32, .Vsingle _ => v
  | .Many64, _ => v
  | _, _ => .Vundef

end Val

end LClight
