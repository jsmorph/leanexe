/-
Derived from CompCert 3.18, the file `common/Memdata.v`.  CompCert is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and AbsInt Angewandte Informatik GmbH, and its
source files carry INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26: transcribed from Coq into Lean, with the changes that
`LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import LeanExe.Native.Clight.Values

/-!
The in-memory representation of values, from CompCert 3.18's `common/Memdata.v`, on a
little-endian target with `Archi.ptr64` true and `align_int64 = align_float64 = 8`, which hold
on x86-64 and AArch64.
-/

namespace LClight

def size_chunk : memory_chunk → _root_.Int
  | .Mbool => 1
  | .Mint8signed => 1
  | .Mint8unsigned => 1
  | .Mint16signed => 2
  | .Mint16unsigned => 2
  | .Mint32 => 4
  | .Mint64 => 8
  | .Mfloat32 => 4
  | .Mfloat64 => 8
  | .Many32 => 4
  | .Many64 => 8

def size_chunk_nat (chunk : memory_chunk) : Nat := (size_chunk chunk).toNat

/-- `align_chunk`, with `Archi.align_int64` and `Archi.align_float64` both 8. -/
def align_chunk : memory_chunk → _root_.Int
  | .Mbool => 1
  | .Mint8signed => 1
  | .Mint8unsigned => 1
  | .Mint16signed => 2
  | .Mint16unsigned => 2
  | .Mint32 => 4
  | .Mint64 => 8
  | .Mfloat32 => 4
  | .Mfloat64 => 8
  | .Many32 => 4
  | .Many64 => 8

inductive quantity where
  | Q32 | Q64
  deriving Repr, DecidableEq

def size_quantity_nat : quantity → Nat
  | .Q32 => 4
  | .Q64 => 8

/-- `memval`. -/
inductive memval where
  | Undef
  | Byte (b : byte)
  | Fragment (v : val) (q : quantity) (n : Nat)
  deriving Repr, DecidableEq, Inhabited

def bytes_of_int : Nat → _root_.Int → List byte
  | 0, _ => []
  | m + 1, x => Byte.repr x :: bytes_of_int m (x / 256)

def int_of_bytes : List byte → _root_.Int
  | [] => 0
  | b :: l => Byte.unsigned b + int_of_bytes l * 256

/-- `encode_int` on a little-endian target, where `rev_if_be` is the identity. -/
def encode_int (sz : Nat) (x : _root_.Int) : List byte := bytes_of_int sz x

def decode_int (b : List byte) : _root_.Int := int_of_bytes b

def inj_bytes (bl : List byte) : List memval := bl.map .Byte

def proj_bytes : List memval → Option (List byte)
  | [] => some []
  | .Byte b :: vl =>
      match proj_bytes vl with
      | none => none
      | some bl => some (b :: bl)
  | _ => none

def inj_value_rec : Nat → val → quantity → List memval
  | 0, _, _ => []
  | m + 1, v, q => .Fragment v q m :: inj_value_rec m v q

def inj_value (q : quantity) (v : val) : List memval := inj_value_rec (size_quantity_nat q) v q

def check_value : Nat → val → quantity → List memval → Bool
  | 0, _, _, [] => true
  | m + 1, v, q, .Fragment v' q' m' :: vl' =>
      v == v' && q == q' && m == m' && check_value m v q vl'
  | _, _, _, _ => false

def proj_value (q : quantity) (vl : List memval) : val :=
  match vl with
  | .Fragment v _ _ :: _ => if check_value (size_quantity_nat q) v q vl then v else .Vundef
  | _ => .Vundef

/-- `encode_val` with `Archi.ptr64` true. -/
def encode_val (chunk : memory_chunk) (v : val) : List memval :=
  match v, chunk with
  | .Vint n, .Mbool | .Vint n, .Mint8signed | .Vint n, .Mint8unsigned =>
      inj_bytes (encode_int 1 (Int.unsigned n))
  | .Vint n, .Mint16signed | .Vint n, .Mint16unsigned => inj_bytes (encode_int 2 (Int.unsigned n))
  | .Vint n, .Mint32 => inj_bytes (encode_int 4 (Int.unsigned n))
  | .Vptr _ _, .Mint32 => List.replicate 4 .Undef
  | .Vlong n, .Mint64 => inj_bytes (encode_int 8 (Int64.unsigned n))
  | .Vptr _ _, .Mint64 => inj_value .Q64 v
  | .Vsingle n, .Mfloat32 => inj_bytes (encode_int 4 (Int.unsigned (Float32.to_bits n)))
  | .Vfloat n, .Mfloat64 => inj_bytes (encode_int 8 (Int64.unsigned (Float.to_bits n)))
  | _, .Many32 => inj_value .Q32 v
  | _, .Many64 => inj_value .Q64 v
  | _, _ => List.replicate (size_chunk_nat chunk) .Undef

/-- `decode_val` with `Archi.ptr64` true. -/
def decode_val (chunk : memory_chunk) (vl : List memval) : val :=
  match proj_bytes vl with
  | some bl =>
      match chunk with
      | .Mbool => Val.norm_bool (.Vint (Int.zero_ext 8 (Int.repr (decode_int bl))))
      | .Mint8signed => .Vint (Int.sign_ext 8 (Int.repr (decode_int bl)))
      | .Mint8unsigned => .Vint (Int.zero_ext 8 (Int.repr (decode_int bl)))
      | .Mint16signed => .Vint (Int.sign_ext 16 (Int.repr (decode_int bl)))
      | .Mint16unsigned => .Vint (Int.zero_ext 16 (Int.repr (decode_int bl)))
      | .Mint32 => .Vint (Int.repr (decode_int bl))
      | .Mint64 => .Vlong (Int64.repr (decode_int bl))
      | .Mfloat32 => .Vsingle (Float32.of_bits (Int.repr (decode_int bl)))
      | .Mfloat64 => .Vfloat (Float.of_bits (Int64.repr (decode_int bl)))
      | .Many32 => .Vundef
      | .Many64 => .Vundef
  | none =>
      match chunk with
      | .Mint32 => .Vundef
      | .Many32 => Val.load_result chunk (proj_value .Q32 vl)
      | .Mint64 => Val.load_result chunk (proj_value .Q64 vl)
      | .Many64 => Val.load_result chunk (proj_value .Q64 vl)
      | _ => .Vundef

end LClight
