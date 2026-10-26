/-
Derived from CompCert 3.18, the file `common/Globalenvs.v`.  CompCert is Copyright Institut National
de Recherche en Informatique et en Automatique (INRIA) and AbsInt Angewandte Informatik GmbH, and
its source files carry INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26: transcribed from Coq into Lean, with the changes that
`LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import LeanExe.Native.Clight.Ctypes

/-!
Global environments and the allocation of globals, from CompCert 3.18's `common/Globalenvs.v`,
without the proof fields of `Genv.t`; `Clight.lean` applies them to a program as `globalenv` and
`init_mem`.  A program's globals take the blocks `1, 2, …` in the order of `prog_defs`, and
`alloc_globals` allocates and initializes them in that order.  `store_zeros` writes one byte at a
time, as in CompCert, so evaluating the initial memory of a large global costs time in proportion
to its size.  `public_symbol`, `invert_symbol`, `find_var_info`, `block_is_volatile`, and
`to_senv` are omitted.
-/

namespace LClight

namespace Genv

structure t (F V : Type) where
  genv_public : List ident
  genv_symb : Std.TreeMap ident block
  genv_defs : Std.TreeMap block (globdef F V)
  genv_next : block

variable {F V : Type}

def find_symbol (ge : t F V) (id : ident) : Option block := ge.genv_symb[id]?

def find_def (ge : t F V) (b : block) : Option (globdef F V) := ge.genv_defs[b]?

def find_funct_ptr (ge : t F V) (b : block) : Option F :=
  match find_def ge b with
  | some (.Gfun f) => some f
  | _ => none

def find_funct (ge : t F V) (v : val) : Option F :=
  match v with
  | .Vptr b ofs => if ofs = Ptrofs.zero then find_funct_ptr ge b else none
  | _ => none

def add_global (ge : t F V) (idg : ident × globdef F V) : t F V :=
  { genv_public := ge.genv_public
    genv_symb := ge.genv_symb.insert idg.1 ge.genv_next
    genv_defs := ge.genv_defs.insert ge.genv_next idg.2
    genv_next := ge.genv_next + 1 }

def add_globals (ge : t F V) (gl : List (ident × globdef F V)) : t F V :=
  gl.foldl add_global ge

def empty_genv (pub : List ident) : t F V :=
  { genv_public := pub, genv_symb := ∅, genv_defs := ∅, genv_next := 1 }

/-- `store_zeros m b p n`, by recursion on `n` read as a natural number, which is zero exactly
when `n ≤ 0`. -/
def store_zeros (m : mem) (b : block) (p n : _root_.Int) : Option mem :=
  go n.toNat m p
where
  go : Nat → mem → _root_.Int → Option mem
    | 0, m, _ => some m
    | k + 1, m, p =>
        match Mem.store .Mint8unsigned m b p Vzero with
        | some m' => go k m' (p + 1)
        | none => none

def store_init_data (ge : t F V) (m : mem) (b : block) (p : _root_.Int) :
    init_data → Option mem
  | .Init_int8 n => Mem.store .Mint8unsigned m b p (.Vint n)
  | .Init_int16 n => Mem.store .Mint16unsigned m b p (.Vint n)
  | .Init_int32 n => Mem.store .Mint32 m b p (.Vint n)
  | .Init_int64 n => Mem.store .Mint64 m b p (.Vlong n)
  | .Init_float32 n => Mem.store .Mfloat32 m b p (.Vsingle n)
  | .Init_float64 n => Mem.store .Mfloat64 m b p (.Vfloat n)
  | .Init_addrof symb ofs =>
      match find_symbol ge symb with
      | none => none
      | some b' => Mem.store Mptr m b p (.Vptr b' ofs)
  | .Init_space _ => some m

def store_init_data_list (ge : t F V) (m : mem) (b : block) (p : _root_.Int) :
    List init_data → Option mem
  | [] => some m
  | id :: idl' =>
      match store_init_data ge m b p id with
      | none => none
      | some m' => store_init_data_list ge m' b (p + init_data_size id) idl'

def perm_globvar (gv : globvar V) : permission :=
  if gv.gvar_volatile then .Nonempty
  else if gv.gvar_readonly then .Readable
  else .Writable

def alloc_global (ge : t F V) (m : mem) : ident × globdef F V → Option mem
  | (_, .Gfun _) =>
      let (m1, b) := Mem.alloc m 0 1
      Mem.drop_perm m1 b 0 1 .Nonempty
  | (_, .Gvar v) =>
      let init := v.gvar_init
      let sz := init_data_list_size init
      let (m1, b) := Mem.alloc m 0 sz
      match store_zeros m1 b 0 sz with
      | none => none
      | some m2 =>
          match store_init_data_list ge m2 b 0 init with
          | none => none
          | some m3 => Mem.drop_perm m3 b 0 sz (perm_globvar v)

def alloc_globals (ge : t F V) (m : mem) : List (ident × globdef F V) → Option mem
  | [] => some m
  | g :: gl' =>
      match alloc_global ge m g with
      | none => none
      | some m' => alloc_globals ge m' gl'

end Genv

end LClight
