/-
Derived from CompCert 3.18, the files `common/Memtype.v`, `common/Memory.v`, and `lib/Maps.v`.
CompCert is Copyright Institut National de Recherche en Informatique et en Automatique (INRIA) and
AbsInt Angewandte Informatik GmbH, and its source files carry INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26: transcribed from Coq into Lean, with the changes that
`LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import Std.Data.TreeMap
import LeanExe.Native.Clight.Memdata

/-!
CompCert 3.18's memory model, from `common/Memtype.v` and `common/Memory.v`, without its proof
fields.  A block's contents are a `ZMap.t memval` whose default is `Undef`, here a tree map from
offsets, and the contents of all blocks are a tree map from blocks, as `PMap` is in CompCert.
Permissions are functions, as in `Memory.v`.  `range_perm` and `valid_access` are propositions
with decision procedures, `range_perm_dec` and `valid_access_dec` in CompCert.

Only the operations that the semantics in this directory use are copied: `perm_order'`,
`perm`, `range_perm`, `valid_access`, `valid_pointer`, `weak_valid_pointer`, `empty`, `alloc`,
`unchecked_free`, `free`, `free_list`, `getN`, `setN`, `load`, `loadv`, `store`, `storev`, and
`drop_perm`.  `loadv` and `storev` check that the accessed bytes end at most at
`Ptrofs.modulus`, as CompCert 3.18 does.

`mem` drops the invariants `access_max`, `nextblock_noaccess`, and `contents_default` of
CompCert's `mem`, so a `mem` need not satisfy them.  Forgetting them maps each CompCert memory to
a `mem`, its image, determined only up to extensional equality: two `mem`s with the same
contents, permissions, and next block stand for the same CompCert memory although their
`Std.TreeMap`s can differ in shape, so no statement about the copy should compare memories with
`=`.  Each operation here maps an image of a CompCert memory to an image of CompCert's result,
so the memories that `init_mem` and these operations produce are images, and a theorem that holds
for every `mem` holds for the images of CompCert's memories; a statement about a `mem` outside
the image says nothing about CompCert.  An external call under an arbitrary `ExtSem` can produce
a memory outside the image, so a theorem should hold for every `X` and be applied with `X` the
image of CompCert's `external_functions_sem`.  Carrying a conclusion about the copy over to
CompCert relies on a rule-for-rule correspondence between the copy's derivations and CompCert's,
which the reviews and the differential tests support and no proof covers.
-/

namespace LClight

inductive permission where
  | Freeable | Writable | Readable | Nonempty
  deriving Repr, DecidableEq

inductive perm_order : permission → permission → Prop
  | perm_refl (p : permission) : perm_order p p
  | perm_F_any (p : permission) : perm_order .Freeable p
  | perm_W_R : perm_order .Writable .Readable
  | perm_any_N (p : permission) : perm_order p .Nonempty

def perm_order_b : permission → permission → Bool
  | .Freeable, _ => true
  | _, .Nonempty => true
  | .Writable, .Writable => true
  | .Writable, .Readable => true
  | .Readable, .Readable => true
  | _, _ => false

theorem perm_order_b_iff (p1 p2 : permission) : perm_order_b p1 p2 = true ↔ perm_order p1 p2 := by
  constructor
  · intro h
    cases p1 <;> cases p2 <;> simp [perm_order_b] at h <;> constructor
  · intro h
    cases p1 <;> cases p2 <;> first | rfl | cases h

instance (p1 p2 : permission) : Decidable (perm_order p1 p2) :=
  decidable_of_iff _ (perm_order_b_iff p1 p2)

inductive perm_kind where
  | Max | Cur
  deriving Repr, DecidableEq

/-- `ZMap.t memval` with default `Undef`. -/
abbrev contents := Std.TreeMap _root_.Int memval

namespace ZMap

def init : contents := ∅
def get (i : _root_.Int) (c : contents) : memval := c.getD i .Undef
def set (i : _root_.Int) (v : memval) (c : contents) : contents := c.insert i v

end ZMap

/-- `Mem.mem` without its three proof fields. -/
structure mem where
  mem_contents : Std.TreeMap block contents
  mem_access : block → _root_.Int → perm_kind → Option permission
  nextblock : block

namespace Mem

/-- `m.(mem_contents)#b`. -/
def contents_of (m : mem) (b : block) : contents := m.mem_contents.getD b ZMap.init

def perm_order' (po : Option permission) (p : permission) : Prop :=
  match po with
  | some p' => perm_order p' p
  | none => False

instance (po : Option permission) (p : permission) : Decidable (perm_order' po p) :=
  match po with
  | some p' => inferInstanceAs (Decidable (perm_order p' p))
  | none => isFalse id

def perm (m : mem) (b : block) (ofs : _root_.Int) (k : perm_kind) (p : permission) : Prop :=
  perm_order' (m.mem_access b ofs k) p

instance (m : mem) (b : block) (ofs : _root_.Int) (k : perm_kind) (p : permission) :
    Decidable (perm m b ofs k p) :=
  inferInstanceAs (Decidable (perm_order' (m.mem_access b ofs k) p))

def range_perm (m : mem) (b : block) (lo hi : _root_.Int) (k : perm_kind) (p : permission) :
    Prop :=
  ∀ ofs, lo ≤ ofs → ofs < hi → perm m b ofs k p

/-- The decision procedure of `range_perm_dec`: the offsets `lo` to `hi - 1` in turn. -/
def range_perm_b (m : mem) (b : block) (lo hi : _root_.Int) (k : perm_kind) (p : permission) :
    Bool :=
  (List.range (hi - lo).toNat).all fun i => decide (perm m b (lo + i) k p)

theorem range_perm_b_iff (m : mem) (b : block) (lo hi : _root_.Int) (k : perm_kind)
    (p : permission) : range_perm_b m b lo hi k p = true ↔ range_perm m b lo hi k p := by
  unfold range_perm_b range_perm
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h ofs h1 h2
    have hp := h (ofs - lo).toNat (by omega)
    have e : lo + (((ofs - lo).toNat : Nat) : _root_.Int) = ofs := by omega
    rwa [e] at hp
  · intro h i hi
    exact h _ (by omega) (by omega)

instance (m : mem) (b : block) (lo hi : _root_.Int) (k : perm_kind) (p : permission) :
    Decidable (range_perm m b lo hi k p) :=
  decidable_of_iff _ (range_perm_b_iff m b lo hi k p)

def valid_access (m : mem) (chunk : memory_chunk) (b : block) (ofs : _root_.Int)
    (p : permission) : Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) .Cur p ∧ align_chunk chunk ∣ ofs

instance (m : mem) (chunk : memory_chunk) (b : block) (ofs : _root_.Int) (p : permission) :
    Decidable (valid_access m chunk b ofs p) :=
  inferInstanceAs
    (Decidable (range_perm m b ofs (ofs + size_chunk chunk) .Cur p ∧ align_chunk chunk ∣ ofs))

def valid_pointer (m : mem) (b : block) (ofs : _root_.Int) : Bool :=
  decide (perm m b ofs .Cur .Nonempty)

def weak_valid_pointer (m : mem) (b : block) (ofs : _root_.Int) : Bool :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1)

def empty : mem :=
  { mem_contents := ∅, mem_access := fun _ _ _ => none, nextblock := 1 }

def alloc (m : mem) (lo hi : _root_.Int) : mem × block :=
  ({ mem_contents := m.mem_contents.insert m.nextblock ZMap.init
     mem_access := fun b ofs k =>
       if b = m.nextblock then (if lo ≤ ofs ∧ ofs < hi then some .Freeable else none)
       else m.mem_access b ofs k
     nextblock := m.nextblock + 1 },
   m.nextblock)

def unchecked_free (m : mem) (b : block) (lo hi : _root_.Int) : mem :=
  { m with
    mem_access := fun b' ofs k =>
      if b' = b ∧ lo ≤ ofs ∧ ofs < hi then none else m.mem_access b' ofs k }

def free (m : mem) (b : block) (lo hi : _root_.Int) : Option mem :=
  if range_perm m b lo hi .Cur .Freeable then some (unchecked_free m b lo hi) else none

def free_list (m : mem) : List (block × _root_.Int × _root_.Int) → Option mem
  | [] => some m
  | (b, lo, hi) :: l =>
      match free m b lo hi with
      | none => none
      | some m' => free_list m' l

def getN : Nat → _root_.Int → contents → List memval
  | 0, _, _ => []
  | n + 1, p, c => ZMap.get p c :: getN n (p + 1) c

def setN : List memval → _root_.Int → contents → contents
  | [], _, c => c
  | v :: vl, p, c => setN vl (p + 1) (ZMap.set p v c)

def load (chunk : memory_chunk) (m : mem) (b : block) (ofs : _root_.Int) : Option val :=
  if valid_access m chunk b ofs .Readable then
    some (decode_val chunk (getN (size_chunk_nat chunk) ofs (contents_of m b)))
  else none

def loadv (chunk : memory_chunk) (m : mem) (addr : val) : Option val :=
  match addr with
  | .Vptr b ofs =>
      if Ptrofs.unsigned ofs + size_chunk chunk ≤ Ptrofs.modulus then
        load chunk m b (Ptrofs.unsigned ofs)
      else none
  | _ => none

def store (chunk : memory_chunk) (m : mem) (b : block) (ofs : _root_.Int) (v : val) :
    Option mem :=
  if valid_access m chunk b ofs .Writable then
    some { m with
      mem_contents := m.mem_contents.insert b (setN (encode_val chunk v) ofs (contents_of m b)) }
  else none

def storev (chunk : memory_chunk) (m : mem) (addr v : val) : Option mem :=
  match addr with
  | .Vptr b ofs =>
      if Ptrofs.unsigned ofs + size_chunk chunk ≤ Ptrofs.modulus then
        store chunk m b (Ptrofs.unsigned ofs) v
      else none
  | _ => none

def drop_perm (m : mem) (b : block) (lo hi : _root_.Int) (p : permission) : Option mem :=
  if range_perm m b lo hi .Cur .Freeable then
    some { m with
      mem_access := fun b' ofs k =>
        if b' = b ∧ lo ≤ ofs ∧ ofs < hi then some p else m.mem_access b' ofs k }
  else none

end Mem

end LClight
