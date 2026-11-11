(* The Rocq meaning of the symbols of the neutral specification clightn/N.nsx, the twin of
   LeanExe/Native/ClightN/Base.lean.  The base symbols are word conversions, which CompCert's
   unsigned, repr, and signed give, Euclid's division by a positive divisor, powers of two, and
   bitwise operations on numbers that are not negative; the laws that NProof.v proves fix their
   meaning where the specification uses them.  The interpreted symbols name CompCert 3.18's
   definitions under test. *)
From Coq Require Import ZArith.
Require Import Integers Values Memory Ctypes Cop Clight.

Definition u32 (x: int) : Z := Int.unsigned x.
Definition r32 (z: Z) : int := Int.repr z.
Definition u64 (x: int64) : Z := Int64.unsigned x.
Definition r64 (z: Z) : int64 := Int64.repr z.
Definition s64 (x: int64) : Z := Int64.signed x.
Definition zdiv (a b: Z) : Z := Z.div a b.
Definition zmod (a b: Z) : Z := Z.modulo a b.
Definition pow2 (k: Z) : Z := Z.pow 2 k.
Definition land (a b: Z) : Z := Z.land a b.
Definition lor (a b: Z) : Z := Z.lor a b.
Definition lxor (a b: Z) : Z := Z.lxor a b.

Definition sem_binop (ce: composite_env) := Cop.sem_binary_operation ce.
Definition sem_cast := Cop.sem_cast.
Definition bool_val := Cop.bool_val.
Definition eval_expr := Clight.eval_expr.
