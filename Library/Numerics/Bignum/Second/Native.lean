module

public import Library.Numerics.Bignum.Second.Call
public import LeanExe.Native.Proof.Native

@[expose] public section

/-!
# The C form of the second iteration's exports

`verified_compile` translates `compiled.module` to a program in the subset of CompCert's Clight that
leanexe's translator emits, with `lx_mem` of `nativeCap` pages, 256 MiB, and states
`compiled.translation_eq`.  The C function `lxf_f` of each export takes its arguments in the order
of the Lean definition, an array as the address of its object in `lx_mem` and a `BigInt` as its
sign word and the address of its magnitude, and returns a word or an array's address, or leaves
several results in the translation's result globals `lx_r0_l`, `lx_r1_l`, and `lx_r2_l`, in the
order of the result's words.

For each new export, `f_spec_trapFree` adds the export's claim to the generated theorem without a
trap: from a store whose heap meets the allocator invariant, has room for the generated bound at
1,000 frames, and holds canonical arguments (nothing for the readers), the call returns the Lean
function's value, which equals the specification's value, and raises `top` by at most the closed
form of `Bound.lean`.  The frames need no premise, since `Bound.lean` proves them for every
argument.  `f_native_spec` carries the claim to the C function, under every `Archi` and every
semantics of external functions, through `LeanExe.Native.ImplementsA.native`: from a C memory
related to such a store, with the arguments represented in it, the call terminates with
`lx_status` 0 and results that represent the Lean function's value.  `f_native_size` states the
premise as arithmetic on the 256 MiB of `lx_mem`: canonical arguments of fewer than `2^32` limbs or
texts of fewer than `2^32` words, and a heap whose `top` plus the closed form is at most `2^28`.
The C memory of 256 MiB bounds the inputs that the C theorems cover, where the WebAssembly module's
memory can grow to 65,535 pages: a product of two operands of 2.2 million limbs each, for example,
has a call theorem in WebAssembly and none in C.

`natOfTextDCWith_spec_trapFree` holds for every bound `E` with the generated bound, and
`natOfTextDCWith_closed_trapFree` adds the closed form for `1 ≤ E ≤ 2^32`.

The theorems concern one call in leanexe's Lean copy of CompCert's Clight.  They state that a
terminating run exists; leanexe's uniqueness theorem for deterministic semantics of external
functions, `LeanExe.Native.NativeA.unique`, is not instantiated, and the translation calls no
external function.  `StoreRel` relates the translation's globals and `lx_mem`, so a C function that
also wrote a global of the host would meet the theorems, which the translation's text, with no
reference to other globals, excludes.  CompCert's theorem assumes that the machine stack does not
overflow: within the 256 MiB of `lx_mem`, `kara`'s body `lxf_6` nests at most 17 calls, below at
most five others, the entry and the bodies of the reader's functions.  The hosted executable that
`ccomp` compiles with `host/bignum2.c` has no theorem as a whole.
-/

namespace Library.Numerics.Bignum.Second

open Library.Numerics.Bignum
open Library.Numerics.MultiPrecision (value Digits)
open LeanExe.Pipeline

/-- A precondition strengthened and a postcondition that uses it and the arguments'
representation, as the first iteration's `ImplementsA.strengthen`. -/
theorem ImplementsA.strengthen {α β : Type} [Represent α] [Represent β] {aborts : Bool}
    {m : Wasm.Module} {k : Nat} {f : α → β} {Pre Pre' : α → Heap → Wasm.Store Unit → Prop}
    {Post Post' : α → Heap → Wasm.Store Unit → Heap → Wasm.Store Unit → Prop}
    (h : ImplementsA aborts m k f Pre Post) (hpre : ∀ x heap store, Pre' x heap store → Pre x heap store)
    (hpost : ∀ heap store params x heap' final, Pre' x heap store →
      Represent.borrowed heap store params x → Post x heap store heap' final →
      Post' x heap store heap' final) :
    ImplementsA aborts m k f Pre' Post' :=
  fun env store heap params x hAt hPre hRep hSep hCap =>
    (h env store heap params x hAt (hpre x heap store hPre) hRep hSep hCap).mono
      fun final _ ⟨heap', a, b, c, d, e⟩ =>
        ⟨heap', a, b, c, d, hpost heap store params x heap' final hPre hRep e⟩

theorem rep_fst {α β : Type} [Represent α] [Represent β] {heap : Heap} {store : Wasm.Store Unit}
    {vs : List Wasm.Value} {p : α × β} (h : Represent.borrowed heap store vs p) :
    ∃ v, Represent.borrowed heap store v p.1 := by
  obtain ⟨f, _, _, h1, _⟩ := h
  exact ⟨f, h1⟩

theorem rep_snd {α β : Type} [Represent α] [Represent β] {heap : Heap} {store : Wasm.Store Unit}
    {vs : List Wasm.Value} {p : α × β} (h : Represent.borrowed heap store vs p) :
    ∃ v, Represent.borrowed heap store v p.2 := by
  obtain ⟨_, s, _, _, h2⟩ := h
  exact ⟨s, h2⟩

theorem rep_arr {heap : Heap} {store : Wasm.Store Unit} {vs : List Wasm.Value} {xs : Array UInt64}
    (h : Represent.borrowed heap store vs xs) : xs.size < 536870912 := by
  obtain ⟨_, _, hb⟩ := h
  exact hb.values.size_lt_memory32

theorem rep_mag {heap : Heap} {store : Wasm.Store Unit} {vs : List Wasm.Value} {x : BigInt}
    (h : Represent.borrowed heap store vs x) : x.mag.size < 536870912 := by
  obtain ⟨_, _, _, _, ⟨_, _, hb⟩⟩ := h
  exact hb.values.size_lt_memory32

/-! ### `natMulKara` -/

set_option maxRecDepth 100000 in
/-- Function 20, `natMulKara`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natMulKara_spec_trapFree :
    ImplementsA false compiled.module 20 (fun x : Array UInt64 × Array UInt64 => natMulKara x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112) ∧
        natMulKara x.1 x.2 = limbsOf (value x.1 * value x.2)) :=
  ImplementsA.strengthen (compiled.natMulKara.trapFree.mono
      (fun x _ _ h => ⟨natMulKara_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natMulKara_room x.1 x.2 (by omega) (by omega)) _), natMulKara_eq hc.1.1 hc.2.1 (by omega) (by omega)⟩

/-- The C function `lxf_natMulKara` computes `natMulKara` as `natMulKara_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natMulKara_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natMulKara_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natMulKara.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natMulKara_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natMulKara_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natMulKara_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 20, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[20]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natMulKara x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ (x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32) ∧
          heap.top.toNat + (24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112) ∧
          natMulKara x.1 x.2 = limbsOf (value x.1 * value x.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natMulKara_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natMulKara.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natMulKara.bound 1000 x ≤ 24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112 := natMulKara_room x.1 x.2 hs.1 hs.2
  omega

/-! ### `intMulKara` -/

set_option maxRecDepth 100000 in
/-- Function 21, `intMulKara`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem intMulKara_spec_trapFree :
    ImplementsA false compiled.module 21 (fun x : BigInt × BigInt => intMulKara x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.1.mag.size + x.2.mag.size) + 80 * min x.1.mag.size x.2.mag.size + 112) ∧
        intMulKara x.1 x.2 = BigInt.ofInt (x.1.toInt * x.2.toInt)) :=
  ImplementsA.strengthen (compiled.intMulKara.trapFree.mono
      (fun x _ _ h => ⟨intMulKara_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre.1
      have e1 := BigInt.eq_ofInt hc.1
      have e2 := BigInt.eq_ofInt hc.2
      have t1 := s1
      have t2 := s2
      rw [e1] at t1
      rw [e2] at t2
      have heq := intMulKara_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← e1, ← e2] at heq
      exact ⟨le_trans hpost (Nat.add_le_add_left (intMulKara_room x.1 x.2 (by omega) (by omega)) _), heq⟩

/-- The C function `lxf_intMulKara` computes `intMulKara` as `intMulKara_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem intMulKara_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intMulKara_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intMulKara.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intMulKara_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intMulKara_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intMulKara_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 21, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[21]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intMulKara x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ (x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (24 * (x.1.mag.size + x.2.mag.size) + 80 * min x.1.mag.size x.2.mag.size + 112) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.1.mag.size + x.2.mag.size) + 80 * min x.1.mag.size x.2.mag.size + 112) ∧
          intMulKara x.1 x.2 = BigInt.ofInt (x.1.toInt * x.2.toInt)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intMulKara_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intMulKara.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.intMulKara.bound 1000 x ≤ 24 * (x.1.mag.size + x.2.mag.size) + 80 * min x.1.mag.size x.2.mag.size + 112 := intMulKara_room x.1 x.2 hs.1 hs.2
  omega

/-! ### `natOfTextDC` -/

set_option maxRecDepth 100000 in
/-- Function 25, `natOfTextDC`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natOfTextDC_spec_trapFree :
    ImplementsA false compiled.module 25 (fun x : Array UInt64 => natOfTextDC x)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.natOfTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (7 * x.size + 168) ∧
        natOfTextDC x = natReadSpec x) :=
  ImplementsA.strengthen (compiled.natOfTextDC.trapFree.mono
      (fun x _ _ h => ⟨natOfTextDC_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.size < 536870912 := rep_arr hr
      exact ⟨le_trans hpost (Nat.add_le_add_left (natOfTextDC_room x (by omega)) _), natOfTextDC_eq x (by omega)⟩

/-- The C function `lxf_natOfTextDC` computes `natOfTextDC` as `natOfTextDC_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natOfTextDC_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natOfTextDC_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natOfTextDC.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natOfTextDC_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natOfTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natOfTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 25, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[25]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => natOfTextDC x)
        (fun x heap _ => (True) ∧ (x.size < 2 ^ 32) ∧
          heap.top.toNat + (7 * x.size + 168) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (7 * x.size + 168) ∧
          natOfTextDC x = natReadSpec x) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natOfTextDC_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natOfTextDC.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natOfTextDC.bound 1000 x ≤ 7 * x.size + 168 := natOfTextDC_room x hs
  omega

/-! ### `intOfTextDC` -/

set_option maxRecDepth 100000 in
/-- Function 26, `intOfTextDC`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem intOfTextDC_spec_trapFree :
    ImplementsA false compiled.module 26 (fun x : Array UInt64 => intOfTextDC x)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.intOfTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (7 * x.size + 168) ∧
        intOfTextDC x = readSpec x) :=
  ImplementsA.strengthen (compiled.intOfTextDC.trapFree.mono
      (fun x _ _ h => ⟨intOfTextDC_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.size < 536870912 := rep_arr hr
      exact ⟨le_trans hpost (Nat.add_le_add_left (intOfTextDC_room x (by omega)) _), intOfTextDC_eq x (by omega)⟩

/-- The C function `lxf_intOfTextDC` computes `intOfTextDC` as `intOfTextDC_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem intOfTextDC_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intOfTextDC_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intOfTextDC.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intOfTextDC_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intOfTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intOfTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 26, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[26]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => intOfTextDC x)
        (fun x heap _ => (True) ∧ (x.size < 2 ^ 32) ∧
          heap.top.toNat + (7 * x.size + 168) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (7 * x.size + 168) ∧
          intOfTextDC x = readSpec x) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intOfTextDC_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intOfTextDC.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.intOfTextDC.bound 1000 x ≤ 7 * x.size + 168 := intOfTextDC_room x hs
  omega

/-! ### `natMulKaraWith` -/

set_option maxRecDepth 100000 in
/-- Function 19, `natMulKaraWith`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natMulKaraWith_spec_trapFree :
    ImplementsA false compiled.module 19 (fun x : UInt64 × Array UInt64 × Array UInt64 => natMulKaraWith x.1 x.2.1 x.2.2)
      (fun x heap store => (Canonical x.2.1 ∧ Canonical x.2.2) ∧ heap.Within store compiled.module (compiled.natMulKaraWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.2.1.size + x.2.2.size) + 80 * min x.2.1.size x.2.2.size + 112) ∧
        natMulKaraWith x.1 x.2.1 x.2.2 = limbsOf (value x.2.1 * value x.2.2)) :=
  ImplementsA.strengthen (compiled.natMulKaraWith.trapFree.mono
      (fun x _ _ h => ⟨natMulKaraWith_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r⟩ := rep_snd hr
      obtain ⟨_, r1⟩ := rep_fst r
      obtain ⟨_, r2⟩ := rep_snd r
      have s1 : x.2.1.size < 536870912 := rep_arr r1
      have s2 : x.2.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natMulKaraWith_room x.1 x.2.1 x.2.2 (by omega) (by omega)) _), natMulKaraWith_eq _ hc.1.1 hc.2.1 (by omega) (by omega)⟩

/-- The C function `lxf_natMulKaraWith` computes `natMulKaraWith` as `natMulKaraWith_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natMulKaraWith_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natMulKaraWith_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natMulKaraWith.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natMulKaraWith_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natMulKaraWith_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natMulKaraWith_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 19, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[19]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : UInt64 × Array UInt64 × Array UInt64 => natMulKaraWith x.1 x.2.1 x.2.2)
        (fun x heap _ => (Canonical x.2.1 ∧ Canonical x.2.2) ∧ (x.2.1.size < 2 ^ 32 ∧ x.2.2.size < 2 ^ 32) ∧
          heap.top.toNat + (24 * (x.2.1.size + x.2.2.size) + 80 * min x.2.1.size x.2.2.size + 112) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.2.1.size + x.2.2.size) + 80 * min x.2.1.size x.2.2.size + 112) ∧
          natMulKaraWith x.1 x.2.1 x.2.2 = limbsOf (value x.2.1 * value x.2.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natMulKaraWith_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natMulKaraWith.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natMulKaraWith.bound 1000 x ≤ 24 * (x.2.1.size + x.2.2.size) + 80 * min x.2.1.size x.2.2.size + 112 := natMulKaraWith_room x.1 x.2.1 x.2.2 hs.1 hs.2
  omega

/-! ### `natOfTextDCWith` -/

set_option maxRecDepth 100000 in
/-- Function 24, `natOfTextDCWith`, returns `natReadSpec` of its text for every threshold and every
bound `E`, and raises `top` by at most its generated bound. -/
theorem natOfTextDCWith_spec_trapFree :
    ImplementsA false compiled.module 24
      (fun x : UInt64 × UInt64 × Array UInt64 => natOfTextDCWith x.1 x.2.1 x.2.2)
      (fun x heap store => True ∧
        heap.Within store compiled.module (compiled.natOfTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natOfTextDCWith.bound 1000 x ∧
        natOfTextDCWith x.1 x.2.1 x.2.2 = natReadSpec x.2.2) :=
  ImplementsA.strengthen (compiled.natOfTextDCWith.trapFree.mono
      (fun x _ _ h => ⟨natOfTextDCWith_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r⟩ := rep_snd hr
      obtain ⟨_, r2⟩ := rep_snd r
      have s1 : x.2.2.size < 536870912 := rep_arr r2
      exact ⟨hpost, natOfTextDCWith_eq _ _ x.2.2 (by omega)⟩

/-- The C function `lxf_natOfTextDCWith` computes `natOfTextDCWith` as
`natOfTextDCWith_spec_trapFree` states, under every `Archi` and every semantics of external
functions. -/
theorem natOfTextDCWith_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natOfTextDCWith_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natOfTextDCWith.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natOfTextDCWith_spec_trapFree compiled.translation_eq hfd hsig⟩

set_option maxRecDepth 100000 in
/-- Function 24, `natOfTextDCWith`, with a bound `1 ≤ E ≤ 2^32` on the base elements, returns
`natReadSpec` of its text and raises `top` by at most the closed form of its bound. -/
theorem natOfTextDCWith_closed_trapFree :
    ImplementsA false compiled.module 24 (fun x : UInt64 × UInt64 × Array UInt64 => natOfTextDCWith x.1 x.2.1 x.2.2)
      (fun x heap store => (1 ≤ x.2.1.toNat ∧ x.2.1.toNat ≤ 2 ^ 32) ∧ heap.Within store compiled.module (compiled.natOfTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (19 * x.2.2.size + 262) ∧
        natOfTextDCWith x.1 x.2.1 x.2.2 = natReadSpec x.2.2) :=
  ImplementsA.strengthen (compiled.natOfTextDCWith.trapFree.mono
      (fun x _ _ h => ⟨natOfTextDCWith_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r⟩ := rep_snd hr
      obtain ⟨_, r2⟩ := rep_snd r
      have s1 : x.2.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natOfTextDCWith_room x.1 x.2.1 x.2.2 hc.1 hc.2 (by omega)) _), natOfTextDCWith_eq _ _ x.2.2 (by omega)⟩

/-- The C function `lxf_natOfTextDCWith` computes `natOfTextDCWith` as
`natOfTextDCWith_closed_trapFree` states, under every `Archi` and every semantics of external
functions. -/
theorem natOfTextDCWith_closed_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natOfTextDCWith_closed_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natOfTextDCWith.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natOfTextDCWith_closed_trapFree compiled.translation_eq hfd hsig⟩

/-- `natOfTextDCWith_closed_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natOfTextDCWith_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 24, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[24]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : UInt64 × UInt64 × Array UInt64 => natOfTextDCWith x.1 x.2.1 x.2.2)
        (fun x heap _ => (1 ≤ x.2.1.toNat ∧ x.2.1.toNat ≤ 2 ^ 32) ∧ (x.2.2.size < 2 ^ 32) ∧
          heap.top.toNat + (19 * x.2.2.size + 262) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (19 * x.2.2.size + 262) ∧
          natOfTextDCWith x.1 x.2.1 x.2.2 = natReadSpec x.2.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natOfTextDCWith_closed_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natOfTextDCWith.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natOfTextDCWith.bound 1000 x ≤ 19 * x.2.2.size + 262 := natOfTextDCWith_room x.1 x.2.1 x.2.2 hp1.1 hp1.2 hs
  omega

end Library.Numerics.Bignum.Second
