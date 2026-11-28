module

public import Library.Numerics.Bignum.Third.Call
public import LeanExe.Native.Proof.Native

@[expose] public section

/-!
# The C form of the third iteration's exports

`verified_compile` translates `compiled.module` to a program in the subset of CompCert's Clight that
leanexe's translator emits, with `lx_mem` of `nativeCap` pages, 256 MiB, and states
`compiled.translation_eq`.  The C function `lxf_f` of each export takes its arguments in the order
of the Lean definition, an array as the address of its object in `lx_mem` and a `BigInt` as its
sign word and the address of its magnitude, and returns an array's address, or leaves several
results in the translation's result globals `lx_r0_l` to `lx_r4_l`, in the order of the result's
words: the status, the quotient, and the remainder of a natural division, and the status and the
sign and magnitude of the quotient and of the remainder of an integer division.

For each new export, `f_spec_trapFree` adds the export's claim to the generated theorem without a
trap: from a store whose heap meets the allocator invariant, has room for the generated bound at
1,000 frames, and holds canonical arguments, the call returns the Lean function's value, which
equals the first iteration's specification, and raises `top` by at most the closed form of
`Bound.lean`.  The frames need no premise, since `Bound.lean` proves them for every argument.
`f_native_spec` carries the claim to the C function, under every `Archi` and every semantics of
external functions, through `LeanExe.Native.ImplementsA.native`: from a C memory related to such a
store, with the arguments represented in it, the call terminates with `lx_status` 0 and results
that represent the Lean function's value.  `f_native_size` states the premise as arithmetic on the
256 MiB of `lx_mem`: canonical arguments of fewer than `2^32` limbs and a heap whose `top` plus the
closed form is at most `2^28` bytes.  The C memory of 256 MiB bounds the inputs that the C theorems
cover, where the WebAssembly module's memory can grow to 65,535 pages: a division of 1.4 million by
700,000 limbs, for example, has a call theorem in WebAssembly and none in C.

The theorems concern one call in leanexe's Lean copy of CompCert's Clight.  They state that a
terminating run exists; leanexe's uniqueness theorem for deterministic semantics of external
functions, `LeanExe.Native.NativeA.unique`, is not instantiated, and the translation calls no
external function.  `StoreRel` relates the translation's globals and `lx_mem`, so a C function that
also wrote a global of the host would meet the theorems, which the translation's text, with no
reference to other globals, excludes.  CompCert's theorem assumes that the machine stack does not
overflow, which the frame counts of `Bound.lean` bound: at most 182 nested calls of the bodies
that take the call depth below an export.  The hosted executable that `ccomp` compiles with
`host/bignum3.c` has no theorem as a whole.
-/

namespace Library.Numerics.Bignum.Third

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

/-! ### `natDivModCheckedBZ` -/

set_option maxRecDepth 100000 in
/-- Function 65, `natDivModCheckedBZ`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natDivModCheckedBZ_spec_trapFree :
    ImplementsA false compiled.module 65 (fun x : Array UInt64 × Array UInt64 => natDivModCheckedBZ x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ∧
        natDivModCheckedBZ x.1 x.2 = natDivModCheckedSpec (value x.1) (value x.2)) :=
  ImplementsA.strengthen (compiled.natDivModCheckedBZ.trapFree.mono
      (fun x _ _ h => ⟨natDivModCheckedBZ_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natDivModCheckedBZ_room x.1 x.2 (by omega) (by omega)) _), natDivModCheckedBZ_eq hc.1 hc.2 (by omega) (by omega)⟩

/-- The C function `lxf_natDivModCheckedBZ` computes `natDivModCheckedBZ` as `natDivModCheckedBZ_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natDivModCheckedBZ_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natDivModCheckedBZ_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natDivModCheckedBZ.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natDivModCheckedBZ_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natDivModCheckedBZ_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natDivModCheckedBZ_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 65, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[65]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natDivModCheckedBZ x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ (x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32) ∧
          heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ∧
          natDivModCheckedBZ x.1 x.2 = natDivModCheckedSpec (value x.1) (value x.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natDivModCheckedBZ_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natDivModCheckedBZ.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natDivModCheckedBZ.bound 1000 x ≤ 128 * x.1.size + 144 * x.2.size + 824 := natDivModCheckedBZ_room x.1 x.2 hs.1 hs.2
  omega

/-! ### `intTDivModCheckedBZ` -/

set_option maxRecDepth 100000 in
/-- Function 66, `intTDivModCheckedBZ`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem intTDivModCheckedBZ_spec_trapFree :
    ImplementsA false compiled.module 66 (fun x : BigInt × BigInt => intTDivModCheckedBZ x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intTDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ∧
        intTDivModCheckedBZ x.1 x.2 = intTDivModCheckedSpec x.1.toInt x.2.toInt) :=
  ImplementsA.strengthen (compiled.intTDivModCheckedBZ.trapFree.mono
      (fun x _ _ h => ⟨intTDivModCheckedBZ_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
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
      have heq := intTDivModCheckedBZ_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← e1, ← e2] at heq
      exact ⟨le_trans hpost (Nat.add_le_add_left (intTDivModCheckedBZ_room x.1 x.2 (by omega) (by omega)) _), heq⟩

/-- The C function `lxf_intTDivModCheckedBZ` computes `intTDivModCheckedBZ` as `intTDivModCheckedBZ_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem intTDivModCheckedBZ_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intTDivModCheckedBZ_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intTDivModCheckedBZ.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intTDivModCheckedBZ_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intTDivModCheckedBZ_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intTDivModCheckedBZ_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 66, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[66]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intTDivModCheckedBZ x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ (x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ∧
          intTDivModCheckedBZ x.1 x.2 = intTDivModCheckedSpec x.1.toInt x.2.toInt) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intTDivModCheckedBZ_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intTDivModCheckedBZ.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.intTDivModCheckedBZ.bound 1000 x ≤ 128 * x.1.mag.size + 144 * x.2.mag.size + 824 := intTDivModCheckedBZ_room x.1 x.2 hs.1 hs.2
  omega

/-! ### `intEDivModCheckedBZ` -/

set_option maxRecDepth 100000 in
/-- Function 67, `intEDivModCheckedBZ`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem intEDivModCheckedBZ_spec_trapFree :
    ImplementsA false compiled.module 67 (fun x : BigInt × BigInt => intEDivModCheckedBZ x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intEDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (248 * x.1.mag.size + 248 * x.2.mag.size + 1472) ∧
        intEDivModCheckedBZ x.1 x.2 = intEDivModCheckedSpec x.1.toInt x.2.toInt) :=
  ImplementsA.strengthen (compiled.intEDivModCheckedBZ.trapFree.mono
      (fun x _ _ h => ⟨intEDivModCheckedBZ_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
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
      have heq := intEDivModCheckedBZ_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← e1, ← e2] at heq
      exact ⟨le_trans hpost (Nat.add_le_add_left (intEDivModCheckedBZ_room x.1 x.2 (by omega) (by omega)) _), heq⟩

/-- The C function `lxf_intEDivModCheckedBZ` computes `intEDivModCheckedBZ` as `intEDivModCheckedBZ_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem intEDivModCheckedBZ_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intEDivModCheckedBZ_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intEDivModCheckedBZ.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intEDivModCheckedBZ_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intEDivModCheckedBZ_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intEDivModCheckedBZ_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 67, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[67]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intEDivModCheckedBZ x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ (x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (248 * x.1.mag.size + 248 * x.2.mag.size + 1472) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (248 * x.1.mag.size + 248 * x.2.mag.size + 1472) ∧
          intEDivModCheckedBZ x.1 x.2 = intEDivModCheckedSpec x.1.toInt x.2.toInt) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intEDivModCheckedBZ_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intEDivModCheckedBZ.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.intEDivModCheckedBZ.bound 1000 x ≤ 248 * x.1.mag.size + 248 * x.2.mag.size + 1472 := intEDivModCheckedBZ_room x.1 x.2 hs.1 hs.2
  omega

/-! ### `natToTextDC` -/

set_option maxRecDepth 100000 in
/-- Function 72, `natToTextDC`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natToTextDC_spec_trapFree :
    ImplementsA false compiled.module 72 (fun x : Array UInt64 => natToTextDC x)
      (fun x heap store => (Canonical x) ∧ heap.Within store compiled.module (compiled.natToTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.size + 1968) ∧
        natToTextDC x = printSpec (value x : ℤ)) :=
  ImplementsA.strengthen (compiled.natToTextDC.trapFree.mono
      (fun x _ _ h => ⟨natToTextDC_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.size < 536870912 := rep_arr hr
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natToTextDC_room x (by omega)) _), natToTextDC_eq hc (by omega)⟩

/-- The C function `lxf_natToTextDC` computes `natToTextDC` as `natToTextDC_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natToTextDC_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natToTextDC_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natToTextDC.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natToTextDC_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natToTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natToTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 72, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[72]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => natToTextDC x)
        (fun x heap _ => (Canonical x) ∧ (x.size < 2 ^ 32) ∧
          heap.top.toNat + (438 * x.size + 1968) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.size + 1968) ∧
          natToTextDC x = printSpec (value x : ℤ)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natToTextDC_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natToTextDC.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natToTextDC.bound 1000 x ≤ 438 * x.size + 1968 := natToTextDC_room x hs
  omega

/-! ### `intToTextDC` -/

set_option maxRecDepth 100000 in
/-- Function 73, `intToTextDC`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem intToTextDC_spec_trapFree :
    ImplementsA false compiled.module 73 (fun x : BigInt => intToTextDC x)
      (fun x heap store => (x.Canonical) ∧ heap.Within store compiled.module (compiled.intToTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.mag.size + 1968) ∧
        intToTextDC x = printSpec x.toInt) :=
  ImplementsA.strengthen (compiled.intToTextDC.trapFree.mono
      (fun x _ _ h => ⟨intToTextDC_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.mag.size < 536870912 := rep_mag hr
      have hc := hpre.1
      have e1 := BigInt.eq_ofInt hc
      have t1 := s1
      rw [e1] at t1
      have heq := intToTextDC_eq (z := x.toInt) (by omega)
      rw [← e1] at heq
      exact ⟨le_trans hpost (Nat.add_le_add_left (intToTextDC_room x (by omega)) _), heq⟩

/-- The C function `lxf_intToTextDC` computes `intToTextDC` as `intToTextDC_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem intToTextDC_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intToTextDC_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intToTextDC.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intToTextDC_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intToTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intToTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 73, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[73]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt => intToTextDC x)
        (fun x heap _ => (x.Canonical) ∧ (x.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (438 * x.mag.size + 1968) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.mag.size + 1968) ∧
          intToTextDC x = printSpec x.toInt) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intToTextDC_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intToTextDC.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.intToTextDC.bound 1000 x ≤ 438 * x.mag.size + 1968 := intToTextDC_room x hs
  omega

/-! ### `natDivModCheckedBZWith` -/

set_option maxRecDepth 100000 in
/-- Function 64, `natDivModCheckedBZWith`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natDivModCheckedBZWith_spec_trapFree :
    ImplementsA false compiled.module 64 (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64 => natDivModCheckedBZWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x heap store => (Canonical x.2.2.2.1 ∧ Canonical x.2.2.2.2) ∧ heap.Within store compiled.module (compiled.natDivModCheckedBZWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.2.2.2.1.size + 144 * x.2.2.2.2.size + 824) ∧
        natDivModCheckedBZWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = natDivModCheckedSpec (value x.2.2.2.1) (value x.2.2.2.2)) :=
  ImplementsA.strengthen (compiled.natDivModCheckedBZWith.trapFree.mono
      (fun x _ _ h => ⟨natDivModCheckedBZWith_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r⟩ := rep_snd hr
      obtain ⟨_, r'⟩ := rep_snd r
      obtain ⟨_, r''⟩ := rep_snd r'
      obtain ⟨_, r1⟩ := rep_fst r''
      obtain ⟨_, r2⟩ := rep_snd r''
      have s1 : x.2.2.2.1.size < 536870912 := rep_arr r1
      have s2 : x.2.2.2.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natDivModCheckedBZWith_room x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 (by omega) (by omega)) _), natDivModCheckedBZWith_eq _ _ _ hc.1 hc.2 (by omega) (by omega)⟩

/-- The C function `lxf_natDivModCheckedBZWith` computes `natDivModCheckedBZWith` as `natDivModCheckedBZWith_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natDivModCheckedBZWith_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natDivModCheckedBZWith_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natDivModCheckedBZWith.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natDivModCheckedBZWith_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natDivModCheckedBZWith_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natDivModCheckedBZWith_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 64, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[64]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64 => natDivModCheckedBZWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (fun x heap _ => (Canonical x.2.2.2.1 ∧ Canonical x.2.2.2.2) ∧ (x.2.2.2.1.size < 2 ^ 32 ∧ x.2.2.2.2.size < 2 ^ 32) ∧
          heap.top.toNat + (128 * x.2.2.2.1.size + 144 * x.2.2.2.2.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.2.2.2.1.size + 144 * x.2.2.2.2.size + 824) ∧
          natDivModCheckedBZWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = natDivModCheckedSpec (value x.2.2.2.1) (value x.2.2.2.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natDivModCheckedBZWith_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natDivModCheckedBZWith.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natDivModCheckedBZWith.bound 1000 x ≤ 128 * x.2.2.2.1.size + 144 * x.2.2.2.2.size + 824 := natDivModCheckedBZWith_room x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hs.1 hs.2
  omega

/-! ### `natToTextDCWith` -/

set_option maxRecDepth 100000 in
/-- Function 71, `natToTextDCWith`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natToTextDCWith_spec_trapFree :
    ImplementsA false compiled.module 71 (fun x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => natToTextDCWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x heap store => (Canonical x.2.2.2.2) ∧ heap.Within store compiled.module (compiled.natToTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.2.2.2.2.size + 1968) ∧
        natToTextDCWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = printSpec (value x.2.2.2.2 : ℤ)) :=
  ImplementsA.strengthen (compiled.natToTextDCWith.trapFree.mono
      (fun x _ _ h => ⟨natToTextDCWith_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h)
    (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r⟩ := rep_snd hr
      obtain ⟨_, r'⟩ := rep_snd r
      obtain ⟨_, r''⟩ := rep_snd r'
      obtain ⟨_, r1⟩ := rep_snd r''
      have s1 : x.2.2.2.2.size < 536870912 := rep_arr r1
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natToTextDCWith_room x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 (by omega)) _), natToTextDCWith_eq _ _ _ _ hc (by omega)⟩

/-- The C function `lxf_natToTextDCWith` computes `natToTextDCWith` as `natToTextDCWith_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natToTextDCWith_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natToTextDCWith_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natToTextDCWith.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natToTextDCWith_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natToTextDCWith_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natToTextDCWith_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 71, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[71]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => natToTextDCWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (fun x heap _ => (Canonical x.2.2.2.2) ∧ (x.2.2.2.2.size < 2 ^ 32) ∧
          heap.top.toNat + (438 * x.2.2.2.2.size + 1968) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.2.2.2.2.size + 1968) ∧
          natToTextDCWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = printSpec (value x.2.2.2.2 : ℤ)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natToTextDCWith_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natToTextDCWith.bound 1000 x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  obtain ⟨hp1, hs, hroom⟩ := hpre
  have hb : compiled.natToTextDCWith.bound 1000 x ≤ 438 * x.2.2.2.2.size + 1968 := natToTextDCWith_room x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hs
  omega

end Library.Numerics.Bignum.Third
