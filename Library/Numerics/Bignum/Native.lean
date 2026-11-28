module

public import Library.Numerics.Bignum.Reused
public import LeanExe.Native.Proof.Native

@[expose] public section

/-!
# The C form of the exports

`verified_compile` translates `compiled.module` to a program in the subset of CompCert's Clight that
leanexe's translator emits, with `lx_mem` of `nativeCap` pages, 256 MiB, and states
`compiled.translation_eq`.  The C function `lxf_f` of each export takes its arguments in the order
of the Lean definition, an array as the address of its object in `lx_mem` and a `BigInt` as its
sign word and the address of its magnitude, and returns a word or an array's address, or leaves
several results in the translation's result globals `lx_r0_l`, `lx_r1_l`, and so on, in the order
of the result's words.

For each export of the library's interface, `f_spec_trapFree` adds the export's claim to the
generated theorem without a trap: from a store whose heap meets the allocator invariant, has room
for the generated bound, and holds canonical arguments (limbs below `2^32` for `natTrim`, nothing
for the text exports), the call returns the Lean function's value, which equals the specification's
value of `Spec.lean`, and raises `top` by at most the closed form of `Bound.lean` or `Export.lean`.
`f_native_spec` carries it to the C function, under every `Archi` and every semantics of external
functions, through `LeanExe.Native.ImplementsA.native`: from a C memory related to such a store,
with the arguments represented in it, the call terminates with `lx_status` 0 and results that
represent the Lean function's value.  `f_native_size` states the premise as arithmetic on the
256 MiB of `lx_mem`: canonical arguments of fewer than `2^32` limbs (texts of fewer than `2^30`
words, and fewer than `2^32` for `intOfText`) and a heap whose `top` plus the closed form is at most
`2^28`.  The C memory of 256 MiB bounds the inputs that the C theorems cover, where the WebAssembly
module's memory can grow to 65,535 pages.  The comparisons allocate
nothing and cannot trap, so their theorems take no room.

The theorems concern one call in leanexe's Lean copy of CompCert's Clight.  The hosted executable
that `ccomp` compiles with `host/bignum.c` has no theorem as a whole.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision (value Digits)
open LeanExe.Pipeline

/-- A precondition strengthened and a postcondition that uses it and the arguments'
representation. -/
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

/-! ### `natTrim` -/

set_option maxRecDepth 100000 in
/-- Function 20, `natTrim`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem natTrim_spec_trapFree :
    ImplementsA false compiled.module 20 (fun x : Array UInt64 => natTrim x)
      (fun x heap store => (Digits x) ∧ heap.Within store compiled.module (compiled.natTrim.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (8 * x.size + 56) ∧
        natTrim x = limbsOf (value x)) :=
  ImplementsA.strengthen compiled.natTrim.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.size < 536870912 := rep_arr hr
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natTrim_bound_le x (by omega)) _), natTrim_eq hc (by omega)⟩

/-- The C function `lxf_natTrim` computes `natTrim` as `natTrim_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem natTrim_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natTrim_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natTrim.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natTrim_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natTrim_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natTrim_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 20, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[20]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => natTrim x)
        (fun x heap _ => (Digits x) ∧ x.size < 2 ^ 32 ∧
          heap.top.toNat + (8 * x.size + 56) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (8 * x.size + 56) ∧
          natTrim x = limbsOf (value x)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natTrim_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natTrim.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.natTrim.bound x ≤ 8 * x.size + 56 := natTrim_bound_le x (by omega)
  omega

/-! ### `natCmp` -/

set_option maxRecDepth 100000 in
/-- Function 21, `natCmp`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem natCmp_spec_trapFree :
    ImplementsA false compiled.module 21 (fun x : Array UInt64 × Array UInt64 => natCmp x.1 x.2)
      (fun x _ _ => Canonical x.1 ∧ Canonical x.2)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (0) ∧
        natCmp x.1 x.2 = cmpSpec (value x.1) (value x.2)) :=
  ImplementsA.strengthen compiled.natCmp.trapFree (fun _ _ _ _ => trivial)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre
      exact ⟨le_trans hpost (Nat.add_le_add_left (natCmp_bound x).le _), natCmp_eq hc.1.1 hc.2.1 (by omega) (by omega)⟩

/-- The C function `lxf_natCmp` computes `natCmp` as `natCmp_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem natCmp_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natCmp_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natCmp.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natCmp_spec_trapFree compiled.translation_eq hfd hsig⟩

/-! ### `natAdd` -/

set_option maxRecDepth 100000 in
/-- Function 22, `natAdd`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem natAdd_spec_trapFree :
    ImplementsA false compiled.module 22 (fun x : Array UInt64 × Array UInt64 => natAdd x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * max x.1.size x.2.size + 232) ∧
        natAdd x.1 x.2 = limbsOf (value x.1 + value x.2)) :=
  ImplementsA.strengthen compiled.natAdd.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natAdd_bound_le x.1 x.2 (by omega) (by omega)) _), natAdd_eq hc.1.1 hc.2.1 (by omega) (by omega)⟩

/-- The C function `lxf_natAdd` computes `natAdd` as `natAdd_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem natAdd_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natAdd_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natAdd.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natAdd_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natAdd_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natAdd_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 22, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[22]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natAdd x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32 ∧
          heap.top.toNat + (104 * max x.1.size x.2.size + 232) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * max x.1.size x.2.size + 232) ∧
          natAdd x.1 x.2 = limbsOf (value x.1 + value x.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natAdd_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natAdd.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.natAdd.bound x ≤ 104 * max x.1.size x.2.size + 232 := natAdd_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `natSub` -/

set_option maxRecDepth 100000 in
/-- Function 23, `natSub`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem natSub_spec_trapFree :
    ImplementsA false compiled.module 23 (fun x : Array UInt64 × Array UInt64 => natSub x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natSub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (88 * max x.1.size x.2.size + 128) ∧
        natSub x.1 x.2 = natSubSpec (value x.1) (value x.2)) :=
  ImplementsA.strengthen compiled.natSub.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natSub_bound_le x.1 x.2 (by omega) (by omega)) _), natSub_eq hc.1.1 hc.2.1 (by omega) (by omega)⟩

/-- The C function `lxf_natSub` computes `natSub` as `natSub_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem natSub_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natSub_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natSub.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natSub_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natSub_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natSub_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 23, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[23]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natSub x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32 ∧
          heap.top.toNat + (88 * max x.1.size x.2.size + 128) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (88 * max x.1.size x.2.size + 128) ∧
          natSub x.1 x.2 = natSubSpec (value x.1) (value x.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natSub_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natSub.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.natSub.bound x ≤ 88 * max x.1.size x.2.size + 128 := natSub_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `natMul` -/

set_option maxRecDepth 100000 in
/-- Function 24, `natMul`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem natMul_spec_trapFree :
    ImplementsA false compiled.module 24 (fun x : Array UInt64 × Array UInt64 => natMul x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natMul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (16 * (x.1.size + x.2.size) + 112) ∧
        natMul x.1 x.2 = limbsOf (value x.1 * value x.2)) :=
  ImplementsA.strengthen compiled.natMul.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natMul_bound_le x.1 x.2 (by omega) (by omega)) _), natMul_eq hc.1.1 hc.2.1 (by omega) (by omega)⟩

/-- The C function `lxf_natMul` computes `natMul` as `natMul_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem natMul_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natMul_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natMul.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natMul_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natMul_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natMul_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 24, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[24]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natMul x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32 ∧
          heap.top.toNat + (16 * (x.1.size + x.2.size) + 112) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (16 * (x.1.size + x.2.size) + 112) ∧
          natMul x.1 x.2 = limbsOf (value x.1 * value x.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natMul_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natMul.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.natMul.bound x ≤ 16 * (x.1.size + x.2.size) + 112 := natMul_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `natDivModChecked` -/

set_option maxRecDepth 100000 in
/-- Function 25, `natDivModChecked`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem natDivModChecked_spec_trapFree :
    ImplementsA false compiled.module 25 (fun x : Array UInt64 × Array UInt64 => natDivModChecked x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natDivModChecked.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ∧
        natDivModChecked x.1 x.2 = natDivModCheckedSpec (value x.1) (value x.2)) :=
  ImplementsA.strengthen compiled.natDivModChecked.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (natDivModChecked_bound_le x.1 x.2 (by omega) (by omega)) _), natDivModChecked_eq hc.1 hc.2 (by omega) (by omega)⟩

/-- The C function `lxf_natDivModChecked` computes `natDivModChecked` as `natDivModChecked_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem natDivModChecked_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natDivModChecked_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.natDivModChecked.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native natDivModChecked_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `natDivModChecked_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natDivModChecked_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 25, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[25]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natDivModChecked x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32 ∧
          heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ∧
          natDivModChecked x.1 x.2 = natDivModCheckedSpec (value x.1) (value x.2)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := natDivModChecked_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.natDivModChecked.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.natDivModChecked.bound x ≤ 128 * x.1.size + 144 * x.2.size + 824 := natDivModChecked_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `intNeg` -/

set_option maxRecDepth 100000 in
/-- Function 26, `intNeg`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intNeg_spec_trapFree :
    ImplementsA false compiled.module 26 (fun x : BigInt => intNeg x)
      (fun x heap store => (x.Canonical) ∧ heap.Within store compiled.module (compiled.intNeg.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (8 * x.mag.size + 56) ∧
        intNeg x = .ofInt (-x.toInt)) :=
  ImplementsA.strengthen compiled.intNeg.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.mag.size < 536870912 := rep_mag hr
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intNeg_bound_le x (by omega)) _), by
        have h := intNeg_eq (a := x.toInt) (by rw [← BigInt.eq_ofInt hc]; omega)
        rw [← BigInt.eq_ofInt hc] at h
        exact h⟩

/-- The C function `lxf_intNeg` computes `intNeg` as `intNeg_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intNeg_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intNeg_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intNeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intNeg_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intNeg_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intNeg_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 26, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[26]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt => intNeg x)
        (fun x heap _ => (x.Canonical) ∧ x.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (8 * x.mag.size + 56) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (8 * x.mag.size + 56) ∧
          intNeg x = .ofInt (-x.toInt)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intNeg_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intNeg.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intNeg.bound x ≤ 8 * x.mag.size + 56 := intNeg_bound_le x (by omega)
  omega

/-! ### `intCmp` -/

set_option maxRecDepth 100000 in
/-- Function 27, `intCmp`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intCmp_spec_trapFree :
    ImplementsA false compiled.module 27 (fun x : BigInt × BigInt => intCmp x.1 x.2)
      (fun x _ _ => x.1.Canonical ∧ x.2.Canonical)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (0) ∧
        intCmp x.1 x.2 = cmpSpec x.1.toInt x.2.toInt) :=
  ImplementsA.strengthen compiled.intCmp.trapFree (fun _ _ _ _ => trivial)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre
      exact ⟨le_trans hpost (Nat.add_le_add_left (intCmp_bound x).le _), by
        have h := intCmp_eq (a := x.1.toInt) (b := x.2.toInt) (by rw [← BigInt.eq_ofInt hc.1]; omega)
          (by rw [← BigInt.eq_ofInt hc.2]; omega)
        rw [← BigInt.eq_ofInt hc.1, ← BigInt.eq_ofInt hc.2] at h
        exact h⟩

/-- The C function `lxf_intCmp` computes `intCmp` as `intCmp_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intCmp_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intCmp_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intCmp.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intCmp_spec_trapFree compiled.translation_eq hfd hsig⟩

/-! ### `intAdd` -/

set_option maxRecDepth 100000 in
/-- Function 28, `intAdd`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intAdd_spec_trapFree :
    ImplementsA false compiled.module 28 (fun x : BigInt × BigInt => intAdd x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * max x.1.mag.size x.2.mag.size + 232) ∧
        intAdd x.1 x.2 = .ofInt (x.1.toInt + x.2.toInt)) :=
  ImplementsA.strengthen compiled.intAdd.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intAdd_bound_le x.1 x.2 (by omega) (by omega)) _), by
        have h := intAdd_eq (a := x.1.toInt) (b := x.2.toInt) (by rw [← BigInt.eq_ofInt hc.1]; omega)
          (by rw [← BigInt.eq_ofInt hc.2]; omega)
        rw [← BigInt.eq_ofInt hc.1, ← BigInt.eq_ofInt hc.2] at h
        exact h⟩

/-- The C function `lxf_intAdd` computes `intAdd` as `intAdd_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intAdd_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intAdd_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intAdd.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intAdd_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intAdd_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intAdd_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 28, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[28]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intAdd x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (104 * max x.1.mag.size x.2.mag.size + 232) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * max x.1.mag.size x.2.mag.size + 232) ∧
          intAdd x.1 x.2 = .ofInt (x.1.toInt + x.2.toInt)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intAdd_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intAdd.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intAdd.bound x ≤ 104 * max x.1.mag.size x.2.mag.size + 232 := intAdd_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `intSub` -/

set_option maxRecDepth 100000 in
/-- Function 29, `intSub`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intSub_spec_trapFree :
    ImplementsA false compiled.module 29 (fun x : BigInt × BigInt => intSub x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intSub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * max x.1.mag.size x.2.mag.size + 232) ∧
        intSub x.1 x.2 = .ofInt (x.1.toInt - x.2.toInt)) :=
  ImplementsA.strengthen compiled.intSub.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intSub_bound_le x.1 x.2 (by omega) (by omega)) _), by
        have h := intSub_eq (a := x.1.toInt) (b := x.2.toInt) (by rw [← BigInt.eq_ofInt hc.1]; omega)
          (by rw [← BigInt.eq_ofInt hc.2]; omega)
        rw [← BigInt.eq_ofInt hc.1, ← BigInt.eq_ofInt hc.2] at h
        exact h⟩

/-- The C function `lxf_intSub` computes `intSub` as `intSub_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intSub_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intSub_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intSub.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intSub_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intSub_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intSub_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 29, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[29]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intSub x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (104 * max x.1.mag.size x.2.mag.size + 232) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * max x.1.mag.size x.2.mag.size + 232) ∧
          intSub x.1 x.2 = .ofInt (x.1.toInt - x.2.toInt)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intSub_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intSub.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intSub.bound x ≤ 104 * max x.1.mag.size x.2.mag.size + 232 := intSub_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `intMul` -/

set_option maxRecDepth 100000 in
/-- Function 30, `intMul`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intMul_spec_trapFree :
    ImplementsA false compiled.module 30 (fun x : BigInt × BigInt => intMul x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intMul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (16 * (x.1.mag.size + x.2.mag.size) + 112) ∧
        intMul x.1 x.2 = .ofInt (x.1.toInt * x.2.toInt)) :=
  ImplementsA.strengthen compiled.intMul.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intMul_bound_le x.1 x.2 (by omega) (by omega)) _), by
        have h := intMul_eq (a := x.1.toInt) (b := x.2.toInt) (by rw [← BigInt.eq_ofInt hc.1]; omega)
          (by rw [← BigInt.eq_ofInt hc.2]; omega)
        rw [← BigInt.eq_ofInt hc.1, ← BigInt.eq_ofInt hc.2] at h
        exact h⟩

/-- The C function `lxf_intMul` computes `intMul` as `intMul_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intMul_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intMul_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intMul.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intMul_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intMul_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intMul_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 30, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[30]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intMul x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (16 * (x.1.mag.size + x.2.mag.size) + 112) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (16 * (x.1.mag.size + x.2.mag.size) + 112) ∧
          intMul x.1 x.2 = .ofInt (x.1.toInt * x.2.toInt)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intMul_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intMul.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intMul.bound x ≤ 16 * (x.1.mag.size + x.2.mag.size) + 112 := intMul_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `intTDivModChecked` -/

set_option maxRecDepth 100000 in
/-- Function 31, `intTDivModChecked`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intTDivModChecked_spec_trapFree :
    ImplementsA false compiled.module 31 (fun x : BigInt × BigInt => intTDivModChecked x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intTDivModChecked.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ∧
        intTDivModChecked x.1 x.2 = intTDivModCheckedSpec x.1.toInt x.2.toInt) :=
  ImplementsA.strengthen compiled.intTDivModChecked.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intTDivModChecked_bound_le x.1 x.2 (by omega) (by omega)) _), by
        have h := intTDivModChecked_eq (a := x.1.toInt) (b := x.2.toInt) (by rw [← BigInt.eq_ofInt hc.1]; omega)
          (by rw [← BigInt.eq_ofInt hc.2]; omega)
        rw [← BigInt.eq_ofInt hc.1, ← BigInt.eq_ofInt hc.2] at h
        exact h⟩

/-- The C function `lxf_intTDivModChecked` computes `intTDivModChecked` as `intTDivModChecked_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intTDivModChecked_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intTDivModChecked_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intTDivModChecked.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intTDivModChecked_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intTDivModChecked_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intTDivModChecked_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 31, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[31]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intTDivModChecked x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ∧
          intTDivModChecked x.1 x.2 = intTDivModCheckedSpec x.1.toInt x.2.toInt) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intTDivModChecked_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intTDivModChecked.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intTDivModChecked.bound x ≤ 128 * x.1.mag.size + 144 * x.2.mag.size + 824 := intTDivModChecked_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `intEDivModChecked` -/

set_option maxRecDepth 100000 in
/-- Function 32, `intEDivModChecked`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intEDivModChecked_spec_trapFree :
    ImplementsA false compiled.module 32 (fun x : BigInt × BigInt => intEDivModChecked x.1 x.2)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intEDivModChecked.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (232 * x.1.mag.size + 232 * x.2.mag.size + 1440) ∧
        intEDivModChecked x.1 x.2 = intEDivModCheckedSpec x.1.toInt x.2.toInt) :=
  ImplementsA.strengthen compiled.intEDivModChecked.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.mag.size < 536870912 := rep_mag r1
      have s2 : x.2.mag.size < 536870912 := rep_mag r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intEDivModChecked_bound_le x.1 x.2 (by omega) (by omega)) _), by
        have h := intEDivModChecked_eq (a := x.1.toInt) (b := x.2.toInt) (by rw [← BigInt.eq_ofInt hc.1]; omega)
          (by rw [← BigInt.eq_ofInt hc.2]; omega)
        rw [← BigInt.eq_ofInt hc.1, ← BigInt.eq_ofInt hc.2] at h
        exact h⟩

/-- The C function `lxf_intEDivModChecked` computes `intEDivModChecked` as `intEDivModChecked_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intEDivModChecked_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intEDivModChecked_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intEDivModChecked.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intEDivModChecked_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intEDivModChecked_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intEDivModChecked_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 32, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[32]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intEDivModChecked x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (232 * x.1.mag.size + 232 * x.2.mag.size + 1440) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (232 * x.1.mag.size + 232 * x.2.mag.size + 1440) ∧
          intEDivModChecked x.1 x.2 = intEDivModCheckedSpec x.1.toInt x.2.toInt) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intEDivModChecked_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intEDivModChecked.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intEDivModChecked.bound x ≤ 232 * x.1.mag.size + 232 * x.2.mag.size + 1440 := intEDivModChecked_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `intToText` -/

set_option maxRecDepth 100000 in
/-- Function 33, `intToText`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intToText_spec_trapFree :
    ImplementsA false compiled.module 33 (fun x : BigInt => intToText x)
      (fun x heap store => (x.Canonical) ∧ heap.Within store compiled.module (compiled.intToText.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (94 * x.mag.size + 424) ∧
        intToText x = printSpec x.toInt) :=
  ImplementsA.strengthen compiled.intToText.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.mag.size < 536870912 := rep_mag hr
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intToText_bound_le x ((BigInt.canonical_iff x).mp hc).1.1 (by omega)) _), by
        have h := intToText_eq (z := x.toInt) (by rw [← BigInt.eq_ofInt hc]; omega)
        rw [← BigInt.eq_ofInt hc] at h
        exact h⟩

/-- The C function `lxf_intToText` computes `intToText` as `intToText_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intToText_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intToText_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intToText.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intToText_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intToText_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intToText_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 33, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[33]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt => intToText x)
        (fun x heap _ => (x.Canonical) ∧ x.mag.size < 2 ^ 32 ∧
          heap.top.toNat + (94 * x.mag.size + 424) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (94 * x.mag.size + 424) ∧
          intToText x = printSpec x.toInt) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intToText_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intToText.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intToText.bound x ≤ 94 * x.mag.size + 424 :=
    intToText_bound_le x ((BigInt.canonical_iff x).mp hpre.1).1.1 (by omega)
  omega

/-! ### `intOfText` -/

set_option maxRecDepth 100000 in
/-- Function 34, `intOfText`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem intOfText_spec_trapFree :
    ImplementsA false compiled.module 34 (fun x : Array UInt64 => intOfText x)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.intOfText.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (2 * x.size + 128) ∧
        intOfText x = readSpec x) :=
  ImplementsA.strengthen compiled.intOfText.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.size < 536870912 := rep_arr hr
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (intOfText_bound_le x (by omega)) _), intOfText_eq x (by omega)⟩

/-- The C function `lxf_intOfText` computes `intOfText` as `intOfText_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem intOfText_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl intOfText_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.intOfText.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native intOfText_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `intOfText_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intOfText_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 34, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[34]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => intOfText x)
        (fun x heap _ => (True) ∧ x.size < 2 ^ 32 ∧
          heap.top.toNat + (2 * x.size + 128) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (2 * x.size + 128) ∧
          intOfText x = readSpec x) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := intOfText_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.intOfText.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.intOfText.bound x ≤ 2 * x.size + 128 := intOfText_bound_le x (by omega)
  omega

/-! ### `textNeg` -/

set_option maxRecDepth 100000 in
/-- Function 35, `textNeg`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textNeg_spec_trapFree :
    ImplementsA false compiled.module 35 (fun x : Array UInt64 => textNeg x)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textNeg.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * x.size + 608) ∧
        textNeg x = textNegSpec x) :=
  ImplementsA.strengthen compiled.textNeg.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      have s1 : x.size < 536870912 := rep_arr hr
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textNeg_bound_le x (by omega)) _), textNeg_eq x (by omega)⟩

/-- The C function `lxf_textNeg` computes `textNeg` as `textNeg_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textNeg_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textNeg_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textNeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textNeg_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textNeg_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textNeg_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 35, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[35]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => textNeg x)
        (fun x heap _ => (True) ∧ x.size < 2 ^ 30 ∧
          heap.top.toNat + (104 * x.size + 608) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (104 * x.size + 608) ∧
          textNeg x = textNegSpec x) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textNeg_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textNeg.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textNeg.bound x ≤ 104 * x.size + 608 := textNeg_bound_le x (by omega)
  omega

/-! ### `textCmp` -/

set_option maxRecDepth 100000 in
/-- Function 36, `textCmp`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textCmp_spec_trapFree :
    ImplementsA false compiled.module 36 (fun x : Array UInt64 × Array UInt64 => textCmp x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textCmp.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (2 * (x.1.size + x.2.size) + 256) ∧
        textCmp x.1 x.2 = textCmpSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textCmp.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textCmp_bound_le x.1 x.2 (by omega) (by omega)) _), textCmp_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textCmp` computes `textCmp` as `textCmp_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textCmp_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textCmp_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textCmp.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textCmp_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textCmp_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textCmp_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 36, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[36]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textCmp x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (2 * (x.1.size + x.2.size) + 256) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (2 * (x.1.size + x.2.size) + 256) ∧
          textCmp x.1 x.2 = textCmpSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textCmp_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textCmp.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textCmp.bound x ≤ 2 * (x.1.size + x.2.size) + 256 := textCmp_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textAdd` -/

set_option maxRecDepth 100000 in
/-- Function 37, `textAdd`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textAdd_spec_trapFree :
    ImplementsA false compiled.module 37 (fun x : Array UInt64 × Array UInt64 => textAdd x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (200 * (x.1.size + x.2.size) + 1006) ∧
        textAdd x.1 x.2 = textAddSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textAdd.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textAdd_bound_le x.1 x.2 (by omega) (by omega)) _), textAdd_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textAdd` computes `textAdd` as `textAdd_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textAdd_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textAdd_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textAdd.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textAdd_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textAdd_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textAdd_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 37, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[37]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textAdd x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (200 * (x.1.size + x.2.size) + 1006) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (200 * (x.1.size + x.2.size) + 1006) ∧
          textAdd x.1 x.2 = textAddSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textAdd_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textAdd.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textAdd.bound x ≤ 200 * (x.1.size + x.2.size) + 1006 := textAdd_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textSub` -/

set_option maxRecDepth 100000 in
/-- Function 38, `textSub`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textSub_spec_trapFree :
    ImplementsA false compiled.module 38 (fun x : Array UInt64 × Array UInt64 => textSub x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textSub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (200 * (x.1.size + x.2.size) + 1006) ∧
        textSub x.1 x.2 = textSubSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textSub.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textSub_bound_le x.1 x.2 (by omega) (by omega)) _), textSub_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textSub` computes `textSub` as `textSub_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textSub_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textSub_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textSub.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textSub_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textSub_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textSub_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 38, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[38]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textSub x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (200 * (x.1.size + x.2.size) + 1006) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (200 * (x.1.size + x.2.size) + 1006) ∧
          textSub x.1 x.2 = textSubSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textSub_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textSub.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textSub.bound x ≤ 200 * (x.1.size + x.2.size) + 1006 := textSub_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textMul` -/

set_option maxRecDepth 100000 in
/-- Function 39, `textMul`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textMul_spec_trapFree :
    ImplementsA false compiled.module 39 (fun x : Array UInt64 × Array UInt64 => textMul x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textMul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (112 * (x.1.size + x.2.size) + 886) ∧
        textMul x.1 x.2 = textMulSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textMul.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textMul_bound_le x.1 x.2 (by omega) (by omega)) _), textMul_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textMul` computes `textMul` as `textMul_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textMul_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textMul_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textMul.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textMul_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textMul_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textMul_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 39, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[39]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textMul x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (112 * (x.1.size + x.2.size) + 886) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (112 * (x.1.size + x.2.size) + 886) ∧
          textMul x.1 x.2 = textMulSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textMul_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textMul.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textMul.bound x ≤ 112 * (x.1.size + x.2.size) + 886 := textMul_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textTDiv` -/

set_option maxRecDepth 100000 in
/-- Function 40, `textTDiv`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textTDiv_spec_trapFree :
    ImplementsA false compiled.module 40 (fun x : Array UInt64 × Array UInt64 => textTDiv x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textTDiv.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (240 * (x.1.size + x.2.size) + 1598) ∧
        textTDiv x.1 x.2 = textTDivSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textTDiv.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textTDiv_bound_le x.1 x.2 (by omega) (by omega)) _), textTDiv_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textTDiv` computes `textTDiv` as `textTDiv_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textTDiv_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textTDiv_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textTDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textTDiv_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textTDiv_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textTDiv_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 40, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[40]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textTDiv x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (240 * (x.1.size + x.2.size) + 1598) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (240 * (x.1.size + x.2.size) + 1598) ∧
          textTDiv x.1 x.2 = textTDivSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textTDiv_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textTDiv.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textTDiv.bound x ≤ 240 * (x.1.size + x.2.size) + 1598 := textTDiv_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textTMod` -/

set_option maxRecDepth 100000 in
/-- Function 41, `textTMod`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textTMod_spec_trapFree :
    ImplementsA false compiled.module 41 (fun x : Array UInt64 × Array UInt64 => textTMod x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textTMod.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (240 * (x.1.size + x.2.size) + 1598) ∧
        textTMod x.1 x.2 = textTModSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textTMod.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textTMod_bound_le x.1 x.2 (by omega) (by omega)) _), textTMod_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textTMod` computes `textTMod` as `textTMod_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textTMod_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textTMod_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textTMod.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textTMod_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textTMod_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textTMod_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 41, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[41]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textTMod x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (240 * (x.1.size + x.2.size) + 1598) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (240 * (x.1.size + x.2.size) + 1598) ∧
          textTMod x.1 x.2 = textTModSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textTMod_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textTMod.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textTMod.bound x ≤ 240 * (x.1.size + x.2.size) + 1598 := textTMod_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textEDiv` -/

set_option maxRecDepth 100000 in
/-- Function 42, `textEDiv`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textEDiv_spec_trapFree :
    ImplementsA false compiled.module 42 (fun x : Array UInt64 × Array UInt64 => textEDiv x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textEDiv.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (344 * (x.1.size + x.2.size) + 2214) ∧
        textEDiv x.1 x.2 = textEDivSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textEDiv.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textEDiv_bound_le x.1 x.2 (by omega) (by omega)) _), textEDiv_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textEDiv` computes `textEDiv` as `textEDiv_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textEDiv_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textEDiv_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textEDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textEDiv_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textEDiv_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textEDiv_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 42, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[42]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textEDiv x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (344 * (x.1.size + x.2.size) + 2214) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (344 * (x.1.size + x.2.size) + 2214) ∧
          textEDiv x.1 x.2 = textEDivSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textEDiv_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textEDiv.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textEDiv.bound x ≤ 344 * (x.1.size + x.2.size) + 2214 := textEDiv_bound_le x.1 x.2 (by omega) (by omega)
  omega

/-! ### `textEMod` -/

set_option maxRecDepth 100000 in
/-- Function 43, `textEMod`, returns the Lean function's value, which meets its specification, and raises
`top` by at most the closed form of its bound. -/
theorem textEMod_spec_trapFree :
    ImplementsA false compiled.module 43 (fun x : Array UInt64 × Array UInt64 => textEMod x.1 x.2)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.textEMod.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (344 * (x.1.size + x.2.size) + 2214) ∧
        textEMod x.1 x.2 = textEModSpec x.1 x.2) :=
  ImplementsA.strengthen compiled.textEMod.trapFree (fun _ _ _ h => h.2)
    fun heap store _ x heap' _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨le_trans hpost (Nat.add_le_add_left (textEMod_bound_le x.1 x.2 (by omega) (by omega)) _), textEMod_eq x.1 x.2 (by omega) (by omega)⟩

/-- The C function `lxf_textEMod` computes `textEMod` as `textEMod_spec_trapFree` states, under every `Archi` and
every semantics of external functions. -/
theorem textEMod_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl textEMod_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textEMod.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native textEMod_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- `textEMod_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem textEMod_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 43, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[43]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => textEMod x.1 x.2)
        (fun x heap _ => (True) ∧ x.1.size < 2 ^ 30 ∧ x.2.size < 2 ^ 30 ∧
          heap.top.toNat + (344 * (x.1.size + x.2.size) + 2214) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (344 * (x.1.size + x.2.size) + 2214) ∧
          textEMod x.1 x.2 = textEModSpec x.1 x.2) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := textEMod_native_spec A X
  refine ⟨fd, ps, rs, hfd, hsig, LeanExe.Native.NativeA.weaken h ?_⟩
  intro E store heap x m hcap hst hpre
  refine ⟨hpre.1, ?_⟩
  show heap.top.toNat + compiled.textEMod.bound x ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  have : LeanExe.Native.nativeCap = 4096 := rfl
  have hb : compiled.textEMod.bound x ≤ 344 * (x.1.size + x.2.size) + 2214 := textEMod_bound_le x.1 x.2 (by omega) (by omega)
  omega

#print axioms natTrim_native_spec
#print axioms natTrim_native_size
#print axioms natCmp_native_spec
#print axioms natAdd_native_spec
#print axioms natAdd_native_size
#print axioms natSub_native_spec
#print axioms natSub_native_size
#print axioms natMul_native_spec
#print axioms natMul_native_size
#print axioms natDivModChecked_native_spec
#print axioms natDivModChecked_native_size
#print axioms intNeg_native_spec
#print axioms intNeg_native_size
#print axioms intCmp_native_spec
#print axioms intAdd_native_spec
#print axioms intAdd_native_size
#print axioms intSub_native_spec
#print axioms intSub_native_size
#print axioms intMul_native_spec
#print axioms intMul_native_size
#print axioms intTDivModChecked_native_spec
#print axioms intTDivModChecked_native_size
#print axioms intEDivModChecked_native_spec
#print axioms intEDivModChecked_native_size
#print axioms intToText_native_spec
#print axioms intToText_native_size
#print axioms intOfText_native_spec
#print axioms intOfText_native_size
#print axioms textNeg_native_spec
#print axioms textNeg_native_size
#print axioms textCmp_native_spec
#print axioms textCmp_native_size
#print axioms textAdd_native_spec
#print axioms textAdd_native_size
#print axioms textSub_native_spec
#print axioms textSub_native_size
#print axioms textMul_native_spec
#print axioms textMul_native_size
#print axioms textTDiv_native_spec
#print axioms textTDiv_native_size
#print axioms textTMod_native_spec
#print axioms textTMod_native_size
#print axioms textEDiv_native_spec
#print axioms textEDiv_native_size
#print axioms textEMod_native_spec
#print axioms textEMod_native_size

end Library.Numerics.Bignum
