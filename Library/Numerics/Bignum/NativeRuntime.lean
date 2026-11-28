module

public import Library.Numerics.Bignum.Native
public import LeanExe.Native.Proof.Main
import all Init.Data.Repr

@[expose] public section

/-!
# The C program around the exports' theorems

`native_names` states that the C function of each export is `lxf_` followed by the export's name,
and it names `lx_init`, `lx_status`, `lx_mem`, and the result globals, so the theorems of
`Native.lean`, which name the C functions and globals by their identifiers, concern the symbols that
a C host uses.  `native_start` states that the program's start meets those theorems' premises on the
environment, the memory, and the heap: `init_mem` of the translation and `lx_init` give a C memory
related to the module's initial store with `lx_mem` of `nativeCap` pages, `lx_status` 0, and the
program's environment, which meets every hypothesis on the environment of `LeanExe.Native.NativeA`,
and the initial heap meets the allocator invariant with `top` at 4,096 bytes.  `alloc_room_native`
and `release_native` are leanexe's theorems of the runtime's functions at this translation, with the
allocator invariant after each call, through which a C host places arguments in `lx_mem` and
releases them; the host's writes of the arguments' words into an allocated block have no theorem.
The functions of MultiPrecision, Uscale, and Int64Text that the module also exports have C theorems
as the call theorems of `Reused.lean` state them: MultiPrecision's specifications for `add`, `sub`,
`mul`, and `divide`, Uscale's for `le`, and the Lean function without a trap within its bound for
the others.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Arithmetic.Uscale (mulSmall wordBits limb cmpStep le)
open Library.Numerics.Decimal.Int64Text (digitCount digitByte isDigitW)
open LeanExe.Pipeline LeanExe.Native LClight

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The C function of each export is `lxf_` followed by the export's name, `lx_init`, `lx_status`,
`lx_mem`, and the result globals `lx_r0_l` to `lx_r4_l` that a host reads are the identifiers that
the theorems name, the translation has five result positions, and no two of its identifiers and no
two of its names coincide. -/
theorem native_names :
    (∀ p ∈ [(initId, "lx_init"),
      (statusId, "lx_status"),
      (memId, "lx_mem"),
      (resId 0 .i64, "lx_r0_l"),
      (resId 1 .i64, "lx_r1_l"),
      (resId 2 .i64, "lx_r2_l"),
      (resId 3 .i64, "lx_r3_l"),
      (resId 4 .i64, "lx_r4_l"),
      (funId 0, "lxf_alloc"),
      (funId 1, "lxf_release"),
      (funId 2, "lxf_width"),
      (funId 3, "lxf_add"),
      (funId 4, "lxf_sub"),
      (funId 5, "lxf_mul"),
      (funId 6, "lxf_significant"),
      (funId 7, "lxf_mulSmall"),
      (funId 8, "lxf_wordBits"),
      (funId 9, "lxf_shortDiv"),
      (funId 10, "lxf_tooBig"),
      (funId 11, "lxf_trial"),
      (funId 12, "lxf_longDiv"),
      (funId 13, "lxf_divide"),
      (funId 14, "lxf_limb"),
      (funId 15, "lxf_cmpStep"),
      (funId 16, "lxf_le"),
      (funId 17, "lxf_digitCount"),
      (funId 18, "lxf_digitByte"),
      (funId 19, "lxf_isDigitW"),
      (funId 20, "lxf_natTrim"),
      (funId 21, "lxf_natCmp"),
      (funId 22, "lxf_natAdd"),
      (funId 23, "lxf_natSub"),
      (funId 24, "lxf_natMul"),
      (funId 25, "lxf_natDivModChecked"),
      (funId 26, "lxf_intNeg"),
      (funId 27, "lxf_intCmp"),
      (funId 28, "lxf_intAdd"),
      (funId 29, "lxf_intSub"),
      (funId 30, "lxf_intMul"),
      (funId 31, "lxf_intTDivModChecked"),
      (funId 32, "lxf_intEDivModChecked"),
      (funId 33, "lxf_intToText"),
      (funId 34, "lxf_intOfText"),
      (funId 35, "lxf_textNeg"),
      (funId 36, "lxf_textCmp"),
      (funId 37, "lxf_textAdd"),
      (funId 38, "lxf_textSub"),
      (funId 39, "lxf_textMul"),
      (funId 40, "lxf_textTDiv"),
      (funId 41, "lxf_textTMod"),
      (funId 42, "lxf_textEDiv"),
      (funId 43, "lxf_textEMod")],
      p ∈ compiled.translation.names) ∧
    compiled.translation.nres = 5 ∧
    (compiled.translation.names.map Prod.fst).Nodup ∧
    (compiled.translation.names.map Prod.snd).Nodup := by
  decide +kernel

/-- The program's start meets the C theorems' premises on the environment, the memory, and the
heap: `init_mem` and `lx_init` give a memory related to `nativeStore` with `lx_status` 0, in the
program's environment, the initial heap meets the allocator invariant with `top` at 4,096 bytes, and
the store's memory has the cap of `nativeCap` pages. -/
theorem native_start (A : Archi) (X : ExtSem) :
    ∃ decl m0 m1, compiled.module.memory = some decl ∧
      init_mem A compiled.translation.cprogram = some m0 ∧
      (initId, globdef.Gfun (.Internal (initFunction nativeCap decl.data))) ∈
        compiled.translation.cprogram.prog_defs ∧
      eval_funcall A X (globalenv compiled.translation.cprogram) m0
        (.Internal (initFunction nativeCap decl.data)) [] E0 m1 .Vundef ∧
      StoreRel A (envOf compiled.translation compiled.module.globals.length nativeCap)
        (nativeStore compiled.module nativeCap) m1 ∧
      StatusRel A (envOf compiled.translation compiled.module.globals.length nativeCap) m1 0 ∧
      EnvOk (envOf compiled.translation compiled.module.globals.length nativeCap) ∧
      (envOf compiled.translation compiled.module.globals.length nativeCap).globals.length =
        compiled.module.globals.length ∧
      (envOf compiled.translation compiled.module.globals.length nativeCap).cap = nativeCap ∧
      compiled.translation.nres ≤
        (envOf compiled.translation compiled.module.globals.length nativeCap).nres ∧
      (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
        ∃ b, Genv.find_symbol
            (envOf compiled.translation compiled.module.globals.length nativeCap).ge (funId k) = some b ∧
          Genv.find_funct_ptr (envOf compiled.translation compiled.module.globals.length nativeCap).ge b =
            some (.Internal fd)) ∧
      (Verified.initialHeap compiled.tables).At (nativeStore compiled.module nativeCap) ∧
      (Verified.initialHeap compiled.tables).top.toNat = 4096 ∧
      (nativeStore compiled.module nativeCap).memoryCap compiled.module 0 = nativeCap := by
  obtain ⟨decl, m0, hdecl, hinit, hE, hmem, hrun⟩ := lx_init_correct compiled.translation_eq A
  obtain ⟨m1, hcall, hst, hs⟩ := hrun X
  exact ⟨decl, m0, m1, hdecl, hinit, hmem, hcall, hst, hs, hE, by simp [envOf], rfl,
    Nat.le_refl _, funcs_found compiled.translation_eq,
    heapAt_nativeStore (Verified.Ready.initial rfl compiled.initial).1 nativeCap, by decide,
    memoryCap_eq hst.2 compiled.module⟩

private theorem alloc_store_native {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E)
    (hG : E.globals.length = compiled.module.globals.length) (hcap : E.cap = nativeCap)
    (hnres : compiled.translation.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧ Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Wasm.Store Unit) (bytes : UInt64) (hHeap : heap.At store)
    (hBytes : bytes.toNat ≤ 4294967296) (hCapS : store.memoryCap compiled.module 0 ≤ 65535)
    (hRoom : heap.Room store compiled.module (LeanExe.Pipeline.allocSize bytes)) (m : mem)
    (hst : StoreRel A E store m) (hs : StatusRel A E m 0) :
    ∃ fd, (funId 0, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      ∃ t m' vres st', eval_funcall A X E.ge m (.Internal fd) [.Vlong bytes] t m' vres ∧
        StoreRel A E st' m' ∧ StatusRel A E m' 0 ∧ heap.Fits (LeanExe.Pipeline.allocSize bytes) ∧
        st' = heap.allocateStore store (LeanExe.Pipeline.allocSize bytes) 1 ∧
        vres = .Vlong (LeanExe.ProofKit.FixedArrayAllocate.root heap.top
          (LeanExe.Pipeline.allocSize bytes) heap.free) :=
  alloc_native_room compiled.translation_eq (Verified.compileWith_runtime _ _ _).alloc
    (by decide +kernel) hE hG hcap hnres hF heap store bytes hHeap hBytes hCapS hRoom m hst hs

/-- The runtime's `alloc` at this translation: from a heap with room for the allocation, the C call
of `lxf_alloc` on `bytes` returns the new block's address with `lx_status` 0, in a memory related to
a store where the heap after the allocation meets the allocator invariant and the block is fresh. -/
theorem alloc_room_native {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E)
    (hG : E.globals.length = compiled.module.globals.length) (hcap : E.cap = nativeCap)
    (hnres : compiled.translation.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧ Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Wasm.Store Unit) (bytes : UInt64) (hHeap : heap.At store)
    (hBytes : bytes.toNat ≤ 4294967296) (hCapS : store.memoryCap compiled.module 0 ≤ 65535)
    (hRoom : heap.Room store compiled.module (LeanExe.Pipeline.allocSize bytes)) (m : mem)
    (hst : StoreRel A E store m) (hs : StatusRel A E m 0) :
    ∃ fd, (funId 0, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      ∃ t m' vres st', eval_funcall A X E.ge m (.Internal fd) [.Vlong bytes] t m' vres ∧
        StoreRel A E st' m' ∧ StatusRel A E m' 0 ∧ heap.Fits (LeanExe.Pipeline.allocSize bytes) ∧
        st' = heap.allocateStore store (LeanExe.Pipeline.allocSize bytes) 1 ∧
        vres = .Vlong (LeanExe.ProofKit.FixedArrayAllocate.root heap.top
          (LeanExe.Pipeline.allocSize bytes) heap.free) ∧
        (heap.allocate (LeanExe.Pipeline.allocSize bytes)).At st' ∧
        (heap.allocate (LeanExe.Pipeline.allocSize bytes)).Block st'
          (LeanExe.ProofKit.FixedArrayAllocate.root heap.top (LeanExe.Pipeline.allocSize bytes)
            heap.free)
          (allocatedCapacity (LeanExe.Pipeline.allocSize bytes) heap.free) 1 := by
  obtain ⟨fd, hfd, t, m', vres, st', hcall, hst', hs', hfits, rfl, hv⟩ :=
    alloc_store_native (X := X) hE hG hcap hnres hF heap store bytes hHeap hBytes hCapS hRoom m hst hs
  exact ⟨fd, hfd, t, m', vres, _, hcall, hst', hs', hfits, rfl, hv, hHeap.allocate 1 hfits,
    hHeap.allocate_block 1 hfits⟩

private theorem release_store_native {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E)
    (hG : E.globals.length = compiled.module.globals.length) (hcap : E.cap = nativeCap)
    (hnres : compiled.translation.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧ Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Wasm.Store Unit) (ptr : UInt64) (words : Array UInt64)
    (hHeap : heap.At store) (hOwned : heap.Owned store ptr words) (m : mem)
    (hst : StoreRel A E store m) (hs : StatusRel A E m 0) :
    ∃ fd, (funId 1, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong ptr] t m' .Vundef ∧
        StoreRel A E (heap.releaseStore store ptr) m' ∧ StatusRel A E m' 0 :=
  LeanExe.Native.release_native compiled.translation_eq (Verified.compileWith_runtime _ _ _).release
    (by decide +kernel) hE hG hcap hnres hF heap store ptr words hHeap hOwned m hst hs

/-- The runtime's `release` at this translation: the C call of `lxf_release` on an owned object
returns with `lx_status` 0 in a memory related to the store after the release, where the heap with
the object's block on the free list meets the allocator invariant. -/
theorem release_native {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E)
    (hG : E.globals.length = compiled.module.globals.length) (hcap : E.cap = nativeCap)
    (hnres : compiled.translation.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧ Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Wasm.Store Unit) (ptr : UInt64) (words : Array UInt64)
    (hHeap : heap.At store) (hOwned : heap.Owned store ptr words) (m : mem)
    (hst : StoreRel A E store m) (hs : StatusRel A E m 0) :
    ∃ fd, (funId 1, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong ptr] t m' .Vundef ∧
        StoreRel A E (heap.releaseStore store ptr) m' ∧ StatusRel A E m' 0 ∧
        (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).At (heap.releaseStore store ptr) := by
  obtain ⟨fd, hfd, t, m', hcall, hst', hs'⟩ :=
    release_store_native (X := X) hE hG hcap hnres hF heap store ptr words hHeap hOwned m hst hs
  exact ⟨fd, hfd, t, m', hcall, hst', hs', hHeap.release hOwned.object⟩

/-- Function 3 of the module, MultiPrecision's `add` on two arrays of digits, returns `addSpec`
without a trap within its generated bound. -/
theorem add_spec_trapFree :
    ImplementsA false compiled.module 3
      (fun x : Array UInt64 × Array UInt64 => Library.Numerics.MultiPrecision.add x.1 x.2)
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.add.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.add.bound x ∧
        Library.Numerics.MultiPrecision.add x.1 x.2 = addSpec x) :=
  ImplementsA.strengthen compiled.add.trapFree (fun _ _ _ h => h.2)
    fun _ _ _ x _ _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨hpost, add_eq x.1 x.2 hc.1 hc.2 (by omega) (by omega)⟩

theorem add_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl add_spec_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.add.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native add_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- Function 4 of the module, MultiPrecision's `sub` on two arrays of digits, returns `subSpec`
without a trap within its generated bound. -/
theorem sub_spec_trapFree :
    ImplementsA false compiled.module 4
      (fun x : Array UInt64 × Array UInt64 => Library.Numerics.MultiPrecision.sub x.1 x.2)
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.sub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.sub.bound x ∧
        Library.Numerics.MultiPrecision.sub x.1 x.2 = subSpec x) :=
  ImplementsA.strengthen compiled.sub.trapFree (fun _ _ _ h => h.2)
    fun _ _ _ x _ _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨hpost, sub_eq x.1 x.2 hc.1 hc.2 (by omega) (by omega)⟩

theorem sub_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl sub_spec_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.sub.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native sub_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- Function 5 of the module, MultiPrecision's `mul` on two arrays of digits, returns `mulSpec`
without a trap within its generated bound. -/
theorem mul_spec_trapFree :
    ImplementsA false compiled.module 5
      (fun x : Array UInt64 × Array UInt64 => Library.Numerics.MultiPrecision.mul x.1 x.2)
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.mul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.mul.bound x ∧
        Library.Numerics.MultiPrecision.mul x.1 x.2 = mulSpec x) :=
  ImplementsA.strengthen compiled.mul.trapFree (fun _ _ _ h => h.2)
    fun _ _ _ x _ _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨hpost, mul_eq x.1 x.2 hc.1 hc.2 (by omega)⟩

theorem mul_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl mul_spec_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.mul.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native mul_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- Function 13 of the module, MultiPrecision's `divide` on two arrays of digits, returns `divSpec`
without a trap within its generated bound. -/
theorem divide_spec_trapFree :
    ImplementsA false compiled.module 13
      (fun x : Array UInt64 × Array UInt64 => Library.Numerics.MultiPrecision.divide x.1 x.2)
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.divide.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.divide.bound x ∧
        Library.Numerics.MultiPrecision.divide x.1 x.2 = divSpec x) :=
  ImplementsA.strengthen compiled.divide.trapFree (fun _ _ _ h => h.2)
    fun _ _ _ x _ _ hpre hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      have hc := hpre.1
      exact ⟨hpost, divide_eq x.1 x.2 hc.1 hc.2 (by omega)⟩

theorem divide_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl divide_spec_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.divide.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native divide_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- Function 16 of the module, Uscale's `le` on two arrays of digits, returns whether the first
value is at most the second, without a trap and without an allocation. -/
theorem le_spec_trapFree :
    ImplementsA false compiled.module 16 (fun x : Array UInt64 × Array UInt64 => le x.1 x.2)
      (fun x _ _ => Digits x.1 ∧ Digits x.2)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.le.bound x ∧
        le x.1 x.2 = decide (value x.1 ≤ value x.2)) :=
  ImplementsA.strengthen compiled.le.trapFree (fun _ _ _ _ => trivial)
    fun _ _ _ x _ _ hc hr hpost => by
      obtain ⟨_, r1⟩ := rep_fst hr
      obtain ⟨_, r2⟩ := rep_snd hr
      have s1 : x.1.size < 536870912 := rep_arr r1
      have s2 : x.2.size < 536870912 := rep_arr r2
      exact ⟨hpost, le_eq hc.1 hc.2 (by omega) (by omega)⟩

theorem le_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl le_spec_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.le.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native le_spec_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_width`, function 2, computes `width` without a trap within its generated
bound. -/
theorem width_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.width.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.width.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.width.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_significant`, function 6, computes `significant` without a trap within its generated
bound. -/
theorem significant_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.significant.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.significant.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.significant.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_mulSmall`, function 7, computes `mulSmall` without a trap within its generated
bound. -/
theorem mulSmall_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.mulSmall.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.mulSmall.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.mulSmall.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_wordBits`, function 8, computes `wordBits` without a trap within its generated
bound. -/
theorem wordBits_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.wordBits.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.wordBits.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.wordBits.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_shortDiv`, function 9, computes `shortDiv` without a trap within its generated
bound. -/
theorem shortDiv_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.shortDiv.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.shortDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.shortDiv.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_tooBig`, function 10, computes `tooBig` without a trap within its generated
bound. -/
theorem tooBig_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.tooBig.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.tooBig.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.tooBig.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_trial`, function 11, computes `trial` without a trap within its generated
bound. -/
theorem trial_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.trial.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.trial.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.trial.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_longDiv`, function 12, computes `longDiv` without a trap within its generated
bound. -/
theorem longDiv_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.longDiv.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.longDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.longDiv.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_limb`, function 14, computes `limb` without a trap within its generated
bound. -/
theorem limb_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.limb.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.limb.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.limb.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_cmpStep`, function 15, computes `cmpStep` without a trap within its generated
bound. -/
theorem cmpStep_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.cmpStep.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.cmpStep.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.cmpStep.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_digitCount`, function 17, computes `digitCount` without a trap within its generated
bound. -/
theorem digitCount_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.digitCount.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.digitCount.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.digitCount.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_digitByte`, function 18, computes `digitByte` without a trap within its generated
bound. -/
theorem digitByte_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.digitByte.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.digitByte.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.digitByte.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_isDigitW`, function 19, computes `isDigitW` without a trap within its generated
bound. -/
theorem isDigitW_native_spec (A : Archi) (X : ExtSem) :
    NativeImpl compiled.isDigitW.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.isDigitW.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    ImplementsA.native compiled.isDigitW.trapFree compiled.translation_eq hfd hsig⟩

#print axioms native_names
#print axioms native_start
#print axioms alloc_room_native
#print axioms release_native
#print axioms add_native_spec
#print axioms sub_native_spec
#print axioms mul_native_spec
#print axioms divide_native_spec
#print axioms le_native_spec
#print axioms width_native_spec
#print axioms significant_native_spec
#print axioms mulSmall_native_spec
#print axioms wordBits_native_spec
#print axioms shortDiv_native_spec
#print axioms tooBig_native_spec
#print axioms trial_native_spec
#print axioms longDiv_native_spec
#print axioms limb_native_spec
#print axioms cmpStep_native_spec
#print axioms digitCount_native_spec
#print axioms digitByte_native_spec
#print axioms isDigitW_native_spec

end Library.Numerics.Bignum
