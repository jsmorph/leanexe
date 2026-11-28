module

public import Library.Numerics.Bignum.Second.Native
public import LeanExe.Native.Proof.Main
import all Init.Data.Repr

@[expose] public section

/-!
# The C program around the second iteration's theorems

`native_names` states that the C function of each export is `lxf_` followed by the export's name,
and it names `lx_init`, `lx_status`, `lx_mem`, and the result globals, so the theorems of
`Native.lean`, which name the C functions and globals by their identifiers, concern the symbols
that a C host uses.  `native_start` states that the program's start meets those theorems' premises
on the environment, the memory, and the heap: `init_mem` of the translation and `lx_init` give a C
memory related to the module's initial store with `lx_mem` of `nativeCap` pages, `lx_status` 0,
and the program's environment, which meets every hypothesis on the environment of
`LeanExe.Native.NativeA`, and the initial heap meets the allocator invariant with `top` at 4,096
bytes.  `alloc_room_native` and `release_native` are leanexe's theorems of the runtime's functions
at this translation, with the allocator invariant after each call, through which a C host places
arguments in `lx_mem` and releases them; the host's writes of the arguments' words into an
allocated block have no theorem.  These four theorems copy the first iteration's
`NativeRuntime.lean` at this translation.  The helpers that the module also exports have C theorems
from their theorems without a trap: the Lean function within the generated bound for `isDigitW`,
`trimSeg`, `readInit`, and `decimalValueDC`, and in place with no room for `addGen`, `subGen`,
`baseMul`, `mulAddSeg`, `kara`, and `readPass`.
-/

namespace Library.Numerics.Bignum.Second

open Library.Numerics.Bignum
open LeanExe.Pipeline LeanExe.Native LClight

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The C function of each export is `lxf_` followed by the export's name, and the functions whose
code takes the call depth are `lxf_` followed by their index (6, 8 to 10, and 13 to 17), the
bodies that the exported entries 18 to 26 call at depth 0; `lx_init`, `lx_status`, `lx_mem`, and the
result globals `lx_r0_l` to `lx_r2_l` that a host reads are the identifiers that the theorems name;
the translation has three result positions; and no two of its identifiers and no two of its names
coincide. -/
theorem native_names :
    (∀ p ∈ [(initId, "lx_init"),
      (statusId, "lx_status"),
      (memId, "lx_mem"),
      (resId 0 .i64, "lx_r0_l"),
      (resId 1 .i64, "lx_r1_l"),
      (resId 2 .i64, "lx_r2_l"),
      (funId 0, "lxf_alloc"),
      (funId 1, "lxf_release"),
      (funId 2, "lxf_isDigitW"),
      (funId 3, "lxf_addGen"),
      (funId 4, "lxf_subGen"),
      (funId 5, "lxf_baseMul"),
      (funId 6, "lxf_6"),
      (funId 7, "lxf_trimSeg"),
      (funId 8, "lxf_8"),
      (funId 9, "lxf_9"),
      (funId 10, "lxf_10"),
      (funId 11, "lxf_mulAddSeg"),
      (funId 12, "lxf_readInit"),
      (funId 13, "lxf_13"),
      (funId 14, "lxf_14"),
      (funId 15, "lxf_15"),
      (funId 16, "lxf_16"),
      (funId 17, "lxf_17"),
      (funId 18, "lxf_kara"),
      (funId 19, "lxf_natMulKaraWith"),
      (funId 20, "lxf_natMulKara"),
      (funId 21, "lxf_intMulKara"),
      (funId 22, "lxf_readPass"),
      (funId 23, "lxf_decimalValueDC"),
      (funId 24, "lxf_natOfTextDCWith"),
      (funId 25, "lxf_natOfTextDC"),
      (funId 26, "lxf_intOfTextDC")],
      p ∈ compiled.translation.names) ∧
    compiled.translation.nres = 3 ∧
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

/-! ## The helpers

The module also exports the helpers of the products and the readers.  Each has a C theorem from its
theorem without a trap in `Call.lean`, or from its generated `trapFree`, through
`LeanExe.Native.ImplementsA.native`. -/

/-- Function 23, `decimalValueDC`, computes the Lean function without a trap for every argument
within its generated bound at 1,000 frames. -/
theorem decimalValueDC_trapFree : ImplementsA false compiled.module 23
    (fun x : UInt64 × UInt64 × Array UInt64 × UInt64 × UInt64 =>
      decimalValueDC x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun x heap store => heap.Within store compiled.module (compiled.decimalValueDC.bound 1000 x))
    (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.decimalValueDC.bound 1000 x) :=
  compiled.decimalValueDC.trapFree.mono
    (fun x _ _ h => ⟨decimalValueDC_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h

/-- The C function `lxf_isDigitW`, function 2, computes the Lean function without a trap within its generated bound, 0, under every `Archi` and every
semantics of external functions. -/
theorem isDigitW_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.isDigitW.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.isDigitW.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native compiled.isDigitW.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_trimSeg`, function 7, computes the Lean function, the canonical limbs of a segment of limbs, within its generated bound, under every `Archi` and every
semantics of external functions. -/
theorem trimSeg_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.trimSeg.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.trimSeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native compiled.trimSeg.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_readInit`, function 12, computes the Lean function within its generated bound, under every `Archi` and every
semantics of external functions. -/
theorem readInit_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.readInit.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.readInit.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native compiled.readInit.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_decimalValueDC`, function 23, computes the Lean function, the canonical limbs of the digits' value, within its generated bound at 1,000 frames, under every `Archi` and every
semantics of external functions. -/
theorem decimalValueDC_native (A : Archi) (X : ExtSem) :
    NativeImpl decimalValueDC_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.decimalValueDC.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native decimalValueDC_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_addGen`, function 3, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem addGen_native (A : Archi) (X : ExtSem) :
    NativeImpl addGen_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.addGen.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native addGen_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_subGen`, function 4, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem subGen_native (A : Archi) (X : ExtSem) :
    NativeImpl subGen_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.subGen.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native subGen_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_baseMul`, function 5, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem baseMul_native (A : Archi) (X : ExtSem) :
    NativeImpl baseMul_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.baseMul.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native baseMul_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_mulAddSeg`, function 11, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem mulAddSeg_native (A : Archi) (X : ExtSem) :
    NativeImpl mulAddSeg_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.mulAddSeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native mulAddSeg_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_kara`, function 18, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem kara_native (A : Archi) (X : ExtSem) :
    NativeImpl kara_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.kara.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native kara_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_readPass`, function 22, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem readPass_native (A : Archi) (X : ExtSem) :
    NativeImpl readPass_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.readPass.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native readPass_trapFree compiled.translation_eq hfd hsig⟩

end Library.Numerics.Bignum.Second

#print axioms Library.Numerics.Bignum.Second.natMulKara_native_size
#print axioms Library.Numerics.Bignum.Second.intMulKara_native_size
#print axioms Library.Numerics.Bignum.Second.natOfTextDC_native_size
#print axioms Library.Numerics.Bignum.Second.intOfTextDC_native_size
#print axioms Library.Numerics.Bignum.Second.natMulKaraWith_native_size
#print axioms Library.Numerics.Bignum.Second.natOfTextDCWith_native_size
#print axioms Library.Numerics.Bignum.Second.native_names
#print axioms Library.Numerics.Bignum.Second.native_start
#print axioms Library.Numerics.Bignum.Second.alloc_room_native
#print axioms Library.Numerics.Bignum.Second.release_native
#print axioms Library.Numerics.Bignum.Second.natOfTextDCWith_native_spec
#print axioms Library.Numerics.Bignum.Second.kara_native
#print axioms Library.Numerics.Bignum.Second.readPass_native
#print axioms Library.Numerics.Bignum.Second.decimalValueDC_native
#print axioms Library.Numerics.Bignum.Second.addGen_native
