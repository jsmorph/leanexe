module

public import Library.Numerics.Bignum.Third.Native
public import LeanExe.Native.Proof.Main
import all Init.Data.Repr

@[expose] public section

/-!
# The C program around the third iteration's theorems

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
allocated block have no theorem.  These four theorems copy the second iteration's
`NativeRuntime.lean` at this translation.  The helpers that the module also exports have C theorems
from their theorems without a trap in `Call.lean`, or from the generated ones: the Lean function
within the generated bound for `trialAt`, `signEDiv`, `textOfChunks`, and `chunksDC`, and in place
with no room for the helpers of the division and of the printer that update the workspace.
-/

namespace Library.Numerics.Bignum.Third

open LeanExe.Pipeline LeanExe.Native LClight

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The C function of each export is `lxf_` followed by the export's name, and the functions whose
code takes the call depth are `lxf_` followed by their index (19, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 45, 46, 48, 49, 51, 52, 53, 54), the
bodies that the exported entries 55 to 73 call at depth 0; `lx_init`, `lx_status`, `lx_mem`, and the
result globals `lx_r0_l` to `lx_r4_l` that a host reads are the identifiers that the theorems name;
the translation has five result positions; and no two of its identifiers and no two of its names
coincide. -/
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
      (funId 5, "lxf_significant"),
      (funId 6, "lxf_mulSmall"),
      (funId 7, "lxf_wordBits"),
      (funId 8, "lxf_shortDiv"),
      (funId 9, "lxf_tooBig"),
      (funId 10, "lxf_trial"),
      (funId 11, "lxf_limb"),
      (funId 12, "lxf_cmpStep"),
      (funId 13, "lxf_le"),
      (funId 14, "lxf_digitCount"),
      (funId 15, "lxf_digitByte"),
      (funId 16, "lxf_addGen"),
      (funId 17, "lxf_subGen"),
      (funId 18, "lxf_baseMul"),
      (funId 19, "lxf_19"),
      (funId 20, "lxf_trimSeg"),
      (funId 21, "lxf_mulAddSeg"),
      (funId 22, "lxf_longDivS"),
      (funId 23, "lxf_divideS"),
      (funId 24, "lxf_natTrim"),
      (funId 25, "lxf_natAdd"),
      (funId 26, "lxf_natSub"),
      (funId 27, "lxf_intToText"),
      (funId 28, "lxf_trialAt"),
      (funId 29, "lxf_mulSubSeg"),
      (funId 30, "lxf_baseDiv"),
      (funId 31, "lxf_31"),
      (funId 32, "lxf_32"),
      (funId 33, "lxf_subFix"),
      (funId 34, "lxf_34"),
      (funId 35, "lxf_35"),
      (funId 36, "lxf_36"),
      (funId 37, "lxf_37"),
      (funId 38, "lxf_38"),
      (funId 39, "lxf_divSmallSeg"),
      (funId 40, "lxf_40"),
      (funId 41, "lxf_41"),
      (funId 42, "lxf_42"),
      (funId 43, "lxf_signTDiv"),
      (funId 44, "lxf_signEDiv"),
      (funId 45, "lxf_45"),
      (funId 46, "lxf_46"),
      (funId 47, "lxf_leafChunks"),
      (funId 48, "lxf_48"),
      (funId 49, "lxf_49"),
      (funId 50, "lxf_textOfChunks"),
      (funId 51, "lxf_51"),
      (funId 52, "lxf_52"),
      (funId 53, "lxf_53"),
      (funId 54, "lxf_54"),
      (funId 55, "lxf_kara"),
      (funId 56, "lxf_mulChunk"),
      (funId 57, "lxf_mulAcc"),
      (funId 58, "lxf_halfStep"),
      (funId 59, "lxf_lowHalf"),
      (funId 60, "lxf_rdiv"),
      (funId 61, "lxf_tdiv"),
      (funId 62, "lxf_udiv"),
      (funId 63, "lxf_divSeg"),
      (funId 64, "lxf_natDivModCheckedBZWith"),
      (funId 65, "lxf_natDivModCheckedBZ"),
      (funId 66, "lxf_intTDivModCheckedBZ"),
      (funId 67, "lxf_intEDivModCheckedBZ"),
      (funId 68, "lxf_powInit"),
      (funId 69, "lxf_toChunks"),
      (funId 70, "lxf_chunksDC"),
      (funId 71, "lxf_natToTextDCWith"),
      (funId 72, "lxf_natToTextDC"),
      (funId 73, "lxf_intToTextDC")],
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

/-! ## The helpers

The module also exports the helpers of the division and the printer.  Each has a C theorem from
its theorem without a trap in `Call.lean`, or from its generated `trapFree`, through
`LeanExe.Native.ImplementsA.native`. -/

/-- Function 70, `chunksDC`, computes the Lean function without a trap for every argument
within its generated bound at 1,000 frames. -/
theorem chunksDC_trapFree : ImplementsA false compiled.module 70
    (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 => chunksDC x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x heap store => heap.Within store compiled.module (compiled.chunksDC.bound 1000 x))
    (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.chunksDC.bound 1000 x) :=
  compiled.chunksDC.trapFree.mono
    (fun x _ _ h => ⟨chunksDC_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h

/-- The C function `lxf_trialAt`, function 28, computes the Lean function, the trial digit, within its generated bound, 0, under every `Archi` and every
semantics of external functions. -/
theorem trialAt_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.trialAt.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.trialAt.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native compiled.trialAt.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_signEDiv`, function 44, computes the Lean function within its generated bound, under every `Archi` and every
semantics of external functions. -/
theorem signEDiv_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.signEDiv.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.signEDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native compiled.signEDiv.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_textOfChunks`, function 50, computes the Lean function, the text of the chunks, within its generated bound, under every `Archi` and every
semantics of external functions. -/
theorem textOfChunks_native (A : Archi) (X : ExtSem) :
    NativeImpl compiled.textOfChunks.trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.textOfChunks.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native compiled.textOfChunks.trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_chunksDC`, function 70, computes the Lean function, the chunks of nine digits, within its generated bound at 1,000 frames, under every `Archi` and every
semantics of external functions. -/
theorem chunksDC_native (A : Archi) (X : ExtSem) :
    NativeImpl chunksDC_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.chunksDC.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native chunksDC_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_mulSubSeg`, function 29, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem mulSubSeg_native (A : Archi) (X : ExtSem) :
    NativeImpl mulSubSeg_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.mulSubSeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native mulSubSeg_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_baseDiv`, function 30, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem baseDiv_native (A : Archi) (X : ExtSem) :
    NativeImpl baseDiv_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.baseDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native baseDiv_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_subFix`, function 33, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem subFix_native (A : Archi) (X : ExtSem) :
    NativeImpl subFix_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.subFix.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native subFix_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_divSmallSeg`, function 39, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem divSmallSeg_native (A : Archi) (X : ExtSem) :
    NativeImpl divSmallSeg_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.divSmallSeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native divSmallSeg_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_signTDiv`, function 43, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem signTDiv_native (A : Archi) (X : ExtSem) :
    NativeImpl signTDiv_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.signTDiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native signTDiv_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_leafChunks`, function 47, computes the Lean function in place, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem leafChunks_native (A : Archi) (X : ExtSem) :
    NativeImpl leafChunks_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.leafChunks.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native leafChunks_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_kara`, function 55, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem kara_native (A : Archi) (X : ExtSem) :
    NativeImpl kara_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.kara.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native kara_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_mulChunk`, function 56, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem mulChunk_native (A : Archi) (X : ExtSem) :
    NativeImpl mulChunk_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.mulChunk.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native mulChunk_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_mulAcc`, function 57, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem mulAcc_native (A : Archi) (X : ExtSem) :
    NativeImpl mulAcc_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.mulAcc.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native mulAcc_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_halfStep`, function 58, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem halfStep_native (A : Archi) (X : ExtSem) :
    NativeImpl halfStep_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.halfStep.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native halfStep_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_lowHalf`, function 59, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem lowHalf_native (A : Archi) (X : ExtSem) :
    NativeImpl lowHalf_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.lowHalf.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native lowHalf_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_rdiv`, function 60, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem rdiv_native (A : Archi) (X : ExtSem) :
    NativeImpl rdiv_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.rdiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native rdiv_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_tdiv`, function 61, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem tdiv_native (A : Archi) (X : ExtSem) :
    NativeImpl tdiv_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.tdiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native tdiv_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_udiv`, function 62, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem udiv_native (A : Archi) (X : ExtSem) :
    NativeImpl udiv_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.udiv.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native udiv_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_divSeg`, function 63, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem divSeg_native (A : Archi) (X : ExtSem) :
    NativeImpl divSeg_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.divSeg.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native divSeg_trapFree compiled.translation_eq hfd hsig⟩

/-- The C function `lxf_powInit`, function 68, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem powInit_native (A : Archi) (X : ExtSem) :
    NativeImpl powInit_trapFree A X nativeCap compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.powInit.native A X
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native powInit_trapFree compiled.translation_eq hfd hsig⟩

end Library.Numerics.Bignum.Third

#print axioms Library.Numerics.Bignum.Third.natDivModCheckedBZ_native_size
#print axioms Library.Numerics.Bignum.Third.intTDivModCheckedBZ_native_size
#print axioms Library.Numerics.Bignum.Third.intEDivModCheckedBZ_native_size
#print axioms Library.Numerics.Bignum.Third.natToTextDC_native_size
#print axioms Library.Numerics.Bignum.Third.intToTextDC_native_size
#print axioms Library.Numerics.Bignum.Third.natDivModCheckedBZWith_native_size
#print axioms Library.Numerics.Bignum.Third.natToTextDCWith_native_size
#print axioms Library.Numerics.Bignum.Third.native_names
#print axioms Library.Numerics.Bignum.Third.native_start
#print axioms Library.Numerics.Bignum.Third.alloc_room_native
#print axioms Library.Numerics.Bignum.Third.release_native
#print axioms Library.Numerics.Bignum.Third.rdiv_native
#print axioms Library.Numerics.Bignum.Third.divSeg_native
#print axioms Library.Numerics.Bignum.Third.chunksDC_native
