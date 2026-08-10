import Project.ProofKit.Array
import Project.ProofKit.FixedArrayAllocator

namespace Project.ProofKit.FixedArrayResult

open Wasm

def lengthStoreProgram (rootLocal : Nat) (length : UInt64) : Wasm.Program :=
  [
  .localGet rootLocal,
  .wrapI64,
  .constI64 length,
  .store64 0
  ]

def payloadAddress (root : UInt64) (index : Nat) : UInt64 :=
  root + (UInt64.ofNat index * 1 + 1) * 8

def payloadStoreProgram (rootLocal scratchLocal index : Nat) : Wasm.Program :=
  [
  .localGet rootLocal,
  .constI64 (UInt64.ofNat index),
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet scratchLocal,
  .store64 0
  ]

def finishProgram (rootLocal destinationLocal returnLocal : Nat) : Wasm.Program :=
  [
  .localGet rootLocal,
  .localSet destinationLocal,
  .localGet destinationLocal,
  .localSet returnLocal
  ]

def finishFrame (frame : Locals) (destinationLocal returnLocal : Nat)
    (root : UInt64) : Locals :=
  { frame with
    locals := (frame.locals.set
      (destinationLocal - frame.params.length) (.i64 root)).set
      (returnLocal - frame.params.length) (.i64 root)
    values := [] }

theorem finishFrame_return_get (frame : Locals)
    (destinationLocal returnLocal : Nat) (root : UInt64)
    (hReturnLower : frame.params.length ≤ returnLocal)
    (hReturnValid : frame.validIndex returnLocal) :
    (finishFrame frame destinationLocal returnLocal root).get returnLocal =
      some (.i64 root) := by
  have hReturnNotParam : ¬returnLocal < frame.params.length :=
    Nat.not_lt.mpr hReturnLower
  have hReturnBound :
      returnLocal < frame.params.length + frame.locals.length := hReturnValid
  have hReturnIndex :
      returnLocal - frame.params.length < frame.locals.length := by
    omega
  simp [finishFrame, Wasm.Locals.get, hReturnNotParam, hReturnBound,
    hReturnIndex]

def writeLength (st : Store Unit) (root length : UInt64) : Store Unit :=
  { st with mem := st.mem.write64 root.toUInt32 length }

def writePayload (st : Store Unit) (root : UInt64) (index : Nat)
    (value : UInt64) : Store Unit :=
  { st with mem := st.mem.write64 (payloadAddress root index).toUInt32 value }

def singletonStore (st : Store Unit) (root value : UInt64) : Store Unit :=
  writePayload (writeLength st root 1) root 0 value

def pairStore (st : Store Unit) (root first second : UInt64) : Store Unit :=
  writePayload (writePayload (writeLength st root 2) root 0 first) root 1 second

theorem writeLength_pages (st : Store Unit) (root length : UInt64) :
    (writeLength st root length).mem.pages = st.mem.pages := by
  simp [writeLength, Mem.write64_pages]

theorem writePayload_pages (st : Store Unit) (root : UInt64) (index : Nat)
    (value : UInt64) :
    (writePayload st root index value).mem.pages = st.mem.pages := by
  simp [writePayload, Mem.write64_pages]

theorem emptyStore_at (st : Store Unit) (root : UInt64)
    (hFit32 : root.toNat + 8 ≤ 4294967296)
    (hFitMemory : root.toNat + 8 ≤ st.mem.pages * 65536) :
    UInt64Array.At (writeLength st root 0) root #[] := by
  refine ⟨by simpa using hFit32, ?_, ?_, ?_⟩
  · simpa [writeLength, Mem.write64_pages] using hFitMemory
  · change (st.mem.write64 root.toUInt32 0).read64 root.toUInt32 = 0
    exact Mem.read64_write64_same ..
  · intro i hi
    simp at hi

theorem singletonStore_at (st : Store Unit) (root value : UInt64)
    (hFit32 : root.toNat + 16 ≤ 4294967296)
    (hFitMemory : root.toNat + 16 ≤ st.mem.pages * 65536) :
    UInt64Array.At (singletonStore st root value) root #[value] := by
  have hRootAddressNat : root.toUInt32.toNat = root.toNat := by
    simpa [UInt64Array.wordAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 2)
        (word := 0) (by simpa using hFit32) (by decide))
  have hPayloadAddressNat :
      (payloadAddress root 0).toUInt32.toNat = root.toNat + 8 := by
    simpa [UInt64Array.wordAddress, payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 2)
        (word := 1) (by simpa using hFit32) (by decide))
  apply UInt64Array.singleton
  · exact hFit32
  · simpa [singletonStore, writePayload, writeLength, Mem.write64_pages] using
      hFitMemory
  · change
      ((st.mem.write64 root.toUInt32 1).write64
        (payloadAddress root 0).toUInt32 value).read64 root.toUInt32 = 1
    calc
      _ = (st.mem.write64 root.toUInt32 1).read64 root.toUInt32 :=
        Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by omega))
      _ = 1 := Mem.read64_write64_same ..
  · change
      ((st.mem.write64 root.toUInt32 1).write64
        (payloadAddress root 0).toUInt32 value).read64
          (root + 8).toUInt32 = value
    have hAddress : payloadAddress root 0 = root + 8 := by
      simp [payloadAddress]
    rw [← hAddress]
    exact Mem.read64_write64_same ..

theorem pairStore_at (st : Store Unit) (root first second : UInt64)
    (hFit32 : root.toNat + 24 ≤ 4294967296)
    (hFitMemory : root.toNat + 24 ≤ st.mem.pages * 65536) :
    UInt64Array.At (pairStore st root first second) root #[first, second] := by
  have hRootAddressNat : root.toUInt32.toNat = root.toNat := by
    simpa [UInt64Array.wordAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3)
        (word := 0) (by simpa using hFit32) (by decide))
  have hFirstAddressNat :
      (payloadAddress root 0).toUInt32.toNat = root.toNat + 8 := by
    simpa [UInt64Array.wordAddress, payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3)
        (word := 1) (by simpa using hFit32) (by decide))
  have hSecondAddressNat :
      (payloadAddress root 1).toUInt32.toNat = root.toNat + 16 := by
    simpa [UInt64Array.wordAddress, payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3)
        (word := 2) (by simpa using hFit32) (by decide))
  have hFirstAddress : payloadAddress root 0 = root + 8 := by
    simp [payloadAddress]
  have hSecondAddress : payloadAddress root 1 = root + 16 := by
    simp [payloadAddress]
  apply UInt64Array.pair
  · exact hFit32
  · simpa [pairStore, writePayload, writeLength, Mem.write64_pages] using
      hFitMemory
  · change
      (((st.mem.write64 root.toUInt32 2).write64
        (payloadAddress root 0).toUInt32 first).write64
        (payloadAddress root 1).toUInt32 second).read64 root.toUInt32 = 2
    calc
      _ = ((st.mem.write64 root.toUInt32 2).write64
          (payloadAddress root 0).toUInt32 first).read64 root.toUInt32 :=
        Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by omega))
      _ = (st.mem.write64 root.toUInt32 2).read64 root.toUInt32 :=
        Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by omega))
      _ = 2 := Mem.read64_write64_same ..
  · change
      (((st.mem.write64 root.toUInt32 2).write64
        (payloadAddress root 0).toUInt32 first).write64
        (payloadAddress root 1).toUInt32 second).read64
          (root + 8).toUInt32 = first
    rw [← hFirstAddress]
    calc
      _ = ((st.mem.write64 root.toUInt32 2).write64
          (payloadAddress root 0).toUInt32 first).read64
            (payloadAddress root 0).toUInt32 :=
        Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by omega))
      _ = first := Mem.read64_write64_same ..
  · change
      (((st.mem.write64 root.toUInt32 2).write64
        (payloadAddress root 0).toUInt32 first).write64
        (payloadAddress root 1).toUInt32 second).read64
          (root + 16).toUInt32 = second
    rw [← hSecondAddress]
    exact Mem.read64_write64_same ..

theorem lengthStore_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (root length : UInt64) (rootLocal : Nat)
    (hValues : frame.values = [])
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hBound : root.toUInt32.toNat + 8 ≤ st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (writeLength st root length) frame env) :
    wp module_ (lengthStoreProgram rootLocal length ++ rest) Q st frame env := by
  simp only [lengthStoreProgram, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hRoot, wp_wrapI64_cons, wp_constI64_cons,
    wp_store64_cons]
  have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
  rw [hTwo32]
  rw [← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, add_zero]
  rw [if_neg (Nat.not_lt.mpr hBound)]
  cases frame
  simp_all [writeLength]

theorem payloadStore_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (root value : UInt64) (rootLocal scratchLocal index : Nat)
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hValue : frame.get scratchLocal = some (.i64 value))
    (hBound : (payloadAddress root index).toUInt32.toNat + 8 ≤
      st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (writePayload st root index value) frame env) :
    wp module_ (payloadStoreProgram rootLocal scratchLocal index ++ rest)
      Q st frame env := by
  have hValueAfter (values : List Value) :
      ({ frame with values := values } : Locals).get scratchLocal =
        some (.i64 value) := by
    simpa only [Wasm.Locals.get] using hValue
  simp only [payloadStoreProgram, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hRoot, wp_constI64_cons, wp_mulI64_cons,
    wp_addI64_cons, wp_wrapI64_cons, hValueAfter, wp_store64_cons]
  have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
  rw [hTwo32]
  rw [← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, add_zero]
  have hPayloadBound :
      (root + (UInt64.ofNat index * 1 + 1) * 8).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536 := by
    simpa [payloadAddress] using hBound
  rw [if_neg (Nat.not_lt.mpr hPayloadBound)]
  simpa [writePayload, payloadAddress] using hNext

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem finishProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (root : UInt64)
    (rootLocal destinationLocal returnLocal : Nat)
    (hValues : frame.values = [])
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hDestinationLower : frame.params.length ≤ destinationLocal)
    (hDestinationValid : frame.validIndex destinationLocal)
    (hReturnLower : frame.params.length ≤ returnLocal)
    (hReturnValid : frame.validIndex returnLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (finishFrame frame destinationLocal returnLocal root) env) :
    wp module_ (finishProgram rootLocal destinationLocal returnLocal ++ rest)
      Q st frame env := by
  have hDestinationNotParam : ¬destinationLocal < frame.params.length :=
    Nat.not_lt.mpr hDestinationLower
  have hDestinationBound :
      destinationLocal < frame.params.length + frame.locals.length :=
    hDestinationValid
  have hDestinationIndex :
      destinationLocal - frame.params.length < frame.locals.length := by
    omega
  have hReturnNotParam : ¬returnLocal < frame.params.length :=
    Nat.not_lt.mpr hReturnLower
  have hReturnBound :
      returnLocal < frame.params.length + frame.locals.length := hReturnValid
  have hReturnIndex :
      returnLocal - frame.params.length < frame.locals.length := by
    omega
  unfold finishProgram
  simp only [List.cons_append, List.nil_append, wp_simp, hValues, hRoot]
  simpa [Wasm.Locals.get, Wasm.Locals.set?, hDestinationNotParam,
    hDestinationBound, hDestinationIndex, hReturnNotParam, hReturnBound,
    hReturnIndex, List.getElem?_set, finishFrame] using hNext

end Project.ProofKit.FixedArrayResult
