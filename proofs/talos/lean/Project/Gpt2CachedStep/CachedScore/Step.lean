import Project.Gpt2CachedStep.CachedKv
import Project.Gpt2CachedStep.CachedScore.Source
import Project.ProofKit.PackedWordRead
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.CachedScore

open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func23[12]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

set_option maxRecDepth 16384 in
theorem emitted_loop :
    func23 = func23.take 12 ++ RangeFoldLoop.program 37 38 stepCode ++ func23.drop 13 := rfl

def parameters (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position source head : Nat) : List Wasm.Value :=
  [.i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
   .i64 qkvOwner, .i64 qkvPtr, .i64 (UInt64.ofNat qkv.size), .i64 (UInt64.ofNat layer),
   .i64 (UInt64.ofNat position), .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat head)]

def Accumulator (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position source head index : Nat) (frame : Locals) : Prop :=
  frame.params = parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position source head ∧
  frame.locals.length = 38 ∧
  frame.locals[1]? = some (.i64 (dotPrefix cache qkv layer position source head index).toUInt64) ∧
  frame.locals[29]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position source head index : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hLayer : layer < 12) (hSource : source ≤ position) (hhead : head < 12)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hindex : index < 64)
    (hready : RangeFoldLoop.Ready 37 38 64 index frame)
    (hacc : Accumulator cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position source head index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 37 38 64 (index + 1) result →
      Accumulator cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position source head (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  simp only [parameters] at hparams
  have hcounter : frame.locals[27]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[28]? = some (.i64 64) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hMulH : ¬ (-1 : UInt64) / 64 < UInt64.ofNat head := by
    change ¬ (288230376151711743 : UInt64) < UInt64.ofNat head
    u64_omega
  have hQI : ¬ UInt64.ofNat head * 64 + UInt64.ofNat index < UInt64.ofNat head * 64 := by
    simpa only [UInt64.ofNat_mul, show UInt64.ofNat 64 = 64 from rfl] using
      CheckedNatAdd.guard_of_fits (head * 64) index
        (by change head * 64 + index < 18446744073709551616; omega)
  have hInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by u64_omega
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hquery : UInt64.ofNat head * 64 + UInt64.ofNat index = UInt64.ofNat (head * 64 + index) := by simp
  simp only [stepCode, func23, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hMulH, hQI])])
  simp only [hquery]
  refine wp_call_tw (PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial qkvOwner qkvPtr qkv (head * 64 + index) hQkv (by omega)) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hMulH, hQI])])
  simp only [hquery]
  refine wp_call_tw (CachedKv.cachedKv_exact env final cacheOwner qkvOwner cachePtr qkvPtr cache qkv
    layer position source (head * 64 + index) hCache hQkv hLayer hSource (by omega) hCacheSize hQkvSize) ?_
  rintro final' values ⟨rfl, rfl⟩
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hInc)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc, true_and]
    rfl
  · simp only [Accumulator, parameters, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, dotPrefix_succ,
      LeanExe.Models.Gpt2.word, and_self]

#print axioms step_spec

end Project.Gpt2CachedStep.CachedScore
