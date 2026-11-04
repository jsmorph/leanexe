import Demos.Gpt32.VerifiedDispatch
import Demos.Gpt32.VerifiedKernels
import Demos.Gpt32.Compose
import LeanExe.WGSL.MemoryModelProof

/-!
The device of `leanexe-webgpu-host session` with the WGSL kernels of `kernelMap`, and the host
theorem of the GPT-2 generation on it.  A buffer holds 32-bit words.  `output NAME n` holds `n` as
a 64-bit word, least significant half first, then `2n` zeros.  `run` dispatches `w` workgroups,
so `workgroupSize · w` invocations.  WebGPU runs submissions in order, each dispatch its own usage
scope, and rejects a dispatch that binds a buffer both read-only and read-write.  `Meets` is
`Dispatch.Meets`, the statement of the Vulkan memory model about one dispatch.
-/

namespace Demos.Gpt32.Verified

open _root_.Demos.Gpt32 LeanExe.WGSL
open LeanExe.Dialect (build_size)

/-- The buffer of `output NAME n`: `n` as a 64-bit word, least significant half first, then
`2n` zeros. -/
def outputWords (n : Nat) : Array UInt32 :=
  Array.ofFn (n := 2 + 2 * n) fun i =>
    if i.val = 0 then UInt32.ofNat n else if i.val = 1 then UInt32.ofNat (n / 2 ^ 32) else 0

theorem outputWords_size (n : Nat) : (outputWords n).size = 2 + 2 * n := by
  simp [outputWords]

theorem outputWords_zero (n : Nat) : (outputWords n)[0]? = some (UInt32.ofNat n) := by
  simp [outputWords]

theorem outputWords_one {n : Nat} (h : n < 2 ^ 32) : (outputWords n)[1]? = some 0 := by
  rw [Array.getElem?_eq_getElem (by simp [outputWords]; omega)]
  simp only [outputWords, Array.getElem_ofFn]
  simp [Nat.div_eq_of_lt (show n < 4294967296 by omega)]

/-- The dispatch of `w` workgroups of kernel `k`. -/
def dispatchOf (k : KernelName) (w : Nat) (bufs : List (Array UInt32)) (o : Array UInt32) :
    Dispatch :=
  ⟨kernelMap k, bufs, o, (kernelMap k).workgroupSize * w⟩

def device : Device UInt32 where
  buffer v := v.arg.wgslBuffer
  words ws := some ws.toArray
  output := outputWords
  run k w bufs o := (kernelMap k).dispatch bufs o ((kernelMap k).workgroupSize * w)
  Meets k w bufs o out := (dispatchOf k w bufs o).Meets out

theorem apply_dispatch {k : KernelName} {vs : List Val} {ys : Array Float32}
    (h : k.apply vs = some ys) :
    (kernelMap k).dispatch (vs.map device.buffer) (outputWords ys.size)
        (64 * ((ys.size + 63) / 64)) = some (device.buffer (.arr ys)) ∧
      (kernelMap k).RaceFree (vs.map device.buffer) (outputWords ys.size).size
        (64 * ((ys.size + 63) / 64)) := by
  unfold KernelName.apply at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rename_i hb <;> simp only [kernelMap, build_size, embed32, layerNorm32,
      Library.Numerics.LinearAlgebra.Binary32.linear32, append32, scores32, headMax32, headSum32,
      probs32, mix32, Library.Numerics.LinearAlgebra.Binary32.add32, geluArray32, logits32]
  · obtain ⟨h1, h2, h3⟩ := hb
    exact embedKernel_dispatch _ _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact layerNormKernel_dispatch _ _ _ _ _ h1 h2 h3 h4 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact linearKernel_dispatch _ _ _ _ _ h1 h2 h3 h4 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := hb
    exact appendKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := hb
    exact scoresKernel_dispatch _ _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2⟩ := hb
    exact headMaxKernel_dispatch _ _ _ h1 h2 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := hb
    exact headSumKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact probsKernel_dispatch _ _ _ _ _ h1 h2 h3 h4 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := hb
    exact mixKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2⟩ := hb
    rw [size_toUInt64 h1]
    exact addKernel_dispatch _ _ h1 h2 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · rw [size_toUInt64 hb]
    exact geluKernel_dispatch _ hb _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := hb
    exact logitsKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)

theorem empty_buffer : device.buffer (.arr #[]) = #[0, 0] := by
  simp only [device, Val.arg, LeanExe.Source.Arg.wgslBuffer, arrayWords]
  ext i h1 h2
  · simp
  · simp only [Array.size_ofFn, Array.size_map, List.size_toArray, List.length_nil] at h1
    simp only [Array.getElem_ofFn]
    match i, h1 with
    | 0, _ => simp [wordHalf]
    | 1, _ => simp [wordHalf]

theorem backend : Backend device where
  word _ := rfl
  float _ := rfl
  empty := by rw [empty_buffer]; rfl
  apply := fun {k _ _} h => by
    obtain ⟨hd, hr⟩ := apply_dispatch h
    have hW := kernelMap_workgroupSize k
    refine ⟨?_, ?_⟩
    · show (kernelMap k).dispatch _ _ ((kernelMap k).workgroupSize * _) = _
      rw [hW]
      exact hd
    · show Dispatch.Meets ⟨_, _, _, (kernelMap k).workgroupSize * _⟩ _
      rw [hW]
      exact Dispatch.meets _ hd hr

/-- The host commands of a generation, run with the WGSL kernels, leave the bits of `step32` in
the score buffers, and every dispatch meets the statement of the Vulkan memory model. -/
theorem generate_host (files : String → Option Val) (dir : String) (s : Shape32)
    (W : Weights32) (ts : List UInt64) (t : UInt64) (st : Store)
    (hnh : s.nh.toNat ≤ 64) (hf : s.f.toNat < 2 ^ 29) (hlen : ts.length < 1024)
    (hts : ∀ t' ∈ t :: ts, (t' / s.chunk).toNat < s.rows.length)
    (hL : Loaded files dir W)
    (hF : _root_.Demos.Gpt32.Fits s W (List.replicate s.layers (#[], #[]))) :
    let cmds := Item.allCmds (setupItems s dir ++ stepsItems s ts 0 ++
      stepItems s t (UInt64.ofNat ts.length))
    let scores := (step32 s W t (UInt64.ofNat ts.length)
      (cachesAfter s W ts 0 (List.replicate s.layers (#[], #[])))).2
    ∃ st' : Store, Cmd.execAll device (hostFiles device files) (st.host device) cmds =
        some (st'.host device) ∧
      Cmd.AllMeet device (hostFiles device files) (st.host device) cmds ∧
      scores.length = s.rows.length ∧
      ∀ c < s.rows.length, st'.host device (.z c) = some (device.buffer (.arr scores[c]!)) :=
  _root_.Demos.Gpt32.generate_host device backend files dir s W ts t st hnh hf hlen hts hL hF

end Demos.Gpt32.Verified

#print axioms Demos.Gpt32.Verified.generate_host
