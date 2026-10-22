import Demos.Gpt32.VerifiedDispatch
import Demos.Gpt32.VerifiedKernels
import Demos.Gpt32.Compose

namespace Demos.Gpt32.Verified

open _root_.Demos.Gpt32 LeanExe.WGSL
open LeanExe.IR (build_size)

theorem apply_dispatch {k : KernelName} {vs : List Val} {ys : Array Float32}
    (h : k.apply vs = some ys) :
    ys.size < 2 ^ 29 ∧
      (kernelMap k).dispatch (vs.map Val.buffer) (outputWords ys.size)
        (64 * ((ys.size + 63) / 64)) = some (Val.buffer (.arr ys)) ∧
      (kernelMap k).RaceFree (vs.map Val.buffer) (outputWords ys.size).size
        (64 * ((ys.size + 63) / 64)) := by
  unfold KernelName.apply at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rename_i hb <;> simp only [kernelMap, build_size, embed32, layerNorm32, linear32,
      append32, scores32, headMax32, headSum32, probs32, mix32, add32, geluArray32,
      logits32]
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h3, embedKernel_dispatch _ _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact ⟨h4, layerNormKernel_dispatch _ _ _ _ _ h1 h2 h3 h4 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact ⟨h4, linearKernel_dispatch _ _ _ _ _ h1 h2 h3 h4 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h3, appendKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h3, scoresKernel_dispatch _ _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2⟩ := hb
    exact ⟨h2, headMaxKernel_dispatch _ _ _ h1 h2 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h3, headSumKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact ⟨h4, probsKernel_dispatch _ _ _ _ _ h1 h2 h3 h4 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h3, mixKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2⟩ := hb
    rw [size_toUInt64 h1]
    exact ⟨h1, addKernel_dispatch _ _ h1 h2 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · rw [size_toUInt64 hb]
    exact ⟨hb, geluKernel_dispatch _ hb _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h3, logitsKernel_dispatch _ _ _ _ h1 h2 h3 _ (outputWords_size _)
      (outputWords_zero _) (outputWords_one (by omega)) _ (by omega) (by omega)⟩

def backend : KernelBackend := ⟨kernelMap, kernelMap_workgroupSize, apply_dispatch⟩

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
    ∃ st' : Store, Cmd.execAll (hostFiles files) st.host cmds kernelMap = some st'.host ∧
      Cmd.AllRaceFree (hostFiles files) st.host cmds kernelMap ∧
      scores.length = s.rows.length ∧
      ∀ c < s.rows.length, st'.host (.z c) = some (Val.arr scores[c]!).buffer :=
  _root_.Demos.Gpt32.generate_host files dir s W ts t st hnh hf hlen hts hL hF backend

end Demos.Gpt32.Verified
