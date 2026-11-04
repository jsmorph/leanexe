import Demos.Gpt32.VerifiedPtxKernels
import Demos.Gpt32.Compose
import LeanExe.PTX.Launch

/-!
The device of `leanexe-cuda-host session` with the PTX kernels of `kernelMap`, and the host theorem
of the GPT-2 generation on it.  A buffer holds 64-bit words.  `words` pairs 32-bit halves, least
significant first, into 64-bit words and rejects an odd count, and `output NAME n` holds `n`
followed by `n` zero words.  `run` launches `w` blocks of 64 threads.  `Meets` is `Launch.Meets`,
the statement of the PTX memory model about one launch.
-/

namespace Demos.Gpt32.VerifiedPtx

open _root_.Demos.Gpt32 LeanExe.PTX
open _root_.Verified.PTX (LaunchSeq)

/-- The 64-bit words of 32-bit halves, least significant half first, or `none` for an odd
count. -/
def pairWords : List UInt32 → Option (List UInt64)
  | [] => some []
  | [_] => none
  | lo :: hi :: rest => (pairWords rest).map (UInt64.ofNat (lo.toNat + hi.toNat * 2 ^ 32) :: ·)

/-- The launch of `w` blocks of 64 threads of kernel `k`. -/
def launchOf (k : KernelName) (w : Nat) (bufs : List (Array UInt64)) (o : Array UInt64) :
    Launch :=
  ⟨kernelMap k, bufs, o, w, 64⟩

def device : Device UInt64 where
  buffer v := v.arg.ptxBuffer
  words ws := (pairWords ws).map List.toArray
  output n := #[UInt64.ofNat n] ++ Array.replicate n 0
  run k w bufs o := (launchOf k w bufs o).seq
  Meets k w bufs o out := (launchOf k w bufs o).Meets out

theorem pair_halves (v : UInt64) :
    UInt64.ofNat (v.toUInt32.toNat + (v >>> 32).toUInt32.toNat * 2 ^ 32) = v := by
  apply UInt64.toNat_inj.mp
  have hv : v.toNat < 2 ^ 64 := v.toNat_lt
  simp only [UInt64.toNat_ofNat', UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow] at hv ⊢
  omega

theorem pair_float (b : UInt32) :
    UInt64.ofNat (b.toNat + (0 : UInt32).toNat * 2 ^ 32) = b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hb : b.toNat < 2 ^ 32 := b.toNat_lt
  simp only [UInt64.toNat_ofNat', UInt32.toNat_toUInt64, UInt32.toNat_zero, Nat.zero_mul,
    Nat.add_zero, Nat.reducePow] at hb ⊢
  omega

/-- A call whose kernel's launch theorem gives the sequential run leaves the call's result, and
its launch meets the PTX memory model. -/
theorem launch_apply {k : KernelName} {vs : List Val} {ys : Array Float32} {n : Nat}
    (hn : ys.size = n)
    (hl : LaunchSeq (kernelMap k) (vs.map Val.arg) n (Array.replicate n 0) ((n + 63) / 64) 64
      (ys.map fun x => x.toBits.toUInt64)) :
    device.run k ((ys.size + 63) / 64) (vs.map device.buffer) (device.output ys.size) =
        some (device.buffer (.arr ys)) ∧
      device.Meets k ((ys.size + 63) / 64) (vs.map device.buffer) (device.output ys.size)
        (device.buffer (.arr ys)) := by
  subst hn
  obtain ⟨hs, hr⟩ := hl
  have hm : vs.map device.buffer = (vs.map Val.arg).map LeanExe.Source.Arg.ptxBuffer := by
    rw [List.map_map]
    rfl
  have hb : device.buffer (.arr ys) =
      #[UInt64.ofNat ys.size] ++ ys.map fun x => x.toBits.toUInt64 := by
    simp [device, Val.arg, LeanExe.Source.Arg.ptxBuffer]
  have hs' : (launchOf k ((ys.size + 63) / 64) (vs.map device.buffer)
      (device.output ys.size)).seq = some (device.buffer (.arr ys)) := by
    rw [hm, hb]
    exact hs
  have hr' : (launchOf k ((ys.size + 63) / 64) (vs.map device.buffer)
      (device.output ys.size)).RaceFree := by
    rw [hm]
    exact hr
  exact ⟨hs', Launch.meets _ hs' hr'⟩

theorem apply_launch {k : KernelName} {vs : List Val} {ys : Array Float32}
    (h : k.apply vs = some ys) :
    device.run k ((ys.size + 63) / 64) (vs.map device.buffer) (device.output ys.size) =
        some (device.buffer (.arr ys)) ∧
      device.Meets k ((ys.size + 63) / 64) (vs.map device.buffer) (device.output ys.size)
        (device.buffer (.arr ys)) := by
  unfold KernelName.apply at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rename_i hb
  · obtain ⟨h1, h2, h3⟩ := hb
    exact launch_apply (embed32_size _ _ _ _ _) (embedKernel_launch _ _ _ _ _ h1 h2 h3
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact launch_apply (layerNorm32_size _ _ _ _ _) (layerNormKernel_launch _ _ _ _ _ h1 h2 h3
      h4 (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact launch_apply (linear32_size _ _ _ _ _) (linearKernel_launch _ _ _ _ _ h1 h2 h3 h4
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3⟩ := hb
    exact launch_apply (append32_size _ _ _ _) (appendKernel_launch _ _ _ _ h1 h2 h3
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3⟩ := hb
    exact launch_apply (scores32_size _ _ _ _ _) (scoresKernel_launch _ _ _ _ _ h1 h2 h3
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2⟩ := hb
    exact launch_apply (headMax32_size _ _ _) (headMaxKernel_launch _ _ _ h1 h2
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3⟩ := hb
    exact launch_apply (headSum32_size _ _ _ _) (headSumKernel_launch _ _ _ _ h1 h2 h3
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact launch_apply (probs32_size _ _ _ _ _) (probsKernel_launch _ _ _ _ _ h1 h2 h3 h4
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3⟩ := hb
    exact launch_apply (mix32_size _ _ _ _) (mixKernel_launch _ _ _ _ h1 h2 h3
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2⟩ := hb
    exact launch_apply (add32_size _ h1) (addKernel_launch _ _ h1 h2
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · exact launch_apply (geluArray32_size hb) (geluKernel_launch _ hb
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1
  · obtain ⟨h1, h2, h3⟩ := hb
    exact launch_apply (logits32_size _ _ _ _) (logitsKernel_launch _ _ _ _ h1 h2 h3
      (Array.replicate _ 0) (by simp) _ 64 (by decide) (by decide) (by omega) (by omega)
      (by omega)).1

theorem backend : Backend device where
  word v := by
    show some #[UInt64.ofNat (v.toUInt32.toNat + (v >>> 32).toUInt32.toNat * 2 ^ 32)] = some #[v]
    rw [pair_halves]
  float x := by
    show some #[UInt64.ofNat (x.toBits.toNat + (0 : UInt32).toNat * 2 ^ 32)] =
      some #[x.toBits.toUInt64]
    rw [pair_float]
  empty := by simp [device, pairWords, Val.arg, LeanExe.Source.Arg.ptxBuffer]
  apply := apply_launch

/-- The host commands of a generation, run with the PTX kernels, leave the bits of `step32` in the
score buffers, and every launch meets the statement of the PTX memory model. -/
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

end Demos.Gpt32.VerifiedPtx

#print axioms Demos.Gpt32.VerifiedPtx.generate_host
