import Demos.Gpt32.Verified

namespace Demos.Gpt32.Verified

open _root_.Demos.Gpt32 LeanExe.WGSL

private abbrev floatWords (xs : Array Float32) : Array UInt64 :=
  xs.map fun x => x.toBits.toUInt64

theorem expKernel_dispatch (x : Array Float32) (hx : x.size < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    expKernel.dispatch [(Arg.array (floatWords x)).buffer] output count =
        some (arrayWords (floatWords (expArray32 x))) ∧
      expKernel.RaceFree [(Arg.array (floatWords x)).buffer] output.size count := by
  have fits : expGpu.spec.Fits (expGpu.args (.cons x .nil)) x.size := by
    refine ⟨rfl, ?_, ?_, hx⟩
    · change ∀ ys, Arg.array ys ∈ [Arg.array (floatWords x)] → ys.size < 2 ^ 29
      simp [floatWords]
      exact hx
    · change ∃ ys, some (Arg.array (floatWords x)) = some (.array ys) ∧ ys.size = x.size
      exact ⟨floatWords x, rfl, by simp [floatWords]⟩
  exact expGpu.dispatch_value _ (.cons x .nil) _ (compiled.expArray32.denote_eq x) x.size fits
    output hOut hL0 hL1 count hCover h32

theorem embedKernel_dispatch (wte wpe : Array Float32) (row p d : UInt64)
    (hw : wte.size < 2 ^ 29) (hp : wpe.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * d.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat d.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : d.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    embedKernel.dispatch [(Arg.array (floatWords wte)).buffer, (Arg.array (floatWords wpe)).buffer,
        (Arg.word row).buffer, (Arg.word p).buffer, (Arg.word d).buffer] output count =
        some (arrayWords (floatWords (embed32 wte wpe row p d))) ∧
      embedKernel.RaceFree [(Arg.array (floatWords wte)).buffer, (Arg.array (floatWords wpe)).buffer,
        (Arg.word row).buffer, (Arg.word p).buffer, (Arg.word d).buffer] output.size count := by
  let env : Env compiled.embed32.func.sig.params :=
    .cons wte (.cons wpe (.cons row (.cons p (.cons d .nil))))
  have fits : embedGpu.spec.Fits (embedGpu.args env) d.toNat := by
    refine ⟨rfl, ?_, ?_, hd⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords wte), .array (floatWords wpe),
        .word row, .word p, .word d] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hw, hp⟩
    · change some (Arg.word d) = some (.word (UInt64.ofNat d.toNat))
      simp only [UInt64.ofNat_toNat]
  exact embedGpu.dispatch_value _ env _ (compiled.embed32.denote_eq wte wpe row p d) d.toNat fits
    output hOut hL0 hL1 count hCover h32

theorem linearKernel_dispatch (x w b : Array Float32) (k m : UInt64) (hx : x.size < 2 ^ 29)
    (hw : w.size < 2 ^ 29) (hb : b.size < 2 ^ 29) (hm : m.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * m.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat m.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : m.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    linearKernel.dispatch [(Arg.array (floatWords x)).buffer, (Arg.array (floatWords w)).buffer,
        (Arg.array (floatWords b)).buffer, (Arg.word k).buffer, (Arg.word m).buffer] output count =
        some (arrayWords (floatWords (Library.Numerics.LinearAlgebra.Binary32.linear32 x w b k m))) ∧
      linearKernel.RaceFree [(Arg.array (floatWords x)).buffer, (Arg.array (floatWords w)).buffer,
        (Arg.array (floatWords b)).buffer, (Arg.word k).buffer, (Arg.word m).buffer] output.size
        count := by
  let env : Env compiled.linear32.func.sig.params := .cons x (.cons w (.cons b (.cons k (.cons m (.nil)))))
  have fits : linearGpu.spec.Fits (linearGpu.args env) m.toNat := by
    refine ⟨rfl, ?_, ?_, hm⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords x), .array (floatWords w), .array (floatWords b), .word k, .word m] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hx, hw, hb⟩
    · change some (Arg.word m) = some (.word (UInt64.ofNat m.toNat))
      simp only [UInt64.ofNat_toNat]
  exact linearGpu.dispatch_value _ env _ (compiled.linear32.denote_eq x w b k m)
    m.toNat fits output hOut hL0 hL1 count hCover h32

theorem logitsKernel_dispatch (h wte : Array Float32) (rows d : UInt64) (hh : h.size < 2 ^ 29)
    (hw : wte.size < 2 ^ 29) (hr : rows.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * rows.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat rows.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : rows.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    logitsKernel.dispatch [(Arg.array (floatWords h)).buffer, (Arg.array (floatWords wte)).buffer,
        (Arg.word rows).buffer, (Arg.word d).buffer] output count =
        some (arrayWords (floatWords (logits32 h wte rows d))) ∧
      logitsKernel.RaceFree [(Arg.array (floatWords h)).buffer,
        (Arg.array (floatWords wte)).buffer, (Arg.word rows).buffer, (Arg.word d).buffer]
        output.size count := by
  let env : Env compiled.logits32.func.sig.params := .cons h (.cons wte (.cons rows (.cons d (.nil))))
  have fits : logitsGpu.spec.Fits (logitsGpu.args env) rows.toNat := by
    refine ⟨rfl, ?_, ?_, hr⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords h), .array (floatWords wte), .word rows, .word d] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hh, hw⟩
    · change some (Arg.word rows) = some (.word (UInt64.ofNat rows.toNat))
      simp only [UInt64.ofNat_toNat]
  exact logitsGpu.dispatch_value _ env _ (compiled.logits32.denote_eq h wte rows d)
    rows.toNat fits output hOut hL0 hL1 count hCover h32

theorem mixKernel_dispatch (pw vc : Array Float32) (p d : UInt64) (hp : pw.size < 2 ^ 29)
    (hv : vc.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * d.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat d.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : d.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    mixKernel.dispatch [(Arg.array (floatWords pw)).buffer, (Arg.array (floatWords vc)).buffer,
        (Arg.word p).buffer, (Arg.word d).buffer] output count =
        some (arrayWords (floatWords (mix32 pw vc p d))) ∧
      mixKernel.RaceFree [(Arg.array (floatWords pw)).buffer, (Arg.array (floatWords vc)).buffer,
        (Arg.word p).buffer, (Arg.word d).buffer] output.size count := by
  let env : Env compiled.mix32.func.sig.params := .cons pw (.cons vc (.cons p (.cons d (.nil))))
  have fits : mixGpu.spec.Fits (mixGpu.args env) d.toNat := by
    refine ⟨rfl, ?_, ?_, hd⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords pw), .array (floatWords vc), .word p, .word d] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hp, hv⟩
    · change some (Arg.word d) = some (.word (UInt64.ofNat d.toNat))
      simp only [UInt64.ofNat_toNat]
  exact mixGpu.dispatch_value _ env _ (compiled.mix32.denote_eq pw vc p d)
    d.toNat fits output hOut hL0 hL1 count hCover h32

theorem scoresKernel_dispatch (q kc : Array Float32) (p d n : UInt64) (hq : q.size < 2 ^ 29)
    (hk : kc.size < 2 ^ 29) (hn : n.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat n.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    scoresKernel.dispatch [(Arg.array (floatWords q)).buffer, (Arg.array (floatWords kc)).buffer,
        (Arg.word p).buffer, (Arg.word d).buffer, (Arg.word n).buffer] output count =
        some (arrayWords (floatWords (scores32 q kc p d n))) ∧
      scoresKernel.RaceFree [(Arg.array (floatWords q)).buffer, (Arg.array (floatWords kc)).buffer,
        (Arg.word p).buffer, (Arg.word d).buffer, (Arg.word n).buffer] output.size count := by
  let env : Env compiled.scores32.func.sig.params := .cons q (.cons kc (.cons p (.cons d (.cons n (.nil)))))
  have fits : scoresGpu.spec.Fits (scoresGpu.args env) n.toNat := by
    refine ⟨rfl, ?_, ?_, hn⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords q), .array (floatWords kc), .word p, .word d, .word n] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hq, hk⟩
    · change some (Arg.word n) = some (.word (UInt64.ofNat n.toNat))
      simp only [UInt64.ofNat_toNat]
  exact scoresGpu.dispatch_value _ env _ (compiled.scores32.denote_eq q kc p d n)
    n.toNat fits output hOut hL0 hL1 count hCover h32

theorem addKernel_dispatch (a b : Array Float32) (ha : a.size < 2 ^ 29) (hb : b.size < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * a.size)
    (hL0 : output[0]? = some (UInt32.ofNat a.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : a.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    addKernel.dispatch [(Arg.array (floatWords a)).buffer, (Arg.array (floatWords b)).buffer]
        output count = some (arrayWords (floatWords (Library.Numerics.LinearAlgebra.Binary32.add32 a b))) ∧
      addKernel.RaceFree [(Arg.array (floatWords a)).buffer, (Arg.array (floatWords b)).buffer]
        output.size count := by
  let env : Env compiled.add32.func.sig.params := .cons a (.cons b (.nil))
  have fits : addGpu.spec.Fits (addGpu.args env) a.size := by
    refine ⟨rfl, ?_, ?_, ha⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords a), .array (floatWords b)] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨ha, hb⟩
    · change ∃ ys, some (Arg.array (floatWords a)) = some (.array ys) ∧ ys.size = a.size
      exact ⟨floatWords a, rfl, by simp [floatWords]⟩
  exact addGpu.dispatch_value _ env _ (compiled.add32.denote_eq a b)
    a.size fits output hOut hL0 hL1 count hCover h32

theorem appendKernel_dispatch (cache row : Array Float32) (base n : UInt64)
    (hc : cache.size < 2 ^ 29) (hr : row.size < 2 ^ 29) (hn : n.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat n.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    appendKernel.dispatch [(Arg.array (floatWords cache)).buffer,
        (Arg.array (floatWords row)).buffer, (Arg.word base).buffer, (Arg.word n).buffer] output
        count = some (arrayWords (floatWords (append32 cache row base n))) ∧
      appendKernel.RaceFree [(Arg.array (floatWords cache)).buffer,
        (Arg.array (floatWords row)).buffer, (Arg.word base).buffer, (Arg.word n).buffer]
        output.size count := by
  let env : Env compiled.append32.func.sig.params := .cons cache (.cons row (.cons base (.cons n (.nil))))
  have fits : appendGpu.spec.Fits (appendGpu.args env) n.toNat := by
    refine ⟨rfl, ?_, ?_, hn⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords cache), .array (floatWords row), .word base, .word n] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hc, hr⟩
    · change some (Arg.word n) = some (.word (UInt64.ofNat n.toNat))
      simp only [UInt64.ofNat_toNat]
  exact appendGpu.dispatch_value _ env _ (compiled.append32.denote_eq cache row base n)
    n.toNat fits output hOut hL0 hL1 count hCover h32

theorem geluKernel_dispatch (x : Array Float32) (hx : x.size < 2 ^ 29) (output : Array UInt32)
    (hOut : output.size = 2 + 2 * x.size) (hL0 : output[0]? = some (UInt32.ofNat x.size))
    (hL1 : output[1]? = some 0) (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    geluKernel.dispatch [(Arg.array (floatWords x)).buffer] output count =
        some (arrayWords (floatWords (geluArray32 x))) ∧
      geluKernel.RaceFree [(Arg.array (floatWords x)).buffer] output.size count := by
  let env : Env compiled.geluArray32.func.sig.params := .cons x (.nil)
  have fits : geluGpu.spec.Fits (geluGpu.args env) x.size := by
    refine ⟨rfl, ?_, ?_, hx⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords x)] → ys.size < 2 ^ 29
      simp [floatWords]
      exact hx
    · change ∃ ys, some (Arg.array (floatWords x)) = some (.array ys) ∧ ys.size = x.size
      exact ⟨floatWords x, rfl, by simp [floatWords]⟩
  exact geluGpu.dispatch_value _ env _ (compiled.geluArray32.denote_eq x)
    x.size fits output hOut hL0 hL1 count hCover h32

theorem probsKernel_dispatch (s mx sm : Array Float32) (p n : UInt64) (hs : s.size < 2 ^ 29)
    (hm : mx.size < 2 ^ 29) (hsm : sm.size < 2 ^ 29) (hn : n.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat n.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    probsKernel.dispatch [(Arg.array (floatWords s)).buffer, (Arg.array (floatWords mx)).buffer,
        (Arg.array (floatWords sm)).buffer, (Arg.word p).buffer, (Arg.word n).buffer] output
        count = some (arrayWords (floatWords (probs32 s mx sm p n))) ∧
      probsKernel.RaceFree [(Arg.array (floatWords s)).buffer, (Arg.array (floatWords mx)).buffer,
        (Arg.array (floatWords sm)).buffer, (Arg.word p).buffer, (Arg.word n).buffer]
        output.size count := by
  let env : Env compiled.probs32.func.sig.params := .cons s (.cons mx (.cons sm (.cons p (.cons n (.nil)))))
  have fits : probsGpu.spec.Fits (probsGpu.args env) n.toNat := by
    refine ⟨rfl, ?_, ?_, hn⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords s), .array (floatWords mx), .array (floatWords sm), .word p, .word n] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hs, hm, hsm⟩
    · change some (Arg.word n) = some (.word (UInt64.ofNat n.toNat))
      simp only [UInt64.ofNat_toNat]
  exact probsGpu.dispatch_value _ env _ (compiled.probs32.denote_eq s mx sm p n)
    n.toNat fits output hOut hL0 hL1 count hCover h32

theorem layerNormKernel_dispatch (x g b : Array Float32) (d : UInt64) (nf : Float32)
    (hx : x.size < 2 ^ 29) (hg : g.size < 2 ^ 29) (hb : b.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * d.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat d.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : d.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    layerNormKernel.dispatch [(Arg.array (floatWords x)).buffer, (Arg.array (floatWords g)).buffer,
        (Arg.array (floatWords b)).buffer, (Arg.word d).buffer, (Arg.float nf.toBits).buffer]
        output count = some (arrayWords (floatWords (layerNorm32 x g b d nf))) ∧
      layerNormKernel.RaceFree [(Arg.array (floatWords x)).buffer,
        (Arg.array (floatWords g)).buffer, (Arg.array (floatWords b)).buffer, (Arg.word d).buffer,
        (Arg.float nf.toBits).buffer] output.size count := by
  let env : Env compiled.layerNorm32.func.sig.params := .cons x (.cons g (.cons b (.cons d (.cons nf (.nil)))))
  have fits : layerNormGpu.spec.Fits (layerNormGpu.args env) d.toNat := by
    refine ⟨rfl, ?_, ?_, hd⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords x), .array (floatWords g), .array (floatWords b), .word d, .float nf.toBits] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hx, hg, hb⟩
    · change some (Arg.word d) = some (.word (UInt64.ofNat d.toNat))
      simp only [UInt64.ofNat_toNat]
  exact layerNormGpu.dispatch_value _ env _ (compiled.layerNorm32.denote_eq x g b d nf)
    d.toNat fits output hOut hL0 hL1 count hCover h32

theorem headMaxKernel_dispatch (s : Array Float32) (p nh : UInt64) (hs : s.size < 2 ^ 29)
    (hnh : nh.toNat < 2 ^ 29) (output : Array UInt32) (hOut : output.size = 2 + 2 * nh.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat nh.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : nh.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    headMaxKernel.dispatch [(Arg.array (floatWords s)).buffer, (Arg.word p).buffer,
        (Arg.word nh).buffer] output count = some (arrayWords (floatWords (headMax32 s p nh))) ∧
      headMaxKernel.RaceFree [(Arg.array (floatWords s)).buffer, (Arg.word p).buffer,
        (Arg.word nh).buffer] output.size count := by
  let env : Env compiled.headMax32.func.sig.params := .cons s (.cons p (.cons nh (.nil)))
  have fits : headMaxGpu.spec.Fits (headMaxGpu.args env) nh.toNat := by
    refine ⟨rfl, ?_, ?_, hnh⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords s), .word p, .word nh] → ys.size < 2 ^ 29
      simp [floatWords]
      exact hs
    · change some (Arg.word nh) = some (.word (UInt64.ofNat nh.toNat))
      simp only [UInt64.ofNat_toNat]
  exact headMaxGpu.dispatch_value _ env _ (compiled.headMax32.denote_eq s p nh)
    nh.toNat fits output hOut hL0 hL1 count hCover h32

theorem headSumKernel_dispatch (s mx : Array Float32) (p nh : UInt64) (hs : s.size < 2 ^ 29)
    (hm : mx.size < 2 ^ 29) (hnh : nh.toNat < 2 ^ 29) (output : Array UInt32)
    (hOut : output.size = 2 + 2 * nh.toNat) (hL0 : output[0]? = some (UInt32.ofNat nh.toNat))
    (hL1 : output[1]? = some 0) (count : Nat) (hCover : nh.toNat ≤ count)
    (h32 : count ≤ 2 ^ 32) :
    headSumKernel.dispatch [(Arg.array (floatWords s)).buffer, (Arg.array (floatWords mx)).buffer,
        (Arg.word p).buffer, (Arg.word nh).buffer] output count =
        some (arrayWords (floatWords (headSum32 s mx p nh))) ∧
      headSumKernel.RaceFree [(Arg.array (floatWords s)).buffer, (Arg.array (floatWords mx)).buffer,
        (Arg.word p).buffer, (Arg.word nh).buffer] output.size count := by
  let env : Env compiled.headSum32.func.sig.params := .cons s (.cons mx (.cons p (.cons nh (.nil))))
  have fits : headSumGpu.spec.Fits (headSumGpu.args env) nh.toNat := by
    refine ⟨rfl, ?_, ?_, hnh⟩
    · change ∀ ys, Arg.array ys ∈ [.array (floatWords s), .array (floatWords mx), .word p, .word nh] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hs, hm⟩
    · change some (Arg.word nh) = some (.word (UInt64.ofNat nh.toNat))
      simp only [UInt64.ofNat_toNat]
  exact headSumGpu.dispatch_value _ env _ (compiled.headSum32.denote_eq s mx p nh)
    nh.toNat fits output hOut hL0 hL1 count hCover h32

end Demos.Gpt32.Verified
