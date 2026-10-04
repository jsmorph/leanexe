import Project.Gpt32.Exec

/-!
The step program computes `step32`: the layer lemma follows the eighteen calls of a layer, and
the step theorem the words, the embedding, the layers, and the scores.
-/

namespace Project.Gpt32

open Project.WGSL LeanExe.Examples.Gpt32

theorem embed32_size (wte wpe : Array Float32) (row p d : UInt64) :
    (embed32 wte wpe row p d).size = d.toNat := build_size' _ _
theorem layerNorm32_size (x g b : Array Float32) (d : UInt64) (nf : Float32) :
    (layerNorm32 x g b d nf).size = d.toNat := build_size' _ _
theorem linear32_size (x w b : Array Float32) (k m : UInt64) :
    (linear32 x w b k m).size = m.toNat := build_size' _ _
theorem append32_size (cache row : Array Float32) (base n : UInt64) :
    (append32 cache row base n).size = n.toNat := build_size' _ _
theorem scores32_size (q kc : Array Float32) (p d n : UInt64) :
    (scores32 q kc p d n).size = n.toNat := build_size' _ _
theorem headMax32_size (s : Array Float32) (p nh : UInt64) :
    (headMax32 s p nh).size = nh.toNat := build_size' _ _
theorem headSum32_size (s mx : Array Float32) (p nh : UInt64) :
    (headSum32 s mx p nh).size = nh.toNat := build_size' _ _
theorem probs32_size (s mx sm : Array Float32) (p n : UInt64) :
    (probs32 s mx sm p n).size = n.toNat := build_size' _ _
theorem mix32_size (pw vc : Array Float32) (p d : UInt64) :
    (mix32 pw vc p d).size = d.toNat := build_size' _ _
theorem add32_size {a : Array Float32} (b : Array Float32) (h : a.size < 2 ^ 29) :
    (add32 a b).size = a.size := by
  rw [add32, build_size', size_toUInt64 h]
theorem geluArray32_size {x : Array Float32} (h : x.size < 2 ^ 29) :
    (geluArray32 x).size = x.size := by
  rw [geluArray32, build_size', size_toUInt64 h]
theorem logits32_size (h wte : Array Float32) (rows d : UInt64) :
    (logits32 h wte rows d).size = rows.toNat := build_size' _ _

theorem Item.execAll_call {files : String → Option Val} {st : Store} {k : KernelName} {n : Nat}
    {out : Buf} {ins : List Buf} (is : List Item) (ys : Array Float32) (hout : out ∉ ins)
    (hk : (ins.mapM st).bind k.apply = some ys) (hn : ys.size = n) :
    Item.execAll files st (.call k n out ins :: is) =
      Item.execAll files (st.set out (.arr ys)) is := by
  cases hvs : ins.mapM st with
  | none => simp [hvs] at hk
  | some vs =>
    simp only [hvs, Option.bind_some] at hk
    simp [Item.execAll, Item.exec, hout, hvs, hk, hn]

/-- The bounds of a step: at most 64 heads, an MLP width below 2^29, and a position below
1,024. -/
structure Bounds (s : Shape32) (p : UInt64) : Prop where
  nh : s.nh.toNat ≤ 64
  f : s.f.toNat < 2 ^ 29
  p : p.toNat < 1024

/-- The words of position `p`. -/
structure Words (s : Shape32) (p : UInt64) (st : Store) : Prop where
  pos : st .pos = some (.word p)
  base : st .base = some (.word (p * (64 * s.nh)))
  top : st .top = some (.word ((p + 1) * (64 * s.nh)))
  width : st .width = some (.word (64 * s.nh))
  hidden : st .hidden = some (.word s.f)
  heads : st .heads = some (.word s.nh)
  scoreLen : st .scoreLen = some (.word (s.nh * 1024))
  nf : st .nf = some (.float (64 * s.nh).toFloat32)

/-- The activations of a step, which every step overwrites. -/
def Buf.scratch : Buf → Bool
  | .x | .h1 | .q | .k | .v | .sc | .mx | .sm | .pw | .o | .a | .r | .h2 | .m1 | .g | .m2
  | .hf | .z _ => true
  | _ => false

theorem Store.set_ne {s : Store} {b c : Buf} {v : Val} (h : c ≠ b) : s.set b v c = s c := by
  simp [Store.set, h]

theorem Buf.ne_of_scratch {c : Buf} (h : c.scratch = false) :
    c ≠ .x ∧ c ≠ .h1 ∧ c ≠ .q ∧ c ≠ .k ∧ c ≠ .v ∧ c ≠ .sc ∧ c ≠ .mx ∧ c ≠ .sm ∧ c ≠ .pw ∧
      c ≠ .o ∧ c ≠ .a ∧ c ≠ .r ∧ c ≠ .h2 ∧ c ≠ .m1 ∧ c ≠ .g ∧ c ≠ .m2 := by
  cases c <;> simp_all [Buf.scratch]

theorem Bounds.d {s : Shape32} {p : UInt64} (h : Bounds s p) :
    (64 * s.nh).toNat = 64 * s.nh.toNat := by
  have := h.nh
  rw [UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  omega

theorem Bounds.n {s : Shape32} {p : UInt64} (h : Bounds s p) :
    (s.nh * 1024).toNat = s.nh.toNat * 1024 := by
  have := h.nh
  rw [UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  omega

theorem Bounds.p1 {s : Shape32} {p : UInt64} (h : Bounds s p) : (p + 1).toNat = p.toNat + 1 := by
  have := h.p
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

theorem Bounds.top {s : Shape32} {p : UInt64} (h : Bounds s p) :
    ((p + 1) * (64 * s.nh)).toNat = (p.toNat + 1) * (64 * s.nh.toNat) ∧
      (p.toNat + 1) * (64 * s.nh.toNat) ≤ 2 ^ 22 := by
  have hn := h.nh
  have hp := h.p
  have hle : (p.toNat + 1) * (64 * s.nh.toNat) ≤ 1024 * (64 * 64) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine ⟨?_, by omega⟩
  rw [UInt64.toNat_mul, h.p1, h.d]
  exact Nat.mod_eq_of_lt (by omega)

/-- Layer `l` at position `p` carries a store with the row `x`, the layer's weights `w`, and its
caches `kc` and `vc` at the parity of `p` to one with `layerStep32`'s row and caches, the caches
at the other parity, and every buffer other than the activations and those caches unchanged. -/
theorem layer_exec (files : String → Option Val) {s : Shape32} {p : UInt64} (l : Nat)
    (w : Layer32) (x kc vc : Array Float32) (st : Store) (is : List Item) (hB : Bounds s p)
    (hW : Words s p st) (hx : st .x = some (.arr x)) (hxs : x.size = 64 * s.nh.toNat)
    (hw : ∀ f : Field, st (.layer l f) = some (.arr (f.get w))) (hws : ∀ f : Field, Small (f.get w))
    (hk : st (.kc l (p % 2).toNat) = some (.arr kc))
    (hv : st (.vc l (p % 2).toNat) = some (.arr vc)) (hks : Small kc) (hvs : Small vc) :
    ∃ st', Item.execAll files st (layerItems s p l ++ is) = Item.execAll files st' is ∧
      st' .x = some (.arr (layerStep32 s.nh s.f p w x kc vc).1) ∧
      (layerStep32 s.nh s.f p w x kc vc).1.size = 64 * s.nh.toNat ∧
      st' (.kc l ((p + 1) % 2).toNat) = some (.arr (layerStep32 s.nh s.f p w x kc vc).2.1) ∧
      st' (.vc l ((p + 1) % 2).toNat) = some (.arr (layerStep32 s.nh s.f p w x kc vc).2.2) ∧
      Small (layerStep32 s.nh s.f p w x kc vc).2.1 ∧
      Small (layerStep32 s.nh s.f p w x kc vc).2.2 ∧
      ∀ c, c.scratch = false → c ≠ .kc l ((p + 1) % 2).toNat →
        c ≠ .vc l ((p + 1) % 2).toNat → st' c = st c := by
  have hd := hB.d
  have hn := hB.n
  have hnh := hB.nh
  have hf := hB.f
  obtain ⟨htop, htop22⟩ := hB.top
  have hpar : (p % 2).toNat ≠ ((p + 1) % 2).toNat := by
    rw [UInt64.toNat_mod, UInt64.toNat_mod, hB.p1]
    simp only [UInt64.reduceToNat]
    omega
  have hpar' := Ne.symm hpar
  obtain ⟨hpos, hbase, htopw, hwidth, hhidden, hheads, hscoreLen, hnf⟩ := hW
  have hg1 := hw .g1
  have hb1 := hw .b1
  have hwq := hw .wq
  have hbq := hw .bq
  have hwk := hw .wk
  have hbk := hw .bk
  have hwv := hw .wv
  have hbv := hw .bv
  have hwo := hw .wo
  have hbo := hw .bo
  have hg2 := hw .g2
  have hb2 := hw .b2
  have hwfc := hw .wfc
  have hbfc := hw .bfc
  have hwproj := hw .wproj
  have hbproj := hw .bproj
  simp only [Field.get] at hg1 hb1 hwq hbq hwk hbk hwv hbv hwo hbo hg2 hb2
  simp only [Field.get] at hwfc hbfc hwproj hbproj
  have sg1 := hws .g1
  have sb1 := hws .b1
  have swq := hws .wq
  have sbq := hws .bq
  have swk := hws .wk
  have sbk := hws .bk
  have swv := hws .wv
  have sbv := hws .bv
  have swo := hws .wo
  have sbo := hws .bo
  have sg2 := hws .g2
  have sb2 := hws .b2
  have swfc := hws .wfc
  have sbfc := hws .bfc
  have swproj := hws .wproj
  have sbproj := hws .bproj
  simp only [Field.get, Small] at sg1 sb1 swq sbq swk sbk swv sbv swo sbo sg2 sb2
  simp only [Field.get, Small] at swfc sbfc swproj sbproj
  simp only [Small] at hks hvs
  generalize hD : 64 * s.nh = D at *
  generalize hb0 : (p % 2).toNat = b at *
  generalize hb1' : ((p + 1) % 2).toNat = b' at *
  let h1 := layerNorm32 x w.g1 w.b1 D D.toFloat32
  let q := linear32 h1 w.wq w.bq D D
  let k := linear32 h1 w.wk w.bk D D
  let v := linear32 h1 w.wv w.bv D D
  let kc' := append32 kc k (p * D) ((p + 1) * D)
  let vc' := append32 vc v (p * D) ((p + 1) * D)
  let sc := scores32 q kc' p D (s.nh * 1024)
  let mx := headMax32 sc p s.nh
  let sm := headSum32 sc mx p s.nh
  let pw := probs32 sc mx sm p (s.nh * 1024)
  let o := mix32 pw vc' p D
  let a := linear32 o w.wo w.bo D D
  let r := add32 x a
  let h2 := layerNorm32 r w.g2 w.b2 D D.toFloat32
  let m1 := linear32 h2 w.wfc w.bfc D s.f
  let g := geluArray32 m1
  let m2 := linear32 g w.wproj w.bproj s.f D
  let y := add32 r m2
  have zh1 : h1.size = 64 * s.nh.toNat := by simp only [h1, layerNorm32_size, hd]
  have zq : q.size = 64 * s.nh.toNat := by simp only [q, linear32_size, hd]
  have zk : k.size = 64 * s.nh.toNat := by simp only [k, linear32_size, hd]
  have zv : v.size = 64 * s.nh.toNat := by simp only [v, linear32_size, hd]
  have zkc : kc'.size = (p + 1).toNat * (64 * s.nh.toNat) := by
    simp only [kc', append32_size, htop, hB.p1]
  have zvc : vc'.size = (p + 1).toNat * (64 * s.nh.toNat) := by
    simp only [vc', append32_size, htop, hB.p1]
  have zsc : sc.size = s.nh.toNat * 1024 := by simp only [sc, scores32_size, hn]
  have zmx : mx.size = s.nh.toNat := by simp only [mx, headMax32_size]
  have zsm : sm.size = s.nh.toNat := by simp only [sm, headSum32_size]
  have zpw : pw.size = s.nh.toNat * 1024 := by simp only [pw, probs32_size, hn]
  have zo : o.size = 64 * s.nh.toNat := by simp only [o, mix32_size, hd]
  have za : a.size = 64 * s.nh.toNat := by simp only [a, linear32_size, hd]
  have zr : r.size = 64 * s.nh.toNat := by
    simp only [r]
    rw [add32_size _ (by omega), hxs]
  have zh2 : h2.size = 64 * s.nh.toNat := by simp only [h2, layerNorm32_size, hd]
  have zm1 : m1.size = s.f.toNat := by simp only [m1, linear32_size]
  have zg : g.size = s.f.toNat := by
    simp only [g]
    rw [geluArray32_size (by omega), zm1]
  have zm2 : m2.size = 64 * s.nh.toNat := by simp only [m2, linear32_size, hd]
  have zy : y.size = 64 * s.nh.toNat := by
    simp only [y]
    rw [add32_size _ (by omega), zr]
  have hp1 := hB.p1
  have hx29 : x.size < 536870912 := by omega
  have hD29 : D.toNat < 536870912 := by omega
  have hN29 : (s.nh * 1024).toNat < 536870912 := by omega
  have hT29 : ((p + 1) * D).toNat < 536870912 := by rw [htop]; omega
  have hnh29 : s.nh.toNat < 536870912 := by omega
  have sh1 : h1.size < 536870912 := by omega
  have sq : q.size < 536870912 := by omega
  have sk : k.size < 536870912 := by omega
  have sv : v.size < 536870912 := by omega
  have skc : kc'.size < 536870912 := by rw [zkc, hp1]; omega
  have svc : vc'.size < 536870912 := by rw [zvc, hp1]; omega
  have ssc : sc.size < 536870912 := by omega
  have smx : mx.size < 536870912 := by omega
  have ssm : sm.size < 536870912 := by omega
  have spw : pw.size < 536870912 := by omega
  have so : o.size < 536870912 := by omega
  have sa : a.size < 536870912 := by omega
  have sr : r.size < 536870912 := by omega
  have sh2 : h2.size < 536870912 := by omega
  have sm1 : m1.size < 536870912 := by omega
  have sg : g.size < 536870912 := by omega
  have sm2 : m2.size < 536870912 := by omega
  simp only [Nat.reducePow] at sg1 sb1 swq sbq swk sbk swv sbv swo sbo sg2 sb2
  simp only [Nat.reducePow] at swfc sbfc swproj sbproj hks hvs hf
  have hstep : layerStep32 s.nh s.f p w x kc vc = (y, kc', vc') := by
    simp only [layerStep32, hD]
    rfl
  let st' := st |>.set .h1 (.arr h1) |>.set .q (.arr q) |>.set .k (.arr k) |>.set .v (.arr v)
    |>.set (.kc l b') (.arr kc') |>.set (.vc l b') (.arr vc') |>.set .sc (.arr sc)
    |>.set .mx (.arr mx) |>.set .sm (.arr sm) |>.set .pw (.arr pw) |>.set .o (.arr o)
    |>.set .a (.arr a) |>.set .r (.arr r) |>.set .h2 (.arr h2) |>.set .m1 (.arr m1)
    |>.set .g (.arr g) |>.set .m2 (.arr m2) |>.set .x (.arr y)
  refine ⟨st', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [layerItems, List.cons_append, List.nil_append, hD, hb0, hb1']
    rw [Item.execAll_call _ h1 (by simp)
        (by simp [-UInt64.toNat_mul, hx, hg1, hb1, hwidth, hnf, KernelName.apply, hx29, sg1, sb1, hD29]; rfl)
        (by omega),
      Item.execAll_call _ q (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hwq, hbq, hwidth, KernelName.apply, sh1, swq, sbq, hD29]; rfl)
        (by omega),
      Item.execAll_call _ k (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hwk, hbk, hwidth, KernelName.apply, sh1, swk, sbk, hD29]; rfl)
        (by omega),
      Item.execAll_call _ v (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hwv, hbv, hwidth, KernelName.apply, sh1, swv, sbv, hD29]; rfl)
        (by omega),
      Item.execAll_call _ kc' (by simp [-UInt64.toNat_mul, hpar'])
        (by simp [-UInt64.toNat_mul, Store.set, hk, hbase, htopw, KernelName.apply, hks, sk, hT29]; rfl)
        (by rw [zkc, hd]),
      Item.execAll_call _ vc' (by simp [-UInt64.toNat_mul, hpar'])
        (by simp [-UInt64.toNat_mul, Store.set, hv, hbase, htopw, KernelName.apply, hvs, sv, hT29]; rfl)
        (by rw [zvc, hd]),
      Item.execAll_call _ sc (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hpos, hwidth, hscoreLen, KernelName.apply, sq, skc, hN29]; rfl)
        (by omega),
      Item.execAll_call _ mx (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hpos, hheads, KernelName.apply, ssc, hnh29]; rfl)
        (by omega),
      Item.execAll_call _ sm (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hpos, hheads, KernelName.apply, ssc, smx, hnh29]; rfl)
        (by omega),
      Item.execAll_call _ pw (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hpos, hscoreLen, KernelName.apply, ssc, smx, ssm, hN29]; rfl)
        (by omega),
      Item.execAll_call _ o (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hpos, hwidth, KernelName.apply, spw, svc, hD29]; rfl)
        (by omega),
      Item.execAll_call _ a (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hwo, hbo, hwidth, KernelName.apply, so, swo, sbo, hD29]; rfl)
        (by omega),
      Item.execAll_call _ r (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hx, KernelName.apply, hx29, sa]; rfl)
        (by omega),
      Item.execAll_call _ h2 (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hg2, hb2, hwidth, hnf, KernelName.apply, sr, sg2, sb2, hD29]; rfl)
        (by omega),
      Item.execAll_call _ m1 (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hwfc, hbfc, hwidth, hhidden, KernelName.apply, sh2, swfc, sbfc, hf]; rfl)
        (by omega),
      Item.execAll_call _ g (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, KernelName.apply, sm1]; rfl)
        (by omega),
      Item.execAll_call _ m2 (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, hwproj, hbproj, hwidth, hhidden, KernelName.apply, sg, swproj, sbproj,
          hD29]; rfl)
        (by omega),
      Item.execAll_call _ y (by simp)
        (by simp [-UInt64.toNat_mul, Store.set, KernelName.apply, sr, sm2]; rfl)
        (by omega)]
  · simp [st', Store.set, hstep]
  · rw [hstep]
    exact zy
  · simp [st', Store.set, hstep]
  · simp [st', Store.set, hstep]
  · rw [hstep]
    exact skc
  · rw [hstep]
    exact svc
  · intro c hc hk' hv'
    obtain ⟨nx, nh1, nq, nk, nv, nsc, nmx, nsm, npw, no, na, nr, nh2, nm1, ng, nm2⟩ :=
      Buf.ne_of_scratch hc
    dsimp only [st']
    rw [Store.set_ne nx, Store.set_ne nm2, Store.set_ne ng, Store.set_ne nm1, Store.set_ne nh2,
      Store.set_ne nr, Store.set_ne na, Store.set_ne no, Store.set_ne npw, Store.set_ne nsm,
      Store.set_ne nmx, Store.set_ne nsc, Store.set_ne hv', Store.set_ne hk', Store.set_ne nv,
      Store.set_ne nk, Store.set_ne nq, Store.set_ne nh1]

end Project.Gpt32
