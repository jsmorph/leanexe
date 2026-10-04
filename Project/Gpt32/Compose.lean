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

/-- The word constants of a step, which every step writes first. -/
def Buf.isWord : Buf → Bool
  | .pos | .base | .top | .row | .width | .hidden | .heads | .scoreLen | .rowCount | .nf => true
  | _ => false

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

theorem Words.set {s : Shape32} {p : UInt64} {st : Store} (h : Words s p st) {b : Buf}
    (hb : b.isWord = false) (v : Val) : Words s p (st.set b v) := by
  have ne : ∀ c : Buf, c.isWord = true → c ≠ b := fun c hc e => by subst e; simp [hc] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨by rw [Store.set_ne (ne _ rfl)]; exact h1, by rw [Store.set_ne (ne _ rfl)]; exact h2,
    by rw [Store.set_ne (ne _ rfl)]; exact h3, by rw [Store.set_ne (ne _ rfl)]; exact h4,
    by rw [Store.set_ne (ne _ rfl)]; exact h5, by rw [Store.set_ne (ne _ rfl)]; exact h6,
    by rw [Store.set_ne (ne _ rfl)]; exact h7, by rw [Store.set_ne (ne _ rfl)]; exact h8⟩

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

theorem layers32_cons (nh f p : UInt64) (w : Layer32) (ws : List Layer32) (kc vc : Array Float32)
    (cs : List (Array Float32 × Array Float32)) (x : Array Float32) :
    layers32 nh f p (w :: ws) ((kc, vc) :: cs) x =
      ((layers32 nh f p ws cs (layerStep32 nh f p w x kc vc).1).1,
        ((layerStep32 nh f p w x kc vc).2.1, (layerStep32 nh f p w x kc vc).2.2) ::
          (layers32 nh f p ws cs (layerStep32 nh f p w x kc vc).1).2) := rfl

/-- The layers `l0` to `l0 + ws.length - 1` at position `p`. -/
theorem layers_exec (files : String → Option Val) {s : Shape32} {p : UInt64} (hB : Bounds s p) :
    ∀ (ws : List Layer32) (cs : List (Array Float32 × Array Float32)) (l0 : Nat)
      (x : Array Float32) (st : Store) (is : List Item),
      ws.length = cs.length → Words s p st → st .x = some (.arr x) →
      x.size = 64 * s.nh.toNat →
      (∀ i < ws.length, ∀ f : Field, st (.layer (l0 + i) f) = some (.arr (f.get ws[i]!))) →
      (∀ w ∈ ws, ∀ f : Field, Small (f.get w)) →
      (∀ i < cs.length, st (.kc (l0 + i) (p % 2).toNat) = some (.arr cs[i]!.1) ∧
        st (.vc (l0 + i) (p % 2).toNat) = some (.arr cs[i]!.2)) →
      (∀ c ∈ cs, Small c.1 ∧ Small c.2) →
      ∃ st', Item.execAll files st ((List.range' l0 ws.length).flatMap (layerItems s p) ++ is) =
          Item.execAll files st' is ∧
        st' .x = some (.arr (layers32 s.nh s.f p ws cs x).1) ∧
        (layers32 s.nh s.f p ws cs x).1.size = 64 * s.nh.toNat ∧
        (layers32 s.nh s.f p ws cs x).2.length = cs.length ∧
        (∀ i < cs.length,
          st' (.kc (l0 + i) ((p + 1) % 2).toNat) =
            some (.arr (layers32 s.nh s.f p ws cs x).2[i]!.1) ∧
          st' (.vc (l0 + i) ((p + 1) % 2).toNat) =
            some (.arr (layers32 s.nh s.f p ws cs x).2[i]!.2)) ∧
        (∀ c ∈ (layers32 s.nh s.f p ws cs x).2, Small c.1 ∧ Small c.2) ∧
        ∀ c, c.scratch = false →
          (∀ i < cs.length, c ≠ .kc (l0 + i) ((p + 1) % 2).toNat ∧
            c ≠ .vc (l0 + i) ((p + 1) % 2).toNat) → st' c = st c
  | [], cs, l0, x, st, is, hlen, _, hx, hxs, _, _, _, _ => by
    cases cs with
    | cons _ _ => simp at hlen
    | nil =>
      refine ⟨st, by simp, hx, hxs, rfl, by simp, by simp [layers32], fun _ _ _ => rfl⟩
  | w :: ws, cs, l0, x, st, is, hlen, hW, hx, hxs, hw, hws, hc, hcs => by
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      obtain ⟨kc, vc⟩ := c
      have hlen' : ws.length = cs.length := by simpa using hlen
      obtain ⟨hk0, hv0⟩ := hc 0 (by simp)
      simp only [Nat.add_zero, List.getElem!_cons_zero] at hk0 hv0
      obtain ⟨hks, hvs⟩ := hcs (kc, vc) (by simp)
      obtain ⟨st1, he1, hx1, hxs1, hk1, hv1, hks1, hvs1, hf1⟩ :=
        layer_exec files l0 w x kc vc st
          ((List.range' (l0 + 1) ws.length).flatMap (layerItems s p) ++ is) hB hW hx hxs
          (by simpa using hw 0 (by simp)) (hws w (by simp)) hk0 hv0 hks hvs
      have hpar : (p % 2).toNat ≠ ((p + 1) % 2).toNat := by
        rw [UInt64.toNat_mod, UInt64.toNat_mod, hB.p1]
        simp only [UInt64.reduceToNat]
        omega
      have hW1 : Words s p st1 := by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hW
        exact ⟨by rw [hf1 _ rfl (by simp) (by simp)]; exact h1,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h2,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h3,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h4,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h5,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h6,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h7,
          by rw [hf1 _ rfl (by simp) (by simp)]; exact h8⟩
      obtain ⟨st2, he2, hx2, hxs2, hlen2, hc2, hcs2, hf2⟩ :=
        layers_exec files hB ws cs (l0 + 1) _ st1 is hlen' hW1 hx1 hxs1
          (fun i hi f => by
            rw [hf1 _ rfl (by simp) (by simp), show l0 + 1 + i = l0 + (i + 1) by omega]
            simpa using hw (i + 1) (by simp; omega) f)
          (fun w' hw' => hws w' (by simp [hw']))
          (fun i hi => by
            rw [hf1 _ rfl (by simp; omega) (by simp),
              hf1 _ rfl (by simp) (by simp; omega),
              show l0 + 1 + i = l0 + (i + 1) by omega]
            simpa using hc (i + 1) (by simp; omega))
          (fun c hc' => hcs c (by simp [hc']))
      refine ⟨st2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.range'_succ, List.flatMap_cons, List.append_assoc]
        rw [he1, he2]
      · rw [layers32_cons]
        exact hx2
      · rw [layers32_cons]
        exact hxs2
      · rw [layers32_cons]
        simp [hlen2]
      · intro i hi
        rw [layers32_cons]
        cases i with
        | zero =>
          simp only [Nat.add_zero, List.getElem!_cons_zero]
          exact ⟨by rw [hf2 _ rfl (fun j hj => by simp; omega)]; exact hk1,
            by rw [hf2 _ rfl (fun j hj => by simp; omega)]; exact hv1⟩
        | succ i =>
          simp only [List.getElem!_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega]
          exact hc2 i (by simpa using hi)
      · rw [layers32_cons]
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨hks1, hvs1⟩
        · exact hcs2 c hc'
      · intro c hc' hne
        rw [hf2 c hc' (fun i hi => by
          have := hne (i + 1) (by simp; omega)
          rwa [show l0 + (i + 1) = l0 + 1 + i by omega] at this)]
        exact hf1 c hc' (by simpa using (hne 0 (by simp)).1) (by simpa using (hne 0 (by simp)).2)

theorem Item.execAll_word (files : String → Option Val) (st : Store) (b : Buf) (v : UInt64)
    (is : List Item) :
    Item.execAll files st (.word b v :: is) = Item.execAll files (st.set b (.word v)) is := rfl

/-- The scores of chunks `c0` to `c0 + n - 1` of the hidden row `h`. -/
theorem logits_exec (files : String → Option Val) (s : Shape32) (W : Weights32)
    (h : Array Float32) (hh : h.size < 536870912) :
    ∀ (n c0 : Nat) (st : Store), st .hf = some (.arr h) →
      st .width = some (.word (64 * s.nh)) →
      (∀ c, c0 ≤ c → c < c0 + n → st (.wte c) = some (.arr W.wte[c]!) ∧
        W.wte[c]!.size < 536870912 ∧ s.rows[c]!.toNat < 536870912) →
      ∃ st', Item.execAll files st
          ((List.range' c0 n).flatMap fun c => logitsItems c s.rows[c]!) = some st' ∧
        (∀ c, c0 ≤ c → c < c0 + n →
          st' (.z c) = some (.arr (logits32 h W.wte[c]! s.rows[c]! (64 * s.nh)))) ∧
        ∀ b, (∀ c, c0 ≤ c → c < c0 + n → b ≠ .z c) → b ≠ .rowCount → st' b = st b
  | 0, c0, st, _, _, _ => ⟨st, by simp [Item.execAll], fun c h1 h2 => by omega, fun _ _ _ => rfl⟩
  | n + 1, c0, st, hh', hw, hc => by
    obtain ⟨hwte, hs, hr⟩ := hc c0 (le_refl _) (by omega)
    let z := logits32 h W.wte[c0]! s.rows[c0]! (64 * s.nh)
    let st1 := (st.set .rowCount (.word s.rows[c0]!)).set (.z c0) (.arr z)
    obtain ⟨st', he', hz, hf⟩ := logits_exec files s W h hh n (c0 + 1) st1
      (by simp [st1, Store.set, hh']) (by simp [st1, Store.set, hw])
      (fun c h1 h2 => by
        obtain ⟨a, b, c'⟩ := hc c (by omega) (by omega)
        exact ⟨by simpa [st1, Store.set] using a, b, c'⟩)
    refine ⟨st', ?_, ?_, ?_⟩
    · simp only [List.range'_succ, List.flatMap_cons, logitsItems, List.cons_append,
        List.nil_append]
      rw [Item.execAll_word, Item.execAll_call _ z (by simp)
        (by
          simp [Store.set, hh', hw, hwte, KernelName.apply, hh]
          exact ⟨⟨by simpa using hs, by simpa using hr⟩, by simp [z]⟩)
        (by simp [z, logits32_size])]
      exact he'
    · intro c h1 h2
      by_cases hc0 : c = c0
      · subst hc0
        rw [hf _ (fun c' h1 _ => by simp; omega) (by simp)]
        simp [st1, Store.set, z]
      · exact hz c (by omega) (by omega)
    · intro b hb hr'
      rw [hf b (fun c h1 h2 => hb c (by omega) (by omega)) hr']
      simp [st1, Store.set, hb c0 (le_refl _) (by omega), hr']

/-- The sizes a step needs: the shape's layers and chunks, and every weight and cache below
2^29 elements. -/
structure Fits (s : Shape32) (W : Weights32) (caches : List (Array Float32 × Array Float32)) :
    Prop where
  layers : W.layers.length = s.layers
  cacheCount : caches.length = s.layers
  chunks : W.wte.length = s.rows.length
  wte : ∀ c < W.wte.length, Small W.wte[c]!
  rows : ∀ c < s.rows.length, SmallWord s.rows[c]!
  wpe : Small W.wpe
  gf : Small W.gf
  bf : Small W.bf
  weights : ∀ w ∈ W.layers, ∀ f : Field, Small (f.get w)
  small : ∀ c ∈ caches, Small c.1 ∧ Small c.2

/-- The store before the step of position `p`: the weights, and the caches of each layer at the
parity of `p`. -/
structure Holds (W : Weights32) (p : UInt64) (caches : List (Array Float32 × Array Float32))
    (st : Store) : Prop where
  wte : ∀ c < W.wte.length, st (.wte c) = some (.arr W.wte[c]!)
  wpe : st .wpe = some (.arr W.wpe)
  gf : st .gf = some (.arr W.gf)
  bf : st .bf = some (.arr W.bf)
  layer : ∀ l < W.layers.length, ∀ f : Field,
    st (.layer l f) = some (.arr (f.get W.layers[l]!))
  caches : ∀ l < caches.length, st (.kc l (p % 2).toNat) = some (.arr caches[l]!.1) ∧
    st (.vc l (p % 2).toNat) = some (.arr caches[l]!.2)

theorem step32_eq (s : Shape32) (W : Weights32) (token p : UInt64)
    (caches : List (Array Float32 × Array Float32)) :
    step32 s W token p caches =
      let x := embed32 (W.wte.getD (token / s.chunk).toNat #[]) W.wpe (token % s.chunk) p
        (64 * s.nh)
      let y := layers32 s.nh s.f p W.layers caches x
      let h := layerNorm32 y.1 W.gf W.bf (64 * s.nh) (64 * s.nh).toFloat32
      (y.2, (W.wte.zip s.rows).map fun (wte, rows) => logits32 h wte rows (64 * s.nh)) := rfl

/-- The step program of `token` at position `p` computes `step32`: it ends in a store holding
the weights, each layer's caches through `p` at the parity of `p + 1`, and the scores of chunk
`c` in `z c`. -/
theorem step_exec (files : String → Option Val) (s : Shape32) (W : Weights32)
    (token p : UInt64) (caches : List (Array Float32 × Array Float32)) (st : Store)
    (hB : Bounds s p) (hF : Fits s W caches) (hT : (token / s.chunk).toNat < s.rows.length)
    (hH : Holds W p caches st) :
    ∃ st', Item.execAll files st (stepItems s token p) = some st' ∧
      Holds W (p + 1) (step32 s W token p caches).1 st' ∧
      Fits s W (step32 s W token p caches).1 ∧
      (step32 s W token p caches).2.length = s.rows.length ∧
      ∀ c < s.rows.length, st' (.z c) = some (.arr (step32 s W token p caches).2[c]!) := by
  have hd := hB.d
  have hnh := hB.nh
  have hD29 : (64 * s.nh).toNat < 536870912 := by omega
  have hc0 : (token / s.chunk).toNat < W.wte.length := by rw [hF.chunks]; exact hT
  let st9 := st |>.set .pos (.word p) |>.set .base (.word (p * (64 * s.nh))) |>.set .top
    (.word ((p + 1) * (64 * s.nh))) |>.set .row (.word (token % s.chunk))
    |>.set .width (.word (64 * s.nh)) |>.set .hidden (.word s.f) |>.set .heads (.word s.nh)
    |>.set .scoreLen (.word (s.nh * 1024)) |>.set .nf (.float (64 * s.nh).toFloat32)
  have h9 : ∀ b, b.isWord = false → st9 b = st b := by
    intro b hb
    cases b <;> simp_all [st9, Store.set, Buf.isWord]
  have hw9 : ∀ rest, Item.execAll files st (wordItems s token p ++ rest) =
      Item.execAll files st9 rest := fun _ => rfl
  have hW9 : Words s p st9 := ⟨by simp [st9, Store.set], by simp [st9, Store.set],
    by simp [st9, Store.set], by simp [st9, Store.set], by simp [st9, Store.set],
    by simp [st9, Store.set], by simp [st9, Store.set], by simp [st9, Store.set]⟩
  let x0 := embed32 W.wte[(token / s.chunk).toNat]! W.wpe (token % s.chunk) p (64 * s.nh)
  let st10 := st9.set .x (.arr x0)
  have hW10 : Words s p st10 := hW9.set rfl _
  have swte0 := hF.wte _ hc0
  have swpe := hF.wpe
  simp only [Small] at swte0 swpe
  obtain ⟨st11, he11, hx11, hxs11, hlen11, hc11, hcs11, hf11⟩ :=
    layers_exec files hB W.layers caches 0 x0 st10
      ([.call .layerNorm (64 * s.nh).toNat .hf [.x, .gf, .bf, .width, .nf]] ++
        (List.range' 0 s.rows.length).flatMap fun c => logitsItems c s.rows[c]!)
      (by rw [hF.layers, hF.cacheCount]) hW10 (by simp [st10, Store.set])
      (by simp only [x0, embed32_size, hd])
      (fun i hi f => by
        rw [Nat.zero_add]
        dsimp only [st10]
        rw [Store.set_ne (by simp), h9 _ rfl]
        exact hH.layer i hi f)
      hF.weights
      (fun i hi => by
        rw [Nat.zero_add]
        dsimp only [st10]
        rw [Store.set_ne (by simp), h9 _ rfl, Store.set_ne (by simp), h9 _ rfl]
        exact hH.caches i hi)
      hF.small
  let y := (layers32 s.nh s.f p W.layers caches x0).1
  let hv := layerNorm32 y W.gf W.bf (64 * s.nh) (64 * s.nh).toFloat32
  have hfr : ∀ b, b.scratch = false → b.isWord = false →
      (∀ l, b ≠ .kc l ((p + 1) % 2).toNat ∧ b ≠ .vc l ((p + 1) % 2).toNat) → st11 b = st b := by
    intro b hs hw hkv
    rw [hf11 b hs (fun i _ => hkv (0 + i))]
    dsimp only [st10]
    rw [Store.set_ne (fun e => by subst e; simp [Buf.scratch] at hs), h9 b hw]
  have hW11 : Words s p st11 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hW10
    exact ⟨by rw [hf11 _ rfl (by simp)]; exact h1, by rw [hf11 _ rfl (by simp)]; exact h2,
      by rw [hf11 _ rfl (by simp)]; exact h3, by rw [hf11 _ rfl (by simp)]; exact h4,
      by rw [hf11 _ rfl (by simp)]; exact h5, by rw [hf11 _ rfl (by simp)]; exact h6,
      by rw [hf11 _ rfl (by simp)]; exact h7, by rw [hf11 _ rfl (by simp)]; exact h8⟩
  have sgf := hF.gf
  have sbf := hF.bf
  simp only [Small] at sgf sbf
  have hy : (layers32 s.nh s.f p W.layers caches x0).1.size < 536870912 := by omega
  let st12 := st11.set .hf (.arr hv)
  have hvs : hv.size < 536870912 := by simp only [hv, layerNorm32_size]; omega
  obtain ⟨st', he', hz', hf'⟩ := logits_exec files s W hv hvs s.rows.length 0 st12
    (by simp [st12, Store.set]) (by simp [st12, Store.set, hW11.width])
    (fun c _ hc => by
      have hcw : c < W.wte.length := by rw [hF.chunks]; omega
      refine ⟨?_, by simpa [Small] using hF.wte c hcw, by simpa [SmallWord] using hF.rows c (by omega)⟩
      dsimp only [st12]
      rw [Store.set_ne (by simp), hfr _ rfl rfl (fun l => by simp)]
      exact hH.wte c hcw)
  have hstep : step32 s W token p caches =
      ((layers32 s.nh s.f p W.layers caches x0).2,
        (W.wte.zip s.rows).map fun (wte, rows) => logits32 hv wte rows (64 * s.nh)) := by
    rw [step32_eq]
    simp only [x0, hv, y, List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hc0, Option.getD_some]
  refine ⟨st', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stepItems, List.append_assoc, List.range_eq_range', ← hF.layers]
    rw [hw9, List.singleton_append]
    rw [Item.execAll_call _ x0 (by simp)
      (by
        simp [-UInt64.toNat_div, st9, Store.set, hH.wte _ hc0, hH.wpe, KernelName.apply]
        exact ⟨⟨by simpa using swte0, by simpa using swpe, by omega⟩, by simp [x0]⟩)
      (by simp only [x0, embed32_size])]
    rw [he11, List.singleton_append, Item.execAll_call _ hv (by simp)
      (by
        simp [hx11, hfr .gf rfl rfl (fun l => by simp), hfr .bf rfl rfl (fun l => by simp),
          hH.gf, hH.bf, hW11.width, hW11.nf, KernelName.apply, hy]
        exact ⟨⟨by simpa using sgf, by simpa using sbf, by omega⟩, rfl⟩)
      (by simp only [hv, layerNorm32_size])]
    exact he'
  · rw [hstep]
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_, fun l hl => ?_⟩
    · rw [hf' _ (fun _ _ _ => by simp) (by simp)]
      dsimp only [st12]
      rw [Store.set_ne (by simp), hfr _ rfl rfl (fun l => by simp)]
      exact hH.wte c hc
    · rw [hf' _ (fun _ _ _ => by simp) (by simp)]
      dsimp only [st12]
      rw [Store.set_ne (by simp), hfr _ rfl rfl (fun l => by simp)]
      exact hH.wpe
    · rw [hf' _ (fun _ _ _ => by simp) (by simp)]
      dsimp only [st12]
      rw [Store.set_ne (by simp), hfr _ rfl rfl (fun l => by simp)]
      exact hH.gf
    · rw [hf' _ (fun _ _ _ => by simp) (by simp)]
      dsimp only [st12]
      rw [Store.set_ne (by simp), hfr _ rfl rfl (fun l => by simp)]
      exact hH.bf
    · intro l hl f
      rw [hf' _ (fun _ _ _ => by simp) (by simp)]
      dsimp only [st12]
      rw [Store.set_ne (by simp), hfr _ rfl rfl (fun l => by simp)]
      exact hH.layer l hl f
    · have hl' : l < caches.length := by rw [← hlen11]; exact hl
      obtain ⟨hk, hv'⟩ := hc11 l hl'
      rw [Nat.zero_add] at hk hv'
      refine ⟨?_, ?_⟩
      · rw [hf' _ (fun _ _ _ => by simp) (by simp)]
        dsimp only [st12]
        rw [Store.set_ne (by simp)]
        exact hk
      · rw [hf' _ (fun _ _ _ => by simp) (by simp)]
        dsimp only [st12]
        rw [Store.set_ne (by simp)]
        exact hv'
  · rw [hstep]
    exact { hF with cacheCount := by rw [hlen11, hF.cacheCount], small := hcs11 }
  · rw [hstep]
    simp [hF.chunks]
  · intro c hc
    rw [hz' c (by omega) (by omega), hstep]
    have hcw : c < W.wte.length := by rw [hF.chunks]; exact hc
    simp [hcw, hc]

/-! ### Setup and sequences of steps -/

theorem Item.execAll_load {files : String → Option Val} {st : Store} {b : Buf} {path : String}
    {v : Val} (h : files path = some v) (is : List Item) :
    Item.execAll files st (.load b path :: is) = Item.execAll files (st.set b v) is := by
  simp [Item.execAll, Item.exec, h]

theorem Item.execAll_empty (files : String → Option Val) (st : Store) (b : Buf)
    (is : List Item) :
    Item.execAll files st (.empty b :: is) = Item.execAll files (st.set b (.arr #[])) is := rfl

theorem Item.execAll_append (files : String → Option Val) :
    ∀ (st : Store) (is js : List Item),
      Item.execAll files st (is ++ js) = (Item.execAll files st is).bind fun st' =>
        Item.execAll files st' js
  | st, [], js => rfl
  | st, i :: is, js => by
    simp only [List.cons_append, Item.execAll]
    cases i.exec files st with
    | none => rfl
    | some st' => exact Item.execAll_append files st' is js

/-- The files of `dir` hold the weights `W`. -/
structure Loaded (files : String → Option Val) (dir : String) (W : Weights32) : Prop where
  wte : ∀ c < W.wte.length, files (weightPath dir s!"wte{c}") = some (.arr W.wte[c]!)
  wpe : files (weightPath dir "wpe") = some (.arr W.wpe)
  gf : files (weightPath dir "gf") = some (.arr W.gf)
  bf : files (weightPath dir "bf") = some (.arr W.bf)
  layer : ∀ l < W.layers.length, ∀ f : Field,
    files (weightPath dir s!"l{l}_{f.name}") = some (.arr (f.get W.layers[l]!))

theorem wte_setup (files : String → Option Val) (dir : String) (W : Weights32) :
    ∀ (n c0 : Nat) (st : Store) (is : List Item),
      (∀ c, c0 ≤ c → c < c0 + n → files (weightPath dir s!"wte{c}") = some (.arr W.wte[c]!)) →
      ∃ st', Item.execAll files st (((List.range' c0 n).map fun c =>
          Item.load (.wte c) (weightPath dir s!"wte{c}")) ++ is) = Item.execAll files st' is ∧
        (∀ c, c0 ≤ c → c < c0 + n → st' (.wte c) = some (.arr W.wte[c]!)) ∧
        ∀ b, (∀ c, c0 ≤ c → c < c0 + n → b ≠ .wte c) → st' b = st b
  | 0, c0, st, is, _ => ⟨st, by simp, fun c h1 h2 => by omega, fun _ _ => rfl⟩
  | n + 1, c0, st, is, h => by
    obtain ⟨st', he, hw, hf⟩ := wte_setup files dir W n (c0 + 1)
      (st.set (.wte c0) (.arr W.wte[c0]!)) is (fun c h1 h2 => h c (by omega) (by omega))
    refine ⟨st', ?_, ?_, ?_⟩
    · simp only [List.range'_succ, List.map_cons, List.cons_append]
      rw [Item.execAll_load (h c0 (le_refl _) (by omega)), he]
    · intro c h1 h2
      by_cases hc : c = c0
      · subst hc
        rw [hf _ (fun c' h1' _ => by simp; omega)]
        simp [Store.set]
      · exact hw c (by omega) (by omega)
    · intro b hb
      rw [hf b (fun c h1 h2 => hb c (by omega) (by omega)),
        Store.set_ne (hb c0 (le_refl _) (by omega))]

theorem layer_setup (files : String → Option Val) (dir : String) (l : Nat) (w : Layer32)
    (st : Store) (is : List Item)
    (h : ∀ f : Field, files (weightPath dir s!"l{l}_{f.name}") = some (.arr (f.get w))) :
    ∃ st', Item.execAll files st (layerSetup dir l ++ is) = Item.execAll files st' is ∧
      (∀ f : Field, st' (.layer l f) = some (.arr (f.get w))) ∧
      st' (.kc l 0) = some (.arr #[]) ∧ st' (.vc l 0) = some (.arr #[]) ∧
      ∀ b, (∀ f, b ≠ .layer l f) → b ≠ .kc l 0 → b ≠ .vc l 0 → st' b = st b := by
  let L := Buf.layer l
  let st' := st |>.set (L .g1) (.arr (Field.get w .g1)) |>.set (L .b1) (.arr (Field.get w .b1))
    |>.set (L .wq) (.arr (Field.get w .wq)) |>.set (L .bq) (.arr (Field.get w .bq))
    |>.set (L .wk) (.arr (Field.get w .wk)) |>.set (L .bk) (.arr (Field.get w .bk))
    |>.set (L .wv) (.arr (Field.get w .wv)) |>.set (L .bv) (.arr (Field.get w .bv))
    |>.set (L .wo) (.arr (Field.get w .wo)) |>.set (L .bo) (.arr (Field.get w .bo))
    |>.set (L .g2) (.arr (Field.get w .g2)) |>.set (L .b2) (.arr (Field.get w .b2))
    |>.set (L .wfc) (.arr (Field.get w .wfc)) |>.set (L .bfc) (.arr (Field.get w .bfc))
    |>.set (L .wproj) (.arr (Field.get w .wproj)) |>.set (L .bproj) (.arr (Field.get w .bproj))
    |>.set (.kc l 0) (.arr #[]) |>.set (.vc l 0) (.arr #[])
  refine ⟨st', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [layerSetup, Field.all, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append]
    rw [Item.execAll_load (h .g1), Item.execAll_load (h .b1), Item.execAll_load (h .wq),
      Item.execAll_load (h .bq), Item.execAll_load (h .wk), Item.execAll_load (h .bk),
      Item.execAll_load (h .wv), Item.execAll_load (h .bv), Item.execAll_load (h .wo),
      Item.execAll_load (h .bo), Item.execAll_load (h .g2), Item.execAll_load (h .b2),
      Item.execAll_load (h .wfc), Item.execAll_load (h .bfc), Item.execAll_load (h .wproj),
      Item.execAll_load (h .bproj), Item.execAll_empty, Item.execAll_empty]
  · intro f
    cases f <;> simp [st', L, Store.set]
  · simp [st', Store.set]
  · simp [st', Store.set]
  · intro b hl hk hv
    dsimp only [st']
    rw [Store.set_ne hv, Store.set_ne hk, Store.set_ne (hl _), Store.set_ne (hl _),
      Store.set_ne (hl _), Store.set_ne (hl _), Store.set_ne (hl _), Store.set_ne (hl _),
      Store.set_ne (hl _), Store.set_ne (hl _), Store.set_ne (hl _), Store.set_ne (hl _),
      Store.set_ne (hl _), Store.set_ne (hl _), Store.set_ne (hl _), Store.set_ne (hl _),
      Store.set_ne (hl _), Store.set_ne (hl _)]

theorem layers_setup (files : String → Option Val) (dir : String) (ws : List Layer32) :
    ∀ (n l0 : Nat) (st : Store) (is : List Item),
      (∀ l, l0 ≤ l → l < l0 + n → ∀ f : Field,
        files (weightPath dir s!"l{l}_{f.name}") = some (.arr (f.get ws[l]!))) →
      ∃ st', Item.execAll files st ((List.range' l0 n).flatMap (layerSetup dir) ++ is) =
          Item.execAll files st' is ∧
        (∀ l, l0 ≤ l → l < l0 + n → (∀ f : Field, st' (.layer l f) = some (.arr (f.get ws[l]!))) ∧
          st' (.kc l 0) = some (.arr #[]) ∧ st' (.vc l 0) = some (.arr #[])) ∧
        ∀ b, (∀ l, l0 ≤ l → l < l0 + n → (∀ f, b ≠ .layer l f) ∧ b ≠ .kc l 0 ∧ b ≠ .vc l 0) →
          st' b = st b
  | 0, l0, st, is, _ => ⟨st, by simp, fun l h1 h2 => by omega, fun _ _ => rfl⟩
  | n + 1, l0, st, is, h => by
    obtain ⟨st1, he1, hw1, hk1, hv1, hf1⟩ := layer_setup files dir l0 ws[l0]! st
      ((List.range' (l0 + 1) n).flatMap (layerSetup dir) ++ is) (h l0 (le_refl _) (by omega))
    obtain ⟨st', he, hw, hf⟩ := layers_setup files dir ws n (l0 + 1) st1 is
      (fun l h1 h2 => h l (by omega) (by omega))
    refine ⟨st', ?_, ?_, ?_⟩
    · simp only [List.range'_succ, List.flatMap_cons, List.append_assoc]
      rw [he1, he]
    · intro l h1 h2
      by_cases hl : l = l0
      · subst hl
        have hs : ∀ b : Buf, (∀ l', l + 1 ≤ l' → l' < l + 1 + n →
            (∀ f, b ≠ .layer l' f) ∧ b ≠ .kc l' 0 ∧ b ≠ .vc l' 0) →
            st' b = st1 b := hf
        refine ⟨fun f => ?_, ?_, ?_⟩
        · rw [hs _ (fun l' h1' _ => ⟨fun f' e => by cases e; omega, by simp, by simp⟩)]
          exact hw1 f
        · rw [hs _ (fun l' h1' _ => ⟨by simp, fun e => by cases e; omega, by simp⟩)]
          exact hk1
        · rw [hs _ (fun l' h1' _ => ⟨by simp, by simp, fun e => by cases e; omega⟩)]
          exact hv1
      · exact hw l (by omega) (by omega)
    · intro b hb
      rw [hf b (fun l h1 h2 => hb l (by omega) (by omega))]
      obtain ⟨h1, h2, h3⟩ := hb l0 (le_refl _) (by omega)
      exact hf1 b h1 h2 h3

/-- The setup program loads the weights and makes the empty caches of position 0. -/
theorem setup_exec (files : String → Option Val) (dir : String) (s : Shape32) (W : Weights32)
    (st : Store) (hL : Loaded files dir W) (hlay : W.layers.length = s.layers)
    (hch : W.wte.length = s.rows.length) :
    ∃ st', Item.execAll files st (setupItems s dir) = some st' ∧
      Holds W 0 (List.replicate s.layers (#[], #[])) st' := by
  obtain ⟨st1, he1, hw1, hf1⟩ := wte_setup files dir W s.rows.length 0 st
    ([.load .wpe (weightPath dir "wpe"), .load .gf (weightPath dir "gf"),
      .load .bf (weightPath dir "bf")] ++ (List.range' 0 s.layers).flatMap (layerSetup dir))
    (fun c _ hc => hL.wte c (by omega))
  let st2 := st1 |>.set .wpe (.arr W.wpe) |>.set .gf (.arr W.gf) |>.set .bf (.arr W.bf)
  obtain ⟨st3, he3, hw3, hf3⟩ := layers_setup files dir W.layers s.layers 0 st2 []
    (fun l _ hl => hL.layer l (by omega))
  refine ⟨st3, ?_, ⟨fun c hc => ?_, ?_, ?_, ?_, fun l hl f => ?_, fun l hl => ?_⟩⟩
  · simp only [setupItems, List.append_assoc, List.range_eq_range']
    rw [he1, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Item.execAll_load hL.wpe, Item.execAll_load hL.gf, Item.execAll_load hL.bf,
      ← List.append_nil ((List.range' 0 s.layers).flatMap (layerSetup dir)), he3]
    rfl
  · rw [hf3 _ (fun l _ _ => ⟨fun f => by simp, by simp, by simp⟩)]
    dsimp only [st2]
    rw [Store.set_ne (by simp), Store.set_ne (by simp), Store.set_ne (by simp)]
    exact hw1 c (by omega) (by omega)
  · rw [hf3 _ (fun l _ _ => ⟨fun f => by simp, by simp, by simp⟩)]
    simp [st2, Store.set]
  · rw [hf3 _ (fun l _ _ => ⟨fun f => by simp, by simp, by simp⟩)]
    simp [st2, Store.set]
  · rw [hf3 _ (fun l _ _ => ⟨fun f => by simp, by simp, by simp⟩)]
    simp [st2, Store.set]
  · exact (hw3 l (by omega) (by omega)).1 f
  · simp only [List.length_replicate] at hl
    obtain ⟨-, hk, hv⟩ := hw3 l (by omega) (by omega)
    simp [hk, hv, hl]

/-- The caches after the tokens `ts` at positions `p`, `p + 1`, and so on. -/
def cachesAfter (s : Shape32) (W : Weights32) :
    List UInt64 → Nat → List (Array Float32 × Array Float32) →
      List (Array Float32 × Array Float32)
  | [], _, cs => cs
  | t :: ts, p, cs => cachesAfter s W ts (p + 1) (step32 s W t (UInt64.ofNat p) cs).1

theorem ofNat_succ {p : Nat} : UInt64.ofNat p + 1 = UInt64.ofNat (p + 1) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The steps of `ts` from position `p` carry a store holding the weights and the caches of
positions below `p` to one holding the caches after `ts`. -/
theorem steps_exec (files : String → Option Val) (s : Shape32) (W : Weights32)
    (hnh : s.nh.toNat ≤ 64) (hf : s.f.toNat < 2 ^ 29) :
    ∀ (ts : List UInt64) (p : Nat) (cs : List (Array Float32 × Array Float32)) (st : Store),
      p + ts.length ≤ 1024 → (∀ t ∈ ts, (t / s.chunk).toNat < s.rows.length) →
      Fits s W cs → Holds W (UInt64.ofNat p) cs st →
      ∃ st', Item.execAll files st (stepsItems s ts p) = some st' ∧
        Holds W (UInt64.ofNat (p + ts.length)) (cachesAfter s W ts p cs) st' ∧
        Fits s W (cachesAfter s W ts p cs)
  | [], p, cs, st, _, _, hF, hH => ⟨st, rfl, by simpa [cachesAfter] using hH, hF⟩
  | t :: ts, p, cs, st, hp, hts, hF, hH => by
    have hB : Bounds s (UInt64.ofNat p) := ⟨hnh, hf, by simp at hp ⊢; omega⟩
    obtain ⟨st1, he1, hH1, hF1, -⟩ :=
      step_exec files s W t (UInt64.ofNat p) cs st hB hF (hts t (by simp)) hH
    rw [ofNat_succ] at hH1
    obtain ⟨st', he, hH', hF'⟩ := steps_exec files s W hnh hf ts (p + 1) _ st1
      (by simp at hp; omega) (fun t' ht' => hts t' (by simp [ht'])) hF1 hH1
    refine ⟨st', ?_, ?_, hF'⟩
    · simp only [stepsItems]
      rw [Item.execAll_append, he1, Option.bind_some, he]
    · simpa [cachesAfter, Nat.add_assoc, Nat.add_comm 1] using hH'

/-- After the setup and the steps of `ts`, the step of `t` at position `ts.length` leaves the
scores of `step32` in the buffers `z c`, as words on the host, and every dispatch of the
commands is race-free. -/
theorem generate_host (files : String → Option Val) (dir : String) (s : Shape32)
    (W : Weights32) (ts : List UInt64) (t : UInt64) (st : Store)
    (hnh : s.nh.toNat ≤ 64) (hf : s.f.toNat < 2 ^ 29) (hlen : ts.length < 1024)
    (hts : ∀ t' ∈ t :: ts, (t' / s.chunk).toNat < s.rows.length)
    (hL : Loaded files dir W) (hF : Fits s W (List.replicate s.layers (#[], #[]))) :
    let cmds := Item.allCmds (setupItems s dir ++ stepsItems s ts 0 ++
      stepItems s t (UInt64.ofNat ts.length))
    let scores := (step32 s W t (UInt64.ofNat ts.length)
      (cachesAfter s W ts 0 (List.replicate s.layers (#[], #[])))).2
    ∃ st' : Store, Cmd.execAll (hostFiles files) st.host cmds = some st'.host ∧
      Cmd.AllRaceFree (hostFiles files) st.host cmds ∧
      scores.length = s.rows.length ∧
      ∀ c < s.rows.length, st'.host (.z c) = some (Val.arr scores[c]!).buffer := by
  intro cmds scores
  obtain ⟨st1, he1, hH1⟩ := setup_exec files dir s W st hL hF.layers hF.chunks
  obtain ⟨st2, he2, hH2, hF2⟩ := steps_exec files s W hnh hf ts 0 _ st1 (by omega)
    (fun t' ht' => hts t' (by simp [ht'])) hF hH1
  have hB : Bounds s (UInt64.ofNat ts.length) := ⟨hnh, hf, by simp; omega⟩
  obtain ⟨st3, he3, -, -, hlen3, hz3⟩ := step_exec files s W t _ _ st2 hB hF2
    (hts t (by simp)) (by simpa using hH2)
  have he : Item.execAll files st (setupItems s dir ++ stepsItems s ts 0 ++
      stepItems s t (UInt64.ofNat ts.length)) = some st3 := by
    rw [Item.execAll_append, Item.execAll_append, he1, Option.bind_some, he2, Option.bind_some,
      he3]
  obtain ⟨hc, hr⟩ := Item.execAll_sim files _ st st3 he
  exact ⟨st3, hc, hr, hlen3, fun c hc' => by simp [Store.host, hz3 c hc', scores]⟩

end Project.Gpt32
