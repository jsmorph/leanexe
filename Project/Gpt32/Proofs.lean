import Project.Gpt32.Kernels
import Project.Gpt32.Specs

/-!
The element lemmas and dispatch theorems of the binary32 GPT-2 kernels of
`Project/Gpt32/Specs.lean`.  `dotLoop_denote` gives the denotation of the compiler's loop that
accumulates products, which four kernels share.
-/

namespace Project.Gpt32

open Project.IR Project.WGSL Project.ProofKit Project.Pipeline LeanExe.Examples.Gpt32

/-- The loop body that adds the product of `A` and `B` to local `acc` through local `tmp`. -/
def dotBody (acc tmp : Nat) (A B : Project.IR.Expr .f32) : Project.IR.Stmt :=
  .seq (.assign tmp (.binF32 .add (.getF32 acc) (.binF32 .mul A B))) (.assign acc (.getF32 tmp))

/-- The loop that accumulates products: `LeanExe.loop n s0 (fun j s => s + fa j * fb j)` in
local `acc`, when `A` and `B` give `fa j` and `fb j` at index `j`. -/
theorem dotLoop_denote {arrays : Nat → Option (Array UInt64)} {L : Nat → Option Wasm.Value}
    {acc tmp limit idx : Nat} {count : Project.IR.Expr .u64} {A B : Project.IR.Expr .f32}
    {n : UInt64} (s0 : Float32) (fa fb : UInt64 → Float32)
    (hdis : [limit, idx, tmp, acc].Nodup)
    (harr : arrays limit = none ∧ arrays idx = none ∧ arrays tmp = none ∧ arrays acc = none)
    (hcount : count.denote L arrays = some n) (hinit : L acc = some (.f32 s0.toBits))
    (hAB : ∀ (k : Nat) (Lc : Nat → Option Wasm.Value), k < n.toNat →
      (∀ j, j ∉ [limit, idx, tmp, acc] → Lc j = L j) → Lc idx = some (.i64 (UInt64.ofNat k)) →
      A.denote Lc arrays = some (fa (UInt64.ofNat k)).toBits ∧
      B.denote Lc arrays = some (fb (UInt64.ofNat k)).toBits) :
    ∃ L', (Stmt.loop limit idx count (dotBody acc tmp A B)).denote arrays L = some L' ∧
      L' acc = some (.f32 (LeanExe.loop n s0 (fun j s => s + fa j * fb j)).toBits) ∧
      ∀ j, j ∉ [limit, idx, tmp, acc] → L' j = L j := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hdis
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hdis
  have hBody : ∀ (k : Nat) (s : Float32) (Lc : Nat → Option Wasm.Value), k < n.toNat →
      (∀ j, j ∉ limit :: idx :: (dotBody acc tmp A B).writes → Lc j = L j) →
      Lc idx = some (.i64 (UInt64.ofNat k)) → Lc limit = some (.i64 n) →
      LocalsHold Lc [acc] (Scalar.values s) →
      ∃ L2, (dotBody acc tmp A B).denote arrays Lc = some L2 ∧
        LocalsHold L2 [acc] (Scalar.values (s + fa (UInt64.ofNat k) * fb (UInt64.ofNat k))) := by
    intro k s Lc hk hframe hidx _ hhold
    have hacc : Lc acc = some (.f32 s.toBits) := by simpa [LocalsHold, Scalar.values] using hhold
    obtain ⟨ha, hb⟩ := hAB k Lc hk
      (fun j hj => hframe j (by simpa [dotBody, Stmt.writes] using hj)) hidx
    have s1 := denote_assign_f32 (L := Lc) (j := tmp)
      (e := .binF32 .add (.getF32 acc) (.binF32 .mul A B))
      (v := (s + fa (UInt64.ofNat k) * fb (UInt64.ofNat k)).toBits) harr.2.2.1 (by
        simp [Project.IR.Expr.denote, hacc, ha, hb, F32Op.apply, F32Bits.toBits_add,
          F32Bits.toBits_mul])
    have s2 := denote_assign_f32 (arrays := arrays) (j := acc) (e := .getF32 tmp)
      (v := (s + fa (UInt64.ofNat k) * fb (UInt64.ofNat k)).toBits) harr.2.2.2
      (L := fun i => if i = tmp then
        some (.f32 (s + fa (UInt64.ofNat k) * fb (UInt64.ofNat k)).toBits) else Lc i)
      (by simp [Project.IR.Expr.denote])
    exact ⟨_, by rw [dotBody, denote_seq_some s1]; exact s2, by simp [LocalsHold, Scalar.values]⟩
  obtain ⟨L', hL', hHold⟩ := Stmt.denote_loop (vars := [acc]) (init := s0) (L := L)
    (body := dotBody acc tmp A B) (fun j s => s + fa j * fb j) h1 ⟨harr.1, harr.2.1⟩
    (by simp [dotBody, Stmt.writes]; omega) (by simp; omega) hcount
    (by simp [LocalsHold, Scalar.values, hinit]) hBody
  refine ⟨L', hL', by simpa [LocalsHold, Scalar.values] using hHold, fun j hj => ?_⟩
  apply Stmt.denote_frame arrays _ L L' hL' j
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [Stmt.loop, Stmt.writes, dotBody, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]

theorem zero_bits : (0.0 : Float32).toBits = 0 := by decide +kernel

/-! ### `linear32` -/

def linearSpec : Spec :=
  { kinds := [.array, .array, .array, .word, .word], index := 7, count := .param 4,
    vars := [(8, .f32), (9, .u64), (10, .u64), (11, .f32)], width := 12,
    body := .seq (.assign 8 (.constF32 0)) (Stmt.loop 9 10 (.get 3)
      (dotBody 8 11 (.ofBits32 (.read 0 (.get 10)))
        (.ofBits32 (.read 1 (.bin .add (.bin .mul (.get 10) (.get 4)) (.get 7)))))),
    element := .toBits32 (.binF32 .add (.getF32 8) (.ofBits32 (.read 2 (.get 7)))) }

theorem linearSpec_eq : specOf gpt32.linear32.ir [.array, .array, .array, .word, .word] =
    some linearSpec := rfl

theorem linearSpec_wf : linearSpec.WF := linearSpec.wf_of_wfb (by decide)

theorem linearSpec_module : linearSpec.module = some linearKernel := by
  rw [linearKernel, kernelOf, linearSpec_eq]
  rfl

theorem arrays_none (args : List Arg) (j : Nat) (h : args.length ≤ j) : Spec.arrays args j = none := by
  simp [Spec.arrays, List.getElem?_eq_none h]

/-- Element `c` of `linear32 x w b k m`. -/
def linearAt (x w b : Array Float32) (k m c : UInt64) : Float32 :=
  LeanExe.loop k 0.0 (fun i acc => acc + x[i.toNat]! * w[(i * m + c).toNat]!) + b[c.toNat]!

theorem linear_element (x w b : Array Float32) (k m c : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h3 : L 3 = some (.i64 k)) (h4 : L 4 = some (.i64 m))
    (h7 : L 7 = some (.i64 c)) (h0 : arrays 0 = some (floatWords x))
    (h1 : arrays 1 = some (floatWords w)) (h2 : arrays 2 = some (floatWords b))
    (hn : ∀ j, 8 ≤ j → j ≤ 11 → arrays j = none) :
    ∃ L', linearSpec.body.denote arrays L = some L' ∧
      linearSpec.element.denote L' arrays = some (linearAt x w b k m c).toBits.toUInt64 := by
  let L1 : Nat → Option Wasm.Value := fun i => if i = 8 then some (.f32 0) else L i
  have s0 : (Project.IR.Stmt.assign 8 (.constF32 0)).denote arrays L = some L1 :=
    denote_assign_f32 (hn 8 (by omega) (by omega)) rfl
  obtain ⟨L', hL', hacc, hframe⟩ := dotLoop_denote (L := L1) (acc := 8) (tmp := 11) (limit := 9)
    (idx := 10) (count := .get 3) (n := k) (A := .ofBits32 (.read 0 (.get 10)))
    (B := .ofBits32 (.read 1 (.bin .add (.bin .mul (.get 10) (.get 4)) (.get 7))))
    0.0 (fun i => x[i.toNat]!)
    (fun i => w[(i * m + c).toNat]!) (by decide)
    ⟨hn 9 (by omega) (by omega), hn 10 (by omega) (by omega), hn 11 (by omega) (by omega),
      hn 8 (by omega) (by omega)⟩
    (by simp [Project.IR.Expr.denote, L1, h3]) (by simp [L1, zero_bits])
    (fun k' Lc _ hf hidx => by
      have hl4 : Lc 4 = some (.i64 m) := (hf 4 (by decide)).trans (by simp [L1, h4])
      have hl7 : Lc 7 = some (.i64 c) := (hf 7 (by decide)).trans (by simp [L1, h7])
      constructor
      · simp [Project.IR.Expr.denote, hidx, h0, floatWords, getElem!_map_toBits32]
      · simp [Project.IR.Expr.denote, hidx, hl4, hl7, h1, floatWords, getElem!_map_toBits32,
          U64Op.apply])
  refine ⟨L', ?_, ?_⟩
  · show (Project.IR.Stmt.seq _ _).denote arrays L = some L'
    rw [denote_seq_some s0]
    exact hL'
  · have hl7 : L' 7 = some (.i64 c) := (hframe 7 (by decide)).trans (by simp [L1, h7])
    simp [linearSpec, Project.IR.Expr.denote, hacc, hl7, h2, floatWords, getElem!_map_toBits32,
      F32Op.apply, linearAt, F32Bits.toBits_add]

/-- The kernel computes `linear32 x w b k m`: with buffers holding the arguments, an output of the
result's size whose length word the host has written, and at least `m` invocations, the output
ends holding the result as a Wasm array, and distinct invocations store to distinct words. -/
theorem linearKernel_dispatch (x w b : Array Float32) (k m : UInt64) (hx : x.size < 2 ^ 29)
    (hw : w.size < 2 ^ 29) (hb : b.size < 2 ^ 29) (hm : m.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * m.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat m.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : m.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    linearKernel.dispatch [(Arg.array (floatWords x)).buffer, (Arg.array (floatWords w)).buffer,
        (Arg.array (floatWords b)).buffer, (Arg.word k).buffer, (Arg.word m).buffer] output count =
        some (arrayWords (floatWords (linear32 x w b k m))) ∧
      linearKernel.RaceFree [(Arg.array (floatWords x)).buffer, (Arg.array (floatWords w)).buffer,
        (Arg.array (floatWords b)).buffer, (Arg.word k).buffer, (Arg.word m).buffer] output.size
        count := by
  have hfits : linearSpec.Fits [.array (floatWords x), .array (floatWords w),
      .array (floatWords b), .word k, .word m] m.toNat :=
    ⟨rfl, by simp; omega, by simp [linearSpec], hm⟩
  have h := linearSpec.dispatch_eq linearSpec_wf linearKernel linearSpec_module _ _ hfits
    (fun c => (linearAt x w b k m c).toBits.toUInt64)
    (fun c _ => linear_element x w b k m _ _ _ (by simp [Spec.locals, linearSpec, Count.sizeLocal?])
      (by simp [Spec.locals, linearSpec, Count.sizeLocal?]) (by simp [Spec.locals, linearSpec])
      (by simp [Spec.arrays]) (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (linear32 x w b k m) = LeanExe.build m
    (fun c => (linearAt x w b k m c).toBits.toUInt64) by
      simp [linear32, linearAt, floatWords, Project.IR.build_map]]
  exact h

/-! ### `logits32` -/

def logitsSpec : Spec :=
  { kinds := [.array, .array, .word, .word], index := 6, count := .param 2,
    vars := [(7, .f32), (8, .u64), (9, .u64), (10, .f32)], width := 11,
    body := .seq (.assign 7 (.constF32 0)) (Stmt.loop 8 9 (.get 3)
      (dotBody 7 10 (.ofBits32 (.read 0 (.get 9)))
        (.ofBits32 (.read 1 (.bin .add (.bin .mul (.get 6) (.get 3)) (.get 9)))))),
    element := .toBits32 (.getF32 7) }

theorem logitsSpec_eq : specOf gpt32.logits32.ir [.array, .array, .word, .word] =
    some logitsSpec := rfl

theorem logitsSpec_wf : logitsSpec.WF := logitsSpec.wf_of_wfb (by decide)

theorem logitsSpec_module : logitsSpec.module = some logitsKernel := by
  rw [logitsKernel, kernelOf, logitsSpec_eq]
  rfl

/-- Element `v` of `logits32 h wte rows d`. -/
def logitsAt (h wte : Array Float32) (d v : UInt64) : Float32 :=
  LeanExe.loop d 0.0 (fun c acc => acc + h[c.toNat]! * wte[(v * d + c).toNat]!)

theorem logits_element (h wte : Array Float32) (d v : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h3 : L 3 = some (.i64 d)) (h6 : L 6 = some (.i64 v))
    (h0 : arrays 0 = some (floatWords h)) (h1 : arrays 1 = some (floatWords wte))
    (hn : ∀ j, 7 ≤ j → j ≤ 10 → arrays j = none) :
    ∃ L', logitsSpec.body.denote arrays L = some L' ∧
      logitsSpec.element.denote L' arrays = some (logitsAt h wte d v).toBits.toUInt64 := by
  let L1 : Nat → Option Wasm.Value := fun i => if i = 7 then some (.f32 0) else L i
  have s0 : (Project.IR.Stmt.assign 7 (.constF32 0)).denote arrays L = some L1 :=
    denote_assign_f32 (hn 7 (by omega) (by omega)) rfl
  obtain ⟨L', hL', hacc, -⟩ := dotLoop_denote (L := L1) (acc := 7) (tmp := 10) (limit := 8)
    (idx := 9) (count := .get 3) (n := d) (A := .ofBits32 (.read 0 (.get 9)))
    (B := .ofBits32 (.read 1 (.bin .add (.bin .mul (.get 6) (.get 3)) (.get 9))))
    0.0 (fun c => h[c.toNat]!) (fun c => wte[(v * d + c).toNat]!) (by decide)
    ⟨hn 8 (by omega) (by omega), hn 9 (by omega) (by omega), hn 10 (by omega) (by omega),
      hn 7 (by omega) (by omega)⟩
    (by simp [Project.IR.Expr.denote, L1, h3]) (by simp [L1, zero_bits])
    (fun k' Lc _ hf hidx => by
      have hl3 : Lc 3 = some (.i64 d) := (hf 3 (by decide)).trans (by simp [L1, h3])
      have hl6 : Lc 6 = some (.i64 v) := (hf 6 (by decide)).trans (by simp [L1, h6])
      constructor
      · simp [Project.IR.Expr.denote, hidx, h0, floatWords, getElem!_map_toBits32]
      · simp [Project.IR.Expr.denote, hidx, hl3, hl6, h1, floatWords, getElem!_map_toBits32,
          U64Op.apply])
  refine ⟨L', ?_, ?_⟩
  · show (Project.IR.Stmt.seq _ _).denote arrays L = some L'
    rw [denote_seq_some s0]
    exact hL'
  · simp [logitsSpec, Project.IR.Expr.denote, hacc, logitsAt]

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
  have hfits : logitsSpec.Fits [.array (floatWords h), .array (floatWords wte), .word rows,
      .word d] rows.toNat :=
    ⟨rfl, by simp; omega, by simp [logitsSpec], hr⟩
  have hd := logitsSpec.dispatch_eq logitsSpec_wf logitsKernel logitsSpec_module _ _ hfits
    (fun v => (logitsAt h wte d v).toBits.toUInt64)
    (fun v _ => logits_element h wte d _ _ _ (by simp [Spec.locals, logitsSpec, Count.sizeLocal?])
      (by simp [Spec.locals, logitsSpec]) (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at hd
  rw [show floatWords (logits32 h wte rows d) = LeanExe.build rows
    (fun v => (logitsAt h wte d v).toBits.toUInt64) by
      simp [logits32, logitsAt, floatWords, Project.IR.build_map]]
  exact hd

/-! ### `mix32` -/

def mixSpec : Spec :=
  { kinds := [.array, .array, .word, .word], index := 6, count := .param 3,
    vars := [(7, .f32), (8, .u64), (9, .u64), (10, .f32)], width := 11,
    body := .seq (.assign 7 (.constF32 0)) (Stmt.loop 8 9 (.bin .add (.get 2) (.const 1))
      (dotBody 7 10
        (.ofBits32 (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 6) (.const 64)) (.const 1024))
          (.get 9))))
        (.ofBits32 (.read 1 (.bin .add (.bin .mul (.get 9) (.get 3)) (.get 6)))))),
    element := .toBits32 (.getF32 7) }

theorem mixSpec_eq : specOf gpt32.mix32.ir [.array, .array, .word, .word] = some mixSpec := rfl

theorem mixSpec_wf : mixSpec.WF := mixSpec.wf_of_wfb (by decide)

theorem mixSpec_module : mixSpec.module = some mixKernel := by
  rw [mixKernel, kernelOf, mixSpec_eq]
  rfl

/-- Element `c` of `mix32 pw vc p d`. -/
def mixAt (pw vc : Array Float32) (p d c : UInt64) : Float32 :=
  LeanExe.loop (p + 1) 0.0 (fun j acc => acc + pw[(c / 64 * 1024 + j).toNat]! * vc[(j * d + c).toNat]!)

theorem mix_element (pw vc : Array Float32) (p d c : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h2 : L 2 = some (.i64 p)) (h3 : L 3 = some (.i64 d))
    (h6 : L 6 = some (.i64 c)) (h0 : arrays 0 = some (floatWords pw))
    (h1 : arrays 1 = some (floatWords vc)) (hn : ∀ j, 7 ≤ j → j ≤ 10 → arrays j = none) :
    ∃ L', mixSpec.body.denote arrays L = some L' ∧
      mixSpec.element.denote L' arrays = some (mixAt pw vc p d c).toBits.toUInt64 := by
  let L1 : Nat → Option Wasm.Value := fun i => if i = 7 then some (.f32 0) else L i
  have s0 : (Project.IR.Stmt.assign 7 (.constF32 0)).denote arrays L = some L1 :=
    denote_assign_f32 (hn 7 (by omega) (by omega)) rfl
  obtain ⟨L', hL', hacc, -⟩ := dotLoop_denote (L := L1) (acc := 7) (tmp := 10) (limit := 8)
    (idx := 9) (count := .bin .add (.get 2) (.const 1)) (n := p + 1)
    (A := .ofBits32 (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 6) (.const 64)) (.const 1024))
      (.get 9))))
    (B := .ofBits32 (.read 1 (.bin .add (.bin .mul (.get 9) (.get 3)) (.get 6))))
    0.0 (fun j => pw[(c / 64 * 1024 + j).toNat]!) (fun j => vc[(j * d + c).toNat]!) (by decide)
    ⟨hn 8 (by omega) (by omega), hn 9 (by omega) (by omega), hn 10 (by omega) (by omega),
      hn 7 (by omega) (by omega)⟩
    (by simp [Project.IR.Expr.denote, L1, h2, U64Op.apply]) (by simp [L1, zero_bits])
    (fun k' Lc _ hf hidx => by
      have hl3 : Lc 3 = some (.i64 d) := (hf 3 (by decide)).trans (by simp [L1, h3])
      have hl6 : Lc 6 = some (.i64 c) := (hf 6 (by decide)).trans (by simp [L1, h6])
      constructor
      · simp [Project.IR.Expr.denote, hidx, hl6, h0, floatWords, getElem!_map_toBits32,
          U64Op.apply]
      · simp [Project.IR.Expr.denote, hidx, hl3, hl6, h1, floatWords, getElem!_map_toBits32,
          U64Op.apply])
  refine ⟨L', ?_, ?_⟩
  · show (Project.IR.Stmt.seq _ _).denote arrays L = some L'
    rw [denote_seq_some s0]
    exact hL'
  · simp [mixSpec, Project.IR.Expr.denote, hacc, mixAt]

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
  have hfits : mixSpec.Fits [.array (floatWords pw), .array (floatWords vc), .word p, .word d]
      d.toNat :=
    ⟨rfl, by simp; omega, by simp [mixSpec], hd⟩
  have h := mixSpec.dispatch_eq mixSpec_wf mixKernel mixSpec_module _ _ hfits
    (fun c => (mixAt pw vc p d c).toBits.toUInt64)
    (fun c _ => mix_element pw vc p d _ _ _ (by simp [Spec.locals, mixSpec, Count.sizeLocal?])
      (by simp [Spec.locals, mixSpec, Count.sizeLocal?]) (by simp [Spec.locals, mixSpec])
      (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (mix32 pw vc p d) = LeanExe.build d
    (fun c => (mixAt pw vc p d c).toBits.toUInt64) by
      simp [mix32, mixAt, floatWords, Project.IR.build_map]]
  exact h

/-! ### `scores32` -/

def scoresA : Project.IR.Expr .f32 :=
  .ofBits32 (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 7) (.const 1024)) (.const 64))
    (.get 10)))

def scoresB : Project.IR.Expr .f32 :=
  .ofBits32 (.read 1 (.bin .add (.bin .add (.bin .mul (.bin .remU (.get 7) (.const 1024)) (.get 3))
    (.bin .mul (.bin .divU (.get 7) (.const 1024)) (.const 64))) (.get 10)))

def scoresSpec : Spec :=
  { kinds := [.array, .array, .word, .word, .word], index := 7, count := .param 4,
    vars := [(8, .f32), (9, .u64), (10, .u64), (11, .f32), (12, .f32)], width := 13,
    body := .seq (.assign 8 (.constF32 0))
      (.seq (Stmt.loop 9 10 (.const 64) (dotBody 8 11 scoresA scoresB)) (.assign 12 (.getF32 8))),
    element := .toBits32 (.iteF32 (.leU (.bin .remU (.get 7) (.const 1024)) (.get 2))
      (.binF32 .mul (.getF32 12) (.constF32 1040187392)) (.constF32 0)) }

theorem scoresSpec_eq : specOf gpt32.scores32.ir [.array, .array, .word, .word, .word] =
    some scoresSpec := rfl

theorem scoresSpec_wf : scoresSpec.WF := scoresSpec.wf_of_wfb (by decide)

theorem scoresSpec_module : scoresSpec.module = some scoresKernel := by
  rw [scoresKernel, kernelOf, scoresSpec_eq]
  rfl

/-- Element `e` of `scores32 q kc p d n`. -/
def scoresAt (q kc : Array Float32) (p d e : UInt64) : Float32 :=
  let dot := LeanExe.loop 64 0.0 (fun t acc =>
    acc + q[(e / 1024 * 64 + t).toNat]! * kc[(e % 1024 * d + e / 1024 * 64 + t).toNat]!)
  if e % 1024 ≤ p then dot * 0.125 else 0.0

theorem scores_element (q kc : Array Float32) (p d e : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h2 : L 2 = some (.i64 p)) (h3 : L 3 = some (.i64 d))
    (h7 : L 7 = some (.i64 e)) (h0 : arrays 0 = some (floatWords q))
    (h1 : arrays 1 = some (floatWords kc)) (hn : ∀ j, 8 ≤ j → j ≤ 12 → arrays j = none) :
    ∃ L', scoresSpec.body.denote arrays L = some L' ∧
      scoresSpec.element.denote L' arrays = some (scoresAt q kc p d e).toBits.toUInt64 := by
  have h8th : (0.125 : Float32).toBits = 1040187392 := by decide +kernel
  let L1 : Nat → Option Wasm.Value := fun i => if i = 8 then some (.f32 0) else L i
  have s0 : (Project.IR.Stmt.assign 8 (.constF32 0)).denote arrays L = some L1 :=
    denote_assign_f32 (hn 8 (by omega) (by omega)) rfl
  obtain ⟨L2, hL2, hacc, hframe⟩ := dotLoop_denote (L := L1) (acc := 8) (tmp := 11) (limit := 9)
    (idx := 10) (count := .const 64) (n := 64) (A := scoresA) (B := scoresB)
    0.0 (fun t => q[(e / 1024 * 64 + t).toNat]!)
    (fun t => kc[(e % 1024 * d + e / 1024 * 64 + t).toNat]!) (by decide)
    ⟨hn 9 (by omega) (by omega), hn 10 (by omega) (by omega), hn 11 (by omega) (by omega),
      hn 8 (by omega) (by omega)⟩
    (by simp [Project.IR.Expr.denote]) (by simp [L1, zero_bits])
    (fun k' Lc _ hf hidx => by
      have hl3 : Lc 3 = some (.i64 d) := (hf 3 (by decide)).trans (by simp [L1, h3])
      have hl7 : Lc 7 = some (.i64 e) := (hf 7 (by decide)).trans (by simp [L1, h7])
      constructor
      · simp [scoresA, Project.IR.Expr.denote, hidx, hl7, h0, floatWords, getElem!_map_toBits32,
          U64Op.apply]
      · simp [scoresB, Project.IR.Expr.denote, hidx, hl3, hl7, h1, floatWords,
          getElem!_map_toBits32, U64Op.apply])
  have s2 := denote_assign_f32 (arrays := arrays) (L := L2) (j := 12) (e := .getF32 8)
    (v := (LeanExe.loop 64 0.0 (fun t s => s + q[(e / 1024 * 64 + t).toNat]! *
      kc[(e % 1024 * d + e / 1024 * 64 + t).toNat]!)).toBits)
    (hn 12 (by omega) (by omega)) (by simp only [Project.IR.Expr.denote, hacc])
  have hbody : scoresSpec.body.denote arrays L = some (fun i => if i = 12 then
      some (.f32 (LeanExe.loop 64 0.0 (fun t s => s + q[(e / 1024 * 64 + t).toNat]! *
        kc[(e % 1024 * d + e / 1024 * 64 + t).toNat]!)).toBits) else L2 i) := by
    show (Project.IR.Stmt.seq _ (.seq _ _)).denote arrays L = some _
    rw [denote_seq_some s0, denote_seq_some hL2]
    exact s2
  refine ⟨_, hbody, ?_⟩
  · have hl2 : L2 2 = some (.i64 p) := (hframe 2 (by decide)).trans (by simp [L1, h2])
    have hl7 : L2 7 = some (.i64 e) := (hframe 7 (by decide)).trans (by simp [L1, h7])
    by_cases hc : e % 1024 ≤ p
    · simp [scoresSpec, scoresAt, Project.IR.Expr.denote, hl2, hl7, U64Op.apply, F32Op.apply, hc,
        F32Bits.toBits_mul, h8th]
    · simp [scoresSpec, scoresAt, Project.IR.Expr.denote, hl2, hl7, U64Op.apply, hc, zero_bits]

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
  have hfits : scoresSpec.Fits [.array (floatWords q), .array (floatWords kc), .word p, .word d,
      .word n] n.toNat :=
    ⟨rfl, by simp; omega, by simp [scoresSpec], hn⟩
  have h := scoresSpec.dispatch_eq scoresSpec_wf scoresKernel scoresSpec_module _ _ hfits
    (fun e => (scoresAt q kc p d e).toBits.toUInt64)
    (fun e _ => scores_element q kc p d _ _ _ (by simp [Spec.locals, scoresSpec, Count.sizeLocal?])
      (by simp [Spec.locals, scoresSpec, Count.sizeLocal?]) (by simp [Spec.locals, scoresSpec])
      (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (scores32 q kc p d n) = LeanExe.build n
    (fun e => (scoresAt q kc p d e).toBits.toUInt64) by
      simp [scores32, scoresAt, floatWords, Project.IR.build_map]]
  exact h

/-! ### `add32`, `embed32`, and `append32`: one expression per element -/

def addSpec : Spec :=
  { kinds := [.array, .array], index := 5, count := .size 2 0, vars := [], width := 6,
    body := .skip,
    element := .toBits32 (.binF32 .add (.ofBits32 (.read 0 (.get 5))) (.ofBits32 (.read 1 (.get 5)))) }

theorem addSpec_eq : specOf gpt32.add32.ir [.array, .array] = some addSpec := rfl

theorem addSpec_wf : addSpec.WF := addSpec.wf_of_wfb (by decide)

theorem addSpec_module : addSpec.module = some addKernel := by
  rw [addKernel, kernelOf, addSpec_eq]
  rfl

theorem addKernel_dispatch (a b : Array Float32) (ha : a.size < 2 ^ 29) (hb : b.size < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * a.size)
    (hL0 : output[0]? = some (UInt32.ofNat a.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : a.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    addKernel.dispatch [(Arg.array (floatWords a)).buffer, (Arg.array (floatWords b)).buffer]
        output count = some (arrayWords (floatWords (add32 a b))) ∧
      addKernel.RaceFree [(Arg.array (floatWords a)).buffer, (Arg.array (floatWords b)).buffer]
        output.size count := by
  have hfits : addSpec.Fits [.array (floatWords a), .array (floatWords b)] (floatWords a).size :=
    ⟨rfl, by simp; omega, ⟨_, rfl, rfl⟩, by simpa using ha⟩
  have h := addSpec.dispatch_eq addSpec_wf addKernel addSpec_module _ _ hfits
    (fun i => (a[i.toNat]! + b[i.toNat]!).toBits.toUInt64)
    (fun k _ => ⟨_, rfl, by
      simp [addSpec, Project.IR.Expr.denote, Spec.locals, Spec.arrays, floatWords,
        getElem!_map_toBits32, F32Op.apply, F32Bits.toBits_add]⟩)
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (add32 a b) = LeanExe.build (UInt64.ofNat (floatWords a).size)
    (fun i => (a[i.toNat]! + b[i.toNat]!).toBits.toUInt64) by
      simp [add32, floatWords, Project.IR.build_map]]
  exact h

def embedSpec : Spec :=
  { kinds := [.array, .array, .word, .word, .word], index := 7, count := .param 4, vars := [],
    width := 8, body := .skip,
    element := .toBits32 (.binF32 .add
      (.ofBits32 (.read 0 (.bin .add (.bin .mul (.get 2) (.get 4)) (.get 7))))
      (.ofBits32 (.read 1 (.bin .add (.bin .mul (.get 3) (.get 4)) (.get 7))))) }

theorem embedSpec_eq : specOf gpt32.embed32.ir [.array, .array, .word, .word, .word] =
    some embedSpec := rfl

theorem embedSpec_wf : embedSpec.WF := embedSpec.wf_of_wfb (by decide)

theorem embedSpec_module : embedSpec.module = some embedKernel := by
  rw [embedKernel, kernelOf, embedSpec_eq]
  rfl

theorem embedKernel_dispatch (wte wpe : Array Float32) (row p d : UInt64)
    (hte : wte.size < 2 ^ 29) (hpe : wpe.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * d.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat d.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : d.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    embedKernel.dispatch [(Arg.array (floatWords wte)).buffer, (Arg.array (floatWords wpe)).buffer,
        (Arg.word row).buffer, (Arg.word p).buffer, (Arg.word d).buffer] output count =
        some (arrayWords (floatWords (embed32 wte wpe row p d))) ∧
      embedKernel.RaceFree [(Arg.array (floatWords wte)).buffer,
        (Arg.array (floatWords wpe)).buffer, (Arg.word row).buffer, (Arg.word p).buffer,
        (Arg.word d).buffer] output.size count := by
  have hfits : embedSpec.Fits [.array (floatWords wte), .array (floatWords wpe), .word row,
      .word p, .word d] d.toNat :=
    ⟨rfl, by simp; omega, by simp [embedSpec], hd⟩
  have h := embedSpec.dispatch_eq embedSpec_wf embedKernel embedSpec_module _ _ hfits
    (fun c => (wte[(row * d + c).toNat]! + wpe[(p * d + c).toNat]!).toBits.toUInt64)
    (fun k _ => ⟨_, rfl, by
      simp [embedSpec, Project.IR.Expr.denote, Spec.locals, Spec.arrays, floatWords,
        getElem!_map_toBits32, F32Op.apply, F32Bits.toBits_add, U64Op.apply, Count.sizeLocal?]⟩)
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (embed32 wte wpe row p d) = LeanExe.build d
    (fun c => (wte[(row * d + c).toNat]! + wpe[(p * d + c).toNat]!).toBits.toUInt64) by
      simp [embed32, floatWords, Project.IR.build_map]]
  exact h

def appendSpec : Spec :=
  { kinds := [.array, .array, .word, .word], index := 6, count := .param 3, vars := [],
    width := 7, body := .skip,
    element := .toBits32 (.iteF32 (.ltU (.get 6) (.get 2)) (.ofBits32 (.read 0 (.get 6)))
      (.ofBits32 (.read 1 (.bin .sub (.get 6) (.get 2))))) }

theorem appendSpec_eq : specOf gpt32.append32.ir [.array, .array, .word, .word] =
    some appendSpec := rfl

theorem appendSpec_wf : appendSpec.WF := appendSpec.wf_of_wfb (by decide)

theorem appendSpec_module : appendSpec.module = some appendKernel := by
  rw [appendKernel, kernelOf, appendSpec_eq]
  rfl

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
  have hfits : appendSpec.Fits [.array (floatWords cache), .array (floatWords row), .word base,
      .word n] n.toNat :=
    ⟨rfl, by simp; omega, by simp [appendSpec], hn⟩
  have h := appendSpec.dispatch_eq appendSpec_wf appendKernel appendSpec_module _ _ hfits
    (fun e => (if e < base then cache[e.toNat]! else row[(e - base).toNat]!).toBits.toUInt64)
    (fun k _ => ⟨_, rfl, by
      simp only [appendSpec, Project.IR.Expr.denote, Spec.locals, Spec.arrays, floatWords,
        Count.sizeLocal?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some]
      by_cases hlt : UInt64.ofNat k < base <;>
        simp [hlt, getElem!_map_toBits32, U64Op.apply]⟩)
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (append32 cache row base n) = LeanExe.build n
    (fun e => (if e < base then cache[e.toNat]! else row[(e - base).toNat]!).toBits.toUInt64) by
      simp [append32, floatWords, Project.IR.build_map]]
  exact h

end Project.Gpt32
