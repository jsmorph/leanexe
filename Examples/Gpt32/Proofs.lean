import Examples.Gpt32.Kernels
import Examples.Gpt32.Specs

/-!
The element lemmas and dispatch theorems of the binary32 GPT-2 kernels of
`Examples/Gpt32/Specs.lean`.  `dotLoop_denote` gives the denotation of the compiler's loop that
accumulates products, which four kernels share.
-/

namespace Examples.Gpt32

open Project.IR Project.WGSL Project.ProofKit Project.Pipeline Examples.Gpt32

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
        Count.sizeLocal?, Option.bind_eq_bind, Option.pure_def]
      by_cases hlt : UInt64.ofNat k < base <;>
        simp [hlt, getElem!_map_toBits32, U64Op.apply]⟩)
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (append32 cache row base n) = LeanExe.build n
    (fun e => (if e < base then cache[e.toNat]! else row[(e - base).toNat]!).toBits.toUInt64) by
      simp [append32, floatWords, Project.IR.build_map]]
  exact h

/-! ### The inlined `exp32` -/

/-- Statements in order, nested to the right as the compiler nests them. -/
def seqList : List Project.IR.Stmt → Project.IR.Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqList rest)

theorem seqList_cons (s : Project.IR.Stmt) (rest : List Project.IR.Stmt) (h : rest ≠ []) :
    seqList (s :: rest) = .seq s (seqList rest) := by
  cases rest with
  | nil => contradiction
  | cons _ _ => rfl

/-- The seven assignments of `exp32` of `xe` into locals `b` to `b + 6`. -/
def expAssigns (b : Nat) (xe : Project.IR.Expr .f32) : List Project.IR.Stmt :=
  let n104 : Project.IR.Expr .f32 := .binF32 .sub (.constF32 2147483648) (.constF32 1120927744)
  [.assign b (.iteF32 (.leF32 xe (.constF32 1118961664)) xe (.constF32 1118961664)),
   .assign (b + 1) (.iteF32 (.leF32 n104 (.getF32 b)) (.getF32 b) n104),
   .assign (b + 2) (.unF32 .nearest (.binF32 .mul (.getF32 (b + 1)) (.constF32 1069066811))),
   .assign (b + 3) (.binF32 .add (.binF32 .sub (.getF32 (b + 1)) (.binF32 .mul (.getF32 (b + 2))
     (.constF32 1060208640))) (.binF32 .mul (.getF32 (b + 2)) (.constF32 962494595))),
   .assign (b + 4) (hornerIR (b + 3) [1065353216, 1065353216, 1056964608, 1042983595, 1026206379,
     1007192201, 985008993] 961547521),
   .assign (b + 5) (.bin .sub (.toBits32 (.binF32 .add (.getF32 (b + 2)) (.constF32 1262485504)))
     (.const 1262485250)),
   .assign (b + 6) (.bin .divU (.get (b + 5)) (.const 2))]

/-- The expression that finishes `exp32` from the locals `b` to `b + 6`. -/
def expTail (b : Nat) : Project.IR.Expr .f32 :=
  .binF32 .mul (.binF32 .mul (.getF32 (b + 4)) (.ofBits32 (.bin .mul (.get (b + 6)) (.const 8388608))))
    (.ofBits32 (.bin .mul (.bin .sub (.get (b + 5)) (.get (b + 6))) (.const 8388608)))

/-- The steps of `exp32`. -/
def expA (x : Float32) : Float32 := if x ≤ 89.0 then x else 89.0
def expC (x : Float32) : Float32 := if -104.0 ≤ expA x then expA x else -104.0
def expK (x : Float32) : Float32 := LeanExe.Float32.nearest (expC x * 1.44269502162933349609375)
def expR (x : Float32) : Float32 :=
  expC x - expK x * 0.693359375 + expK x * 0.000212194441701285541057586669921875
def expP (x : Float32) : Float32 :=
  1.0 + expR x * (1.0 + expR x * (0.5 + expR x * (0.16666667163372039794921875 +
    expR x * (0.0416666679084300994873046875 + expR x * (0.008333333767950534820556640625 +
    expR x * (0.001388888922519981861114501953125 +
    expR x * 0.000198412701138295233249664306640625))))))
def expM (x : Float32) : UInt64 := (expK x + 12582912.0).toBits.toUInt64 - 1262485250
def expH (x : Float32) : UInt64 := expM x / 2

theorem exp32_steps (x : Float32) : exp32 x = expP x * Float32.ofBits (expH x * 8388608).toUInt32 *
    Float32.ofBits ((expM x - expH x) * 8388608).toUInt32 := rfl

/-- The locals after the seven assignments. -/
def expLocals (b : Nat) (x : Float32) (L : Nat → Option Wasm.Value) : Nat → Option Wasm.Value :=
  fun i => if i = b + 6 then some (.i64 (expH x)) else if i = b + 5 then some (.i64 (expM x))
    else if i = b + 4 then some (.f32 (expP x).toBits) else if i = b + 3 then some (.f32 (expR x).toBits)
    else if i = b + 2 then some (.f32 (expK x).toBits) else if i = b + 1 then some (.f32 (expC x).toBits)
    else if i = b then some (.f32 (expA x).toBits) else L i

theorem denote_seqList_append {arrays : Nat → Option (Array UInt64)} :
    ∀ (A rest : List Project.IR.Stmt) (L L' : Nat → Option Wasm.Value), A ≠ [] → rest ≠ [] →
      (seqList A).denote arrays L = some L' →
      (seqList (A ++ rest)).denote arrays L = (seqList rest).denote arrays L'
  | [], _, _, _, h, _, _ => absurd rfl h
  | [s], rest, L, L', _, hr, hA => by
      have hA' : s.denote arrays L = some L' := hA
      rw [List.singleton_append, seqList_cons s rest hr, denote_seq_some hA']
  | s :: t :: u, rest, L, L', _, hr, hA => by
      rw [seqList_cons s (t :: u) (by simp)] at hA
      simp only [Project.IR.Stmt.denote, Option.bind_eq_some_iff] at hA
      obtain ⟨L1, h1, h2⟩ := hA
      rw [List.cons_append, seqList_cons s _ (by simp), denote_seq_some h1]
      exact denote_seqList_append (t :: u) rest L1 L' (by simp) hr h2

theorem exp_literals :
    (89.0 : Float32).toBits = 1118961664 ∧ (104.0 : Float32).toBits = 1120927744 ∧
    (1.44269502162933349609375 : Float32).toBits = 1069066811 ∧
    (0.693359375 : Float32).toBits = 1060208640 ∧
    (0.000212194441701285541057586669921875 : Float32).toBits = 962494595 ∧
    (1.0 : Float32).toBits = 1065353216 ∧ (0.5 : Float32).toBits = 1056964608 ∧
    (0.16666667163372039794921875 : Float32).toBits = 1042983595 ∧
    (0.0416666679084300994873046875 : Float32).toBits = 1026206379 ∧
    (0.008333333767950534820556640625 : Float32).toBits = 1007192201 ∧
    (0.001388888922519981861114501953125 : Float32).toBits = 985008993 ∧
    (0.000198412701138295233249664306640625 : Float32).toBits = 961547521 ∧
    (12582912.0 : Float32).toBits = 1262485504 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The seven assignments of `exp32` of `xe` at locals `b` to `b + 6` leave `expLocals`, from
which `expTail` gives `exp32`'s bits. -/
theorem expAssigns_denote (b : Nat) (xe : Project.IR.Expr .f32) (x : Float32)
    (arrays : Nat → Option (Array UInt64)) (L : Nat → Option Wasm.Value)
    (hx : xe.denote L arrays = some x.toBits) (hn : ∀ j, b ≤ j → j ≤ b + 6 → arrays j = none) :
    (seqList (expAssigns b xe)).denote arrays L = some (expLocals b x L) ∧
      (expTail b).denote (expLocals b x L) arrays = some (exp32 x).toBits := by
  obtain ⟨h89, h104, hlog, hhi, hlo, h1, h05, hc3, hc4, hc5, hc6, hc7, hM⟩ := exp_literals
  let L0 := fun i => if i = b then some (Wasm.Value.f32 (expA x).toBits) else L i
  let L1 := fun i => if i = b + 1 then some (Wasm.Value.f32 (expC x).toBits) else L0 i
  let L2 := fun i => if i = b + 2 then some (Wasm.Value.f32 (expK x).toBits) else L1 i
  let L3 := fun i => if i = b + 3 then some (Wasm.Value.f32 (expR x).toBits) else L2 i
  let L4 := fun i => if i = b + 4 then some (Wasm.Value.f32 (expP x).toBits) else L3 i
  let L5 := fun i => if i = b + 5 then some (Wasm.Value.i64 (expM x)) else L4 i
  let L6 := fun i => if i = b + 6 then some (Wasm.Value.i64 (expH x)) else L5 i
  have s0 := denote_assign_f32 (arrays := arrays) (L := L) (j := b)
    (e := .iteF32 (.leF32 xe (.constF32 1118961664)) xe (.constF32 1118961664))
    (v := (expA x).toBits) (hn b (by omega) (by omega)) (by
      simp only [Project.IR.Expr.denote, hx, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, ite_some]
      simp only [expA, apply_ite Float32.toBits, F32Bits.le_iff, h89])
  have s1 := denote_assign_f32 (arrays := arrays) (L := L0) (j := b + 1)
    (e := .iteF32 (.leF32 (.binF32 .sub (.constF32 2147483648) (.constF32 1120927744)) (.getF32 b))
      (.getF32 b) (.binF32 .sub (.constF32 2147483648) (.constF32 1120927744)))
    (v := (expC x).toBits) (hn (b + 1) (by omega) (by omega)) (by
      simp only [Project.IR.Expr.denote, L0, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, F32Op.apply, ite_some]
      simp only [expC, apply_ite Float32.toBits, F32Bits.le_iff, F32Bits.toBits_neg, h104])
  have s2 := denote_assign_f32 (arrays := arrays) (L := L1) (j := b + 2)
    (e := .unF32 .nearest (.binF32 .mul (.getF32 (b + 1)) (.constF32 1069066811)))
    (v := (expK x).toBits) (hn (b + 2) (by omega) (by omega)) (by
      simp only [Project.IR.Expr.denote, L1, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.map_some, F32Op.apply, F32UnOp.apply]
      simp only [expK, F32Nearest.toBits_nearest, F32Bits.toBits_mul, hlog])
  have s3 := denote_assign_f32 (arrays := arrays) (L := L2) (j := b + 3)
    (e := .binF32 .add (.binF32 .sub (.getF32 (b + 1)) (.binF32 .mul (.getF32 (b + 2))
      (.constF32 1060208640))) (.binF32 .mul (.getF32 (b + 2)) (.constF32 962494595)))
    (v := (expR x).toBits) (hn (b + 3) (by omega) (by omega)) (by
      have e1 : L2 (b + 1) = some (.f32 (expC x).toBits) := by simp [L2, L1]
      have e2 : L2 (b + 2) = some (.f32 (expK x).toBits) := by simp [L2]
      simp only [Project.IR.Expr.denote, e1, e2, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, F32Op.apply]
      simp only [expR, F32Bits.toBits_add, F32Bits.toBits_sub, F32Bits.toBits_mul, hhi, hlo])
  have s4 := denote_assign_f32 (arrays := arrays) (L := L3) (j := b + 4)
    (e := hornerIR (b + 3) [1065353216, 1065353216, 1056964608, 1042983595, 1026206379,
      1007192201, 985008993] 961547521)
    (v := (expP x).toBits) (hn (b + 4) (by omega) (by omega)) (by
      have e3 : L3 (b + 3) = some (.f32 (expR x).toBits) := by simp [L3]
      simp only [hornerIR, Project.IR.Expr.denote, e3, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, F32Op.apply]
      simp only [expP, F32Bits.toBits_add, F32Bits.toBits_mul, h1, h05, hc3, hc4, hc5, hc6, hc7])
  have s5 := denote_assign_u64 (arrays := arrays) (L := L4) (j := b + 5)
    (e := .bin .sub (.toBits32 (.binF32 .add (.getF32 (b + 2)) (.constF32 1262485504)))
      (.const 1262485250))
    (v := expM x) (hn (b + 5) (by omega) (by omega)) (by
      have e2 : L4 (b + 2) = some (.f32 (expK x).toBits) := by simp [L4, L3, L2]
      simp only [Project.IR.Expr.denote, e2, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.map_some, F32Op.apply, U64Op.apply]
      simp only [expM, F32Bits.toBits_add, hM])
  have s6 := denote_assign_u64 (arrays := arrays) (L := L5) (j := b + 6)
    (e := .bin .divU (.get (b + 5)) (.const 2))
    (v := expH x) (hn (b + 6) (by omega) (by omega)) (by
      have e5 : L5 (b + 5) = some (.i64 (expM x)) := by simp [L5]
      simp only [Project.IR.Expr.denote, e5, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, U64Op.apply, show (2 : UInt64) ≠ 0 by decide, ↓reduceIte]
      rfl)
  have hL6 : L6 = expLocals b x L := by
    funext i
    simp only [L6, L5, L4, L3, L2, L1, L0, expLocals]
  constructor
  · rw [← hL6]
    simp only [expAssigns]
    rw [seqList_cons _ _ (by simp), denote_seq_some s0, seqList_cons _ _ (by simp),
      denote_seq_some s1, seqList_cons _ _ (by simp), denote_seq_some s2,
      seqList_cons _ _ (by simp), denote_seq_some s3, seqList_cons _ _ (by simp),
      denote_seq_some s4, seqList_cons _ _ (by simp), denote_seq_some s5]
    exact s6
  · have e4 : expLocals b x L (b + 4) = some (.f32 (expP x).toBits) := by simp [expLocals]
    have e5 : expLocals b x L (b + 5) = some (.i64 (expM x)) := by simp [expLocals]
    have e6 : expLocals b x L (b + 6) = some (.i64 (expH x)) := by simp [expLocals]
    simp only [expTail, Project.IR.Expr.denote, e4, e5, e6, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.map_some, F32Op.apply, U64Op.apply]
    rw [exp32_steps, F32Bits.toBits_mul, F32Bits.toBits_mul, F32Bits.toBits_ofBits,
      F32Bits.toBits_ofBits, isNaN_pow23, isNaN_pow23]
    rfl

/-! ### `geluArray32` -/

def geluX : Project.IR.Expr .f32 := .ofBits32 (.read 0 (.get 4))

def geluArg : Project.IR.Expr .f32 :=
  .binF32 .mul (.constF32 1073741824) (.binF32 .mul (.constF32 1061962282) (.binF32 .add geluX
    (.binF32 .mul (.binF32 .mul (.binF32 .mul (.constF32 1027024659) geluX) geluX) geluX)))

def geluSpec : Spec :=
  { kinds := [.array], index := 4, count := .size 1 0,
    vars := [(5, .f32), (6, .f32), (7, .f32), (8, .f32), (9, .f32), (10, .u64), (11, .u64)],
    width := 12, body := seqList (expAssigns 5 geluArg),
    element := .toBits32 (.binF32 .mul (.binF32 .mul (.constF32 1056964608) geluX)
      (.binF32 .sub (.constF32 1073741824) (.binF32 .div (.constF32 1073741824)
        (.binF32 .add (expTail 5) (.constF32 1065353216))))) }

theorem geluSpec_eq : specOf gpt32.geluArray32.ir [.array] = some geluSpec := rfl

theorem geluSpec_wf : geluSpec.WF := geluSpec.wf_of_wfb (by decide)

theorem geluSpec_module : geluSpec.module = some geluKernel := by
  rw [geluKernel, kernelOf, geluSpec_eq]
  rfl

theorem gelu_element (x : Array Float32) (i : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h4 : L 4 = some (.i64 i))
    (h0 : arrays 0 = some (floatWords x)) (hn : ∀ j, 5 ≤ j → j ≤ 11 → arrays j = none) :
    ∃ L', geluSpec.body.denote arrays L = some L' ∧
      geluSpec.element.denote L' arrays = some (gelu32 x[i.toNat]!).toBits.toUInt64 := by
  have h2 : (2.0 : Float32).toBits = 1073741824 := by decide +kernel
  have hc : (0.79788458347320556640625 : Float32).toBits = 1061962282 := by decide +kernel
  have hq : (0.044715 : Float32).toBits = 1027024659 := by decide +kernel
  have h05 : (0.5 : Float32).toBits = 1056964608 := by decide +kernel
  have h1 : (1.0 : Float32).toBits = 1065353216 := by decide +kernel
  generalize hxv : x[i.toNat]! = xv
  have hX : ∀ L0 : Nat → Option Wasm.Value, L0 4 = some (.i64 i) →
      geluX.denote L0 arrays = some xv.toBits := fun L0 h => by
    simp [geluX, Project.IR.Expr.denote, h, h0, floatWords, getElem!_map_toBits32, hxv]
  let z : Float32 := 2.0 * (0.79788458347320556640625 * (xv + 0.044715 * xv * xv * xv))
  have hz : geluArg.denote L arrays = some z.toBits := by
    simp only [geluArg, Project.IR.Expr.denote, hX L h4, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, F32Op.apply]
    simp only [z, F32Bits.toBits_mul, F32Bits.toBits_add, h2, hc, hq]
  obtain ⟨hbody, htail⟩ := expAssigns_denote 5 geluArg z arrays L hz hn
  refine ⟨_, hbody, ?_⟩
  have h4' : expLocals 5 z L 4 = some (.i64 i) := by simp [expLocals, h4]
  simp only [geluSpec, Project.IR.Expr.denote, hX _ h4', htail, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_some, F32Op.apply]
  simp only [gelu32, z, F32Bits.toBits_mul, F32Bits.toBits_sub, F32Bits.toBits_div,
    F32Bits.toBits_add, h05, h2, h1]

theorem geluKernel_dispatch (x : Array Float32) (hx : x.size < 2 ^ 29) (output : Array UInt32)
    (hOut : output.size = 2 + 2 * x.size) (hL0 : output[0]? = some (UInt32.ofNat x.size))
    (hL1 : output[1]? = some 0) (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    geluKernel.dispatch [(Arg.array (floatWords x)).buffer] output count =
        some (arrayWords (floatWords (geluArray32 x))) ∧
      geluKernel.RaceFree [(Arg.array (floatWords x)).buffer] output.size count := by
  have hfits : geluSpec.Fits [.array (floatWords x)] (floatWords x).size :=
    ⟨rfl, by simp; omega, ⟨_, rfl, rfl⟩, by simpa using hx⟩
  have h := geluSpec.dispatch_eq geluSpec_wf geluKernel geluSpec_module _ _ hfits
    (fun i => (gelu32 x[i.toNat]!).toBits.toUInt64)
    (fun k _ => gelu_element x _ _ _ (by simp [Spec.locals, geluSpec]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (geluArray32 x) = LeanExe.build (UInt64.ofNat (floatWords x).size)
    (fun i => (gelu32 x[i.toNat]!).toBits.toUInt64) by
      simp [geluArray32, floatWords, Project.IR.build_map]]
  exact h

/-! ### `probs32` -/

def probsArg : Project.IR.Expr .f32 :=
  .binF32 .sub (.ofBits32 (.read 0 (.get 7))) (.ofBits32 (.read 1 (.bin .divU (.get 7) (.const 1024))))

def probsSpec : Spec :=
  { kinds := [.array, .array, .array, .word, .word], index := 7, count := .param 4,
    vars := [(8, .f32), (9, .f32), (10, .f32), (11, .f32), (12, .f32), (13, .u64), (14, .u64),
      (15, .f32)], width := 16,
    body := seqList (expAssigns 8 probsArg ++ [.assign 15 (.binF32 .div (expTail 8)
      (.ofBits32 (.read 2 (.bin .divU (.get 7) (.const 1024)))))]),
    element := .toBits32 (.iteF32 (.leU (.bin .remU (.get 7) (.const 1024)) (.get 3))
      (.getF32 15) (.constF32 0)) }

theorem probsSpec_eq : specOf gpt32.probs32.ir [.array, .array, .array, .word, .word] =
    some probsSpec := rfl

theorem probsSpec_wf : probsSpec.WF := probsSpec.wf_of_wfb (by decide)

theorem probsSpec_module : probsSpec.module = some probsKernel := by
  rw [probsKernel, kernelOf, probsSpec_eq]
  rfl

/-- Element `e` of `probs32 s mx sm p n`. -/
def probsAt (s mx sm : Array Float32) (p e : UInt64) : Float32 :=
  let w := exp32 (s[e.toNat]! - mx[(e / 1024).toNat]!) / sm[(e / 1024).toNat]!
  if e % 1024 ≤ p then w else 0.0

theorem probs_element (s mx sm : Array Float32) (p e : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h3 : L 3 = some (.i64 p)) (h7 : L 7 = some (.i64 e))
    (h0 : arrays 0 = some (floatWords s)) (h1 : arrays 1 = some (floatWords mx))
    (h2 : arrays 2 = some (floatWords sm)) (hn : ∀ j, 8 ≤ j → j ≤ 15 → arrays j = none) :
    ∃ L', probsSpec.body.denote arrays L = some L' ∧
      probsSpec.element.denote L' arrays = some (probsAt s mx sm p e).toBits.toUInt64 := by
  let z : Float32 := s[e.toNat]! - mx[(e / 1024).toNat]!
  have hz : probsArg.denote L arrays = some z.toBits := by
    simp [probsArg, Project.IR.Expr.denote, h7, h0, h1, floatWords, getElem!_map_toBits32,
      U64Op.apply, F32Op.apply, z, F32Bits.toBits_sub]
  obtain ⟨hbody, htail⟩ := expAssigns_denote 8 probsArg z arrays L hz
    (fun j h1 h2 => hn j h1 (by omega))
  have h7' : expLocals 8 z L 7 = some (.i64 e) := by simp [expLocals, h7]
  let w : Float32 := exp32 z / sm[(e / 1024).toNat]!
  have s15 := denote_assign_f32 (arrays := arrays) (L := expLocals 8 z L) (j := 15)
    (e := .binF32 .div (expTail 8) (.ofBits32 (.read 2 (.bin .divU (.get 7) (.const 1024)))))
    (v := w.toBits) (hn 15 (by omega) (by omega)) (by
      simp only [Project.IR.Expr.denote, htail, h7', h2, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.map_some, U64Op.apply, F32Op.apply,
        show (1024 : UInt64) ≠ 0 by decide, ↓reduceIte]
      simp [w, floatWords, getElem!_map_toBits32, F32Bits.toBits_div])
  have hb : probsSpec.body.denote arrays L =
      some (fun i => if i = 15 then some (.f32 w.toBits) else expLocals 8 z L i) := by
    show (seqList (expAssigns 8 probsArg ++ _)).denote arrays L = _
    rw [denote_seqList_append _ _ L _ (by simp [expAssigns]) (by simp) hbody]
    exact s15
  refine ⟨_, hb, ?_⟩
  have h3' : expLocals 8 z L 3 = some (.i64 p) := by simp [expLocals, h3]
  have h15 : (fun i => if i = 15 then some (Wasm.Value.f32 w.toBits) else expLocals 8 z L i) 15 =
      some (.f32 w.toBits) := by simp
  have h7'' : (fun i => if i = 15 then some (Wasm.Value.f32 w.toBits) else expLocals 8 z L i) 7 =
      some (.i64 e) := by simp [h7']
  have h3'' : (fun i => if i = 15 then some (Wasm.Value.f32 w.toBits) else expLocals 8 z L i) 3 =
      some (.i64 p) := by simp [h3']
  simp only [probsSpec, Project.IR.Expr.denote, h7'', h3'', Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, U64Op.apply, show (1024 : UInt64) ≠ 0 by decide,
    ↓reduceIte, ite_some, Option.map_some]
  by_cases hc : e % 1024 ≤ p
  · simp [probsAt, hc, w, z]
  · simp [probsAt, hc, zero_bits]

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
  have hfits : probsSpec.Fits [.array (floatWords s), .array (floatWords mx),
      .array (floatWords sm), .word p, .word n] n.toNat :=
    ⟨rfl, by simp; omega, by simp [probsSpec], hn⟩
  have h := probsSpec.dispatch_eq probsSpec_wf probsKernel probsSpec_module _ _ hfits
    (fun e => (probsAt s mx sm p e).toBits.toUInt64)
    (fun e _ => probs_element s mx sm p _ _ _ (by simp [Spec.locals, probsSpec, Count.sizeLocal?])
      (by simp [Spec.locals, probsSpec]) (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (by simp [Spec.arrays]) (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (probs32 s mx sm p n) = LeanExe.build n
    (fun e => (probsAt s mx sm p e).toBits.toUInt64) by
      simp [probs32, probsAt, floatWords, Project.IR.build_map]]
  exact h

/-! ### The accumulating loop with any term -/

/-- The loop body that adds `T` to local `acc` through local `tmp`. -/
def accBody (acc tmp : Nat) (T : Project.IR.Expr .f32) : Project.IR.Stmt :=
  .seq (.assign tmp (.binF32 .add (.getF32 acc) T)) (.assign acc (.getF32 tmp))

theorem accLoop_denote {arrays : Nat → Option (Array UInt64)} {L : Nat → Option Wasm.Value}
    {acc tmp limit idx : Nat} {count : Project.IR.Expr .u64} {T : Project.IR.Expr .f32}
    {n : UInt64} (s0 : Float32) (ft : UInt64 → Float32)
    (hdis : [limit, idx, tmp, acc].Nodup)
    (harr : arrays limit = none ∧ arrays idx = none ∧ arrays tmp = none ∧ arrays acc = none)
    (hcount : count.denote L arrays = some n) (hinit : L acc = some (.f32 s0.toBits))
    (hT : ∀ (k : Nat) (Lc : Nat → Option Wasm.Value), k < n.toNat →
      (∀ j, j ∉ [limit, idx, tmp, acc] → Lc j = L j) → Lc idx = some (.i64 (UInt64.ofNat k)) →
      T.denote Lc arrays = some (ft (UInt64.ofNat k)).toBits) :
    ∃ L', (Stmt.loop limit idx count (accBody acc tmp T)).denote arrays L = some L' ∧
      L' acc = some (.f32 (LeanExe.loop n s0 (fun j s => s + ft j)).toBits) ∧
      ∀ j, j ∉ [limit, idx, tmp, acc] → L' j = L j := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hdis
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hdis
  have hBody : ∀ (k : Nat) (s : Float32) (Lc : Nat → Option Wasm.Value), k < n.toNat →
      (∀ j, j ∉ limit :: idx :: (accBody acc tmp T).writes → Lc j = L j) →
      Lc idx = some (.i64 (UInt64.ofNat k)) → Lc limit = some (.i64 n) →
      LocalsHold Lc [acc] (Scalar.values s) →
      ∃ L2, (accBody acc tmp T).denote arrays Lc = some L2 ∧
        LocalsHold L2 [acc] (Scalar.values (s + ft (UInt64.ofNat k))) := by
    intro k s Lc hk hframe hidx _ hhold
    have hacc : Lc acc = some (.f32 s.toBits) := by simpa [LocalsHold, Scalar.values] using hhold
    have ht := hT k Lc hk (fun j hj => hframe j (by simpa [accBody, Stmt.writes] using hj)) hidx
    have s1 := denote_assign_f32 (L := Lc) (j := tmp) (e := .binF32 .add (.getF32 acc) T)
      (v := (s + ft (UInt64.ofNat k)).toBits) harr.2.2.1 (by
        simp [Project.IR.Expr.denote, hacc, ht, F32Op.apply, F32Bits.toBits_add])
    have s2 := denote_assign_f32 (arrays := arrays) (j := acc) (e := .getF32 tmp)
      (v := (s + ft (UInt64.ofNat k)).toBits) harr.2.2.2
      (L := fun i => if i = tmp then some (.f32 (s + ft (UInt64.ofNat k)).toBits) else Lc i)
      (by simp [Project.IR.Expr.denote])
    exact ⟨_, by rw [accBody, denote_seq_some s1]; exact s2, by simp [LocalsHold, Scalar.values]⟩
  obtain ⟨L', hL', hHold⟩ := Stmt.denote_loop (vars := [acc]) (init := s0) (L := L)
    (body := accBody acc tmp T) (fun j s => s + ft j) h1 ⟨harr.1, harr.2.1⟩
    (by simp [accBody, Stmt.writes]; omega) (by simp; omega) hcount
    (by simp [LocalsHold, Scalar.values, hinit]) hBody
  refine ⟨L', hL', by simpa [LocalsHold, Scalar.values] using hHold, fun j hj => ?_⟩
  apply Stmt.denote_frame arrays _ L L' hL' j
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [Stmt.loop, Stmt.writes, accBody, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]

/-! ### `layerNorm32` -/

def lnD : Project.IR.Expr .f32 := .binF32 .sub (.ofBits32 (.read 0 (.get 15))) (.getF32 12)

def layerNormSpec : Spec :=
  { kinds := [.array, .array, .array, .word, .float], index := 7, count := .param 3,
    vars := [(8, .f32), (9, .u64), (10, .u64), (11, .f32), (12, .f32), (13, .f32), (14, .u64),
      (15, .u64), (16, .f32), (17, .f32)], width := 18,
    body := .seq (.assign 8 (.constF32 0))
      (.seq (Stmt.loop 9 10 (.get 3) (accBody 8 11 (.ofBits32 (.read 0 (.get 10)))))
      (.seq (.assign 12 (.binF32 .div (.getF32 8) (.getF32 4)))
      (.seq (.assign 13 (.constF32 0))
      (.seq (Stmt.loop 14 15 (.get 3) (dotBody 13 16 lnD lnD))
        (.assign 17 (.binF32 .div (.getF32 13) (.getF32 4))))))),
    element := .toBits32 (.binF32 .add (.binF32 .mul (.binF32 .mul (.binF32 .sub
      (.ofBits32 (.read 0 (.get 7))) (.getF32 12)) (.binF32 .div (.constF32 1065353216)
      (.unF32 .sqrt (.binF32 .add (.getF32 17) (.constF32 925353388)))))
      (.ofBits32 (.read 1 (.get 7)))) (.ofBits32 (.read 2 (.get 7)))) }

theorem layerNormSpec_eq :
    specOf gpt32.layerNorm32.ir [.array, .array, .array, .word, .float] = some layerNormSpec :=
  rfl

theorem layerNormSpec_wf : layerNormSpec.WF := layerNormSpec.wf_of_wfb (by decide)

theorem layerNormSpec_module : layerNormSpec.module = some layerNormKernel := by
  rw [layerNormKernel, kernelOf, layerNormSpec_eq]
  rfl

/-- Element `c` of `layerNorm32 x g b d nf`. -/
def layerNormAt (x g b : Array Float32) (d : UInt64) (nf : Float32) (c : UInt64) : Float32 :=
  let mean := LeanExe.loop d 0.0 (fun i acc => acc + x[i.toNat]!) / nf
  let var := LeanExe.loop d 0.0 (fun i acc => acc + (x[i.toNat]! - mean) * (x[i.toNat]! - mean)) / nf
  (x[c.toNat]! - mean) * (1.0 / (var + 0.00001).sqrt) * g[c.toNat]! + b[c.toNat]!

theorem layerNorm_element (x g b : Array Float32) (d : UInt64) (nf : Float32) (c : UInt64)
    (L : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (h3 : L 3 = some (.i64 d)) (h4 : L 4 = some (.f32 nf.toBits)) (h7 : L 7 = some (.i64 c))
    (h0 : arrays 0 = some (floatWords x)) (h1 : arrays 1 = some (floatWords g))
    (h2 : arrays 2 = some (floatWords b)) (hn : ∀ j, 8 ≤ j → j ≤ 17 → arrays j = none) :
    ∃ L', layerNormSpec.body.denote arrays L = some L' ∧
      layerNormSpec.element.denote L' arrays = some (layerNormAt x g b d nf c).toBits.toUInt64 := by
  have h1b : (1.0 : Float32).toBits = 1065353216 := by decide +kernel
  have heps : (0.00001 : Float32).toBits = 925353388 := by decide +kernel
  let sum := LeanExe.loop d 0.0 (fun i acc => acc + x[i.toNat]!)
  let mean := sum / nf
  let sq := LeanExe.loop d 0.0 (fun i acc => acc + (x[i.toNat]! - mean) * (x[i.toNat]! - mean))
  let var := sq / nf
  let L1 : Nat → Option Wasm.Value := fun i => if i = 8 then some (.f32 0) else L i
  have s0 : (Project.IR.Stmt.assign 8 (.constF32 0)).denote arrays L = some L1 :=
    denote_assign_f32 (hn 8 (by omega) (by omega)) rfl
  obtain ⟨L2, hL2, hsum, hf2⟩ := accLoop_denote (L := L1) (acc := 8) (tmp := 11) (limit := 9)
    (idx := 10) (count := .get 3) (n := d) (T := .ofBits32 (.read 0 (.get 10)))
    0.0 (fun i => x[i.toNat]!) (by decide)
    ⟨hn 9 (by omega) (by omega), hn 10 (by omega) (by omega), hn 11 (by omega) (by omega),
      hn 8 (by omega) (by omega)⟩
    (by simp [Project.IR.Expr.denote, L1, h3]) (by simp [L1, zero_bits])
    (fun k' Lc _ _ hidx => by
      simp [Project.IR.Expr.denote, hidx, h0, floatWords, getElem!_map_toBits32])
  have l2_4 : L2 4 = some (.f32 nf.toBits) := (hf2 4 (by decide)).trans (by simp [L1, h4])
  have s12 := denote_assign_f32 (arrays := arrays) (L := L2) (j := 12)
    (e := .binF32 .div (.getF32 8) (.getF32 4)) (v := mean.toBits) (hn 12 (by omega) (by omega))
    (by simp [Project.IR.Expr.denote, hsum, l2_4, F32Op.apply, mean, sum, F32Bits.toBits_div])
  let L3 : Nat → Option Wasm.Value := fun i => if i = 12 then some (.f32 mean.toBits) else L2 i
  let L4 : Nat → Option Wasm.Value := fun i => if i = 13 then some (.f32 0) else L3 i
  have s13 : (Project.IR.Stmt.assign 13 (.constF32 0)).denote arrays L3 = some L4 :=
    denote_assign_f32 (hn 13 (by omega) (by omega)) rfl
  obtain ⟨L5, hL5, hsq, hf5⟩ := dotLoop_denote (L := L4) (acc := 13) (tmp := 16) (limit := 14)
    (idx := 15) (count := .get 3) (n := d) (A := lnD) (B := lnD)
    0.0 (fun i => x[i.toNat]! - mean) (fun i => x[i.toNat]! - mean) (by decide)
    ⟨hn 14 (by omega) (by omega), hn 15 (by omega) (by omega), hn 16 (by omega) (by omega),
      hn 13 (by omega) (by omega)⟩
    (by simp [Project.IR.Expr.denote, L4, L3, (hf2 3 (by decide)).trans (by simp [L1, h3] :
      L1 3 = some (.i64 d))]) (by simp [L4, zero_bits])
    (fun k' Lc _ hf hidx => by
      have hl12 : Lc 12 = some (.f32 mean.toBits) := (hf 12 (by decide)).trans (by simp [L4, L3])
      constructor <;>
        simp [lnD, Project.IR.Expr.denote, hidx, hl12, h0, floatWords, getElem!_map_toBits32,
          F32Op.apply, F32Bits.toBits_sub])
  have l5_4 : L5 4 = some (.f32 nf.toBits) := (hf5 4 (by decide)).trans (by simp [L4, L3, l2_4])
  have s17 := denote_assign_f32 (arrays := arrays) (L := L5) (j := 17)
    (e := .binF32 .div (.getF32 13) (.getF32 4)) (v := var.toBits) (hn 17 (by omega) (by omega))
    (by simp [Project.IR.Expr.denote, hsq, l5_4, F32Op.apply, var, sq, F32Bits.toBits_div])
  have hb : layerNormSpec.body.denote arrays L =
      some (fun i => if i = 17 then some (.f32 var.toBits) else L5 i) := by
    show (Project.IR.Stmt.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _))))).denote arrays L = _
    rw [denote_seq_some s0, denote_seq_some hL2, denote_seq_some s12, denote_seq_some s13,
      denote_seq_some hL5]
    exact s17
  refine ⟨_, hb, ?_⟩
  have l7 : L5 7 = some (.i64 c) :=
    (hf5 7 (by decide)).trans (by simp [L4, L3, (hf2 7 (by decide)).trans (by simp [L1, h7] :
      L1 7 = some (.i64 c))])
  have l12 : L5 12 = some (.f32 mean.toBits) := (hf5 12 (by decide)).trans (by simp [L4, L3])
  simp only [layerNormSpec, Project.IR.Expr.denote, ↓reduceIte, l7, l12, h0, h1, h2,
    show (7 : Nat) ≠ 17 by decide, show (12 : Nat) ≠ 17 by decide, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_some, F32Op.apply, F32UnOp.apply, floatWords,
    getElem!_map_toBits32, Option.some.injEq]
  simp only [layerNormAt, F32Bits.toBits_add, F32Bits.toBits_mul, F32Bits.toBits_sub,
    F32Bits.toBits_div, F32Bits.toBits_sqrt, h1b, heps, mean, sum, var, sq]

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
  have hfits : layerNormSpec.Fits [.array (floatWords x), .array (floatWords g),
      .array (floatWords b), .word d, .float nf.toBits] d.toNat :=
    ⟨rfl, by simp; omega, by simp [layerNormSpec], hd⟩
  have h := layerNormSpec.dispatch_eq layerNormSpec_wf layerNormKernel layerNormSpec_module _ _
    hfits (fun c => (layerNormAt x g b d nf c).toBits.toUInt64)
    (fun c _ => layerNorm_element x g b d nf _ _ _
      (by simp [Spec.locals, layerNormSpec, Count.sizeLocal?])
      (by simp [Spec.locals, layerNormSpec, Count.sizeLocal?]) (by simp [Spec.locals, layerNormSpec])
      (by simp [Spec.arrays]) (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (layerNorm32 x g b d nf) = LeanExe.build d
    (fun c => (layerNormAt x g b d nf c).toBits.toUInt64) by
      simp [layerNorm32, layerNormAt, floatWords, Project.IR.build_map]]
  exact h

/-! ### `headMax32` -/

def hmR : Project.IR.Expr .f32 :=
  .ofBits32 (.read 0 (.bin .add (.bin .add (.bin .mul (.get 5) (.const 1024)) (.get 8)) (.const 1)))

def hmBody : Project.IR.Stmt :=
  .seq (.assign 9 (.iteF32 (.leF32 (.getF32 6) hmR) hmR (.getF32 6))) (.assign 6 (.getF32 9))

def headMaxSpec : Spec :=
  { kinds := [.array, .word, .word], index := 5, count := .param 2,
    vars := [(6, .f32), (7, .u64), (8, .u64), (9, .f32)], width := 10,
    body := .seq (.assign 6 (.ofBits32 (.read 0 (.bin .mul (.get 5) (.const 1024)))))
      (Stmt.loop 7 8 (.get 1) hmBody),
    element := .toBits32 (.getF32 6) }

theorem headMaxSpec_eq : specOf gpt32.headMax32.ir [.array, .word, .word] = some headMaxSpec :=
  rfl

theorem headMaxSpec_wf : headMaxSpec.WF := headMaxSpec.wf_of_wfb (by decide)

theorem headMaxSpec_module : headMaxSpec.module = some headMaxKernel := by
  rw [headMaxKernel, kernelOf, headMaxSpec_eq]
  rfl

/-- Element `h` of `headMax32 s p nh`. -/
def headMaxAt (s : Array Float32) (p h : UInt64) : Float32 :=
  LeanExe.loop p s[(h * 1024).toNat]! (fun j acc => max acc s[(h * 1024 + j + 1).toNat]!)

theorem headMax_element (s : Array Float32) (p h : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h1 : L 1 = some (.i64 p)) (h5 : L 5 = some (.i64 h))
    (h0 : arrays 0 = some (floatWords s)) (hn : ∀ j, 6 ≤ j → j ≤ 9 → arrays j = none) :
    ∃ L', headMaxSpec.body.denote arrays L = some L' ∧
      headMaxSpec.element.denote L' arrays = some (headMaxAt s p h).toBits.toUInt64 := by
  let L1 : Nat → Option Wasm.Value := fun i =>
    if i = 6 then some (.f32 s[(h * 1024).toNat]!.toBits) else L i
  have s0 : (Project.IR.Stmt.assign 6 (.ofBits32 (.read 0 (.bin .mul (.get 5) (.const 1024))))).denote
      arrays L = some L1 :=
    denote_assign_f32 (hn 6 (by omega) (by omega)) (by
      simp [Project.IR.Expr.denote, h5, h0, floatWords, getElem!_map_toBits32, U64Op.apply])
  have hBody : ∀ (k : Nat) (acc : Float32) (Lc : Nat → Option Wasm.Value), k < p.toNat →
      (∀ j, j ∉ 7 :: 8 :: hmBody.writes → Lc j = L1 j) →
      Lc 8 = some (.i64 (UInt64.ofNat k)) → Lc 7 = some (.i64 p) →
      LocalsHold Lc [6] (Scalar.values acc) →
      ∃ L2, hmBody.denote arrays Lc = some L2 ∧
        LocalsHold L2 [6] (Scalar.values (max acc s[(h * 1024 + UInt64.ofNat k + 1).toNat]!)) := by
    intro k acc Lc _ hframe hidx _ hhold
    have h6 : Lc 6 = some (.f32 acc.toBits) := by simpa [LocalsHold, Scalar.values] using hhold
    have hl5 : Lc 5 = some (.i64 h) := (hframe 5 (by decide)).trans (by simp [L1, h5])
    let v := max acc s[(h * 1024 + UInt64.ofNat k + 1).toNat]!
    have hR : hmR.denote Lc arrays = some s[(h * 1024 + UInt64.ofNat k + 1).toNat]!.toBits := by
      simp [hmR, Project.IR.Expr.denote, hidx, hl5, h0, floatWords, getElem!_map_toBits32,
        U64Op.apply]
    have s1 := denote_assign_f32 (L := Lc) (j := 9) (e := .iteF32 (.leF32 (.getF32 6) hmR) hmR (.getF32 6))
      (v := v.toBits) (hn 9 (by omega) (by omega)) (by
        simp only [Project.IR.Expr.denote, h6, hR, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, ite_some]
        simp only [v, F32Bits.toBits_max])
    have s2 := denote_assign_f32 (arrays := arrays) (j := 6) (e := .getF32 9) (v := v.toBits)
      (hn 6 (by omega) (by omega))
      (L := fun i => if i = 9 then some (.f32 v.toBits) else Lc i) (by simp [Project.IR.Expr.denote])
    exact ⟨_, by rw [hmBody, denote_seq_some s1]; exact s2, by simp [LocalsHold, Scalar.values, v]⟩
  obtain ⟨L', hL', hHold⟩ := Stmt.denote_loop (vars := [6]) (init := s[(h * 1024).toNat]!)
    (L := L1) (body := hmBody) (count := .get 1) (n := p)
    (fun j acc => max acc s[(h * 1024 + j + 1).toNat]!) (by decide)
    ⟨hn 7 (by omega) (by omega), hn 8 (by omega) (by omega)⟩ (by decide) (by simp)
    (by simp [Project.IR.Expr.denote, L1, h1]) (by simp [LocalsHold, Scalar.values, L1]) hBody
  refine ⟨L', ?_, ?_⟩
  · show (Project.IR.Stmt.seq _ _).denote arrays L = some L'
    rw [denote_seq_some s0]
    exact hL'
  · have h6 : L' 6 = some (.f32 (headMaxAt s p h).toBits) := by
      simpa [LocalsHold, Scalar.values, headMaxAt] using hHold
    simp [headMaxSpec, Project.IR.Expr.denote, h6]

theorem headMaxKernel_dispatch (s : Array Float32) (p nh : UInt64) (hs : s.size < 2 ^ 29)
    (hnh : nh.toNat < 2 ^ 29) (output : Array UInt32) (hOut : output.size = 2 + 2 * nh.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat nh.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : nh.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    headMaxKernel.dispatch [(Arg.array (floatWords s)).buffer, (Arg.word p).buffer,
        (Arg.word nh).buffer] output count = some (arrayWords (floatWords (headMax32 s p nh))) ∧
      headMaxKernel.RaceFree [(Arg.array (floatWords s)).buffer, (Arg.word p).buffer,
        (Arg.word nh).buffer] output.size count := by
  have hfits : headMaxSpec.Fits [.array (floatWords s), .word p, .word nh] nh.toNat :=
    ⟨rfl, by simp; omega, by simp [headMaxSpec], hnh⟩
  have h := headMaxSpec.dispatch_eq headMaxSpec_wf headMaxKernel headMaxSpec_module _ _ hfits
    (fun h => (headMaxAt s p h).toBits.toUInt64)
    (fun c _ => headMax_element s p _ _ _ (by simp [Spec.locals, headMaxSpec, Count.sizeLocal?])
      (by simp [Spec.locals, headMaxSpec]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (headMax32 s p nh) = LeanExe.build nh
    (fun h => (headMaxAt s p h).toBits.toUInt64) by
      simp [headMax32, headMaxAt, floatWords, Project.IR.build_map]]
  exact h

/-! ### `headSum32` -/

def hsArg : Project.IR.Expr .f32 :=
  .binF32 .sub (.ofBits32 (.read 0 (.bin .add (.bin .mul (.get 6) (.const 1024)) (.get 9))))
    (.ofBits32 (.read 1 (.get 6)))

def hsBody : Project.IR.Stmt :=
  seqList (expAssigns 10 hsArg ++ [.assign 17 (.binF32 .add (.getF32 7) (expTail 10)),
    .assign 7 (.getF32 17)])

def headSumSpec : Spec :=
  { kinds := [.array, .array, .word, .word], index := 6, count := .param 3,
    vars := [(7, .f32), (8, .u64), (9, .u64), (10, .f32), (11, .f32), (12, .f32), (13, .f32),
      (14, .f32), (15, .u64), (16, .u64), (17, .f32)], width := 18,
    body := .seq (.assign 7 (.constF32 0)) (Stmt.loop 8 9 (.bin .add (.get 2) (.const 1)) hsBody),
    element := .toBits32 (.getF32 7) }

theorem headSumSpec_eq : specOf gpt32.headSum32.ir [.array, .array, .word, .word] =
    some headSumSpec := rfl

theorem headSumSpec_wf : headSumSpec.WF := headSumSpec.wf_of_wfb (by decide)

theorem headSumSpec_module : headSumSpec.module = some headSumKernel := by
  rw [headSumKernel, kernelOf, headSumSpec_eq]
  rfl

/-- Element `h` of `headSum32 s mx p nh`. -/
def headSumAt (s mx : Array Float32) (p h : UInt64) : Float32 :=
  LeanExe.loop (p + 1) 0.0 (fun j acc => acc + exp32 (s[(h * 1024 + j).toNat]! - mx[h.toNat]!))

theorem headSum_element (s mx : Array Float32) (p h : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h2 : L 2 = some (.i64 p)) (h6 : L 6 = some (.i64 h))
    (h0 : arrays 0 = some (floatWords s)) (h1 : arrays 1 = some (floatWords mx))
    (hn : ∀ j, 7 ≤ j → j ≤ 17 → arrays j = none) :
    ∃ L', headSumSpec.body.denote arrays L = some L' ∧
      headSumSpec.element.denote L' arrays = some (headSumAt s mx p h).toBits.toUInt64 := by
  let L1 : Nat → Option Wasm.Value := fun i => if i = 7 then some (.f32 0) else L i
  have s0 : (Project.IR.Stmt.assign 7 (.constF32 0)).denote arrays L = some L1 :=
    denote_assign_f32 (hn 7 (by omega) (by omega)) rfl
  have hBody : ∀ (k : Nat) (acc : Float32) (Lc : Nat → Option Wasm.Value), k < (p + 1).toNat →
      (∀ j, j ∉ 8 :: 9 :: hsBody.writes → Lc j = L1 j) →
      Lc 9 = some (.i64 (UInt64.ofNat k)) → Lc 8 = some (.i64 (p + 1)) →
      LocalsHold Lc [7] (Scalar.values acc) →
      ∃ L2, hsBody.denote arrays Lc = some L2 ∧
        LocalsHold L2 [7] (Scalar.values
          (acc + exp32 (s[(h * 1024 + UInt64.ofNat k).toNat]! - mx[h.toNat]!))) := by
    intro k acc Lc _ hframe hidx _ hhold
    have h7 : Lc 7 = some (.f32 acc.toBits) := by simpa [LocalsHold, Scalar.values] using hhold
    have hl6 : Lc 6 = some (.i64 h) := (hframe 6 (by decide)).trans (by simp [L1, h6])
    let z : Float32 := s[(h * 1024 + UInt64.ofNat k).toNat]! - mx[h.toNat]!
    have hz : hsArg.denote Lc arrays = some z.toBits := by
      simp [hsArg, Project.IR.Expr.denote, hidx, hl6, h0, h1, floatWords, getElem!_map_toBits32,
        U64Op.apply, F32Op.apply, z, F32Bits.toBits_sub]
    obtain ⟨hexp, htail⟩ := expAssigns_denote 10 hsArg z arrays Lc hz
      (fun j h1 h2 => hn j (by omega) (by omega))
    have h7' : expLocals 10 z Lc 7 = some (.f32 acc.toBits) := by simp [expLocals, h7]
    let v := acc + exp32 z
    have s17 := denote_assign_f32 (arrays := arrays) (L := expLocals 10 z Lc) (j := 17)
      (e := .binF32 .add (.getF32 7) (expTail 10)) (v := v.toBits) (hn 17 (by omega) (by omega))
      (by simp [Project.IR.Expr.denote, h7', htail, F32Op.apply, v, F32Bits.toBits_add])
    have s7 := denote_assign_f32 (arrays := arrays) (j := 7) (e := .getF32 17) (v := v.toBits)
      (hn 7 (by omega) (by omega))
      (L := fun i => if i = 17 then some (.f32 v.toBits) else expLocals 10 z Lc i)
      (by simp [Project.IR.Expr.denote])
    exact ⟨_, by
      show (seqList (expAssigns 10 hsArg ++ _)).denote arrays Lc = _
      rw [denote_seqList_append _ _ Lc _ (by simp [expAssigns]) (by simp) hexp]
      show (Project.IR.Stmt.seq _ _).denote arrays _ = _
      rw [denote_seq_some s17]
      exact s7, by simp [LocalsHold, Scalar.values, v, z]⟩
  obtain ⟨L', hL', hHold⟩ := Stmt.denote_loop (vars := [7]) (init := (0.0 : Float32))
    (L := L1) (body := hsBody) (count := .bin .add (.get 2) (.const 1)) (n := p + 1)
    (fun j acc => acc + exp32 (s[(h * 1024 + j).toNat]! - mx[h.toNat]!)) (by decide)
    ⟨hn 8 (by omega) (by omega), hn 9 (by omega) (by omega)⟩ (by decide) (by simp)
    (by simp [Project.IR.Expr.denote, L1, h2, U64Op.apply])
    (by simp [LocalsHold, Scalar.values, L1, zero_bits]) hBody
  refine ⟨L', ?_, ?_⟩
  · show (Project.IR.Stmt.seq _ _).denote arrays L = some L'
    rw [denote_seq_some s0]
    exact hL'
  · have h7 : L' 7 = some (.f32 (headSumAt s mx p h).toBits) := by
      simpa [LocalsHold, Scalar.values, headSumAt] using hHold
    simp [headSumSpec, Project.IR.Expr.denote, h7]

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
  have hfits : headSumSpec.Fits [.array (floatWords s), .array (floatWords mx), .word p, .word nh]
      nh.toNat :=
    ⟨rfl, by simp; omega, by simp [headSumSpec], hnh⟩
  have h := headSumSpec.dispatch_eq headSumSpec_wf headSumKernel headSumSpec_module _ _ hfits
    (fun h => (headSumAt s mx p h).toBits.toUInt64)
    (fun c _ => headSum_element s mx p _ _ _
      (by simp [Spec.locals, headSumSpec, Count.sizeLocal?]) (by simp [Spec.locals, headSumSpec])
      (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 _ => arrays_none _ j (by simp; omega)))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (headSum32 s mx p nh) = LeanExe.build nh
    (fun h => (headSumAt s mx p h).toBits.toUInt64) by
      simp [headSum32, headSumAt, floatWords, Project.IR.build_map]]
  exact h

end Examples.Gpt32
