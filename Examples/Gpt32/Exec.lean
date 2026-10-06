import Examples.Gpt32.HostProgram
import Examples.Gpt32.Proofs
import Project.IR.Combinators

/-!
The meaning of the programs of `Examples/Gpt32/HostProgram.lean`.

A host command acts on a store of named buffers of 32-bit words as `leanexe-webgpu-host session`
does: `load` reads a file, `words` and `output` make a buffer, replacing any buffer of that name,
and `run` dispatches `workgroups` workgroups, so `workgroupSize · workgroups` invocations, with
the inputs at bindings `0` to `k - 1` and the output at `k`.  WebGPU rejects a dispatch that binds
a buffer both read-only and read-write, so the output's name must differ from every input's.  The
host submits each dispatch separately, and WebGPU runs submissions in order, each dispatch its own
usage scope, so the commands act in sequence.  A dispatch acts on the device as `Module.dispatch`
does only when it is race-free, which `Cmd.RaceFree` states.

A typed item acts on a store of binary32 arrays, words, and floats.  A call checks the bounds of
its kernel's dispatch theorem and its element count, then stores the kernel's Lean function of
its inputs.
-/

namespace Examples.Gpt32

open Project.WGSL Examples.Gpt32
open Project.IR (build_size)

abbrev HostStore := Buf → Option (Array UInt32)

def HostStore.set (s : HostStore) (b : Buf) (ws : Array UInt32) : HostStore :=
  fun b' => if b' = b then some ws else s b'

/-- The buffer of `output NAME n`: `n` as a 64-bit word, least significant half first, then
`2n` zeros. -/
def outputWords (n : Nat) : Array UInt32 :=
  Array.ofFn (n := 2 + 2 * n) fun i =>
    if i.val = 0 then UInt32.ofNat n else if i.val = 1 then UInt32.ofNat (n / 2 ^ 32) else 0

def Cmd.exec (files : String → Option (Array UInt32)) (s : HostStore) : Cmd → Option HostStore
  | .load b path => (files path).map (s.set b)
  | .words b ws => some (s.set b ws.toArray)
  | .output b n => some (s.set b (outputWords n))
  | .run k w out ins =>
    if out ∈ ins then none
    else do
      let bufs ← ins.mapM s
      let o ← s out
      let o' ← k.module.dispatch bufs o (k.module.workgroupSize * w)
      pure (s.set out o')

def Cmd.RaceFree (s : HostStore) : Cmd → Prop
  | .run k w out ins => ∀ bufs o, ins.mapM s = some bufs → s out = some o →
      k.module.RaceFree bufs o.size (k.module.workgroupSize * w)
  | _ => True

def Cmd.execAll (files : String → Option (Array UInt32)) : HostStore → List Cmd → Option HostStore
  | s, [] => some s
  | s, c :: cs => (c.exec files s).bind fun s' => Cmd.execAll files s' cs

/-- Every dispatch of `cs`, run from `s`, is race-free. -/
def Cmd.AllRaceFree (files : String → Option (Array UInt32)) : HostStore → List Cmd → Prop
  | _, [] => True
  | s, c :: cs => c.RaceFree s ∧ ∀ s', c.exec files s = some s' → Cmd.AllRaceFree files s' cs

inductive Val where
  | arr (xs : Array Float32)
  | word (v : UInt64)
  | float (x : Float32)

def Val.buffer : Val → Array UInt32
  | .arr xs => (Arg.array (floatWords xs)).buffer
  | .word v => (Arg.word v).buffer
  | .float x => (Arg.float x.toBits).buffer

abbrev Store := Buf → Option Val

def Store.set (s : Store) (b : Buf) (v : Val) : Store :=
  fun b' => if b' = b then some v else s b'

def Store.host (s : Store) : HostStore := fun b => (s b).map Val.buffer

abbrev Small (xs : Array Float32) : Prop := xs.size < 2 ^ 29

abbrev SmallWord (v : UInt64) : Prop := v.toNat < 2 ^ 29

/-- Kernel `k` of the arguments `vs`, when they have the kinds and the bounds of its dispatch
theorem. -/
def KernelName.apply : KernelName → List Val → Option (Array Float32)
  | .embed, [.arr wte, .arr wpe, .word row, .word p, .word d] =>
    if Small wte ∧ Small wpe ∧ SmallWord d then some (embed32 wte wpe row p d) else none
  | .layerNorm, [.arr x, .arr g, .arr b, .word d, .float nf] =>
    if Small x ∧ Small g ∧ Small b ∧ SmallWord d then some (layerNorm32 x g b d nf) else none
  | .linear, [.arr x, .arr w, .arr b, .word k, .word m] =>
    if Small x ∧ Small w ∧ Small b ∧ SmallWord m then some (linear32 x w b k m) else none
  | .append, [.arr cache, .arr row, .word base, .word n] =>
    if Small cache ∧ Small row ∧ SmallWord n then some (append32 cache row base n) else none
  | .scores, [.arr q, .arr kc, .word p, .word d, .word n] =>
    if Small q ∧ Small kc ∧ SmallWord n then some (scores32 q kc p d n) else none
  | .headMax, [.arr s, .word p, .word nh] =>
    if Small s ∧ SmallWord nh then some (headMax32 s p nh) else none
  | .headSum, [.arr s, .arr mx, .word p, .word nh] =>
    if Small s ∧ Small mx ∧ SmallWord nh then some (headSum32 s mx p nh) else none
  | .probs, [.arr s, .arr mx, .arr sm, .word p, .word n] =>
    if Small s ∧ Small mx ∧ Small sm ∧ SmallWord n then some (probs32 s mx sm p n) else none
  | .mix, [.arr pw, .arr vc, .word p, .word d] =>
    if Small pw ∧ Small vc ∧ SmallWord d then some (mix32 pw vc p d) else none
  | .add, [.arr a, .arr b] =>
    if Small a ∧ Small b then some (add32 a b) else none
  | .gelu, [.arr x] =>
    if Small x then some (geluArray32 x) else none
  | .logits, [.arr h, .arr wte, .word rows, .word d] =>
    if Small h ∧ Small wte ∧ SmallWord rows then some (logits32 h wte rows d) else none
  | _, _ => none

def Item.exec (files : String → Option Val) (s : Store) : Item → Option Store
  | .call k n out ins =>
    if out ∈ ins then none
    else do
      let vs ← ins.mapM s
      let ys ← k.apply vs
      if ys.size = n then some (s.set out (.arr ys)) else none
  | .word b v => some (s.set b (.word v))
  | .float b x => some (s.set b (.float x))
  | .empty b => some (s.set b (.arr #[]))
  | .load b path => (files path).map (s.set b)

def Item.execAll (files : String → Option Val) : Store → List Item → Option Store
  | s, [] => some s
  | s, i :: is => (i.exec files s).bind fun s' => Item.execAll files s' is

def Item.allCmds (items : List Item) : List Cmd := items.flatMap Item.cmds

/-! ### Typed calls and host commands -/

theorem Spec.module_workgroupSize {K : Spec} {m : Module} (h : K.module = some m) :
    m.workgroupSize = 64 := by
  unfold Spec.module at h
  cases h1 : trStmt K.layout K.body (1 + K.width) with
  | none => simp [h1] at h
  | some a =>
    cases h2 : trExpr K.layout K.element a.2 with
    | none => simp [h1, h2] at h
    | some b =>
      simp only [h1, h2, bind, Option.bind, pure, Option.some.injEq] at h
      rw [← h]

theorem KernelName.workgroupSize (k : KernelName) : k.module.workgroupSize = 64 := by
  cases k
  · exact Spec.module_workgroupSize embedSpec_module
  · exact Spec.module_workgroupSize layerNormSpec_module
  · exact Spec.module_workgroupSize linearSpec_module
  · exact Spec.module_workgroupSize appendSpec_module
  · exact Spec.module_workgroupSize scoresSpec_module
  · exact Spec.module_workgroupSize headMaxSpec_module
  · exact Spec.module_workgroupSize headSumSpec_module
  · exact Spec.module_workgroupSize probsSpec_module
  · exact Spec.module_workgroupSize mixSpec_module
  · exact Spec.module_workgroupSize addSpec_module
  · exact Spec.module_workgroupSize geluSpec_module
  · exact Spec.module_workgroupSize logitsSpec_module

theorem outputWords_size (n : Nat) : (outputWords n).size = 2 + 2 * n := by
  simp [outputWords]

theorem outputWords_zero (n : Nat) : (outputWords n)[0]? = some (UInt32.ofNat n) := by
  simp [outputWords]

theorem outputWords_one {n : Nat} (h : n < 2 ^ 32) : (outputWords n)[1]? = some 0 := by
  rw [Array.getElem?_eq_getElem (by simp [outputWords]; omega)]
  simp only [outputWords, Array.getElem_ofFn]
  simp [Nat.div_eq_of_lt (show n < 4294967296 by omega)]

theorem size_toUInt64 {xs : Array Float32} (h : xs.size < 2 ^ 29) :
    xs.size.toUInt64.toNat = xs.size := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  omega

/-- A call's result is what its kernel's dispatch leaves in an output of the host's form. -/
theorem KernelName.apply_dispatch {k : KernelName} {vs : List Val} {ys : Array Float32}
    (h : k.apply vs = some ys) :
    ys.size < 2 ^ 29 ∧
      k.module.dispatch (vs.map Val.buffer) (outputWords ys.size) (64 * ((ys.size + 63) / 64)) =
        some (Val.buffer (.arr ys)) ∧
      k.module.RaceFree (vs.map Val.buffer) (outputWords ys.size).size
        (64 * ((ys.size + 63) / 64)) := by
  unfold KernelName.apply at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rename_i hb <;> simp only [build_size, embed32, layerNorm32, linear32,
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

def hostFiles (files : String → Option Val) : String → Option (Array UInt32) :=
  fun path => (files path).map Val.buffer

theorem HostStore.mapM_set {s : HostStore} {b : Buf} {ws : Array UInt32} :
    ∀ {ins : List Buf}, b ∉ ins → ins.mapM (s.set b ws) = ins.mapM s
  | [], _ => rfl
  | i :: is, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [List.mapM_cons, HostStore.set, ite_eq_right (fun e : i = b => h.1 e.symm),
      HostStore.mapM_set h.2]

theorem Store.mapM_host (s : Store) : ∀ (ins : List Buf) (vs : List Val),
    ins.mapM s = some vs → ins.mapM s.host = some (vs.map Val.buffer)
  | [], vs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | i :: is, vs, h => by
    cases hi : s i with
    | none => simp [List.mapM_cons, hi] at h
    | some v =>
      cases his : is.mapM s with
      | none => simp [List.mapM_cons, hi, his] at h
      | some ws =>
        simp only [List.mapM_cons, hi, his, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        simp [List.mapM_cons, Store.host, hi, Store.mapM_host s is ws his]

theorem HostStore.set_set (s : HostStore) (b : Buf) (x y : Array UInt32) :
    (s.set b x).set b y = s.set b y := by
  funext b'
  simp only [HostStore.set]
  split <;> rfl

theorem Val.empty_buffer : (Val.arr #[]).buffer = #[0, 0] := by
  simp only [Val.buffer, Arg.buffer, arrayWords]
  ext i h1 h2
  · simp
  · simp only [Array.size_ofFn, Array.size_map, List.size_toArray, List.length_nil] at h1
    simp only [Array.getElem_ofFn]
    match i, h1 with
    | 0, _ => simp [wordHalf]
    | 1, _ => simp [wordHalf]

theorem Store.host_set (s : Store) (b : Buf) (v : Val) :
    (s.set b v).host = s.host.set b v.buffer := by
  funext b'
  simp only [Store.host, Store.set, HostStore.set]
  split <;> rfl

theorem Item.exec_sim (files : String → Option Val) {s s' : Store} {i : Item}
    (h : i.exec files s = some s') :
    Cmd.execAll (hostFiles files) s.host i.cmds = some s'.host ∧
      Cmd.AllRaceFree (hostFiles files) s.host i.cmds := by
  cases i with
  | call k n out ins =>
    simp only [Item.exec] at h
    split at h
    · cases h
    rename_i hout
    cases hvs : ins.mapM s with
    | none => simp [hvs] at h
    | some vs =>
      cases hk : k.apply vs with
      | none => simp [hvs, hk] at h
      | some ys =>
        simp only [hvs, hk, bind, Option.bind] at h
        split at h
        · rename_i hn
          simp only [Option.some.injEq] at h
          subst hn h
          have hW := k.workgroupSize
          obtain ⟨hsmall, hd, hr⟩ :=
            KernelName.apply_dispatch hk
          have hins : ins.mapM (s.host.set out (outputWords ys.size)) =
              some (vs.map Val.buffer) := by
            rw [HostStore.mapM_set hout]
            exact Store.mapM_host s ins vs hvs
          refine ⟨?_, trivial, fun s1 h1 => ⟨?_, fun _ _ => trivial⟩⟩
          · simp [Item.cmds, Cmd.execAll, Cmd.exec, hout, hins, HostStore.set_set, hW, hd,
              Store.host_set, HostStore.set]
          · simp only [Cmd.exec, Option.some.injEq] at h1
            subst h1
            intro bufs o hb ho
            rw [hins, Option.some.injEq] at hb
            simp only [HostStore.set, ite_true, Option.some.injEq] at ho
            subst hb ho
            rw [hW]
            exact hr
        · cases h
  | word b v =>
    simp only [Item.exec, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, Store.host_set, Val.buffer, Arg.buffer],
      trivial, fun _ _ => trivial⟩
  | float b x =>
    simp only [Item.exec, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, Store.host_set, Val.buffer, Arg.buffer],
      trivial, fun _ _ => trivial⟩
  | empty b =>
    simp only [Item.exec, Option.some.injEq] at h
    subst h
    refine ⟨?_, trivial, fun _ _ => trivial⟩
    simp [Item.cmds, Cmd.execAll, Cmd.exec, Store.host_set, Val.empty_buffer]
  | load b path =>
    simp only [Item.exec] at h
    cases hf : files path with
    | none => simp [hf] at h
    | some v =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, hostFiles, hf, Store.host_set],
        trivial, fun _ _ => trivial⟩

theorem Cmd.execAll_append (files : String → Option (Array UInt32)) :
    ∀ (s : HostStore) (cs ds : List Cmd),
      Cmd.execAll files s (cs ++ ds) = (Cmd.execAll files s cs).bind fun s' =>
        Cmd.execAll files s' ds
  | s, [], ds => rfl
  | s, c :: cs, ds => by
    simp only [List.cons_append, Cmd.execAll]
    cases c.exec files s with
    | none => rfl
    | some s' => exact Cmd.execAll_append files s' cs ds

theorem Cmd.allRaceFree_append (files : String → Option (Array UInt32)) :
    ∀ (s : HostStore) (cs ds : List Cmd), Cmd.AllRaceFree files s cs →
      (∀ s', Cmd.execAll files s cs = some s' → Cmd.AllRaceFree files s' ds) →
      Cmd.AllRaceFree files s (cs ++ ds)
  | s, [], ds, _, h => h s rfl
  | s, c :: cs, ds, ⟨hc, hcs⟩, h => ⟨hc, fun s' hs' =>
      Cmd.allRaceFree_append files s' cs ds (hcs s' hs') fun s'' h'' =>
        h s'' (by simp [Cmd.execAll, hs', h''])⟩

/-- A run of typed items is a run of their host commands, from the encoded store to the encoded
result, with every dispatch race-free. -/
theorem Item.execAll_sim (files : String → Option Val) :
    ∀ (items : List Item) (s s' : Store), Item.execAll files s items = some s' →
      Cmd.execAll (hostFiles files) s.host (Item.allCmds items) = some s'.host ∧
        Cmd.AllRaceFree (hostFiles files) s.host (Item.allCmds items)
  | [], s, s', h => by
    simp only [Item.execAll, Option.some.injEq] at h
    subst h
    exact ⟨rfl, trivial⟩
  | i :: is, s, s', h => by
    simp only [Item.execAll] at h
    cases hi : i.exec files s with
    | none => simp [hi] at h
    | some s1 =>
      simp only [hi, Option.bind_some] at h
      obtain ⟨he, hr⟩ := Item.exec_sim files hi
      obtain ⟨he', hr'⟩ := Item.execAll_sim files is s1 s' h
      have hcat : Item.allCmds (i :: is) = i.cmds ++ Item.allCmds is := by
        simp [Item.allCmds]
      rw [hcat]
      refine ⟨?_, Cmd.allRaceFree_append _ _ _ _ hr fun s'' h'' => ?_⟩
      · rw [Cmd.execAll_append, he, Option.bind_some, he']
      · rw [he, Option.some.injEq] at h''
        subst h''
        exact hr'

end Examples.Gpt32
