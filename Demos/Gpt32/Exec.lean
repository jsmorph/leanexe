import Demos.Gpt32.HostProgram
import LeanExe.Dialect.Lemmas
import LeanExe.Source.Build

/-!
The meaning of the programs of `Demos/Gpt32/HostProgram.lean` on a device.

A host command acts on a store of named buffers of a device's words as a host session does:
`load` reads a file, `words` and `output` make a buffer, replacing any buffer of that name, and
`run` runs a kernel on `w` groups of 64 threads, workgroups in WGSL and blocks in PTX, with the
inputs at parameters `0` to `k - 1` and the output at `k`.  The output's name must differ from
every input's.  A `Device` gives the buffers of these commands, the run of a kernel, and `Meets`,
the statement of the device's memory model about one run.  The session runs the commands in order,
so the commands act in sequence, and `Cmd.AllMeet` states `Meets` for each run from the store that
the commands before it leave.  `Demos/Gpt32/VerifiedHost.lean` gives the device of the WGSL kernels
and `Demos/Gpt32/VerifiedPtxHost.lean` the device of the PTX kernels.

A typed item acts on a store of binary32 arrays, words, and floats.  A call checks the bounds of
its kernel's theorems and its element count, then stores the kernel's Lean function of its
inputs.  `Item.execAll_sim` turns a run of items into a run of their commands on any device with
a `Backend`.
-/

namespace Demos.Gpt32

open Demos.Gpt32

inductive Val where
  | arr (xs : Array Float32)
  | word (v : UInt64)
  | float (x : Float32)

/-- The kernel argument of a value: the bits of an array's elements, a word, or a float's bits. -/
def Val.arg : Val → LeanExe.Source.Arg
  | .arr xs => .array (xs.map fun x => x.toBits.toUInt64)
  | .word v => .word v
  | .float x => .float x.toBits

/-- A device of the host: the buffer that holds a value; the buffer of a `words` command, or
`none` when the host rejects the words; the buffer of `output n`; the run of kernel `k` on `w`
groups of 64 threads with its inputs and its output's initial words; and `Meets k w ins o out`,
the statement of the device's memory model that the run of `k` with `ins` and `o` leaves `out`. -/
structure Device (Word : Type) where
  buffer : Val → Array Word
  words : List UInt32 → Option (Array Word)
  output : Nat → Array Word
  run : KernelName → Nat → List (Array Word) → Array Word → Option (Array Word)
  Meets : KernelName → Nat → List (Array Word) → Array Word → Array Word → Prop

abbrev HostStore (Word : Type) := Buf → Option (Array Word)

def HostStore.set {Word : Type} (s : HostStore Word) (b : Buf) (ws : Array Word) :
    HostStore Word :=
  fun b' => if b' = b then some ws else s b'

def Cmd.exec {Word : Type} (D : Device Word) (files : String → Option (Array Word))
    (s : HostStore Word) : Cmd → Option (HostStore Word)
  | .load b path => (files path).map (s.set b)
  | .words b ws => (D.words ws).map (s.set b)
  | .output b n => some (s.set b (D.output n))
  | .run k w out ins =>
    if out ∈ ins then none
    else do
      let bufs ← ins.mapM s
      let o ← s out
      let o' ← D.run k w bufs o
      pure (s.set out o')

/-- The run of a command from `s` meets the device's memory model. -/
def Cmd.Meets {Word : Type} (D : Device Word) (s : HostStore Word) : Cmd → Prop
  | .run k w out ins => ∀ bufs o o', ins.mapM s = some bufs → s out = some o →
      D.run k w bufs o = some o' → D.Meets k w bufs o o'
  | _ => True

def Cmd.execAll {Word : Type} (D : Device Word) (files : String → Option (Array Word))
    (s : HostStore Word) : List Cmd → Option (HostStore Word)
  | [] => some s
  | c :: cs => (Cmd.exec D files s c).bind fun s' => Cmd.execAll D files s' cs

/-- Every run of `cs`, from the store that the commands before it leave, meets the device's
memory model. -/
def Cmd.AllMeet {Word : Type} (D : Device Word) (files : String → Option (Array Word))
    (s : HostStore Word) : List Cmd → Prop
  | [] => True
  | c :: cs => Cmd.Meets D s c ∧
      ∀ s', Cmd.exec D files s c = some s' → Cmd.AllMeet D files s' cs

abbrev Store := Buf → Option Val

def Store.set (s : Store) (b : Buf) (v : Val) : Store :=
  fun b' => if b' = b then some v else s b'

def Store.host {Word : Type} (s : Store) (D : Device Word) : HostStore Word :=
  fun b => (s b).map D.buffer

abbrev Small (xs : Array Float32) : Prop := xs.size < 2 ^ 29

abbrev SmallWord (v : UInt64) : Prop := v.toNat < 2 ^ 29

/-- Kernel `k` of the arguments `vs`, when they have the kinds and the bounds of its theorems. -/
def KernelName.apply : KernelName → List Val → Option (Array Float32)
  | .embed, [.arr wte, .arr wpe, .word row, .word p, .word d] =>
    if Small wte ∧ Small wpe ∧ SmallWord d then some (embed32 wte wpe row p d) else none
  | .layerNorm, [.arr x, .arr g, .arr b, .word d, .float nf] =>
    if Small x ∧ Small g ∧ Small b ∧ SmallWord d then some (layerNorm32 x g b d nf) else none
  | .linear, [.arr x, .arr w, .arr b, .word k, .word m] =>
    if Small x ∧ Small w ∧ Small b ∧ SmallWord m then some (Library.Numerics.LinearAlgebra.Binary32.linear32 x w b k m) else none
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
    if Small a ∧ Small b then some (Library.Numerics.LinearAlgebra.Binary32.add32 a b) else none
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

theorem size_toUInt64 {xs : Array Float32} (h : xs.size < 2 ^ 29) :
    xs.size.toUInt64.toNat = xs.size := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  omega

/-- The facts that relate a device to the typed items: the buffers of the `words` commands of a
word, a float, and an empty array, and for each call, that the run of its kernel on enough groups
of 64 threads, from the output of the call's size, leaves the call's result and meets the
device's memory model. -/
structure Backend {Word : Type} (D : Device Word) : Prop where
  word : ∀ v : UInt64, D.words [v.toUInt32, (v >>> 32).toUInt32] = some (D.buffer (.word v))
  float : ∀ x : Float32, D.words [x.toBits, 0] = some (D.buffer (.float x))
  empty : D.words [0, 0] = some (D.buffer (.arr #[]))
  apply : ∀ {k vs ys}, k.apply vs = some ys →
    D.run k ((ys.size + 63) / 64) (vs.map D.buffer) (D.output ys.size) =
        some (D.buffer (.arr ys)) ∧
      D.Meets k ((ys.size + 63) / 64) (vs.map D.buffer) (D.output ys.size) (D.buffer (.arr ys))

def hostFiles {Word : Type} (D : Device Word) (files : String → Option Val) :
    String → Option (Array Word) :=
  fun path => (files path).map D.buffer

theorem HostStore.mapM_set {Word : Type} {s : HostStore Word} {b : Buf} {ws : Array Word} :
    ∀ {ins : List Buf}, b ∉ ins → ins.mapM (s.set b ws) = ins.mapM s
  | [], _ => rfl
  | i :: is, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [List.mapM_cons, HostStore.set, ite_eq_right (fun e : i = b => h.1 e.symm),
      HostStore.mapM_set h.2]

theorem Store.mapM_host {Word : Type} (D : Device Word) (s : Store) :
    ∀ (ins : List Buf) (vs : List Val),
      ins.mapM s = some vs → ins.mapM (s.host D) = some (vs.map D.buffer)
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
        simp [List.mapM_cons, Store.host, hi, Store.mapM_host D s is ws his]

theorem HostStore.set_set {Word : Type} (s : HostStore Word) (b : Buf) (x y : Array Word) :
    (s.set b x).set b y = s.set b y := by
  funext b'
  simp only [HostStore.set]
  split <;> rfl

theorem Store.host_set {Word : Type} (D : Device Word) (s : Store) (b : Buf) (v : Val) :
    (s.set b v).host D = (s.host D).set b (D.buffer v) := by
  funext b'
  simp only [Store.host, Store.set, HostStore.set]
  split <;> rfl

theorem Item.exec_sim {Word : Type} (D : Device Word) (hB : Backend D)
    (files : String → Option Val) {s s' : Store} {i : Item} (h : i.exec files s = some s') :
    Cmd.execAll D (hostFiles D files) (s.host D) i.cmds = some (s'.host D) ∧
      Cmd.AllMeet D (hostFiles D files) (s.host D) i.cmds := by
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
          obtain ⟨hd, hm⟩ := hB.apply hk
          have hins : ins.mapM ((s.host D).set out (D.output ys.size)) =
              some (vs.map D.buffer) := by
            rw [HostStore.mapM_set hout]
            exact Store.mapM_host D s ins vs hvs
          refine ⟨?_, trivial, fun s1 h1 => ⟨?_, fun _ _ => trivial⟩⟩
          · simp [Item.cmds, Cmd.execAll, Cmd.exec, hout, hins, HostStore.set_set, hd,
              Store.host_set, HostStore.set]
          · simp only [Cmd.exec, Option.some.injEq] at h1
            subst h1
            intro bufs o o' hb ho hr
            rw [hins, Option.some.injEq] at hb
            simp only [HostStore.set, ite_true, Option.some.injEq] at ho
            subst hb ho
            rw [hd, Option.some.injEq] at hr
            subst hr
            exact hm
        · cases h
  | word b v =>
    simp only [Item.exec, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, hB.word, Store.host_set], trivial,
      fun _ _ => trivial⟩
  | float b x =>
    simp only [Item.exec, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, hB.float, Store.host_set], trivial,
      fun _ _ => trivial⟩
  | empty b =>
    simp only [Item.exec, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, hB.empty, Store.host_set], trivial,
      fun _ _ => trivial⟩
  | load b path =>
    simp only [Item.exec] at h
    cases hf : files path with
    | none => simp [hf] at h
    | some v =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp [Item.cmds, Cmd.execAll, Cmd.exec, hostFiles, hf, Store.host_set],
        trivial, fun _ _ => trivial⟩

theorem Cmd.execAll_append {Word : Type} (D : Device Word)
    (files : String → Option (Array Word)) :
    ∀ (s : HostStore Word) (cs ds : List Cmd),
      Cmd.execAll D files s (cs ++ ds) = (Cmd.execAll D files s cs).bind fun s' =>
        Cmd.execAll D files s' ds
  | s, [], ds => rfl
  | s, c :: cs, ds => by
    simp only [List.cons_append, Cmd.execAll]
    cases c.exec D files s with
    | none => rfl
    | some s' => exact Cmd.execAll_append D files s' cs ds

theorem Cmd.allMeet_append {Word : Type} (D : Device Word)
    (files : String → Option (Array Word)) :
    ∀ (s : HostStore Word) (cs ds : List Cmd), Cmd.AllMeet D files s cs →
      (∀ s', Cmd.execAll D files s cs = some s' → Cmd.AllMeet D files s' ds) →
      Cmd.AllMeet D files s (cs ++ ds)
  | s, [], ds, _, h => h s rfl
  | s, c :: cs, ds, ⟨hc, hcs⟩, h => ⟨hc, fun s' hs' =>
      Cmd.allMeet_append D files s' cs ds (hcs s' hs') fun s'' h'' =>
        h s'' (by simp [Cmd.execAll, hs', h''])⟩

/-- A run of typed items is a run of their host commands, from the encoded store to the encoded
result, with every run meeting the device's memory model. -/
theorem Item.execAll_sim {Word : Type} (D : Device Word) (hB : Backend D)
    (files : String → Option Val) (items : List Item) (s s' : Store)
    (h : Item.execAll files s items = some s') :
    Cmd.execAll D (hostFiles D files) (s.host D) (Item.allCmds items) = some (s'.host D) ∧
      Cmd.AllMeet D (hostFiles D files) (s.host D) (Item.allCmds items) := by
  induction items generalizing s with
  | nil =>
    simp only [Item.execAll, Option.some.injEq] at h
    subst h
    exact ⟨rfl, trivial⟩
  | cons i is ih =>
    simp only [Item.execAll] at h
    cases hi : i.exec files s with
    | none => simp [hi] at h
    | some s1 =>
      simp only [hi, Option.bind_some] at h
      obtain ⟨he, hr⟩ := Item.exec_sim D hB files hi
      obtain ⟨he', hr'⟩ := ih s1 h
      have hcat : Item.allCmds (i :: is) = i.cmds ++ Item.allCmds is := by
        simp [Item.allCmds]
      rw [hcat]
      refine ⟨?_, Cmd.allMeet_append D _ _ _ _ hr fun s'' h'' => ?_⟩
      · rw [Cmd.execAll_append, he, Option.bind_some, he']
      · rw [he, Option.some.injEq] at h''
        subst h''
        exact hr'

end Demos.Gpt32
