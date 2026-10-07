import Verified.Compile
import LeanExe.Pipeline.Allocation
import LeanExe.TalosCompat

/-! The states of the verified compiler's proof: how locals hold words, how words represent values
in a heap and store, the steps that a heap and store take, and `Holds`, the facts about the
variables in scope. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- Half the locals of `s`, the number of positions: a function's locals are its parameters, an
i64 local for each further position, and an f64 local for every position. -/
def _root_.Wasm.Locals.half (s : Locals) : Nat := (s.params.length + s.locals.length) / 2

/-- `after` agrees with `before` on the parameters, the number of locals, and both locals of every
position below `base`: the code of an expression with scratch from `base` on changes nothing
else. -/
structure Frame (base : Nat) (before after : Locals) : Prop where
  params : after.params = before.params
  length : after.locals.length = before.locals.length
  below : ∀ j < base,
    after.get j = before.get j ∧ after.get (j + before.half) = before.get (j + before.half)

theorem Frame.half {base : Nat} {s s' : Locals} (h : Frame base s s') : s'.half = s.half := by
  simp [Locals.half, h.params, h.length]

theorem Frame.refl (base : Nat) (s : Locals) : Frame base s s :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Frame.trans {base : Nat} {s1 s2 s3 : Locals} (h1 : Frame base s1 s2)
    (h2 : Frame base s2 s3) : Frame base s1 s3 :=
  ⟨h2.params.trans h1.params, h2.length.trans h1.length, fun j hj =>
    ⟨(h2.below j hj).1.trans (h1.below j hj).1, by
      have := (h2.below j hj).2
      rw [h1.half] at this
      exact this.trans (h1.below j hj).2⟩⟩

/-- The operand stack plays no part in a frame. -/
theorem Frame.values {base : Nat} {s s' : Locals} {values : List Value}
    (h : Frame base { s with values } s') : Frame base s s' :=
  ⟨h.params, h.length, h.below⟩

theorem Frame.ofValues {base : Nat} {s : Locals} {values : List Value} :
    Frame base s { s with values } :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Frame.mono {base base' : Nat} {s s' : Locals} (h : Frame base' s s') (hb : base ≤ base') :
    Frame base s s' :=
  ⟨h.params, h.length, fun j hj => h.below j (by omega)⟩

@[simp] theorem Locals.get_values (s : Locals) (vs : List Value) (i : Nat) :
    ({ s with values := vs } : Locals).get i = s.get i := rfl

@[simp] theorem Locals.half_values (s : Locals) (vs : List Value) :
    ({ s with values := vs } : Locals).half = s.half := rfl

/-- Local `i`, past the parameters, after a store of `v`. -/
def setLocal (s : Locals) (i : Nat) (v : Value) : Locals :=
  { s with locals := s.locals.set (i - s.params.length) v }

@[simp] theorem Locals.half_setLocal (s : Locals) (i : Nat) (v : Value) :
    (setLocal s i v).half = s.half := by
  simp [Locals.half, setLocal]

theorem Locals.set?_local {s : Locals} {i : Nat} (v : Value) (hLow : s.params.length ≤ i)
    (hHigh : i < s.params.length + s.locals.length) :
    s.set? i v = some (setLocal s i v) := by
  simp [Locals.set?, setLocal, Nat.not_lt.mpr hLow, hHigh]

theorem Locals.get_setLocal_same {s : Locals} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length) :
    (setLocal s i v).get i = some v := by
  simp [Locals.get, setLocal, Nat.not_lt.mpr hLow, hHigh,
    List.getElem?_set_self (show i - s.params.length < s.locals.length by omega)]

theorem Locals.get_setLocal_ne {s : Locals} {i j : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hne : j ≠ i) : (setLocal s i v).get j = s.get j := by
  simp only [Locals.get, setLocal, List.length_set]
  split
  · rfl
  · split
    · rw [List.getElem?_set_ne (by omega)]
    · rfl

/-- A store to an i64 local of a position at or above `base` keeps the frame below `base`. -/
theorem Frame.set {base : Nat} {s : Locals} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hBase : base ≤ i) (hHigh : i < s.half) :
    Frame base s (setLocal s i v) :=
  ⟨rfl, by simp [Verified.setLocal], fun j hj =>
    ⟨Locals.get_setLocal_ne hLow (by omega), Locals.get_setLocal_ne hLow (by omega)⟩⟩

/-- A store, with a new operand stack, to an i64 local of a position at or above `base`. -/
theorem Frame.setValues {base : Nat} {s : Locals} {vs : List Value} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hBase : base ≤ i) (hHigh : i < s.half) :
    Frame base s (setLocal { s with values := vs } i v) :=
  Frame.ofValues.trans (@Frame.set base { s with values := vs } i v hLow hBase hHigh)

/-- A position below the half has its i64 local among the locals. -/
theorem Locals.lt_total {s : Locals} {i : Nat} (h : i < s.half) :
    i < s.params.length + s.locals.length := by
  simp only [Locals.half] at h; omega

/-- The local of position `p` for a word of type `ty` lies past the parameters and among the
locals when the position does. -/
theorem slotIndex_bounds {s : Locals} {p : Nat} (ty : ValueType) (hLow : s.params.length ≤ p)
    (hHigh : p < s.half) :
    s.params.length ≤ slotIndex s.half p ty ∧
      slotIndex s.half p ty < s.params.length + s.locals.length := by
  have : 2 * s.half ≤ s.params.length + s.locals.length := by
    simp only [Locals.half]; omega
  cases ty <;> simp only [slotIndex] <;> omega

/-- A store of `v` to local `i`, past the parameters. -/
theorem wp_localSet_local {m : Module} {rest : Program} {Q : Assertion α} {store : Store α}
    {env : HostEnv α} {s : Locals} {i : Nat} {v : Value} {vs : List Value}
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length)
    (h : wp m rest Q store (setLocal { s with values := vs } i v) env) :
    wp m (.localSet i :: rest) Q store { s with values := v :: vs } env := by
  rw [wp_localSet_cons]
  simp only
  rw [Locals.set?_local (s := { s with values := v :: vs }) v hLow hHigh]
  exact h

/-- Positions `loc` to `loc + vals.length - 1` hold `vals`, word `k` in the local of its type
`tys[k]`. -/
def LocalsHold (s : Locals) (loc : Nat) (tys : List ValueType) (vals : List Value) : Prop :=
  ∀ k (hk : k < vals.length), s.get (slotIndex s.half (loc + k) (tys.getD k .i64)) = some vals[k]

/-- Loading positions that hold `vals` pushes `vals` in order. -/
theorem wp_loadCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    (vals : List Value) {h loc : Nat} {tys : List ValueType} {s : Locals} {rest : Program}
    (hw : vals.length = tys.length) (hh : s.half = h) (hold : LocalsHold s loc tys vals)
    (hk : wp m rest Q store { s with values := vals.reverse ++ s.values } host) :
    wp m (loadCode h loc tys ++ rest) Q store s host := by
  induction vals generalizing loc tys s with
  | nil =>
    cases tys with
    | nil => simpa [loadCode] using hk
    | cons _ _ => exact absurd hw (by simp)
  | cons v vs ih =>
    cases tys with
    | nil => exact absurd hw (by simp)
    | cons ty tys =>
      have h0 : s.get (slotIndex h loc ty) = some v := by
        have := hold 0 (by simp)
        rw [hh] at this
        simpa using this
      simp only [loadCode, List.cons_append, wp_localGet_cons, h0]
      refine ih (s := { s with values := v :: s.values }) (by simpa using hw) (by simpa using hh)
        (fun k hk => ?_) ?_
      · have := hold (k + 1) (by simp; omega)
        rw [show loc + (k + 1) = loc + 1 + k by omega] at this
        simpa [-Locals.get] using this
      · simpa [List.append_assoc] using hk

/-- Storing the top words `vals` of the stack, of types `tys`, at positions `loc` on leaves them
there, keeps the frame below `loc`, and changes no position above them below the half. -/
theorem wp_storeCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    {rest : Program} (vals : List Value) (h loc : Nat) (tys : List ValueType) (s : Locals)
    (vs : List Value) (hw : vals.length = tys.length) (hh : s.half = h)
    (hLow : s.params.length ≤ loc) (hHigh : loc + tys.length ≤ s.half)
    (hNext : ∀ s', Frame loc s s' → LocalsHold s' loc tys vals →
      (∀ j, loc + tys.length ≤ j → j < s.half →
        s'.get j = s.get j ∧ s'.get (j + s.half) = s.get (j + s.half)) →
      wp m rest Q store { s' with values := vs } host) :
    wp m (storeCode h loc tys ++ rest) Q store { s with values := vals.reverse ++ vs } host := by
  induction vals generalizing loc tys s vs rest with
  | nil =>
    cases tys with
    | nil =>
      exact hNext s (Frame.refl loc s) (fun k hk => absurd hk (by simp)) fun _ _ _ => ⟨rfl, rfl⟩
    | cons _ _ => exact absurd hw (by simp)
  | cons v vals ih =>
    cases tys with
    | nil => exact absurd hw (by simp)
    | cons ty tys =>
      simp only [storeCode, List.append_assoc, List.reverse_cons, List.cons_append,
        List.nil_append, List.length_cons] at hHigh ⊢
      have hw' : vals.length = tys.length := by simpa using hw
      refine ih (loc + 1) tys s (v :: vs) hw' hh (by omega) (by omega)
        fun s1 hF1 hold1 habove1 => ?_
      have hh1 : s1.half = s.half := hF1.half
      have hb := slotIndex_bounds (s := s) ty hLow (by omega)
      rw [← hh]
      have hp1 : s1.params.length = s.params.length := by rw [hF1.params]
      have hl1 : s1.locals.length = s.locals.length := hF1.length
      have hLow1 : s1.params.length ≤ slotIndex s.half loc ty := by rw [hp1]; exact hb.1
      have hHigh1 : slotIndex s.half loc ty < s1.params.length + s1.locals.length := by
        rw [hp1, hl1]; exact hb.2
      refine wp_localSet_local hLow1 hHigh1 ?_
      have hne : ∀ j, j < loc ∨ loc + 1 + tys.length ≤ j → j < s.half →
          j ≠ slotIndex s.half loc ty ∧ j + s.half ≠ slotIndex s.half loc ty := by
        intro j hj hjh
        cases ty <;> simp only [slotIndex] <;> omega
      refine hNext (setLocal { s1 with values := vs } (slotIndex s.half loc ty) v)
        ⟨hF1.params, by simp [setLocal, hl1], fun j hj => ?_⟩ (fun k hk => ?_)
        fun j hj hjh => ?_
      · have hn := hne j (Or.inl hj) (by omega)
        rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.1,
          Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.2]
        exact hF1.below j (by omega)
      · simp only [Locals.half_setLocal, Locals.half_values, hh1]
        cases k with
        | zero =>
          simpa [-Locals.get] using Locals.get_setLocal_same (s := { s1 with values := vs })
            (v := v) (i := slotIndex s.half loc ty) hLow1 hHigh1
        | succ k =>
          have hk' : k < vals.length := by simp at hk; omega
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          have hold := hold1 k hk'
          rw [show loc + 1 + k = loc + (k + 1) by omega, hh1] at hold
          have hne' : slotIndex s.half (loc + (k + 1)) (tys.getD k .i64) ≠
              slotIndex s.half loc ty := by
            have : loc + (k + 1) < s.half := by simp at hk; omega
            cases ty <;> cases tys.getD k .i64 <;> simp only [slotIndex] <;> omega
          rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hne']
          simpa [-Locals.get] using hold
      · simp only [List.length_cons] at hj
        have hn := hne j (Or.inr (by omega)) hjh
        rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.1,
          Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.2]
        exact habove1 j (by omega) hjh


/-- The copy of the f64 parameter words, of types `tys` at positions `p` on, to the f64 locals of
their positions: each such local then holds its parameter, and no local below `h + p`
changes. -/
theorem wp_paramCopyCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    {h : Nat} : (tys : List ValueType) → (p : Nat) → ∀ {s : Locals} {rest : Program},
    p + tys.length ≤ s.params.length → s.params.length ≤ h →
    h + h ≤ s.params.length + s.locals.length →
    (∀ s', s'.params = s.params → s'.locals.length = s.locals.length →
      s'.values = s.values → (∀ j < h + p, s'.get j = s.get j) →
      (∀ q, p ≤ q → q < p + tys.length → tys.getD (q - p) .i64 = .f64 →
        s'.get (q + h) = s.get q) →
      wp m rest Q store s' host) →
    wp m (paramCopyCode h p tys ++ rest) Q store s host
  | [], _, s, _, _, _, _, hNext => by
    simpa [paramCopyCode] using
      hNext s rfl rfl rfl (fun _ _ => rfl) fun q h1 h2 => by simp at h2; omega
  | ty :: tys, p, s, rest, hP, hH, hT, hNext => by
    simp only [List.length_cons] at hP
    by_cases hty : ty = .f64
    · subst hty
      obtain ⟨v, hv⟩ : ∃ v, s.get p = some v :=
        ⟨s.params[p], by simp [Locals.get, show p < s.params.length by omega]⟩
      simp only [paramCopyCode, List.cons_append, List.nil_append, wp_localGet_cons, hv]
      refine wp_localSet_local (s := s) (vs := s.values) (by omega) (by omega) ?_
      have hLowS : ({ s with values := s.values } : Locals).params.length ≤ p + h := by
        show s.params.length ≤ p + h; omega
      refine wp_paramCopyCode tys (p + 1)
        (s := setLocal { s with values := s.values } (p + h) v)
        (by simp [setLocal]; omega) (by simp [setLocal]; omega)
        (by simp [setLocal]; omega) fun s' hp' hl' hv' hlow hcopy => ?_
      refine hNext s' (by rw [hp']; rfl) (by rw [hl']; simp [setLocal]) (by rw [hv']; rfl)
        (fun j hj => ?_) fun q h1 h2 hq => ?_
      · rw [hlow j (by omega)]
        exact Locals.get_setLocal_ne hLowS (by omega)
      · have h2' : q < p + 1 + tys.length := by simp only [List.length_cons] at h2; omega
        by_cases hqp : q = p
        · subst hqp
          have hHigh : q + h < s.params.length + s.locals.length := by omega
          rw [hlow (q + h) (by omega), Locals.get_setLocal_same hLowS hHigh]
          exact hv.symm
        · have hq' : tys.getD (q - (p + 1)) .i64 = .f64 := by
            rw [show q - p = (q - (p + 1)) + 1 by omega] at hq; simpa using hq
          rw [hcopy q (by omega) h2' hq']
          exact Locals.get_setLocal_ne hLowS (by omega)
    · have hCode : paramCopyCode h p (ty :: tys) = paramCopyCode h (p + 1) tys := by
        cases ty <;> first | rfl | exact absurd rfl hty
      rw [hCode]
      refine wp_paramCopyCode tys (p + 1) (by omega) hH hT
        fun s' hp' hl' hv' hlow hcopy => hNext s' hp' hl' hv' (fun j hj => hlow j (by omega))
          fun q h1 h2 hq => ?_
      have h2' : q < p + 1 + tys.length := by simp only [List.length_cons] at h2; omega
      by_cases hqp : q = p
      · subst hqp; simp at hq; exact absurd hq hty
      · have hq' : tys.getD (q - (p + 1)) .i64 = .f64 := by
          rw [show q - p = (q - (p + 1)) + 1 by omega] at hq; simpa using hq
        exact hcopy q (by omega) h2' hq'

theorem Ty.scalar_pair {a b : Ty} (h : (Ty.pair a b).scalar = true) :
    a.scalar = true ∧ b.scalar = true := by
  simpa [Ty.scalar] using h

/-- The array `xs` at `ptr` in `heap` at `store`, borrowed or owned. -/
def Mode.array : Mode → Heap → Store Unit → UInt64 → Array UInt64 → Prop
  | .borrowed, heap, store, ptr, xs => heap.Borrowed store ptr xs
  | .owned, heap, store, ptr, xs => heap.Owned store ptr xs

/-- The blocks of the objects that an owned value's arrays occupy, each as its start and
length. -/
def Ty.blocks (store : Store Unit) : (t : Ty) → List Value → t.denote → List (Nat × Nat)
  | .word, _, _ | .bool, _, _ => []
  | .pair a b, ws, p =>
    a.blocks store (ws.take a.width) p.1 ++ b.blocks store (ws.drop a.width) p.2
  | .array, ws, _ => match ws with
    | [.i64 ptr] => [block store ptr]
    | _ => []

/-- The addresses of a value's arrays. -/
def Ty.pointers : (t : Ty) → List Value → List UInt64
  | .word, _ | .bool, _ => []
  | .pair a b, ws => a.pointers (ws.take a.width) ++ b.pointers (ws.drop a.width)
  | .array, ws => match ws with
    | [.i64 ptr] => [ptr]
    | _ => []

/-- The regions of a borrowed value's arrays: each array's length word and elements. -/
def Ty.reads : (t : Ty) → List Value → t.denote → List (Nat × Nat)
  | .word, _, _ | .bool, _, _ => []
  | .pair a b, ws, p => a.reads (ws.take a.width) p.1 ++ b.reads (ws.drop a.width) p.2
  | .array, ws, xs => match ws with
    | [.i64 ptr] => [(ptr.toNat, 8 * (xs.size + 1))]
    | _ => []

/-- The regions that a value occupies: its blocks when owned, and its arrays' regions when
borrowed. -/
def Ty.regions (mode : Mode) (store : Store Unit) (t : Ty) (ws : List Value) (v : t.denote) :
    List (Nat × Nat) :=
  match mode with
  | .owned => t.blocks store ws v
  | .borrowed => t.reads ws v

/-- The words `ws` represent the value `v` of type `t` in `heap` at `store`, with the arrays that
the value contains held in mode `mode`: a word as itself, a `Bool` as 1 or 0, a pair as its first
component's words followed by its second's, and an array as its address.  The components of an
owned pair occupy disjoint blocks. -/
def Ty.Rep (mode : Mode) (heap : Heap) (store : Store Unit) :
    (t : Ty) → List Value → t.denote → Prop
  | .word, ws, v => ws = [.i64 v]
  | .bool, ws, b => ws = [.i64 (boolWord b)]
  | .pair a b, ws, p =>
    ∃ first second, ws = first ++ second ∧ a.Rep mode heap store first p.1 ∧
      b.Rep mode heap store second p.2 ∧
      (mode = .owned → ∀ x ∈ a.blocks store first p.1, ∀ y ∈ b.blocks store second p.2,
        regionsDisjoint x y)
  | .array, ws, xs => ∃ ptr, ws = [.i64 ptr] ∧ mode.array heap store ptr xs

theorem Mode.array.borrow {mode : Mode} {heap : Heap} {store : Store Unit} {ptr : UInt64}
    {xs : Array UInt64} (h : mode.array heap store ptr xs) : heap.Borrowed store ptr xs := by
  cases mode
  · exact h
  · exact Heap.Owned.borrowed h

@[simp] theorem Ty.rep_word {mode : Mode} {heap : Heap} {store : Store Unit} {ws : List Value}
    {v : UInt64} : Ty.Rep mode heap store .word ws v ↔ ws = [.i64 v] := Iff.rfl

@[simp] theorem Ty.rep_bool {mode : Mode} {heap : Heap} {store : Store Unit} {ws : List Value}
    {b : Bool} : Ty.Rep mode heap store .bool ws b ↔ ws = [.i64 (boolWord b)] := Iff.rfl

theorem Ty.Rep.length {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      ws.length = t.width
  | .word, _, _, h | .bool, _, _, h => by subst h; rfl
  | .pair _ _, _, _, ⟨_, _, h, h1, h2, _⟩ => by
    subst h; simp [Ty.width, h1.length, h2.length]
  | .array, _, _, ⟨_, h, _⟩ => by subst h; rfl

theorem Ty.blocks_append {store : Store Unit} {a b : Ty} {first second : List Value}
    {p : a.denote × b.denote} (h : first.length = a.width) :
    (Ty.pair a b).blocks store (first ++ second) p =
      a.blocks store first p.1 ++ b.blocks store second p.2 := by
  simp [Ty.blocks, ← h]

theorem Ty.reads_append {a b : Ty} {first second : List Value} {p : a.denote × b.denote}
    (h : first.length = a.width) :
    (Ty.pair a b).reads (first ++ second) p = a.reads first p.1 ++ b.reads second p.2 := by
  simp [Ty.reads, ← h]

theorem Ty.regions_append {mode : Mode} {store : Store Unit} {a b : Ty}
    {first second : List Value} {p : a.denote × b.denote} (h : first.length = a.width) :
    (Ty.pair a b).regions mode store (first ++ second) p =
      a.regions mode store first p.1 ++ b.regions mode store second p.2 := by
  cases mode
  · exact Ty.reads_append h
  · exact Ty.blocks_append h

theorem Ty.blocks_scalar {store : Store Unit} :
    (t : Ty) → t.scalar = true → (ws : List Value) → (v : t.denote) → t.blocks store ws v = []
  | .word, _, _, _ | .bool, _, _, _ => rfl
  | .pair a b, h, ws, p => by
    simp only [Ty.blocks, a.blocks_scalar (Ty.scalar_pair h).1,
      b.blocks_scalar (Ty.scalar_pair h).2, List.append_nil]
  | .array, h, _, _ => absurd h (by decide)

theorem Ty.regions_scalar {mode : Mode} {store : Store Unit} :
    (t : Ty) → t.scalar = true → (ws : List Value) → (v : t.denote) → t.regions mode store ws v = []
  | .word, _, _, _ | .bool, _, _, _ => by cases mode <;> rfl
  | .pair a b, h, ws, p => by
    cases mode
    · simp only [Ty.regions, Ty.reads]
      have ha := a.regions_scalar (mode := .borrowed) (store := store) (Ty.scalar_pair h).1
        (ws.take a.width) p.1
      have hb := b.regions_scalar (mode := .borrowed) (store := store) (Ty.scalar_pair h).2
        (ws.drop a.width) p.2
      simp only [Ty.regions] at ha hb
      rw [ha, hb]; rfl
    · exact Ty.blocks_scalar _ h ws p
  | .array, h, _, _ => absurd h (by decide)

theorem Ty.reads_scalar :
    (t : Ty) → t.scalar = true → (ws : List Value) → (v : t.denote) → t.reads ws v = []
  | .word, _, _, _ | .bool, _, _, _ => rfl
  | .pair a b, h, ws, p => by
    simp only [Ty.reads, a.reads_scalar (Ty.scalar_pair h).1 _ p.1,
      b.reads_scalar (Ty.scalar_pair h).2 _ p.2, List.append_nil]
  | .array, h, _, _ => absurd h (by decide)

theorem Ty.pointers_scalar : (t : Ty) → t.scalar = true → (ws : List Value) → t.pointers ws = []
  | .word, _, _ | .bool, _, _ => rfl
  | .pair a b, h, ws => by
    simp only [Ty.pointers, a.pointers_scalar (Ty.scalar_pair h).1,
      b.pointers_scalar (Ty.scalar_pair h).2, List.append_nil]
  | .array, h, _ => absurd h (by decide)

/-- A value's blocks are those at its arrays' addresses. -/
theorem Ty.blocks_pointers {store : Store Unit} :
    (t : Ty) → (ws : List Value) → (v : t.denote) →
      t.blocks store ws v = (t.pointers ws).map (block store)
  | .word, _, _ | .bool, _, _ => rfl
  | .pair a b, ws, p => by
    simp only [Ty.blocks, Ty.pointers, List.map_append, a.blocks_pointers, b.blocks_pointers]
  | .array, ws, _ => by
    simp only [Ty.blocks, Ty.pointers]
    split <;> rfl

/-- The blocks of an owned value are pairwise disjoint. -/
theorem Ty.Rep.pairwise {heap : Heap} {store : Store Unit} :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep .owned heap store ws v →
      (t.blocks store ws v).Pairwise regionsDisjoint
  | .word, _, _, _ | .bool, _, _, _ => List.Pairwise.nil
  | .pair _ _, _, _, ⟨first, second, h, h1, h2, hd⟩ => by
    subst h
    rw [Ty.blocks_append h1.length]
    exact List.pairwise_append.mpr ⟨h1.pairwise, h2.pairwise, hd rfl⟩
  | .array, _, _, ⟨_, h, _⟩ => by subst h; simp [Ty.blocks]

/-- A region apart from a value's regions lies apart from its arrays' words. -/
theorem Ty.Rep.reads_apart {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      ∀ r, (∀ c ∈ t.regions mode store ws v, regionsDisjoint r c) →
      ∀ c ∈ t.reads ws v, regionsDisjoint r c
  | .word, _, _, _, _, _, _, hc | .bool, _, _, _, _, _, _, hc => by simp [Ty.reads] at hc
  | .pair _ _, _, _, ⟨first, second, h, h1, h2, _⟩, r, hr, c, hc => by
    subst h
    rw [Ty.reads_append h1.length] at hc
    rw [Ty.regions_append h1.length] at hr
    rcases List.mem_append.mp hc with hc | hc
    · exact h1.reads_apart r (fun c' h' => hr c' (List.mem_append_left _ h')) c hc
    · exact h2.reads_apart r (fun c' h' => hr c' (List.mem_append_right _ h')) c hc
  | .array, _, _, ⟨ptr, h, ha⟩, r, hr, c, hc => by
    subst h
    simp only [Ty.reads, List.mem_singleton] at hc
    subst hc
    cases mode
    · exact hr _ (by simp [Ty.regions, Ty.reads])
    · have := hr (block store ptr) (by simp [Ty.regions, Ty.blocks])
      exact regionsDisjoint_symm (Heap.Owned.region_apart ha (regionsDisjoint_symm this))

/-- A value read where a borrowed one suffices. -/
theorem Ty.Rep.borrow {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      t.Rep .borrowed heap store ws v
  | .word, _, _, h | .bool, _, _, h => h
  | .pair _ _, _, _, ⟨first, second, h, h1, h2, _⟩ =>
    ⟨first, second, h, h1.borrow, h2.borrow, nofun⟩
  | .array, _, _, ⟨ptr, h, ha⟩ => ⟨ptr, h, ha.borrow⟩

/-- A value whose type holds no arrays has the same words in either mode. -/
theorem Ty.Rep.owned {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → t.scalar = true → {ws : List Value} → {v : t.denote} →
      t.Rep mode heap store ws v → t.Rep .owned heap store ws v
  | .word, _, _, _, h | .bool, _, _, _, h => h
  | .pair a _, hs, _, _, ⟨first, second, h, h1, h2, _⟩ =>
    ⟨first, second, h, h1.owned (Ty.scalar_pair hs).1, h2.owned (Ty.scalar_pair hs).2,
      fun _ x hx => by rw [a.blocks_scalar (Ty.scalar_pair hs).1] at hx; exact nomatch hx⟩
  | .array, hs, _, _, _ => absurd hs (by decide)

/-- The words of the values of a context, in order, the value of variable `i` held in mode
`modes i`. -/
def Env.Rep (modes : Nat → Mode) (heap : Heap) (store : Store Unit) :
    {Γ : List Ty} → List Value → Env Γ → Prop
  | _, ws, .nil => ws = []
  | _, ws, .cons (t := t) v env =>
    ∃ first rest, ws = first ++ rest ∧ t.Rep (modes 0) heap store first v ∧
      Env.Rep (fun i => modes (i + 1)) heap store rest env

/-- The addresses of the arrays of the owned values among the words `ws` of a context's values,
in order. -/
def Env.moves (modes : Nat → Mode) : {Γ : List Ty} → List Value → Env Γ → List UInt64
  | _, _, .nil => []
  | _, ws, .cons (t := t) _ env =>
    (match modes 0 with
      | .owned => t.pointers (ws.take t.width)
      | .borrowed => []) ++ Env.moves (fun i => modes (i + 1)) (ws.drop t.width) env

/-- The regions of the arrays of the borrowed values among the words `ws` of a context's values,
in order. -/
def Env.reads (modes : Nat → Mode) : {Γ : List Ty} → List Value → Env Γ → List (Nat × Nat)
  | _, _, .nil => []
  | _, ws, .cons (t := t) v env =>
    (match modes 0 with
      | .owned => []
      | .borrowed => t.reads (ws.take t.width) v) ++
      Env.reads (fun i => modes (i + 1)) (ws.drop t.width) env

theorem Env.moves_cons {modes : Nat → Mode} {t : Ty} {Γ : List Ty} {v : t.denote} {env : Env Γ}
    {first rest : List Value} (h : first.length = t.width) :
    Env.moves modes (first ++ rest) (.cons v env) =
      (match modes 0 with
        | .owned => t.pointers first
        | .borrowed => []) ++ Env.moves (fun i => modes (i + 1)) rest env := by
  simp [Env.moves, ← h]

theorem Env.reads_cons {modes : Nat → Mode} {t : Ty} {Γ : List Ty} {v : t.denote} {env : Env Γ}
    {first rest : List Value} (h : first.length = t.width) :
    Env.reads modes (first ++ rest) (.cons v env) =
      (match modes 0 with
        | .owned => []
        | .borrowed => t.reads first v) ++ Env.reads (fun i => modes (i + 1)) rest env := by
  simp [Env.reads, ← h]

theorem widthSum_cons (t : Ty) (ts : List Ty) : widthSum (t :: ts) = t.width + widthSum ts := by
  simp [widthSum]

theorem Env.Rep.length {modes : Nat → Mode} {heap : Heap} {store : Store Unit} :
    {Γ : List Ty} → {ws : List Value} → {env : Env Γ} → Env.Rep modes heap store ws env →
      ws.length = widthSum Γ
  | _, _, .nil, h => by subst h; rfl
  | _, _, .cons _ _, h => by
    obtain ⟨_, _, h, h1, h2⟩ := h
    subst h; simp [widthSum_cons, h1.length, h2.length]

/-- How the verified compiler passes arguments: as the words of their values, each held in the
mode that `paramMode Γ ms` gives.  The call reads the borrowed values' arrays and consumes the
owned values' arrays. -/
@[instance_reducible] def Env.represent (Γ : List Ty) (ms : List Mode) : Represent (Env Γ) where
  width _ := widthSum Γ
  borrowed heap store vs env := Env.Rep (paramMode Γ ms) heap store vs env
  owned heap store vs env := Env.Rep (paramMode Γ ms) heap store vs env
  blocks _ _ _ := []
  reads _ vs env := Env.reads (paramMode Γ ms) vs env
  moves _ vs env := Env.moves (paramMode Γ ms) vs env

/-- How the verified compiler returns a value: as its words, owned by the caller. -/
@[instance_reducible] def Ty.represent (t : Ty) : Represent t.denote where
  width _ := t.width
  borrowed heap store vs v := t.Rep .borrowed heap store vs v
  owned heap store vs v := t.Rep .owned heap store vs v
  blocks store vs v := t.blocks store vs v
  reads _ _ _ := []
  moves _ _ _ := []

/-- A step from `heap` at `store` to `heap'` at `store'`: the allocator invariant holds after it,
the memory caps are unchanged, and every region of `heap` in `keep` keeps its bytes, is a region
of `heap'`, and lies apart from the blocks `fresh`.  The regions outside `keep` are those of the
blocks that the step consumes. -/
structure Step (heap : Heap) (store : Store Unit) (keep : Nat × Nat → Prop) (heap' : Heap)
    (store' : Store Unit) (fresh : List (Nat × Nat)) : Prop where
  at_ : heap'.At store'
  caps : store'.memoryCaps = store.memoryCaps
  keeps : ∀ r, heap.Region r → 0 < r.2 → keep r →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store'.mem.bytes a = store.mem.bytes a) ∧
      heap'.Region r ∧ ∀ b ∈ fresh, regionsDisjoint r b

namespace Step

variable {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit}
  {keep keep1 keep2 : Nat × Nat → Prop} {fresh fresh1 fresh2 : List (Nat × Nat)}

theorem refl (h : heap.At store) (keep : Nat × Nat → Prop) : Step heap store keep heap store [] :=
  ⟨h, rfl, fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, nofun⟩⟩

/-- Two steps in a row, the second keeping what the first keeps and leaves apart from its
blocks. -/
theorem transBoth (h1 : Step heap store keep1 heap1 store1 fresh1)
    (h2 : Step heap1 store1 keep2 heap2 store2 fresh2)
    (hKeep : ∀ r, keep r → keep1 r ∧ ((∀ b ∈ fresh1, regionsDisjoint r b) → keep2 r)) :
    Step heap store keep heap2 store2 (fresh1 ++ fresh2) := by
  refine ⟨h2.at_, h2.caps.trans h1.caps, fun r hr hpos hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := hKeep r hk
  obtain ⟨hBytes1, hRegion1, hFresh1⟩ := h1.keeps r hr hpos hk1
  obtain ⟨hBytes2, hRegion2, hFresh2⟩ := h2.keeps r hRegion1 hpos (hk2 hFresh1)
  refine ⟨fun a hl hh => (hBytes2 a hl hh).trans (hBytes1 a hl hh), hRegion2, fun b hb => ?_⟩
  rcases List.mem_append.mp hb with hb | hb
  · exact hFresh1 b hb
  · exact hFresh2 b hb

theorem trans (h1 : Step heap store keep1 heap1 store1 fresh1)
    (h2 : Step heap1 store1 keep2 heap2 store2 fresh2)
    (hKeep : ∀ r, keep r → keep1 r ∧ ((∀ b ∈ fresh1, regionsDisjoint r b) → keep2 r)) :
    Step heap store keep heap2 store2 fresh2 :=
  let h := h1.transBoth h2 hKeep
  ⟨h.at_, h.caps, fun r hr hpos hk => by
    obtain ⟨hb, hreg, hf⟩ := h.keeps r hr hpos hk
    exact ⟨hb, hreg, fun b hb' => hf b (List.mem_append_right _ hb')⟩⟩

/-- A step for fewer kept regions and fewer fresh blocks. -/
theorem mono (h : Step heap store keep1 heap1 store1 fresh1) {keep' : Nat × Nat → Prop}
    {fresh' : List (Nat × Nat)} (hKeep : ∀ r, keep' r → keep1 r)
    (hFresh : ∀ b ∈ fresh', b ∈ fresh1) : Step heap store keep' heap1 store1 fresh' :=
  ⟨h.at_, h.caps, fun r hr hpos hk => by
    obtain ⟨hb, hreg, hf⟩ := h.keeps r hr hpos (hKeep r hk)
    exact ⟨hb, hreg, fun b hb' => hf b (hFresh b hb')⟩⟩

theorem cap (h : Step heap store keep heap1 store1 fresh) (m : Module) :
    store1.memoryCap m 0 = store.memoryCap m 0 := by
  simp [Store.memoryCap, h.caps]

theorem borrowed (h : Step heap store keep heap1 store1 fresh) {p : UInt64} {xs : Array UInt64}
    (hp : heap.Borrowed store p xs) (hk : keep (p.toNat, 8 * (xs.size + 1))) :
    heap1.Borrowed store1 p xs ∧ ∀ b ∈ fresh, regionsDisjoint (p.toNat, 8 * (xs.size + 1)) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := h.keeps _ hp.region (by show 0 < 8 * (xs.size + 1); omega) hk
  exact ⟨hp.keepIn h.at_ hBytes hRegion, hFresh⟩

theorem owned (h : Step heap store keep heap1 store1 fresh) {p : UInt64} {xs : Array UInt64}
    (hp : heap.Owned store p xs) (hk : keep (block store p)) :
    (heap1.Owned store1 p xs ∧ capacityAt store1 p = capacityAt store p) ∧
      ∀ b ∈ fresh, regionsDisjoint (block store p) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := h.keeps _ hp.region (by simp [block]) hk
  exact ⟨hp.keepIn h.at_ hBytes hRegion, hFresh⟩

end Step

/-- An array after a step that keeps its region: it is still held in its mode, its region is the
same, and the region lies apart from the step's fresh blocks. -/
theorem Mode.array.step {mode : Mode} {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)} {ptr : UInt64} {xs : Array UInt64}
    (hStep : Step heap store keep heap' store' fresh) (h : mode.array heap store ptr xs)
    (hKeep : ∀ r ∈ Ty.array.regions mode store [.i64 ptr] xs, keep r) :
    mode.array heap' store' ptr xs ∧
      Ty.array.regions mode store' [.i64 ptr] xs = Ty.array.regions mode store [.i64 ptr] xs ∧
      ∀ r ∈ Ty.array.regions mode store [.i64 ptr] xs, ∀ b ∈ fresh, regionsDisjoint r b := by
  cases mode
  · obtain ⟨h1, h2⟩ := hStep.borrowed h (hKeep _ (List.mem_singleton_self _))
    refine ⟨h1, rfl, fun r hr => ?_⟩
    rw [List.mem_singleton.mp hr]
    exact h2
  · obtain ⟨⟨h1, hCap⟩, h2⟩ := hStep.owned h (hKeep _ (List.mem_singleton_self _))
    refine ⟨h1, ?_, fun r hr => ?_⟩
    · simp [Ty.regions, Ty.blocks, block_eq hCap]
    · rw [List.mem_singleton.mp hr]
      exact h2

/-- A value after a step that keeps its regions: its words still represent it, its regions are
the same, and they lie apart from the step's fresh blocks. -/
theorem Ty.Rep.step {mode : Mode} {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (hStep : Step heap store keep heap' store' fresh) :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      (∀ r ∈ t.regions mode store ws v, keep r) →
      t.Rep mode heap' store' ws v ∧ t.regions mode store' ws v = t.regions mode store ws v ∧
        ∀ r ∈ t.regions mode store ws v, ∀ b ∈ fresh, regionsDisjoint r b
  | .word, _, _, h, _ => ⟨h, by cases mode <;> rfl, by cases mode <;> exact nofun⟩
  | .bool, _, _, h, _ => ⟨h, by cases mode <;> rfl, by cases mode <;> exact nofun⟩
  | .pair a b, _, p, ⟨first, second, rfl, h1, h2, hd⟩, hKeep => by
    have hl := h1.length
    rw [Ty.regions_append hl] at hKeep
    obtain ⟨r1, e1, f1⟩ := h1.step hStep fun r hr => hKeep r (List.mem_append_left _ hr)
    obtain ⟨r2, e2, f2⟩ := h2.step hStep fun r hr => hKeep r (List.mem_append_right _ hr)
    refine ⟨⟨first, second, rfl, r1, r2, fun hm x hx y hy => ?_⟩, ?_, ?_⟩
    · subst hm
      have e1' : a.blocks store' first p.1 = a.blocks store first p.1 := e1
      have e2' : b.blocks store' second p.2 = b.blocks store second p.2 := e2
      rw [e1'] at hx
      rw [e2'] at hy
      exact hd rfl x hx y hy
    · rw [Ty.regions_append hl, Ty.regions_append hl, e1, e2]
    · rw [Ty.regions_append hl]
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact f1 r hr
      · exact f2 r hr
  | .array, _, _, ⟨ptr, rfl, ha⟩, hKeep => by
    obtain ⟨h1, h2, h3⟩ := ha.step hStep hKeep
    exact ⟨⟨ptr, rfl, h1⟩, h2, h3⟩

theorem Ty.types_length : (t : Ty) → t.types.length = t.width
  | .word | .bool | .array => rfl
  | .pair a b => by simp [Ty.types, Ty.width, a.types_length, b.types_length]

theorem Ty.Rep.typed {mode : Mode} {heap : Heap} {store : Store Unit} {t : Ty} {ws : List Value}
    {v : t.denote} (h : t.Rep mode heap store ws v) : ws.length = t.types.length := by
  rw [Ty.types_length]; exact h.length

/-- Positions that hold two lists in a row hold each. -/
theorem LocalsHold.append {s : Locals} {loc : Nat} {tys1 tys2 : List ValueType}
    {first second : List Value} (hl : first.length = tys1.length) :
    LocalsHold s loc (tys1 ++ tys2) (first ++ second) ↔
      LocalsHold s loc tys1 first ∧ LocalsHold s (loc + first.length) tys2 second := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD] at this
    · have := h (first.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD] at this
      rw [Nat.add_assoc]
      simpa [hl] using this
  · rintro ⟨h1, h2⟩ k hk
    by_cases hk1 : k < first.length
    · rw [List.getElem_append_left hk1, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact h1 k hk1
    · rw [List.getElem_append_right (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), ← hl, ← List.getD_eq_getElem?_getD]
      have := h2 (k - first.length) (by simp at hk; omega)
      rw [show loc + first.length + (k - first.length) = loc + k by omega] at this
      exact this

/-- A position that holds one i64 word holds it in its own local. -/
theorem LocalsHold.word {s : Locals} {loc : Nat} {w : Value} (h : LocalsHold s loc [.i64] [w]) :
    s.get loc = some w := by
  simpa [slotIndex] using h 0 (by simp)

/-- Locals that agree below `base` hold the same words at positions below `base`. -/
theorem LocalsHold.frame {base : Nat} {s s' : Locals} (hF : Frame base s s') {loc : Nat}
    {tys : List ValueType} {ws : List Value} (hl : ws.length = tys.length)
    (hb : loc + tys.length ≤ base) : LocalsHold s' loc tys ws ↔ LocalsHold s loc tys ws := by
  have hSame : ∀ k < ws.length, ∀ ty,
      s'.get (slotIndex s'.half (loc + k) ty) = s.get (slotIndex s.half (loc + k) ty) := by
    intro k hk ty
    rw [hF.half]
    have := hF.below (loc + k) (by omega)
    cases ty <;> simp only [slotIndex] <;> first | exact this.1 | exact this.2
  constructor
  · intro hold k hk
    rw [← hSame k hk]
    exact hold k hk
  · intro hold k hk
    rw [hSame k hk]
    exact hold k hk

/-- Words at positions that a change of locals keeps stay held. -/
theorem LocalsHold.keep {s s' : Locals} {lo loc : Nat} {tys : List ValueType} {ws : List Value}
    (hold : LocalsHold s loc tys ws) (hHalf : s'.half = s.half)
    (hKeep : ∀ j, lo ≤ j → j < s.half →
      s'.get j = s.get j ∧ s'.get (j + s.half) = s.get (j + s.half))
    (hLo : lo ≤ loc) (hHi : loc + ws.length ≤ s.half) : LocalsHold s' loc tys ws := by
  intro k hk
  have ha := hKeep (loc + k) (by omega) (by omega)
  have hk' := hold k hk
  rw [hHalf]
  revert hk'
  cases tys.getD k .i64 <;> simp only [slotIndex] <;> intro hk' <;>
    first | (rw [ha.1]; exact hk') | (rw [ha.2]; exact hk')

/-- Positions that hold words of given types and length determine them. -/
theorem LocalsHold.unique {s : Locals} {loc : Nat} {tys : List ValueType} {ws1 ws2 : List Value}
    (h1 : LocalsHold s loc tys ws1) (h2 : LocalsHold s loc tys ws2)
    (hl : ws1.length = ws2.length) : ws1 = ws2 := by
  apply List.ext_getElem hl
  intro k hk1 hk2
  have := (h1 k hk1).symm.trans (h2 k hk2)
  exact Option.some.inj this

theorem Var.index_lt {Γ : List Ty} {t : Ty} (x : Var Γ t) : x.index < Γ.length := by
  induction x with
  | here => simp [Var.index]
  | there y ih => simp [Var.index]; omega

theorem Var.getElem?_index {Γ : List Ty} {t : Ty} : (x : Var Γ t) → Γ[x.index]? = some t
  | .here => rfl
  | .there x => by simp [Var.index, x.getElem?_index]

theorem Var.index_ofIndex : (Γ : List Ty) → (i : Nat) → {t : Ty} → (h : Γ[i]? = some t) →
    (Var.ofIndex Γ i h).index = i
  | _ :: _, 0, _, h => by simp at h; subst h; rfl
  | _ :: Γ, i + 1, _, h => by
    simp only [Var.ofIndex, Var.index]
    rw [Var.index_ofIndex Γ i]
  | [], _, _, h => by simp at h

/-- The facts about the variables live in `live`.  Each starts at its slot's local, its words end
below `base`, and its locals hold words that represent its value in its mode in `heap` at
`store`.  The blocks of a live owned variable lie apart from the regions of every other live
variable: from its blocks when it is owned and from its arrays when it is borrowed. -/
def Holds {Γ : List Ty} (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (base : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals) : Prop :=
  (∀ (t : Ty) (x : Var Γ t), live x.index = true →
    (slots.getD x.index default).loc + t.width ≤ base ∧
    ∃ ws, LocalsHold s (slots.getD x.index default).loc t.types ws ∧
      t.Rep (slots.getD x.index default).mode heap store ws (env.get x)) ∧
  ∀ (t u : Ty) (x : Var Γ t) (y : Var Γ u), live x.index = true → live y.index = true →
    x.index ≠ y.index → (slots.getD x.index default).mode = .owned →
    ∀ wx wy, LocalsHold s (slots.getD x.index default).loc t.types wx → wx.length = t.width →
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ b ∈ t.blocks store wx (env.get x),
        ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), regionsDisjoint b c

/-- A value lies apart from the variables live in `live`: its regions lie apart from those of
each live variable when either is owned. -/
def Holds.Apart {Γ : List Ty} (env : Env Γ) (slots : List Slot) (live : Nat → Bool)
    (store : Store Unit) (s : Locals) (t : Ty) (mode : Mode) (ws : List Value) (v : t.denote) :
    Prop :=
  ∀ (u : Ty) (y : Var Γ u), live y.index = true →
    (mode = .owned ∨ (slots.getD y.index default).mode = .owned) →
    ∀ wy, LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ b ∈ t.regions mode store ws v,
        ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), regionsDisjoint b c

/-- The region `r` lies apart from the blocks of the owned variables live in `liveIn` and not in
`liveOut`, those that die between the two. -/
def Holds.KeepDying {Γ : List Ty} (env : Env Γ) (slots : List Slot) (liveIn liveOut : Nat → Bool)
    (store : Store Unit) (s : Locals) (r : Nat × Nat) : Prop :=
  ∀ (t : Ty) (x : Var Γ t), liveIn x.index = true → liveOut x.index = false →
    (slots.getD x.index default).mode = .owned →
    ∀ wx, LocalsHold s (slots.getD x.index default).loc t.types wx → wx.length = t.width →
      ∀ b ∈ t.blocks store wx (env.get x), regionsDisjoint r b

namespace Holds

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool} {base : Nat}
  {heap : Heap} {store : Store Unit} {s : Locals}

/-- The words of a live variable. -/
theorem get (h : Holds env slots live base heap store s) {t : Ty} (x : Var Γ t)
    (hx : live x.index = true) :
    (slots.getD x.index default).loc + t.width ≤ base ∧
    ∃ ws, LocalsHold s (slots.getD x.index default).loc t.types ws ∧
      t.Rep (slots.getD x.index default).mode heap store ws (env.get x) :=
  h.1 t x hx

/-- `Holds` for fewer variables. -/
theorem live_mono (h : Holds env slots live base heap store s) {live' : Nat → Bool}
    (hLive : ∀ i, live' i = true → live i = true) : Holds env slots live' base heap store s :=
  ⟨fun t x hx => h.1 t x (hLive _ hx),
    fun t u x y hx hy => h.2 t u x y (hLive _ hx) (hLive _ hy)⟩

/-- `Holds` for fewer variables, compared on the indices of variables. -/
theorem live_mono' (h : Holds env slots live base heap store s) {live' : Nat → Bool}
    (hLive : ∀ i < Γ.length, live' i = true → live i = true) :
    Holds env slots live' base heap store s :=
  ⟨fun t x hx => h.1 t x (hLive _ x.index_lt hx),
    fun t u x y hx hy => h.2 t u x y (hLive _ x.index_lt hx) (hLive _ y.index_lt hy)⟩

theorem mono (h : Holds env slots live base heap store s) {base' : Nat} (hb : base ≤ base') :
    Holds env slots live base' heap store s :=
  ⟨fun t x hx => ⟨by have := (h.1 t x hx).1; omega, (h.1 t x hx).2⟩, h.2⟩

/-- Locals that agree below `base` hold the same words for a live variable. -/
theorem hold_agree (h : Holds env slots live base heap store s) {s' : Locals}
    (hF : Frame base s s') {t : Ty} {x : Var Γ t} (hx : live x.index = true)
    {ws : List Value} (hl : ws.length = t.width) :
    LocalsHold s' (slots.getD x.index default).loc t.types ws ↔
      LocalsHold s (slots.getD x.index default).loc t.types ws := by
  have hBelow := (h.1 t x hx).1
  have hSame : ∀ k < ws.length, ∀ ty,
      s'.get (slotIndex s'.half ((slots.getD x.index default).loc + k) ty) =
        s.get (slotIndex s.half ((slots.getD x.index default).loc + k) ty) := by
    intro k hk ty
    rw [hF.half]
    have := hF.below _ (show (slots.getD x.index default).loc + k < base by omega)
    cases ty <;> simp only [slotIndex] <;> first | exact this.1 | exact this.2
  constructor
  · intro hold k hk
    rw [← hSame k hk]
    exact hold k hk
  · intro hold k hk
    rw [hSame k hk]
    exact hold k hk

/-- `Holds` with a lower bound for the variables' locals, which another `Holds` gives. -/
theorem lower {base' : Nat} (h : Holds env slots live base' heap store s) {live0 : Nat → Bool}
    {heap0 : Heap} {store0 : Store Unit} {s0 : Locals}
    (h0 : Holds env slots live0 base heap0 store0 s0)
    (hLive : ∀ i, live i = true → live0 i = true) : Holds env slots live base heap store s :=
  ⟨fun t x hx => ⟨(h0.1 t x (hLive _ hx)).1, (h.1 t x hx).2⟩, h.2⟩

/-- `Holds` depends only on the locals below `base`. -/
theorem agree (h : Holds env slots live base heap store s) {s' : Locals}
    (hs : Frame base s s') : Holds env slots live base heap store s' := by
  refine ⟨fun t x hx => ?_, fun t u x y hx hy hxy hm wx wy hwx hlx hwy hly => ?_⟩
  · obtain ⟨hBelow, ws, hold, hRep⟩ := h.1 t x hx
    exact ⟨hBelow, ws, (h.hold_agree hs hx hRep.length).mpr hold, hRep⟩
  · exact h.2 t u x y hx hy hxy hm wx wy ((h.hold_agree hs hx hlx).mp hwx) hlx
      ((h.hold_agree hs hy hly).mp hwy) hly

theorem frame (h : Holds env slots live base heap store s) {base' : Nat} {s' : Locals}
    (hf : Frame base' s s') (hb : base ≤ base') : Holds env slots live base heap store s' :=
  h.agree (hf.mono hb)

theorem setLocal (h : Holds env slots live base heap store s) {i : Nat} {v : Value}
    (hi : base ≤ i) (hLow : s.params.length ≤ i) (hHigh : i < s.half) :
    Holds env slots live base heap store (Verified.setLocal s i v) :=
  h.agree (Frame.set hLow hi hHigh)

/-- The regions of each variable live in `live` lie apart from the blocks of the owned variables
that die between `liveIn` and `live`. -/
theorem keepDying {liveIn : Nat → Bool} (h : Holds env slots liveIn base heap store s)
    (hLive : ∀ i, live i = true → liveIn i = true) {u : Ty} {y : Var Γ u}
    (hy : live y.index = true) {wy : List Value}
    (hwy : LocalsHold s (slots.getD y.index default).loc u.types wy) (hly : wy.length = u.width) :
    ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y),
      KeepDying env slots liveIn live store s c := by
  intro c hc t x hx hxOut hm wx hwx hlx b hb
  have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hxOut; exact nomatch hxOut
  exact regionsDisjoint_symm (h.2 t u x y hx (hLive _ hy) hne hm wx wy hwx hlx hwy hly b hb c hc)

/-- `Holds` after a step that keeps the regions of the live variables. -/
theorem step (h : Holds env slots live base heap store s) {keep : Nat × Nat → Prop}
    {heap' : Heap} {store' : Store Unit} {fresh : List (Nat × Nat)}
    (hStep : Step heap store keep heap' store' fresh)
    (hKeep : ∀ (u : Ty) (y : Var Γ u), live y.index = true → ∀ wy,
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), keep c) :
    Holds env slots live base heap' store' s := by
  -- The regions of each live variable are the same after the step.
  have hSame : ∀ (u : Ty) (y : Var Γ u), live y.index = true → ∀ wy,
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      u.regions (slots.getD y.index default).mode store' wy (env.get y) =
        u.regions (slots.getD y.index default).mode store wy (env.get y) := by
    intro u y hy wy hwy hly
    obtain ⟨_, ws, hold, hRep⟩ := h.1 u y hy
    obtain rfl := LocalsHold.unique hwy hold (hly.trans hRep.length.symm)
    exact (hRep.step hStep (hKeep u y hy _ hwy hly)).2.1
  refine ⟨fun t x hx => ?_, fun t u x y hx hy hxy hm wx wy hwx hlx hwy hly b hb c hc => ?_⟩
  · obtain ⟨hBelow, ws, hold, hRep⟩ := h.1 t x hx
    exact ⟨hBelow, ws, hold, (hRep.step hStep (hKeep t x hx ws hold hRep.length)).1⟩
  · have hbx := hSame t x hx wx hwx hlx
    have hcy := hSame u y hy wy hwy hly
    simp only [Ty.regions, hm] at hbx
    rw [hbx] at hb
    rw [hcy] at hc
    exact h.2 t u x y hx hy hxy hm wx wy hwx hlx hwy hly b hb c hc

/-- A binding adds its value, in the locals from `base` on in mode `mode`, as variable 0, when
the value lies apart from the variables live in the body. -/
theorem push {t : Ty} {v : t.denote} {mode : Mode} {live' : Nat → Bool}
    (h : Holds env slots (fun i => live' (i + 1)) base heap store s) {ws : List Value}
    (hold : LocalsHold s base t.types ws) (hRep : t.Rep mode heap store ws v)
    (hApart : Holds.Apart env slots (fun i => live' (i + 1)) store s t mode ws v) :
    Holds (Env.cons v env) (⟨base, mode⟩ :: slots) live' (base + t.width) heap store s := by
  refine ⟨fun t' x hx => ?_, fun t1 t2 x y hx hy hxy hm wx wy hwx hlx hwy hly => ?_⟩
  · cases x with
    | here => exact ⟨by simp [Var.index], ws, by simpa [Var.index] using hold,
        by simpa [Var.index, Env.get] using hRep⟩
    | there y =>
      simp only [Var.index, Env.get, List.getD_cons_succ]
      obtain ⟨hBelow, rest⟩ := h.1 _ y hx
      exact ⟨by omega, rest⟩
  · cases x with
    | here =>
      cases y with
      | here => exact absurd rfl hxy
      | there y =>
        change mode = .owned at hm
        change LocalsHold s base t.types wx at hwx
        change LocalsHold s (slots.getD y.index default).loc t2.types wy at hwy
        obtain rfl := LocalsHold.unique hwx hold (hlx.trans hRep.length.symm)
        subst hm
        exact hApart _ y hy (Or.inl rfl) wy hwy hly
    | there x =>
      cases y with
      | here =>
        change (slots.getD x.index default).mode = .owned at hm
        change LocalsHold s (slots.getD x.index default).loc t1.types wx at hwx
        change LocalsHold s base t.types wy at hwy
        obtain rfl := LocalsHold.unique hwy hold (hly.trans hRep.length.symm)
        intro b hb c hc
        have hRegions : t1.regions (slots.getD x.index default).mode store wx (env.get x) =
            t1.blocks store wx (env.get x) := by rw [hm]; rfl
        exact regionsDisjoint_symm (hApart _ x hx (Or.inr hm) wx hwx hlx c hc b
          (hRegions ▸ hb))
      | there y =>
        change (slots.getD x.index default).mode = .owned at hm
        change LocalsHold s (slots.getD x.index default).loc t1.types wx at hwx
        change LocalsHold s (slots.getD y.index default).loc t2.types wy at hwy
        exact h.2 t1 t2 x y hx hy (fun he => hxy (by simp [Var.index, he])) hm wx wy hwx hlx hwy
          hly

/-- The facts about the variables of a context without its first variable. -/
theorem pop {t : Ty} {v : t.denote} {sl : Slot} {live' : Nat → Bool}
    (h : Holds (Env.cons v env) (sl :: slots) live' base heap store s) :
    Holds env slots (fun i => live' (i + 1)) base heap store s :=
  ⟨fun t' x hx => h.1 t' (.there x) hx,
    fun t1 t2 x y hx hy hxy hm => h.2 t1 t2 (.there x) (.there y) hx hy
      (fun he => hxy (Nat.succ.inj he)) hm⟩

/-- The regions of a live variable after a step that keeps them are the same, and the variable
still holds its value. -/
theorem regions_after (h : Holds env slots live base heap store s) {keep : Nat × Nat → Prop}
    {heap' : Heap} {store' : Store Unit} {fresh : List (Nat × Nat)}
    (hStep : Step heap store keep heap' store' fresh) {u : Ty} {y : Var Γ u}
    (hy : live y.index = true) {wy : List Value}
    (hwy : LocalsHold s (slots.getD y.index default).loc u.types wy) (hly : wy.length = u.width)
    (hKeep : ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), keep c) :
    u.regions (slots.getD y.index default).mode store' wy (env.get y) =
        u.regions (slots.getD y.index default).mode store wy (env.get y) ∧
      ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y),
        ∀ b ∈ fresh, regionsDisjoint c b := by
  obtain ⟨_, ws, hold, hRep⟩ := h.1 u y hy
  obtain rfl := LocalsHold.unique hwy hold (hly.trans hRep.length.symm)
  obtain ⟨-, h2, h3⟩ := hRep.step hStep hKeep
  exact ⟨h2, h3⟩

end Holds

/-- The blocks that a value occupies when owned, and none when borrowed: those that its holder
must consume. -/
def Mode.fresh (mode : Mode) (store : Store Unit) (t : Ty) (ws : List Value) (v : t.denote) :
    List (Nat × Nat) :=
  match mode with
  | .owned => t.blocks store ws v
  | .borrowed => []

namespace Holds

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool} {base : Nat}
  {heap : Heap} {store : Store Unit} {s : Locals}

/-- `Holds` for live sets that agree on the indices of variables. -/
theorem congr_live (h : Holds env slots live base heap store s) {live' : Nat → Bool}
    (hL : ∀ i < Γ.length, live' i = true → live i = true) :
    Holds env slots live' base heap store s :=
  h.live_mono' hL

theorem KeepDying.congr {liveIn liveOut liveIn' liveOut' : Nat → Bool} {r : Nat × Nat}
    (h : KeepDying env slots liveIn liveOut store s r)
    (hSub : ∀ i < Γ.length, liveIn' i = true → liveOut' i = false →
      liveIn i = true ∧ liveOut i = false) :
    KeepDying env slots liveIn' liveOut' store s r :=
  fun t x hx hxo hm => let ⟨a, b⟩ := hSub _ x.index_lt hx hxo; h t x a b hm

theorem Apart.live_mono {t : Ty} {mode : Mode} {ws : List Value} {v : t.denote}
    (h : Holds.Apart env slots live store s t mode ws v) {live' : Nat → Bool}
    (hLive : ∀ i, live' i = true → live i = true) :
    Holds.Apart env slots live' store s t mode ws v :=
  fun u y hy => h u y (hLive _ hy)

/-- A value apart from the variables of a context is apart from those after its first. -/
theorem Apart.pop {t u : Ty} {v : u.denote} {sl : Slot} {live' : Nat → Bool} {mode : Mode}
    {ws : List Value} {w : t.denote}
    (h : Holds.Apart (Env.cons v env) (sl :: slots) live' store s t mode ws w) :
    Holds.Apart env slots (fun i => live' (i + 1)) store s t mode ws w :=
  fun u y hy => h u (.there y) hy

/-- A value without arrays lies apart from every variable. -/
theorem Apart.ofScalar {t : Ty} {mode : Mode} {ws : List Value} {v : t.denote}
    (h : t.scalar = true) : Holds.Apart env slots live store s t mode ws v :=
  fun _ _ _ _ _ _ _ b hb => by rw [Ty.regions_scalar t h] at hb; exact nomatch hb

/-- A pair apart from the live variables has each component apart from them. -/
theorem Apart.fst {a b : Ty} {mode : Mode} {first second : List Value}
    {p : a.denote × b.denote}
    (h : Holds.Apart env slots live store s (.pair a b) mode (first ++ second) p)
    (hl : first.length = a.width) : Holds.Apart env slots live store s a mode first p.1 :=
  fun u y hy hm wy hwy hly x hx c hc => h u y hy hm wy hwy hly x
    (by rw [Ty.regions_append hl]; exact List.mem_append_left _ hx) c hc

theorem Apart.snd {a b : Ty} {mode : Mode} {first second : List Value}
    {p : a.denote × b.denote}
    (h : Holds.Apart env slots live store s (.pair a b) mode (first ++ second) p)
    (hl : first.length = a.width) : Holds.Apart env slots live store s b mode second p.2 :=
  fun u y hy hm wy hwy hly x hx c hc => h u y hy hm wy hwy hly x
    (by rw [Ty.regions_append hl]; exact List.mem_append_right _ hx) c hc

/-- A value apart from the variables of a context and from a new variable 0, in the locals from
`loc` on in mode `mv`, is apart from the variables of the context with it. -/
theorem Apart.push {t u : Ty} {v : u.denote} {loc : Nat} {mv mode : Mode} {live' : Nat → Bool}
    {ws wv : List Value} {w : t.denote}
    (h : Holds.Apart env slots (fun i => live' (i + 1)) store s t mode ws w)
    (hold : LocalsHold s loc u.types wv) (hl : wv.length = u.width)
    (hHere : mode = .owned ∨ mv = .owned →
      ∀ b ∈ t.regions mode store ws w, ∀ c ∈ u.regions mv store wv v, regionsDisjoint b c) :
    Holds.Apart (Env.cons v env) (⟨loc, mv⟩ :: slots) live' store s t mode ws w := by
  intro u' y hy hm wy hwy hly
  cases y with
  | here =>
    change LocalsHold s loc u.types wy at hwy
    obtain rfl := LocalsHold.unique hwy hold (hly.trans hl.symm)
    exact hHere hm
  | there y => exact h u' y hy hm wy hwy hly

/-- A value apart from the live variables stays apart in locals that agree below `base`. -/
theorem Apart.agree (h : Holds env slots live base heap store s) {t : Ty} {mode : Mode}
    {ws : List Value} {v : t.denote} (hApart : Holds.Apart env slots live store s t mode ws v)
    {s' : Locals} (hs : Frame base s s') :
    Holds.Apart env slots live store s' t mode ws v :=
  fun u y hy hm wy hwy hly => hApart u y hy hm wy ((h.hold_agree hs hy hly).mp hwy) hly

/-- Every region lies apart from the blocks of the variables that die where none dies. -/
theorem KeepDying.none {live : Nat → Bool} {r : Nat × Nat} :
    KeepDying env slots live live store s r :=
  fun _ _ hx hxo => by rw [hx] at hxo; exact nomatch hxo

theorem KeepDying.mono {liveIn liveOut liveIn' liveOut' : Nat → Bool} {r : Nat × Nat}
    (h : KeepDying env slots liveIn liveOut store s r)
    (hSub : ∀ i, liveIn' i = true → liveOut' i = false → liveIn i = true ∧ liveOut i = false) :
    KeepDying env slots liveIn' liveOut' store s r :=
  fun t x hx hxo hm => let ⟨a, b⟩ := hSub _ hx hxo; h t x a b hm

/-- The facts that carry from a state to the one after a subexpression's step: when the step
keeps the regions of the variables live after it, those regions are unchanged.  So a region
apart from the blocks of variables that die later is apart from them in either state. -/
theorem KeepDying.transfer (h : Holds env slots live base heap store s)
    {liveIn liveOut liveMid : Nat → Bool} {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    {fresh : List (Nat × Nat)}
    (hStep : Step heap store (KeepDying env slots live liveMid store s) heap1 store1 fresh)
    (hFrame : Frame base s s1) (hMid : ∀ i, liveMid i = true → live i = true)
    (hSub : ∀ i, liveIn i = true → liveOut i = false → liveMid i = true) {r : Nat × Nat}
    (hr : KeepDying env slots liveIn liveOut store s r) :
    KeepDying env slots liveIn liveOut store1 s1 r := by
  intro t x hx hxo hm wx hwx hlx b hb
  have hxMid := hSub _ hx hxo
  have hwx' := (h.live_mono hMid |>.hold_agree hFrame hxMid hlx).mp hwx
  have hSame := (h.regions_after hStep (hMid _ hxMid) hwx' hlx
    (h.keepDying hMid hxMid hwx' hlx)).1
  simp only [Ty.regions, hm] at hSame
  rw [hSame] at hb
  exact hr t x hx hxo hm wx hwx' hlx b hb

/-- A value apart from the live variables stays apart after a step that keeps its regions and
theirs. -/
theorem Apart.transfer (h : Holds env slots live base heap store s) {t : Ty} {mode : Mode}
    {ws : List Value} {v : t.denote} (hApart : Holds.Apart env slots live store s t mode ws v)
    {keep : Nat × Nat → Prop} {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    {fresh : List (Nat × Nat)} (hStep : Step heap store keep heap1 store1 fresh)
    (hFrame : Frame base s s1)
    (hKeep : ∀ (u : Ty) (y : Var Γ u), live y.index = true → ∀ wy,
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), keep c)
    (hSame : t.regions mode store1 ws v = t.regions mode store ws v) :
    Holds.Apart env slots live store1 s1 t mode ws v := by
  intro u y hy hm wy hwy hly b hb c hc
  have hwy' := (h.hold_agree hFrame hy hly).mp hwy
  have := (h.regions_after hStep hy hwy' hly (hKeep u y hy wy hwy' hly)).1
  rw [this] at hc
  rw [hSame] at hb
  exact hApart u y hy hm wy hwy' hly b hb c hc

end Holds


/-! The instances that Lean synthesizes for the source types, rebuilt by recursion over `Ty`, and
their agreement with the verified compiler's representation.  A function's theorem for Lean's
types follows from them, for every signature, without a proof per signature. -/

/-- The `Scalar` instance that Lean synthesizes for a type without arrays. -/
@[instance_reducible] def Ty.scalarInst : (t : Ty) → t.scalar = true → Scalar t.denote
  | .word, _ => instScalarUInt64
  | .bool, _ => @instScalarOfFlat Bool UInt64 instFlatBoolUInt64 instScalarUInt64
  | .pair a b, h => @instScalarProd a.denote b.denote (a.scalarInst (Ty.scalar_pair h).1)
      (b.scalarInst (Ty.scalar_pair h).2)
  | .array, h => absurd h (by decide)

/-- The `Represent` instance that Lean synthesizes for a type: the one from `Scalar` for a type
without arrays, and the instances for pairs and arrays otherwise. -/
@[instance_reducible] def Ty.leanInst : (t : Ty) → Represent t.denote
  | .word => @instRepresentOfScalar UInt64 instScalarUInt64
  | .bool => @instRepresentOfScalar Bool
      (@instScalarOfFlat Bool UInt64 instFlatBoolUInt64 instScalarUInt64)
  | .pair a b =>
    if h : (Ty.pair a b).scalar = true then
      @instRepresentOfScalar _ ((Ty.pair a b).scalarInst h)
    else @instRepresentProd _ _ a.leanInst b.leanInst
  | .array => instRepresentArrayUInt64

/-- The words of a value of a type without arrays. -/
theorem Ty.scalar_rep {mode : Mode} {heap : Heap} {store : Store Unit} :
    (t : Ty) → (h : t.scalar = true) → {ws : List Value} → {v : t.denote} →
      (ws = @Scalar.values _ (t.scalarInst h) v ↔ t.Rep mode heap store ws v)
  | .word, _, _, _ | .bool, _, _, _ => Iff.rfl
  | .pair a b, h, ws, p => by
    constructor
    · rintro rfl
      exact ⟨_, _, rfl, (a.scalar_rep (Ty.scalar_pair h).1).mp rfl,
        (b.scalar_rep (Ty.scalar_pair h).2).mp rfl, fun _ x hx => by
          rw [a.blocks_scalar (Ty.scalar_pair h).1] at hx; exact nomatch hx⟩
    · rintro ⟨first, second, rfl, h1, h2, -⟩
      rw [(a.scalar_rep (Ty.scalar_pair h).1).mpr h1, (b.scalar_rep (Ty.scalar_pair h).2).mpr h2]
      rfl
  | .array, h, _, _ => absurd h (by decide)

theorem Ty.leanInst_scalar : (t : Ty) → (h : t.scalar = true) →
    t.leanInst = @instRepresentOfScalar _ (t.scalarInst h)
  | .word, _ | .bool, _ => rfl
  | .pair _ _, h => by rw [Ty.leanInst, dite_eq_left h]
  | .array, h => absurd h (by decide)

/-- Lean's instance agrees with the verified compiler's representation of a borrowed value. -/
theorem Ty.leanInst_borrowed {heap : Heap} {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} →
      (@Represent.borrowed _ t.leanInst heap store ws v ↔ t.Rep .borrowed heap store ws v)
  | .word, _, _ | .bool, _, _ | .array, _, _ => Iff.rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h]
      exact (Ty.pair a b).scalar_rep h
    · rw [Ty.leanInst, dite_eq_right h]
      constructor
      · rintro ⟨first, second, rfl, h1, h2⟩
        exact ⟨first, second, rfl, a.leanInst_borrowed.mp h1, b.leanInst_borrowed.mp h2, nofun⟩
      · rintro ⟨first, second, rfl, h1, h2, -⟩
        exact ⟨first, second, rfl, a.leanInst_borrowed.mpr h1, b.leanInst_borrowed.mpr h2⟩

theorem Ty.scalarInst_length : (t : Ty) → (h : t.scalar = true) → (v : t.denote) →
    (@Scalar.values _ (t.scalarInst h) v).length = t.width
  | .word, _, _ | .bool, _, _ => rfl
  | .pair a b, h, p => by
    show (@Scalar.values _ (a.scalarInst (Ty.scalar_pair h).1) p.1 ++
      @Scalar.values _ (b.scalarInst (Ty.scalar_pair h).2) p.2).length = _
    rw [List.length_append, a.scalarInst_length, b.scalarInst_length]
    rfl
  | .array, h, _ => absurd h (by decide)

/-- Lean's instance gives a value the verified compiler's width. -/
theorem Ty.leanInst_width : (t : Ty) → (v : t.denote) → @Represent.width _ t.leanInst v = t.width
  | .word, _ | .bool, _ | .array, _ => rfl
  | .pair a b, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h]
      exact (Ty.pair a b).scalarInst_length h p
    · rw [Ty.leanInst, dite_eq_right h]
      show @Represent.width _ a.leanInst p.1 + @Represent.width _ b.leanInst p.2 = _
      rw [a.leanInst_width, b.leanInst_width]
      rfl

/-- Lean's instance gives a value the verified compiler's blocks. -/
theorem Ty.leanInst_blocks {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} →
      @Represent.blocks _ t.leanInst store ws v = t.blocks store ws v
  | .word, _, _ | .bool, _, _ | .array, _, _ => rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h, Ty.blocks_scalar _ h]
      rfl
    · rw [Ty.leanInst, dite_eq_right h]
      show @Represent.blocks _ a.leanInst store (ws.take (@Represent.width _ a.leanInst p.1)) p.1 ++
        @Represent.blocks _ b.leanInst store (ws.drop (@Represent.width _ a.leanInst p.1)) p.2 = _
      rw [a.leanInst_width, a.leanInst_blocks, b.leanInst_blocks]
      rfl

/-- Lean's instance agrees with the verified compiler's representation of an owned value. -/
theorem Ty.leanInst_owned {heap : Heap} {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} →
      (@Represent.owned _ t.leanInst heap store ws v ↔ t.Rep .owned heap store ws v)
  | .word, _, _ | .bool, _, _ | .array, _, _ => Iff.rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h]
      exact (Ty.pair a b).scalar_rep h
    · rw [Ty.leanInst, dite_eq_right h]
      constructor
      · rintro ⟨first, second, rfl, h1, h2, hd⟩
        refine ⟨first, second, rfl, a.leanInst_owned.mp h1, b.leanInst_owned.mp h2,
          fun _ x hx y hy => ?_⟩
        rw [← a.leanInst_blocks] at hx
        rw [← b.leanInst_blocks] at hy
        exact hd x hx y hy
      · rintro ⟨first, second, rfl, h1, h2, hd⟩
        refine ⟨first, second, rfl, a.leanInst_owned.mpr h1, b.leanInst_owned.mpr h2,
          fun x hx y hy => ?_⟩
        rw [a.leanInst_blocks] at hx
        rw [b.leanInst_blocks] at hy
        exact hd rfl x hx y hy

theorem Ty.leanInst_moves {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} → @Represent.moves _ t.leanInst store ws v = []
  | .word, _, _ | .bool, _, _ | .array, _, _ => rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h]
      rfl
    · rw [Ty.leanInst, dite_eq_right h]
      show @Represent.moves _ a.leanInst store _ p.1 ++
        @Represent.moves _ b.leanInst store _ p.2 = []
      rw [a.leanInst_moves, b.leanInst_moves]
      rfl

theorem Ty.leanInst_reads {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} →
      @Represent.reads _ t.leanInst store ws v = t.reads ws v
  | .word, _, _ | .bool, _, _ | .array, _, _ => rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h, Ty.reads_scalar _ h]
      rfl
    · rw [Ty.leanInst, dite_eq_right h]
      show @Represent.reads _ a.leanInst store (ws.take (@Represent.width _ a.leanInst p.1)) p.1 ++
        @Represent.reads _ b.leanInst store (ws.drop (@Represent.width _ a.leanInst p.1)) p.2 = _
      rw [a.leanInst_width, a.leanInst_reads, b.leanInst_reads]
      rfl

theorem Ty.paramMode_scalar : (t : Ty) → t.scalar = true → (m : Mode) → t.paramMode m = .borrowed
  | .word, _, _ | .bool, _, _ | .pair _ _, _, _ => rfl
  | .array, h, _ => absurd h (by decide)

/-- The Lean type of an argument of type `t` at a parameter for which the mode `m` was chosen:
`Moved` for an owned array. -/
abbrev Ty.argTy : Ty → Mode → Type
  | .array, .owned => Moved (Array UInt64)
  | t, _ => t.denote

/-- The value of an argument. -/
def Ty.argVal : (t : Ty) → (m : Mode) → t.argTy m → t.denote
  | .array, .owned, x => x.val
  | .array, .borrowed, x => x
  | .word, _, x | .bool, _, x | .pair _ _, _, x => x

/-- The `Represent` instance that Lean synthesizes for an argument. -/
@[instance_reducible] def Ty.argInst : (t : Ty) → (m : Mode) → Represent (t.argTy m)
  | .array, .owned => instRepresentMovedArrayUInt64
  | .array, .borrowed => Ty.leanInst .array
  | .word, _ => Ty.leanInst .word
  | .bool, _ => Ty.leanInst .bool
  | .pair a b, _ => Ty.leanInst (.pair a b)

/-- The `Scalar` instance that Lean synthesizes for an argument without arrays. -/
@[instance_reducible] def Ty.argScalarInst : (t : Ty) → (m : Mode) → t.scalar = true →
    Scalar (t.argTy m)
  | .word, _, h => Ty.scalarInst .word h
  | .bool, _, h => Ty.scalarInst .bool h
  | .pair a b, _, h => Ty.scalarInst (.pair a b) h
  | .array, _, h => absurd h (by decide)

theorem Ty.argScalar_values : (t : Ty) → (m : Mode) → (h : t.scalar = true) → (x : t.argTy m) →
    @Scalar.values _ (t.argScalarInst m h) x = @Scalar.values _ (t.scalarInst h) (t.argVal m x)
  | .word, _, _, _ | .bool, _, _, _ | .pair _ _, _, _, _ => rfl
  | .array, _, h, _ => absurd h (by decide)

theorem Ty.argInst_scalar : (t : Ty) → (m : Mode) → (h : t.scalar = true) →
    t.argInst m = @instRepresentOfScalar _ (t.argScalarInst m h)
  | .word, _, h | .bool, _, h | .pair _ _, _, h => Ty.leanInst_scalar _ h
  | .array, _, h => absurd h (by decide)

theorem Ty.argInst_width : (t : Ty) → (m : Mode) → (x : t.argTy m) →
    @Represent.width _ (t.argInst m) x = t.width
  | .array, .owned, _ | .array, .borrowed, _ => rfl
  | .word, _, x | .bool, _, x | .pair _ _, _, x => Ty.leanInst_width _ x

/-- Lean's instance for an argument agrees with the verified compiler's representation. -/
theorem Ty.argInst_borrowed {heap : Heap} {store : Store Unit} :
    (t : Ty) → (m : Mode) → {ws : List Value} → {x : t.argTy m} →
      (@Represent.borrowed _ (t.argInst m) heap store ws x ↔
        t.Rep (t.paramMode m) heap store ws (t.argVal m x))
  | .array, .owned, _, _ | .array, .borrowed, _, _ => Iff.rfl
  | .word, _, _, _ | .bool, _, _, _ | .pair _ _, _, _, _ => Ty.leanInst_borrowed _

theorem Ty.argInst_moves {store : Store Unit} :
    (t : Ty) → (m : Mode) → {ws : List Value} → {x : t.argTy m} →
      @Represent.moves _ (t.argInst m) store ws x =
        match t.paramMode m with
        | .owned => t.pointers ws
        | .borrowed => []
  | .array, .owned, _, _ | .array, .borrowed, _, _ => rfl
  | .word, _, _, _ | .bool, _, _, _ | .pair _ _, _, _, _ => Ty.leanInst_moves _

theorem Ty.argInst_reads {store : Store Unit} :
    (t : Ty) → (m : Mode) → {ws : List Value} → {x : t.argTy m} →
      @Represent.reads _ (t.argInst m) store ws x =
        match t.paramMode m with
        | .owned => []
        | .borrowed => t.reads ws (t.argVal m x)
  | .array, .owned, _, _ | .array, .borrowed, _, _ => rfl
  | .word, _, _, _ | .bool, _, _, _ | .pair _ _, _, _, _ => Ty.leanInst_reads _

/-- The Lean type of a function's arguments, for parameters of types `ps` for which the modes `ms`
were chosen: `Unit` for none, the argument's type for one, and the right-nested product of the
arguments' types for more. -/
abbrev argsTy : List Ty → List Mode → Type
  | [], _ => Unit
  | [t], ms => t.argTy (ms.headD .borrowed)
  | t :: u :: ts, ms => t.argTy (ms.headD .borrowed) × argsTy (u :: ts) ms.tail

/-- The `Scalar` instance that Lean synthesizes for arguments without arrays. -/
@[instance_reducible] def argsScalarInst : (ps : List Ty) → (ms : List Mode) →
    ps.all Ty.scalar = true → Scalar (argsTy ps ms)
  | [], _, _ => instScalarUnit
  | [t], _, h => t.argScalarInst _ (by simpa using h)
  | t :: u :: ts, ms, h =>
    @instScalarProd (t.argTy (ms.headD .borrowed)) (argsTy (u :: ts) ms.tail)
      (t.argScalarInst _ (by simp at h; exact h.1))
      (argsScalarInst (u :: ts) ms.tail (by simp at h ⊢; exact h.2))

/-- The `Represent` instance that Lean synthesizes for a function's arguments. -/
@[instance_reducible] def argsInst : (ps : List Ty) → (ms : List Mode) → Represent (argsTy ps ms)
  | [], _ => @instRepresentOfScalar Unit instScalarUnit
  | [t], ms => t.argInst (ms.headD .borrowed)
  | t :: u :: ts, ms =>
    if h : (t :: u :: ts).all Ty.scalar = true then
      @instRepresentOfScalar _ (argsScalarInst (t :: u :: ts) ms h)
    else @instRepresentProd _ _ (t.argInst (ms.headD .borrowed)) (argsInst (u :: ts) ms.tail)

/-- The values of a function's arguments, from Lean's argument tuple. -/
def Env.ofArgs : (ps : List Ty) → (ms : List Mode) → argsTy ps ms → Env ps
  | [], _, _ => .nil
  | [t], _, x => .cons (t.argVal _ x) .nil
  | t :: _ :: _, ms, x => .cons (t.argVal _ x.1) (Env.ofArgs _ ms.tail x.2)

theorem argsScalar_rep {heap : Heap} {store : Store Unit} :
    (ps : List Ty) → (ms : List Mode) → (h : ps.all Ty.scalar = true) → {ws : List Value} →
      {y : argsTy ps ms} →
      (ws = @Scalar.values _ (argsScalarInst ps ms h) y ↔
        Env.Rep (paramMode ps ms) heap store ws (Env.ofArgs ps ms y))
  | [], _, _, _, _ => Iff.rfl
  | [t], ms, h, ws, y => by
    have ht : t.scalar = true := by simpa using h
    rw [show (@Scalar.values _ (argsScalarInst [t] ms h) y) =
      @Scalar.values _ (t.argScalarInst _ ht) y from rfl, t.argScalar_values, t.scalar_rep ht]
    constructor
    · intro hy; exact ⟨ws, [], by simp, hy, rfl⟩
    · rintro ⟨first, rest, rfl, h1, rfl⟩; rw [List.append_nil]; exact h1
  | t :: u :: ts, ms, h, ws, y => by
    have ht : t.scalar = true := by simp at h; exact h.1
    have hv : @Scalar.values _ (argsScalarInst (t :: u :: ts) ms h) y =
        @Scalar.values _ (t.scalarInst ht) (t.argVal _ y.1) ++
          @Scalar.values _ (argsScalarInst (u :: ts) ms.tail (by simp at h ⊢; exact h.2)) y.2 := by
      rw [← t.argScalar_values _ ht]
      rfl
    rw [hv]
    constructor
    · rintro rfl
      exact ⟨_, _, rfl, (t.scalar_rep ht).mp rfl, (argsScalar_rep (u :: ts) ms.tail _).mp rfl⟩
    · rintro ⟨first, rest, rfl, h1, h2⟩
      rw [(t.scalar_rep ht).mpr h1, (argsScalar_rep (u :: ts) ms.tail _).mpr h2]

theorem argsInst_scalar : (ps : List Ty) → (ms : List Mode) → (h : ps.all Ty.scalar = true) →
    argsInst ps ms = @instRepresentOfScalar _ (argsScalarInst ps ms h)
  | [], _, _ => rfl
  | [t], _, h => t.argInst_scalar _ (by simpa using h)
  | _ :: _ :: _, _, h => by rw [argsInst, dite_eq_left h]

/-- Lean's instance for the arguments agrees with the verified compiler's representation. -/
theorem argsInst_borrowed {heap : Heap} {store : Store Unit} :
    (ps : List Ty) → (ms : List Mode) → {ws : List Value} → {y : argsTy ps ms} →
      (@Represent.borrowed _ (argsInst ps ms) heap store ws y ↔
        Env.Rep (paramMode ps ms) heap store ws (Env.ofArgs ps ms y))
  | [], _, _, _ => Iff.rfl
  | [t], ms, ws, y => by
    rw [show (@Represent.borrowed _ (argsInst [t] ms) heap store ws y) =
      @Represent.borrowed _ (t.argInst _) heap store ws y from rfl, t.argInst_borrowed]
    constructor
    · intro hy; exact ⟨ws, [], by simp, hy, rfl⟩
    · rintro ⟨first, rest, rfl, h1, rfl⟩; rw [List.append_nil]; exact h1
  | t :: u :: ts, ms, ws, y => by
    by_cases h : (t :: u :: ts).all Ty.scalar = true
    · rw [argsInst_scalar _ _ h]
      exact argsScalar_rep _ _ h
    · rw [argsInst, dite_eq_right h]
      constructor
      · rintro ⟨first, rest, rfl, h1, h2⟩
        exact ⟨first, rest, rfl, (t.argInst_borrowed _).mp h1,
          (argsInst_borrowed (u :: ts) ms.tail).mp h2⟩
      · rintro ⟨first, rest, rfl, h1, h2⟩
        exact ⟨first, rest, rfl, (t.argInst_borrowed _).mpr h1,
          (argsInst_borrowed (u :: ts) ms.tail).mpr h2⟩

theorem Env.moves_scalar : {ps : List Ty} → (ms : List Mode) → ps.all Ty.scalar = true →
    (ws : List Value) → (env : Env ps) → Env.moves (paramMode ps ms) ws env = []
  | [], _, _, _, .nil => rfl
  | t :: _, ms, h, ws, .cons _ env => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Env.moves, paramMode, paramModes, List.getD_cons_zero,
      t.paramMode_scalar h.1, List.nil_append]
    exact Env.moves_scalar ms.tail h.2 _ env

theorem Env.reads_scalar : {ps : List Ty} → (ms : List Mode) → ps.all Ty.scalar = true →
    (ws : List Value) → (env : Env ps) → Env.reads (paramMode ps ms) ws env = []
  | [], _, _, _, .nil => rfl
  | t :: _, ms, h, ws, .cons v env => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Env.reads, paramMode, paramModes, List.getD_cons_zero,
      t.paramMode_scalar h.1, t.reads_scalar h.1, List.nil_append]
    exact Env.reads_scalar ms.tail h.2 _ env

theorem argsInst_moves {store : Store Unit} :
    (ps : List Ty) → (ms : List Mode) → {ws : List Value} → {y : argsTy ps ms} →
      ws.length = widthSum ps →
      @Represent.moves _ (argsInst ps ms) store ws y =
        Env.moves (paramMode ps ms) ws (Env.ofArgs ps ms y)
  | [], _, _, _, _ => rfl
  | [t], ms, ws, y, hl => by
    rw [show (@Represent.moves _ (argsInst [t] ms) store ws y) =
      @Represent.moves _ (t.argInst _) store ws y from rfl, t.argInst_moves]
    simp only [Env.ofArgs, Env.moves, paramMode, paramModes, List.getD_cons_zero, List.append_nil]
    rw [List.take_of_length_le (show ws.length ≤ t.width by simp [widthSum] at hl; omega)]
  | t :: u :: ts, ms, ws, y, hl => by
    by_cases h : (t :: u :: ts).all Ty.scalar = true
    · rw [argsInst_scalar _ _ h, Env.moves_scalar _ h]
      rfl
    · rw [argsInst, dite_eq_right h]
      show @Represent.moves _ (t.argInst _) store
          (ws.take (@Represent.width _ (t.argInst _) y.1)) y.1 ++
        @Represent.moves _ (argsInst (u :: ts) ms.tail) store
          (ws.drop (@Represent.width _ (t.argInst _) y.1)) y.2 = _
      rw [t.argInst_width, t.argInst_moves, argsInst_moves (u :: ts) ms.tail
        (by rw [List.length_drop, hl, widthSum_cons]; omega)]
      rfl

theorem argsInst_reads {store : Store Unit} :
    (ps : List Ty) → (ms : List Mode) → {ws : List Value} → {y : argsTy ps ms} →
      ws.length = widthSum ps →
      @Represent.reads _ (argsInst ps ms) store ws y =
        Env.reads (paramMode ps ms) ws (Env.ofArgs ps ms y)
  | [], _, _, _, _ => rfl
  | [t], ms, ws, y, hl => by
    rw [show (@Represent.reads _ (argsInst [t] ms) store ws y) =
      @Represent.reads _ (t.argInst _) store ws y from rfl, t.argInst_reads]
    simp only [Env.ofArgs, Env.reads, paramMode, paramModes, List.getD_cons_zero, List.append_nil]
    rw [List.take_of_length_le (show ws.length ≤ t.width by simp [widthSum] at hl; omega)]
  | t :: u :: ts, ms, ws, y, hl => by
    by_cases h : (t :: u :: ts).all Ty.scalar = true
    · rw [argsInst_scalar _ _ h, Env.reads_scalar _ h]
      rfl
    · rw [argsInst, dite_eq_right h]
      show @Represent.reads _ (t.argInst _) store
          (ws.take (@Represent.width _ (t.argInst _) y.1)) y.1 ++
        @Represent.reads _ (argsInst (u :: ts) ms.tail) store
          (ws.drop (@Represent.width _ (t.argInst _) y.1)) y.2 = _
      rw [t.argInst_width, t.argInst_reads, argsInst_reads (u :: ts) ms.tail
        (by rw [List.length_drop, hl, widthSum_cons]; omega)]
      rfl

end Verified
