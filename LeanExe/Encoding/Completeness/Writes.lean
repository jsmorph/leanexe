import LeanExe.Encoding.Completeness.Modules
import LeanExe.Encoding.RoundTrip

/-! `Writes result bytes` states that an encoder's result is `bytes`.  The lemmas compose the bytes
of a module from the bytes of its parts, so that the kernel checks each part, such as one function
body, in its own theorem with memory bounded by that part (`encode_of_parts`).  `funcOk`,
`restOk`, and `codesOk` are the claims that `verified_compile` decides per function and for the
rest of the module, with the bytes from a native evaluation of the encoder (`encodeParts`). -/

namespace Wasm.Encoding

def Writes (result : Result relation value) (bytes : List UInt8) : Prop :=
  ∃ output, result = .ok output ∧ output.val = bytes

theorem writes_of_toOption {result : Result relation value} {bytes : List UInt8}
    (h : result.toOption.map (·.val) = some bytes) : Writes result bytes := by
  cases hr : result with
  | error e => simp [hr, Except.toOption] at h
  | ok o =>
      simp only [hr, Except.toOption, Option.map_some, Option.some.injEq] at h
      exact ⟨o, rfl, h⟩

theorem u32_writes (value : Nat) (bound : value < 2 ^ 32) :
    Writes (u32 value) (unsigned 32 value) := by
  simp only [Writes, u32, bound, dite_true]
  exact ⟨_, rfl, rfl⟩

/-- Each value writes the bytes at its position. -/
def AllWrite (encode : (value : α) → Result relation value) : List α → List (List UInt8) → Prop
  | [], [] => True
  | v :: vs, b :: bs => Writes (encode v) b ∧ AllWrite encode vs bs
  | _, _ => False

theorem items_writes (encode : (value : α) → Result relation value) :
    ∀ (values : List α) (bs : List (List UInt8)), AllWrite encode values bs →
      Writes (items encode values) bs.flatten
  | [], [], _ => ⟨_, rfl, rfl⟩
  | v :: vs, b :: bs, ⟨hab, h⟩ => by
      obtain ⟨first, hf, hfv⟩ := hab
      obtain ⟨rest, hr, hrv⟩ := items_writes encode vs bs h
      simp only [Writes, items, hf, hr]
      refine ⟨_, rfl, ?_⟩
      simp [hfv, hrv]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem vector_writes (encode : (value : α) → Result relation value) (values : List α)
    (bs : List (List UInt8)) (bound : values.length < 2 ^ 32)
    (h : AllWrite encode values bs) :
    Writes (vector encode values) (unsigned 32 values.length ++ bs.flatten) := by
  obtain ⟨count, hc, hcv⟩ := u32_writes values.length bound
  obtain ⟨body, hb, hbv⟩ := items_writes encode values bs h
  simp only [Writes, vector, hc, hb]
  refine ⟨_, rfl, ?_⟩
  simp [hcv, hbv]

theorem section_writes (id : UInt8) {result : Result relation value} {bytes : List UInt8}
    (h : Writes result bytes) (bound : bytes.length < 2 ^ 32) :
    Writes ((result >>= sectionBytes id : Except String _)) (id :: (unsigned 32 bytes.length ++ bytes)) := by
  obtain ⟨payload, hp, hpv⟩ := h
  obtain ⟨size, hs, hsv⟩ := u32_writes payload.val.length (by rw [hpv]; exact bound)
  rw [hp]
  show Writes (sectionBytes id payload) _
  simp only [Writes, sectionBytes, hs]
  refine ⟨_, rfl, ?_⟩
  simp [hsv, hpv]

/-- The module from the bytes of its sections. -/
theorem module_writes (m : Wasm.Module) (hshape : Spec.Shape m)
    (b1 b2 b3 b5 b6 b7 b10 bd : List UInt8)
    (h1 : Writes ((vector functionType m.types >>= sectionBytes 1 : Except String _)) b1)
    (h2 : Writes ((vector (importFunction m.types) m.imports >>= sectionBytes 2 : Except String _)) b2)
    (h3 : Writes ((vector (functionIndex m.types) m.funcs >>= sectionBytes 3 : Except String _)) b3)
    (h5 : Writes ((vector memory (Spec.memoryDecls m) >>= sectionBytes 5 : Except String _)) b5)
    (h6 : Writes ((vector global m.globals >>= sectionBytes 6 : Except String _)) b6)
    (h7 : Writes ((vector exportEntry (Spec.exports m) >>= sectionBytes 7 : Except String _)) b7)
    (h10 : Writes ((vector functionBody m.funcs >>= sectionBytes 10 : Except String _)) b10)
    (hd : Writes (dataSection (Spec.dataSegments m)) bd) :
    encode m = .ok ⟨([0, 97, 115, 109, 1, 0, 0, 0] ++ b1 ++ b2 ++ b3 ++ b5 ++ b6 ++ b7 ++ b10 ++
      bd).toArray⟩ := by
  obtain ⟨o1, e1, v1⟩ := h1
  obtain ⟨o2, e2, v2⟩ := h2
  obtain ⟨o3, e3, v3⟩ := h3
  obtain ⟨o5, e5, v5⟩ := h5
  obtain ⟨o6, e6, v6⟩ := h6
  obtain ⟨o7, e7, v7⟩ := h7
  obtain ⟨o10, e10, v10⟩ := h10
  obtain ⟨od, ed, vd⟩ := hd
  have hmod : ∃ out, module m = .ok out ∧ out.val = [0, 97, 115, 109, 1, 0, 0, 0] ++ o1.val ++
      o2.val ++ o3.val ++ o5.val ++ o6.val ++ o7.val ++ o10.val ++ od.val := by
    simp only [module, shape_produces m hshape, e1, e2, e3, e5, e6, e7, e10, ed]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨out, ho, hov⟩ := hmod
  unfold encode
  rw [ho]
  simp only [Except.map, hov, v1, v2, v3, v5, v6, v7, v10, vd]

/-- `AllWrite` from the facts at each index. -/
theorem allWrite_of_getElem! [Inhabited α] (encode : (value : α) → Result relation value) :
    ∀ (l : List α) (bs : List (List UInt8)), l.length = bs.length →
      (∀ k < l.length, Writes (encode l[k]!) bs[k]!) → AllWrite encode l bs
  | [], [], _, _ => trivial
  | a :: l, b :: bs, hlen, h =>
      ⟨h 0 (by simp),
        allWrite_of_getElem! encode l bs (by simpa using hlen)
          (fun k hk => h (k + 1) (by simp only [List.length_cons]; omega))⟩
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

theorem forall_lt_zero (P : Nat → Prop) : ∀ k < 0, P k :=
  fun k hk => absurd hk (Nat.not_lt_zero k)

theorem forall_lt_succ {P : Nat → Prop} {n : Nat} (h : ∀ k < n, P k) (hn : P n) :
    ∀ k < n + 1, P k := fun k hk => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | h'
  · exact h k h'
  · exact h' ▸ hn

/-- The claim per function: the body writes `b`, and its locals are within the decoder's limit. -/
def funcOk (f : Wasm.Function) (b : List UInt8) : Bool :=
  (functionBody f).toOption.map (·.val) == some b && decide (f.locals.length ≤ Decoder.maxLocals)

/-- The claim for the rest of the module: its shape and the six sections before the code as
`s`. -/
def restOk (m : Wasm.Module) (s : List (List UInt8)) : Bool :=
  (shape m).isOk &&
    ((vector functionType m.types : Except String _) >>= sectionBytes 1).toOption.map (·.val) == some (s.getD 0 []) &&
    ((vector (importFunction m.types) m.imports : Except String _) >>= sectionBytes 2).toOption.map (·.val) ==
      some (s.getD 1 []) &&
    ((vector (functionIndex m.types) m.funcs : Except String _) >>= sectionBytes 3).toOption.map (·.val) ==
      some (s.getD 2 []) &&
    ((vector memory (Spec.memoryDecls m) : Except String _) >>= sectionBytes 5).toOption.map (·.val) ==
      some (s.getD 3 []) &&
    ((vector global m.globals : Except String _) >>= sectionBytes 6).toOption.map (·.val) == some (s.getD 4 []) &&
    ((vector exportEntry (Spec.exports m) : Except String _) >>= sectionBytes 7).toOption.map (·.val) ==
      some (s.getD 5 [])

/-- The claim for the data section. -/
def dataOk (m : Wasm.Module) (d : List UInt8) : Bool :=
  (dataSection (Spec.dataSegments m)).toOption.map (·.val) == some d

/-- The payload of the code section from the bodies. -/
def codePayload (bodies : List (List UInt8)) : List UInt8 :=
  unsigned 32 bodies.length ++ bodies.flatten

/-- The bounds that the code section needs. -/
def codesOk (bodies : List (List UInt8)) : Bool :=
  decide (bodies.length < 2 ^ 32) && decide ((codePayload bodies).length < 2 ^ 32)

/-- The bytes of a module from its parts. -/
def assemble (s : List (List UInt8)) (bodies : List (List UInt8)) (d : List UInt8) : List UInt8 :=
  [0, 97, 115, 109, 1, 0, 0, 0] ++ s.getD 0 [] ++ s.getD 1 [] ++ s.getD 2 [] ++ s.getD 3 [] ++
    s.getD 4 [] ++ s.getD 5 [] ++
    (10 :: (unsigned 32 (codePayload bodies).length ++ codePayload bodies)) ++ d

theorem shape_of_isOk (m : Wasm.Module) (h : (shape m).isOk = true) : Spec.Shape m := by
  cases hs : shape m with
  | error e => simp [hs, Except.isOk, Except.toBool] at h
  | ok p => exact p.down

/-- **The encoding from its parts**: the claims per function and for the rest of the module give
the bytes of `encode m` and the bound on the locals that `decode_encode` needs. -/
theorem encode_of_parts (m : Wasm.Module) (s bodies : List (List UInt8)) (d : List UInt8)
    (hrest : restOk m s = true) (hdata : dataOk m d = true) (hlen : m.funcs.length = bodies.length)
    (hcodes : codesOk bodies = true)
    (hfun : ∀ k < m.funcs.length, funcOk m.funcs[k]! bodies[k]! = true) :
    encode m = .ok ⟨(assemble s bodies d).toArray⟩ ∧
      ∀ f ∈ m.funcs, f.locals.length ≤ Decoder.maxLocals := by
  simp only [restOk, Bool.and_eq_true, beq_iff_eq] at hrest
  obtain ⟨⟨⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩ := hrest
  have hd : (dataSection (Spec.dataSegments m)).toOption.map (·.val) = some d := by
    simpa [dataOk] using hdata
  simp only [codesOk, Bool.and_eq_true, decide_eq_true_eq] at hcodes
  obtain ⟨hn, hp⟩ := hcodes
  have hw : ∀ k < m.funcs.length, Writes (functionBody m.funcs[k]!) bodies[k]! ∧
      m.funcs[k]!.locals.length ≤ Decoder.maxLocals := by
    intro k hk
    have := hfun k hk
    simp only [funcOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨writes_of_toOption this.1, this.2⟩
  have hF : AllWrite functionBody m.funcs bodies :=
    allWrite_of_getElem! functionBody m.funcs bodies hlen (fun k hk => (hw k hk).1)
  have h10 := section_writes 10 (vector_writes functionBody m.funcs bodies (by omega) hF)
    (by rw [hlen]; exact hp)
  rw [hlen] at h10
  refine ⟨?_, ?_⟩
  · have := module_writes m (shape_of_isOk m hs) _ _ _ _ _ _ _ _ (writes_of_toOption h1)
      (writes_of_toOption h2) (writes_of_toOption h3) (writes_of_toOption h5)
      (writes_of_toOption h6) (writes_of_toOption h7) h10 (writes_of_toOption hd)
    rw [this]
    rfl
  · intro f hf
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hf
    have := (hw k hk).2
    rwa [getElem!_pos m.funcs k hk] at this

/-- The bytes of the parts of `encode m`: the six sections before the code, the body of each
function, and the data section. -/
def encodeParts (m : Wasm.Module) :
    Except String (List (List UInt8) × List (List UInt8) × List UInt8) := do
  let s1 ← (vector functionType m.types : Except String _) >>= sectionBytes 1
  let s2 ← (vector (importFunction m.types) m.imports : Except String _) >>= sectionBytes 2
  let s3 ← (vector (functionIndex m.types) m.funcs : Except String _) >>= sectionBytes 3
  let s5 ← (vector memory (Spec.memoryDecls m) : Except String _) >>= sectionBytes 5
  let s6 ← (vector global m.globals : Except String _) >>= sectionBytes 6
  let s7 ← (vector exportEntry (Spec.exports m) : Except String _) >>= sectionBytes 7
  let bodies ← m.funcs.mapM fun f => (functionBody f).map (·.val)
  let d ← dataSection (Spec.dataSegments m)
  pure ([s1.val, s2.val, s3.val, s5.val, s6.val, s7.val], bodies, d.val)

end Wasm.Encoding
