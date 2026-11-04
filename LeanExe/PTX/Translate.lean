import LeanExe.PTX.Runs
import LeanExe.Source.Denote
import LeanExe.ProofKit.F32Canonical

/-!
The translation of source expressions and statements of words, Booleans, and binary32 values into
PTX statements, and its simulation lemmas.  A source word is the word of a `.b64` register, a
Boolean is the word 0 or 1, and a binary32 value is its bits, zero-extended.  A predicate holds only
the test of a branch or a loop, and a `.f32` register holds an operand or a result only inside the
code of one binary32 operation or comparison.  Each expression node writes a fresh register,
numbered from a counter that also numbers the `.b32`, `.f32`, and `.pred` registers that the node
uses.  `and`, `or`, and `ite` evaluate the selected operand in a branch, as the denotation does.
The code of a binary32 operation replaces a NaN result by `0x7fc00000`, which gives Talos's result
whatever NaN the device returns (`canonical_f32_bin`, `canonical_f32_sqrt`, and
`canonical_f32_nearest`).

From registers that hold the source locals and arrays as a `Layout` states, and an oracle whose
loads return the arrays' words, `trExpr_sim` states that an expression's code runs without
stopping and without stores, keeps the registers below the counter, and leaves the expression's
word in its result register.  `trStmt_sim` states that a statement's code runs the same way, keeps
the registers below the counter other than those of assigned locals, and leaves registers that
agree with the statement's new locals.
-/

namespace LeanExe.PTX

/-- Where the source values live: the `.b64` register of each word or binary32 local, the
registers of each array's pointer and length, and the type of each local that statements may
assign. -/
structure Layout where
  scalar : Nat → Option Nat
  array : Nat → Option (Nat × Nat)
  assigned : Nat → Option Source.ScalarType

/-- An unguarded instruction. -/
abbrev inst (i : Instr) : Stmt := .instr none i

/-- The word of a source value: a word itself, 0 or 1 for a Boolean, and the bits of a binary32
value. -/
def wordOf : (type : Source.ScalarType) → type.denote → UInt64
  | .u64, v => v
  | .bool, b => if b then 1 else 0
  | .f64, v => v
  | .f32, v => v.toUInt64

/-- The code of `d := l op r` on the words of registers `l` and `r`. -/
def binCode (op : Source.U64Op) (d l r : Nat) : List Stmt :=
  match op with
  | .add => [inst (.bin64 .add d l (.reg r))]
  | .sub => [inst (.bin64 .sub d l (.reg r))]
  | .mul => [inst (.bin64 .mulLo d l (.reg r))]
  | .bitAnd => [inst (.bin64 .and d l (.reg r))]
  | .bitOr => [inst (.bin64 .or d l (.reg r))]
  | .bitXor => [inst (.bin64 .xor d l (.reg r))]
  | .divU => [inst (.setp .eq d r (.imm 0)),
      .ite d [inst (.mov64 d (.imm 0))] [inst (.bin64 .div d l (.reg r))]]
  | .remU => [inst (.setp .eq d r (.imm 0)),
      .ite d [inst (.mov64 d (.reg l))] [inst (.bin64 .rem d l (.reg r))]]
  | .shiftLeft => [inst (.bin64 .and d r (.imm 63)), inst (.narrow d d),
      inst (.shift .shl d l (.reg d))]
  | .shiftRight => [inst (.bin64 .and d r (.imm 63)), inst (.narrow d d),
      inst (.shift .shr d l (.reg d))]

/-- The code of `d := 1` when `l c r` holds and `d := 0` otherwise. -/
def cmpCode (c : Cmp) (d l r : Nat) : List Stmt :=
  [inst (.setp c d l (.reg r)), inst (.selp d (.imm 1) (.imm 0) d)]

/-- The PTX operation of a binary32 operation. -/
def f32Op : Source.F32Op → BinF
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

/-- `.f32` register `f` from the low half of the word in `.b64` register `v`, through `.b32`
register `w`. -/
def toFCode (f w v : Nat) : List Stmt := [inst (.narrow w v), inst (.toF f w)]

/-- The replacement of a NaN in `.f32` register `d` by the canonical NaN, and the move of its bits
into `.b64` register `d`. -/
def fromFCode (d : Nat) : List Stmt :=
  [inst (.testNaN d d), inst (.selpF d (.imm Wasm.IEEE32.canonicalNaN) (.reg d) d),
    inst (.ofF d d), inst (.widen d d)]

/-- The code of `d := l op r` on the binary32 values whose bits registers `l` and `r` hold. -/
def binFCode (op : Source.F32Op) (d l r : Nat) : List Stmt :=
  toFCode d d l ++ toFCode (d + 1) d r ++ [inst (.binF (f32Op op) d d (d + 1))] ++ fromFCode d

/-- The code of `d := op a` on the binary32 value whose bits register `a` holds.  `abs` clears the
sign bit, which keeps a NaN's payload as Talos's `abs` does. -/
def unFCode (op : Source.F32UnOp) (d a : Nat) : List Stmt :=
  match op with
  | .sqrt => toFCode d d a ++ [inst (.sqrtF d d)] ++ fromFCode d
  | .nearest => toFCode d d a ++ [inst (.rniF d d)] ++ fromFCode d
  | .abs => [inst (.bin64 .and d a (.imm 0x7fffffff))]

/-- The code of `d := 1` when the ordered comparison `c` of two binary32 values holds and `d := 0`
otherwise. -/
def cmpFCode (c : CmpF) (d l r : Nat) : List Stmt :=
  toFCode d d l ++ toFCode (d + 1) d r ++
    [inst (.setpF c d d (d + 1)), inst (.selp d (.imm 1) (.imm 0) d)]

/-- The code of two operands, the right one's numbered from the register after the left one's
code, followed by `k n2 vl vr`.  Register `n2`, the first after both operands' code, holds the
result. -/
def joinCode (left : Option (List Stmt × Nat × Nat))
    (right : Nat → Option (List Stmt × Nat × Nat)) (k : Nat → Nat → Nat → List Stmt) :
    Option (List Stmt × Nat × Nat) :=
  match left with
  | some (sl, vl, n1) => match right n1 with
    | some (sr, vr, n2) => some (sl ++ sr ++ k n2 vl vr, n2, n2 + 1)
    | none => none
  | none => none

/-- The code of an expression from register `next` on, its result register, and the next free
register, or `none` outside the subset of words, Booleans, and binary32 values. -/
def trExpr (F : Layout) : {type : Source.ScalarType} → Source.Expr type → Nat →
    Option (List Stmt × Nat × Nat)
  | .u64, .get j, next => (F.scalar j).map fun r => ([], r, next)
  | .u64, .const c, next => some ([inst (.mov64 next (.imm c))], next, next + 1)
  | .bool, .bconst b, next =>
      some ([inst (.mov64 next (.imm (if b then 1 else 0)))], next, next + 1)
  | .u64, .bin op left right, next =>
      joinCode (trExpr F left next) (trExpr F right) (binCode op)
  | .bool, .eq left right, next => joinCode (trExpr F left next) (trExpr F right) (cmpCode .eq)
  | .bool, .ne left right, next => joinCode (trExpr F left next) (trExpr F right) (cmpCode .ne)
  | .bool, .ltU left right, next => joinCode (trExpr F left next) (trExpr F right) (cmpCode .lt)
  | .bool, .leU left right, next => joinCode (trExpr F left next) (trExpr F right) (cmpCode .le)
  | .bool, .not operand, next => (trExpr F operand next).map fun (so, vo, n1) =>
      (so ++ [inst (.bin64 .xor n1 vo (.imm 1))], n1, n1 + 1)
  | .bool, .and left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right (n1 + 1)
      pure (sl ++ [inst (.setp .ne n1 vl (.imm 0)),
        .ite n1 (sr ++ [inst (.mov64 n1 (.reg vr))]) [inst (.mov64 n1 (.imm 0))]], n1, n2)
  | .bool, .or left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right (n1 + 1)
      pure (sl ++ [inst (.setp .ne n1 vl (.imm 0)),
        .ite n1 [inst (.mov64 n1 (.imm 1))] (sr ++ [inst (.mov64 n1 (.reg vr))])], n1, n2)
  | .u64, .ite c t e, next => do
      let (sc, vc, n1) ← trExpr F c next
      let (st, vt, n2) ← trExpr F t (n1 + 1)
      let (se, ve, n3) ← trExpr F e n2
      pure (sc ++ [inst (.setp .ne n1 vc (.imm 0)),
        .ite n1 (st ++ [inst (.mov64 n1 (.reg vt))]) (se ++ [inst (.mov64 n1 (.reg ve))])],
        n1, n3)
  | .u64, .read array position, next => do
      let (base, len) ← F.array array
      let (sp, vp, n1) ← trExpr F position next
      pure (sp ++ [inst (.mov64 n1 (.imm 0)), inst (.setp .lt n1 vp (.reg len)),
        .ite n1 [inst (.shift .shl (n1 + 1) vp (.imm 3)),
          inst (.bin64 .add (n1 + 1) base (.reg (n1 + 1))), inst (.ld n1 (n1 + 1) 8)] []],
        n1, n1 + 2)
  | .f32, .getF32 j, next => (F.scalar j).map fun r => ([], r, next)
  | .f32, .constF32 bits, next => some ([inst (.mov64 next (.imm bits.toUInt64))], next, next + 1)
  | .f32, .binF32 op left right, next =>
      joinCode (trExpr F left next) (trExpr F right) (binFCode op)
  | .f32, .unF32 op operand, next => (trExpr F operand next).map fun (so, vo, n1) =>
      (so ++ unFCode op n1 vo, n1, n1 + 1)
  | .f32, .ofBits32 operand, next => (trExpr F operand next).map fun (so, vo, n1) =>
      (so ++ [inst (.bin64 .and n1 vo (.imm 0xffffffff))], n1, n1 + 1)
  | .u64, .toBits32 operand, next => trExpr F operand next
  | .f32, .iteF32 c t e, next => do
      let (sc, vc, n1) ← trExpr F c next
      let (st, vt, n2) ← trExpr F t (n1 + 1)
      let (se, ve, n3) ← trExpr F e n2
      pure (sc ++ [inst (.setp .ne n1 vc (.imm 0)),
        .ite n1 (st ++ [inst (.mov64 n1 (.reg vt))]) (se ++ [inst (.mov64 n1 (.reg ve))])],
        n1, n3)
  | .bool, .eqF32 left right, next =>
      joinCode (trExpr F left next) (trExpr F right) (cmpFCode .eq)
  | .bool, .ltF32 left right, next =>
      joinCode (trExpr F left next) (trExpr F right) (cmpFCode .lt)
  | .bool, .leF32 left right, next =>
      joinCode (trExpr F left next) (trExpr F right) (cmpFCode .le)
  | _, _, _ => none

/-- The code of a statement from register `next` on and the next free register, or `none` outside
the subset. -/
def trStmt (F : Layout) : Source.Stmt → Nat → Option (List Stmt × Nat)
  | .skip, next => some ([], next)
  | .assign (type := .u64) j e, next => do
      let r ← F.scalar j
      if F.assigned j = some .u64 then
        let (se, v, n1) ← trExpr F e next
        pure (se ++ [inst (.mov64 r (.reg v))], n1)
      else none
  | .assign (type := .f32) j e, next => do
      let r ← F.scalar j
      if F.assigned j = some .f32 then
        let (se, v, n1) ← trExpr F e next
        pure (se ++ [inst (.mov64 r (.reg v))], n1)
      else none
  | .seq a b, next => do
      let (sa, n1) ← trStmt F a next
      let (sb, n2) ← trStmt F b n1
      pure (sa ++ sb, n2)
  | .ite c a b, next => do
      let (sc, vc, n1) ← trExpr F c next
      let (sa, n2) ← trStmt F a (n1 + 1)
      let (sb, n3) ← trStmt F b (n1 + 1)
      pure (sc ++ [inst (.setp .ne n1 vc (.imm 0)), .ite n1 sa sb], max n2 n3)
  | .while c body, next => do
      let (sc, vc, n1) ← trExpr F c next
      let (sb, n2) ← trStmt F body (n1 + 1)
      pure ([.while_ (sc ++ [inst (.setp .ne n1 vc (.imm 0))]) n1 sb], n2)
  | _, _ => none

/-! ### Registers -/

@[simp] theorem Local.set64_r64_self (l : Local) (d : Nat) (v : Val64) :
    (l.set64 d v).r64 d = some v := by simp [Local.set64]

theorem Local.set64_r64_ne (l : Local) {d r : Nat} (v : Val64) (h : r ≠ d) :
    (l.set64 d v).r64 r = l.r64 r := by simp [Local.set64, h]

@[simp] theorem Local.set64_returned (l : Local) (d : Nat) (v : Val64) :
    (l.set64 d v).returned = l.returned := rfl

@[simp] theorem Local.set32_r64 (l : Local) (d : Nat) (v : UInt32) : (l.set32 d v).r64 = l.r64 :=
  rfl

@[simp] theorem Local.set32_r32_self (l : Local) (d : Nat) (v : UInt32) :
    (l.set32 d v).r32 d = some v := by simp [Local.set32]

theorem Local.set32_r32_ne (l : Local) {d r : Nat} (v : UInt32) (h : r ≠ d) :
    (l.set32 d v).r32 r = l.r32 r := by simp [Local.set32, h]

@[simp] theorem Local.set64_r32 (l : Local) (d : Nat) (v : Val64) : (l.set64 d v).r32 = l.r32 :=
  rfl

@[simp] theorem Local.setf_r64 (l : Local) (d : Nat) (v : F32Val) : (l.setf d v).r64 = l.r64 :=
  rfl

@[simp] theorem Local.setf_r32 (l : Local) (d : Nat) (v : F32Val) : (l.setf d v).r32 = l.r32 :=
  rfl

@[simp] theorem Local.setf_rp (l : Local) (d : Nat) (v : F32Val) : (l.setf d v).rp = l.rp := rfl

@[simp] theorem Local.setf_returned (l : Local) (d : Nat) (v : F32Val) :
    (l.setf d v).returned = l.returned := rfl

@[simp] theorem Local.setf_rf_self (l : Local) (d : Nat) (v : F32Val) :
    (l.setf d v).rf d = some v := by simp [Local.setf]

theorem Local.setf_rf_ne (l : Local) {d r : Nat} (v : F32Val) (h : r ≠ d) :
    (l.setf d v).rf r = l.rf r := by simp [Local.setf, h]

@[simp] theorem Local.set32_rf (l : Local) (d : Nat) (v : UInt32) : (l.set32 d v).rf = l.rf := rfl

@[simp] theorem Local.set64_rf (l : Local) (d : Nat) (v : Val64) : (l.set64 d v).rf = l.rf := rfl

@[simp] theorem Local.setp_rf (l : Local) (d : Nat) (v : Bool) : (l.setp d v).rf = l.rf := rfl

@[simp] theorem Local.set32_returned (l : Local) (d : Nat) (v : UInt32) :
    (l.set32 d v).returned = l.returned := rfl

@[simp] theorem Local.setp_r64 (l : Local) (d : Nat) (v : Bool) : (l.setp d v).r64 = l.r64 := rfl

@[simp] theorem Local.setp_rp_self (l : Local) (d : Nat) (v : Bool) :
    (l.setp d v).rp d = some v := by simp [Local.setp]

@[simp] theorem Local.setp_returned (l : Local) (d : Nat) (v : Bool) :
    (l.setp d v).returned = l.returned := rfl

theorem Local.word_of {l : Local} {r : Nat} {x : UInt64} (h : l.r64 r = some (.word x)) :
    l.word r = some x := by simp [Local.word, h]

/-- The `.b64` registers below `n` hold the same values in `l` and `l'`. -/
def Same (n : Nat) (l l' : Local) : Prop := ∀ r, r < n → l'.r64 r = l.r64 r

theorem Same.refl (n : Nat) (l : Local) : Same n l l := fun _ _ => rfl

theorem Same.trans {n : Nat} {a b c : Local} (h1 : Same n a b) (h2 : Same n b c) : Same n a c :=
  fun r hr => (h2 r hr).trans (h1 r hr)

theorem Same.mono {n n' : Nat} {a b : Local} (h : Same n' a b) (hle : n ≤ n') : Same n a b :=
  fun r hr => h r (by omega)

theorem Same.set64 {n d : Nat} (hd : n ≤ d) (l : Local) (v : Val64) : Same n l (l.set64 d v) :=
  fun r hr => Local.set64_r64_ne l v (by omega)

/-- Code that sets register `d` to the word `w` and keeps the registers below `d`. -/
def SetsReg (s : Shape) (o : Oracle) (l : Local) (code : List Stmt) (d : Nat) (w : UInt64) :
    Prop :=
  Runs s o l code fun l' => Same d l l' ∧ l'.r64 d = some (.word w)

/-- The code of an expression, run from `l`, keeps the registers below `next` and leaves the word
`w` in register `res`. -/
def ExprRuns (s : Shape) (o : Oracle) (l : Local) (code : List Stmt) (res next : Nat)
    (w : UInt64) : Prop :=
  Runs s o l code fun l' => Same next l l' ∧ l'.r64 res = some (.word w)

/-! ### Single instructions -/

theorem Runs.mov {s : Shape} {o : Oracle} {l : Local} {d : Nat} {a : Src64} {v : Val64}
    {P : Local → Prop} (hr : l.returned = false) (ha : a.get l = some v)
    (hP : P (l.set64 d v)) : Runs s o l [inst (.mov64 d a)] P :=
  Runs.step hr (fun evs => by simp [Instr.exec, ha]) (by simpa using hr) hP

theorem Runs.bin {s : Shape} {o : Oracle} {l : Local} {op : Bin64} {d a : Nat} {b : Src64}
    {x y z : Val64} {P : Local → Prop} (hr : l.returned = false) (ha : l.r64 a = some x)
    (hb : b.get l = some y) (hz : op.apply x y = some z) (hP : P (l.set64 d z)) :
    Runs s o l [inst (.bin64 op d a b)] P :=
  Runs.step hr (fun evs => by simp [Instr.exec, ha, hb, hz]) (by simpa using hr) hP

theorem Runs.setp {s : Shape} {o : Oracle} {l : Local} {c : Cmp} {p a : Nat} {b : Src64}
    {x y : UInt64} {P : Local → Prop} (hr : l.returned = false) (ha : l.r64 a = some (.word x))
    (hb : b.word l = some y) (hP : P (l.setp p (c.apply x y))) :
    Runs s o l [inst (.setp c p a b)] P :=
  Runs.step hr (fun evs => by simp [Instr.exec, Local.word_of ha, hb]) (by simpa using hr) hP

theorem Runs.selp {s : Shape} {o : Oracle} {l : Local} {d : Nat} {t f : Src64} {p : Nat}
    {c : Bool} {v : Val64} {P : Local → Prop} (hr : l.returned = false) (hp : l.rp p = some c)
    (hv : (if c then t else f).get l = some v) (hP : P (l.set64 d v)) :
    Runs s o l [inst (.selp d t f p)] P :=
  Runs.step hr (fun evs => by simp [Instr.exec, hp, hv]) (by simpa using hr) hP

theorem Runs.narrow {s : Shape} {o : Oracle} {l : Local} {d a : Nat} {x : UInt64}
    {P : Local → Prop} (hr : l.returned = false) (ha : l.r64 a = some (.word x))
    (hP : P (l.set32 d x.toUInt32)) : Runs s o l [inst (.narrow d a)] P :=
  Runs.step hr (fun evs => by simp [Instr.exec, Local.word_of ha]) (by simpa using hr) hP

theorem Runs.shift {s : Shape} {o : Oracle} {l : Local} {op : Shift} {d a : Nat} {b : Src32}
    {x : UInt64} {n : UInt32} {P : Local → Prop} (hr : l.returned = false)
    (ha : l.r64 a = some (.word x)) (hb : b.get l = some n)
    (hP : P (l.set64 d (.word (op.apply x n)))) : Runs s o l [inst (.shift op d a b)] P :=
  Runs.step hr (fun evs => by simp [Instr.exec, Local.word_of ha, hb]) (by simpa using hr) hP

/-- A load of word `k` of buffer `j`, whose value the oracle gives as `v` after any events. -/
theorem Runs.load {s : Shape} {o : Oracle} {l : Local} {d a : Nat} {imm : UInt64} {j : Nat}
    {off : UInt64} {size k : Nat} {v : UInt64} {P : Local → Prop} (hr : l.returned = false)
    (ha : l.r64 a = some (.ptr j off)) (hsize : s.sizes[j]? = some size)
    (hk : wordAt size off imm = some k) (hv : ∀ c, o c j k = v)
    (hP : P (l.set64 d (.word v))) : Runs s o l [inst (.ld d a imm)] P := by
  intro evs
  refine ⟨[.read j k v], l.set64 d (.word v), ?_, rfl, by simpa using hr, hP⟩
  simp [Stmt.execList, Stmt.exec, Instr.exec, hr, ha, hsize, hk, hv, Res.andThen]

/-! ### Layouts -/

/-- Every register of the layout is below `n`. -/
structure Layout.Below (F : Layout) (n : Nat) : Prop where
  scalar : ∀ j r, F.scalar j = some r → r < n
  array : ∀ a base len, F.array a = some (base, len) → base < n ∧ len < n

theorem Layout.Below.mono {F : Layout} {n n' : Nat} (h : F.Below n) (hle : n ≤ n') :
    F.Below n' :=
  ⟨fun j r hr => by have := h.scalar j r hr; omega,
   fun a b len ha => by have := h.array a b len ha; omega⟩

/-- Distinct word locals have distinct registers, and the register of an assigned local is
neither the pointer nor the length register of an array. -/
structure Layout.Distinct (F : Layout) : Prop where
  scalar : ∀ j j' r, F.scalar j = some r → F.scalar j' = some r → j = j'
  assigned : ∀ j t r a base len, F.assigned j = some t → F.scalar j = some r →
    F.array a = some (base, len) → r ≠ base ∧ r ≠ len

/-- The registers of `l` hold the word and binary32 locals of `L` and each array of `arrays`: a
pointer to the start of a buffer whose first word is the length and whose next words, as the
oracle gives them, are the elements. -/
structure Layout.Agrees (F : Layout) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (s : Shape) (o : Oracle) (l : Local) : Prop where
  word : ∀ j v, L j = some (.i64 v) → ∃ r, F.scalar j = some r ∧ l.r64 r = some (.word v)
  float : ∀ j b, L j = some (.f32 b) →
    ∃ r, F.scalar j = some r ∧ l.r64 r = some (.word b.toUInt64)
  array : ∀ a xs, arrays a = some xs → xs.size < 2 ^ 29 ∧ ∃ base len b,
    F.array a = some (base, len) ∧ l.r64 base = some (.ptr b 0) ∧
    l.r64 len = some (.word (UInt64.ofNat xs.size)) ∧ s.sizes[b]? = some (xs.size + 1) ∧
    ∀ c k (hk : k < xs.size), o c b (k + 1) = xs[k]

theorem Layout.Agrees.same {F : Layout} {L : Nat → Option Wasm.Value}
    {arrays : Nat → Option (Array UInt64)} {s : Shape} {o : Oracle} {l l' : Local} {n : Nat}
    (h : F.Agrees L arrays s o l) (hB : F.Below n) (hs : Same n l l') :
    F.Agrees L arrays s o l' where
  word j v hj := by
    obtain ⟨r, hr, hv⟩ := h.word j v hj
    exact ⟨r, hr, (hs r (hB.scalar j r hr)).trans hv⟩
  float j b hj := by
    obtain ⟨r, hr, hv⟩ := h.float j b hj
    exact ⟨r, hr, (hs r (hB.scalar j r hr)).trans hv⟩
  array a xs ha := by
    obtain ⟨hsz, base, len, b, hF, hb, hl, hsize, ho⟩ := h.array a xs ha
    have := hB.array a base len hF
    exact ⟨hsz, base, len, b, hF, (hs base this.1).trans hb, (hs len this.2).trans hl, hsize,
      ho⟩

/-! ### Expressions -/

theorem joinCode_eq_some {left : Option (List Stmt × Nat × Nat)}
    {right : Nat → Option (List Stmt × Nat × Nat)} {k : Nat → Nat → Nat → List Stmt}
    {code : List Stmt} {res next' : Nat} (h : joinCode left right k = some (code, res, next')) :
    ∃ sl vl n1 sr vr, left = some (sl, vl, n1) ∧ right n1 = some (sr, vr, res) ∧
      code = sl ++ sr ++ k res vl vr ∧ next' = res + 1 := by
  rcases left with _ | ⟨sl, vl, n1⟩
  · cases h
  · rcases hr : right n1 with _ | ⟨sr, vr, n2⟩
    · simp [joinCode, hr] at h
    · simp only [joinCode, hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨sl, vl, n1, sr, vr, rfl, hr, rfl, rfl⟩

/-- An expression's code uses registers from `next` up to `next'`, and its result is below
`next'` when the layout's registers are below `next`. -/
theorem trExpr_mono (F : Layout) : ∀ {type : Source.ScalarType} (e : Source.Expr type)
    (next : Nat) (code : List Stmt) (res next' : Nat),
    trExpr F e next = some (code, res, next') →
      next ≤ next' ∧ (F.Below next → res < next') := by
  intro type e
  induction e with
  | get j | getF32 j =>
      intro next code res next' h
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_refl _, fun hB => hB.scalar j r hr⟩
  | const c | bconst c | constF32 c =>
      intro next code res next' h
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at h
      omega
  | bin _ left right ihl ihr | eq left right ihl ihr | ne left right ihl ihr
  | ltU left right ihl ihr | leU left right ihl ihr | binF32 _ left right ihl ihr
  | eqF32 left right ihl ihr | ltF32 left right ihl ihr | leF32 left right ihl ihr =>
      intro next code res next' h
      obtain ⟨sl, vl, n1, sr, vr, hl, hr, -, rfl⟩ := joinCode_eq_some h
      have := (ihl _ _ _ _ hl).1
      have := (ihr _ _ _ _ hr).1
      exact ⟨by omega, fun _ => by omega⟩
  | not operand ih | unF32 _ operand ih | ofBits32 operand ih =>
      intro next code res next' h
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨⟨so, vo, n1⟩, ho, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      have := (ih _ _ _ _ ho).1
      exact ⟨by omega, fun _ => by omega⟩
  | and left right ihl ihr | or left right ihl ihr =>
      intro next code res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hl : trExpr F left next with
      | none => simp [hl] at h
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hr : trExpr F right (n1 + 1) with
        | none => simp [hl, hr] at h
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hr, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨-, rfl, rfl⟩ := h
          have := (ihl _ _ _ _ hl).1
          have := (ihr _ _ _ _ hr).1
          exact ⟨by omega, fun _ => by omega⟩
  | ite c t e ihc iht ihe | iteF32 c t e ihc iht ihe =>
      intro next code res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ht : trExpr F t (n1 + 1) with
        | none => simp [hc, ht] at h
        | some rt =>
          obtain ⟨st, vt, n2⟩ := rt
          cases he : trExpr F e n2 with
          | none => simp [hc, ht, he] at h
          | some re =>
            obtain ⟨se, ve, n3⟩ := re
            simp only [hc, ht, he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨-, rfl, rfl⟩ := h
            have := (ihc _ _ _ _ hc).1
            have := (iht _ _ _ _ ht).1
            have := (ihe _ _ _ _ he).1
            exact ⟨by omega, fun _ => by omega⟩
  | read array position ih =>
      intro next code res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hF : F.array array with
      | none => simp [hF] at h
      | some bl =>
        obtain ⟨base, len⟩ := bl
        cases hp : trExpr F position next with
        | none => simp [hF, hp] at h
        | some rp =>
          obtain ⟨sp, vp, n1⟩ := rp
          simp only [hF, hp, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨-, rfl, rfl⟩ := h
          have := (ih _ _ _ _ hp).1
          exact ⟨by omega, fun _ => by omega⟩
  | toBits32 operand ih =>
      intro next code res next' h
      exact ih next code res next' h
  | _ =>
      intro next code res next' h
      simp [trExpr] at h

theorem and63 (y : UInt64) : (y &&& 63).toUInt32.toUInt64 = y % 64 := by
  apply UInt64.toNat_inj.mp
  have h : ∀ n : Nat, n &&& 63 = n % 64 := fun n => Nat.and_two_pow_sub_one_eq_mod n 6
  simp [UInt64.toNat_and, h]

theorem binCode_sets {s : Shape} {o : Oracle} {l : Local} (op : Source.U64Op) {d vl vr : Nat}
    {x y : UInt64} (hr : l.returned = false) (hvl : vl < d) (hx : l.r64 vl = some (.word x))
    (hy : l.r64 vr = some (.word y)) : SetsReg s o l (binCode op d vl vr) d (op.apply x y) := by
  have hset : ∀ (l' : Local) (v : Val64), (∀ r, r < d → l'.r64 r = l.r64 r) →
      Same d l (l'.set64 d v) := fun l' v h r hr' =>
    (Local.set64_r64_ne l' v (by omega)).trans (h r hr')
  have hval : ∀ (l' : Local) (v : UInt64), (∀ r, r < d → l'.r64 r = l.r64 r) →
      (fun l'' => Same d l l'' ∧ l''.r64 d = some (.word v)) (l'.set64 d (.word v)) :=
    fun l' v h => ⟨hset l' _ h, by simp⟩
  have hy' : (Src64.reg vr).get l = some (.word y) := hy
  cases op with
  | add => exact Runs.bin hr hx hy' rfl (hval l _ fun _ _ => rfl)
  | sub => exact Runs.bin hr hx hy' rfl (hval l _ fun _ _ => rfl)
  | mul => exact Runs.bin hr hx hy' rfl (hval l _ fun _ _ => rfl)
  | bitAnd => exact Runs.bin hr hx hy' rfl (hval l _ fun _ _ => rfl)
  | bitOr => exact Runs.bin hr hx hy' rfl (hval l _ fun _ _ => rfl)
  | bitXor => exact Runs.bin hr hx hy' rfl (hval l _ fun _ _ => rfl)
  | divU =>
      refine Runs.append (P := (· = l.setp d (Cmp.apply .eq y 0)))
        (Runs.setp hr hy (by simp [Src64.word, Src64.get]) rfl) ?_
      rintro l' rfl hr'
      by_cases hy0 : y = 0
      · refine Runs.ite_true hr' (by simp [Cmp.apply, hy0]) ?_
        exact Runs.mov hr' (v := .word 0) rfl
          (by simpa [Source.U64Op.apply, hy0] using hval (l.setp d _) 0 fun _ _ => rfl)
      · refine Runs.ite_false hr' (by simp [Cmp.apply, hy0]) ?_
        exact Runs.bin hr' (x := .word x) hx hy' (z := .word (x / y)) (by simp [Bin64.apply, hy0])
          (by simpa [Source.U64Op.apply, hy0] using hval (l.setp d _) (x / y) fun _ _ => rfl)
  | remU =>
      refine Runs.append (P := (· = l.setp d (Cmp.apply .eq y 0)))
        (Runs.setp hr hy (by simp [Src64.word, Src64.get]) rfl) ?_
      rintro l' rfl hr'
      by_cases hy0 : y = 0
      · refine Runs.ite_true hr' (by simp [Cmp.apply, hy0]) ?_
        exact Runs.mov hr' (v := .word x) hx
          (by simpa [Source.U64Op.apply, hy0] using hval (l.setp d _) x fun _ _ => rfl)
      · refine Runs.ite_false hr' (by simp [Cmp.apply, hy0]) ?_
        exact Runs.bin hr' (x := .word x) hx hy' (z := .word (x % y)) (by simp [Bin64.apply, hy0])
          (by simpa [Source.U64Op.apply, hy0] using hval (l.setp d _) (x % y) fun _ _ => rfl)
  | shiftLeft | shiftRight =>
      refine Runs.append (P := (· = l.set64 d (.word (y &&& 63))))
        (Runs.bin hr hy rfl rfl rfl) ?_
      rintro l1 rfl hr1
      refine Runs.append (P := (· = (l.set64 d (.word (y &&& 63))).set32 d (y &&& 63).toUInt32))
        (Runs.narrow hr1 (by simp) rfl) ?_
      rintro l2 rfl hr2
      have hlt : (y &&& 63).toUInt32.toNat < 64 := by
        have h64 : (y % 64).toNat < 64 := by simp [UInt64.toNat_mod]; omega
        rw [← and63 y] at h64
        simpa using h64
      refine Runs.shift hr2 (x := x) (n := (y &&& 63).toUInt32)
        (by simp [Local.set64_r64_ne _ _ (show vl ≠ d by omega), hx]) (by simp [Src32.get]) ?_
      refine ⟨hset _ _ fun r hr' => ?_, ?_⟩
      · simp [Local.set64_r64_ne _ _ (show r ≠ d by omega)]
      · simp only [Local.set64_r64_self, Shift.apply, hlt, ↓reduceIte, and63]
        rfl

theorem cmpCode_sets {s : Shape} {o : Oracle} {l : Local} (c : Cmp) {d vl vr : Nat}
    {x y : UInt64} (hr : l.returned = false) (hx : l.r64 vl = some (.word x))
    (hy : l.r64 vr = some (.word y)) :
    SetsReg s o l (cmpCode c d vl vr) d (if c.apply x y then 1 else 0) := by
  refine Runs.append (P := (· = l.setp d (c.apply x y)))
    (Runs.setp hr hx (by simp [Src64.word, Src64.get, hy]) rfl) ?_
  rintro l' rfl hr'
  refine Runs.selp hr' (c := c.apply x y) (by simp) (v := .word (if c.apply x y then 1 else 0))
    (by cases c.apply x y <;> simp [Src64.get]) ⟨fun r hr'' => ?_, by simp⟩
  simp [Local.set64_r64_ne _ _ (show r ≠ d by omega)]

theorem F32Val.isNaN_ofResult (r : UInt32) : (F32Val.ofResult r).isNaN = Wasm.IEEE32.isNaN r := by
  unfold F32Val.ofResult
  split <;> simp_all [F32Val.isNaN]

theorem f32Op_apply (op : Source.F32Op) (a b : UInt32) : (f32Op op).apply a b = op.apply a b := by
  cases op <;> rfl

theorem toF_runs {s : Shape} {o : Oracle} {l : Local} {f w v : Nat} {b : UInt32}
    (hr : l.returned = false) (hv : l.r64 v = some (.word b.toUInt64)) :
    Runs s o l (toFCode f w v) (· = (l.set32 w b).setf f (.bits b)) := by
  have hb : b.toUInt64.toUInt32 = b := by simp
  refine Runs.cons (Runs.narrow hr hv rfl) fun l1 h1 hr1 => ?_
  subst h1
  rw [hb]
  exact Runs.step hr1 (fun evs => by simp [Instr.exec]) (by simpa using hr1) rfl

/-- The replacement of a NaN result `r` by the canonical NaN gives `r` when Talos's NaN results
are canonical, and moves its bits into `.b64` register `d`. -/
theorem fromF_sets {s : Shape} {o : Oracle} {l : Local} {d : Nat} {r : UInt32}
    (hr : l.returned = false) (hf : l.rf d = some (F32Val.ofResult r))
    (hc : canonical32 r = r) : SetsReg s o l (fromFCode d) d r.toUInt64 := by
  let c := (F32Val.ofResult r).isNaN
  have hsel : ((if c then SrcF.imm Wasm.IEEE32.canonicalNaN else SrcF.reg d).get
      (l.setp d c)) = some (.bits r) := by
    by_cases h : Wasm.IEEE32.isNaN r = true
    · have hcn : Wasm.IEEE32.canonicalNaN = r := by simpa [canonical32, h] using hc
      simp [c, F32Val.isNaN_ofResult, h, SrcF.get, hcn]
    · simp [c, F32Val.isNaN_ofResult, h, SrcF.get, hf, F32Val.ofResult]
  refine Runs.cons (Runs.step (l' := l.setp d c) hr (fun evs => by simp [Instr.exec, hf, c])
    (by simpa using hr) rfl) fun l1 h1 hr1 => ?_
  subst h1
  refine Runs.cons (Runs.step (l' := (l.setp d c).setf d (.bits r)) hr1
    (fun evs => by simp [Instr.exec, hsel]) (by simpa using hr1) rfl) fun l2 h2 hr2 => ?_
  subst h2
  refine Runs.cons (Runs.step (l' := ((l.setp d c).setf d (.bits r)).set32 d r) hr2
    (fun evs => by simp [Instr.exec]) (by simpa using hr2) rfl) fun l3 h3 hr3 => ?_
  subst h3
  exact Runs.step (l' := (((l.setp d c).setf d (.bits r)).set32 d r).set64 d (.word r.toUInt64))
    hr3 (fun evs => by simp [Instr.exec]) hr3
    ⟨fun i hi => Local.set64_r64_ne _ _ (show i ≠ d by omega), by simp⟩

theorem binFCode_sets {s : Shape} {o : Oracle} {l : Local} (op : Source.F32Op) {d vl vr : Nat}
    {a b : UInt32} (hr : l.returned = false) (hx : l.r64 vl = some (.word a.toUInt64))
    (hy : l.r64 vr = some (.word b.toUInt64)) :
    SetsReg s o l (binFCode op d vl vr) d (op.apply a b).toUInt64 := by
  unfold binFCode
  let l1 := (l.set32 d a).setf d (.bits a)
  let l2 := (l1.set32 d b).setf (d + 1) (.bits b)
  let l3 := l2.setf d (.ofResult (op.apply a b))
  have h12 : Runs s o l (toFCode d d vl ++ toFCode (d + 1) d vr) (· = l2) :=
    Runs.append (toF_runs hr hx) fun l' h hr' => by
      subst h
      exact toF_runs hr' (by simpa using hy)
  have h123 : Runs s o l (toFCode d d vl ++ toFCode (d + 1) d vr ++
      [inst (.binF (f32Op op) d d (d + 1))]) (· = l3) :=
    Runs.append h12 fun l' h hr' => by
      subst h
      exact Runs.step (l' := l3) hr' (fun evs => by
        simp [Instr.exec, l3, l2, l1, Local.setf_rf_ne _ _ (show d ≠ d + 1 by omega), f32Op_apply,
          F32Val.repr]) hr' rfl
  refine Runs.append h123 fun l' h hr' => ?_
  subst h
  exact (fromF_sets hr' (by simp [l3]) (canonical_f32_bin op a b)).mono
    fun l4 ⟨h4, hv4⟩ => ⟨fun i hi => (h4 i hi).trans rfl, hv4⟩

theorem unFCode_sets {s : Shape} {o : Oracle} {l : Local} (op : Source.F32UnOp) {d va : Nat}
    {a : UInt32} (hr : l.returned = false) (hx : l.r64 va = some (.word a.toUInt64)) :
    SetsReg s o l (unFCode op d va) d (op.apply a).toUInt64 := by
  cases op with
  | sqrt =>
      let l2 := ((l.set32 d a).setf d (.bits a)).setf d (.ofResult (Wasm.IEEE32.sqrt a))
      have h1 : Runs s o l (toFCode d d va ++ [inst (.sqrtF d d)]) (· = l2) :=
        Runs.append (toF_runs hr hx) fun l' h hr' => by
          subst h
          exact Runs.step (l' := l2) hr' (fun evs => by simp [Instr.exec, F32Val.repr, l2]) hr'
            rfl
      refine Runs.append h1 fun l' h hr' => ?_
      subst h
      exact (fromF_sets hr' (by simp [l2]) (canonical_f32_sqrt a)).mono fun l3 ⟨h3, hv3⟩ =>
        ⟨fun i hi => (h3 i hi).trans rfl, by simpa [Source.F32UnOp.apply] using hv3⟩
  | nearest =>
      let l2 := ((l.set32 d a).setf d (.bits a)).setf d (.ofResult (Wasm.IEEE32.nearest a))
      have h1 : Runs s o l (toFCode d d va ++ [inst (.rniF d d)]) (· = l2) :=
        Runs.append (toF_runs hr hx) fun l' h hr' => by
          subst h
          exact Runs.step (l' := l2) hr' (fun evs => by simp [Instr.exec, F32Val.repr, l2]) hr'
            rfl
      refine Runs.append h1 fun l' h hr' => ?_
      subst h
      exact (fromF_sets hr' (by simp [l2]) (canonical_f32_nearest a)).mono fun l3 ⟨h3, hv3⟩ =>
        ⟨fun i hi => (h3 i hi).trans rfl, by simpa [Source.F32UnOp.apply] using hv3⟩
  | abs =>
      have habs : (Wasm.IEEE32.abs a).toUInt64 = a.toUInt64 &&& 0x7fffffff := by
        apply UInt64.toNat_inj.mp
        have h : ∀ n : Nat, n &&& 2147483647 = n % 2147483648 := fun n =>
          Nat.and_two_pow_sub_one_eq_mod n 31
        have ha := a.toNat_lt
        simp [Wasm.IEEE32.abs, Wasm.IEEE32.encodeFinite, Wasm.IEEE32.exponent,
          Wasm.IEEE32.fraction, UInt64.toNat_and, h]
        omega
      exact Runs.bin hr hx rfl rfl ⟨Same.set64 (le_refl _) l _,
        by simp [Source.F32UnOp.apply, habs]⟩

theorem cmpFCode_sets {s : Shape} {o : Oracle} {l : Local} (c : CmpF) {d vl vr : Nat}
    {a b : UInt32} (hr : l.returned = false) (hx : l.r64 vl = some (.word a.toUInt64))
    (hy : l.r64 vr = some (.word b.toUInt64)) :
    SetsReg s o l (cmpFCode c d vl vr) d (if c.apply a b then 1 else 0) := by
  unfold cmpFCode
  let l2 := (((l.set32 d a).setf d (.bits a)).set32 d b).setf (d + 1) (.bits b)
  have h12 : Runs s o l (toFCode d d vl ++ toFCode (d + 1) d vr) (· = l2) :=
    Runs.append (toF_runs hr hx) fun l' h hr' => by
      subst h
      exact toF_runs hr' (by simpa using hy)
  refine Runs.append h12 fun l' h hr2 => ?_
  subst h
  refine Runs.cons (Runs.step (l' := l2.setp d (c.apply a b)) hr2 (fun evs => by
    simp [Instr.exec, l2, Local.setf_rf_ne _ _ (show d ≠ d + 1 by omega), F32Val.repr]) hr2 rfl)
    fun l3 h3 hr3 => ?_
  subst h3
  refine Runs.selp hr3 (c := c.apply a b) (by simp) (v := .word (if c.apply a b then 1 else 0))
    (by cases c.apply a b <;> simp [Src64.get]) ⟨fun i hi => ?_, by simp⟩
  exact (Local.set64_r64_ne _ _ (show i ≠ d by omega)).trans rfl

theorem ExprRuns.two {s : Shape} {o : Oracle} {l : Local} {sl sr k : List Stmt}
    {vl vr next n1 n2 : Nat} {wl wr w : UInt64} (hn1 : next ≤ n1) (hvl : vl < n1)
    (hn2 : n1 ≤ n2)
    (hL : ExprRuns s o l sl vl next wl)
    (hR : ∀ l1, Same next l l1 → l1.returned = false → ExprRuns s o l1 sr vr n1 wr)
    (hK : ∀ l2, l2.returned = false → l2.r64 vl = some (.word wl) →
      l2.r64 vr = some (.word wr) → SetsReg s o l2 k n2 w) :
    ExprRuns s o l (sl ++ sr ++ k) n2 next w := by
  have h12 : Runs s o l (sl ++ sr) fun l2 => Same next l l2 ∧
      l2.r64 vl = some (.word wl) ∧ l2.r64 vr = some (.word wr) :=
    Runs.append hL fun l1 ⟨h1, hv1⟩ hr1 => (hR l1 h1 hr1).mono fun l2 ⟨h2, hv2⟩ =>
      ⟨h1.trans (h2.mono hn1), (h2 vl hvl).trans hv1, hv2⟩
  exact Runs.append h12 fun l2 ⟨h2, hv1, hv2⟩ hr2 =>
    (hK l2 hr2 hv1 hv2).mono fun l3 ⟨h3, hv3⟩ =>
    ⟨h2.trans (h3.mono (by omega)), hv3⟩

/-- From registers that agree with the source locals and arrays, the code of an expression runs
without stopping or storing, keeps the registers below `next`, and leaves the expression's word in
its result register. -/
theorem trExpr_sim (F : Layout) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (s : Shape) (o : Oracle) :
    ∀ {type : Source.ScalarType} (e : Source.Expr type) (next : Nat) (code : List Stmt)
      (res next' : Nat), trExpr F e next = some (code, res, next') →
    ∀ v, e.denote L arrays = some v → ∀ l, F.Agrees L arrays s o l → F.Below next →
      l.returned = false → ExprRuns s o l code res next (wordOf type v) := by
  intro type e
  induction e with
  | get j =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨r, hrj, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hL : L j = some (.i64 v) := by
        simp only [Source.Expr.denote] at hv
        split at hv <;> simp_all
      obtain ⟨r', hr', hw⟩ := hA.word j v hL
      rw [hrj] at hr'
      cases hr'
      exact Runs.nil hr ⟨Same.refl _ _, hw⟩
  | const c =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Source.Expr.denote, Option.some.injEq] at hv
      subst hv
      exact Runs.mov hr (v := .word c) rfl ⟨Same.set64 (le_refl _) l _, by simp [wordOf]⟩
  | bconst b =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Source.Expr.denote, Option.some.injEq] at hv
      subst hv
      exact Runs.mov hr rfl ⟨Same.set64 (le_refl _) l _, by simp [wordOf]⟩
  | bin op left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      have hvl := ml.2 hB
      exact ExprRuns.two ml.1 hvl mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => binCode_sets op hr2 (by omega) h2l h2r)
  | eq left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpCode_sets .eq hr2 h2l h2r)
  | ne left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpCode_sets .ne hr2 h2l h2r)
  | ltU left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpCode_sets .lt hr2 h2l h2r)
  | leU left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpCode_sets .le hr2 h2l h2r)
  | not operand ih =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨⟨so, vo, n1⟩, ho, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Source.Expr.denote, Option.map_eq_some_iff] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      have mo := trExpr_mono F _ _ _ _ _ ho
      refine Runs.append (ih _ _ _ _ ho b hb l hA hB hr) fun l1 ⟨h1, hw⟩ hr1 => ?_
      exact Runs.bin hr1 hw rfl rfl
        ⟨h1.trans (Same.set64 mo.1 l1 _), by cases b <;> simp [wordOf]⟩
  | and left right ihl ihr | or left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hl : trExpr F left next with
      | none => simp [hl] at h
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hrt : trExpr F right (n1 + 1) with
        | none => simp [hl, hrt] at h
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hrt, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have ml := trExpr_mono F _ _ _ _ _ hl
          have mr := trExpr_mono F _ _ _ _ _ hrt
          simp only [Source.Expr.denote, Option.bind_eq_bind] at hv
          cases hdl : left.denote L arrays with
          | none => simp [hdl] at hv
          | some bl =>
            simp only [hdl, Option.bind_some] at hv
            refine Runs.append (ihl _ _ _ _ hl bl hdl l hA hB hr) fun l1 ⟨h1, hw1⟩ hr1 => ?_
            refine Runs.append (P := (· = l1.setp n1 bl))
              (Runs.setp hr1 hw1 rfl (by cases bl <;> simp [Cmp.apply, wordOf])) ?_
            rintro l2 rfl hr2
            have h2 : Same next l (l1.setp n1 bl) := h1.trans fun _ _ => rfl
            cases bl with
            | true =>
                simp only [↓reduceIte, Option.pure_def, Option.some.injEq] at hv
                refine Runs.ite_true hr2 (by simp) ?_
                first
                | (subst hv
                   exact Runs.mov hr2 rfl
                     ⟨h2.trans (Same.set64 (by omega) _ _), by simp [wordOf]⟩)
                | (refine Runs.append (ihr _ _ _ _ hrt v hv _ (hA.same hB h2)
                     (hB.mono (by omega)) hr2) fun l3 ⟨h3, hw3⟩ hr3 => ?_
                   exact Runs.mov hr3 hw3
                     ⟨(h2.trans (h3.mono (by omega))).trans (Same.set64 (by omega) l3 _),
                      by simp⟩)
            | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def,
                  Option.some.injEq] at hv
                refine Runs.ite_false hr2 (by simp) ?_
                first
                | (subst hv
                   exact Runs.mov hr2 rfl
                     ⟨h2.trans (Same.set64 (by omega) _ _), by simp [wordOf]⟩)
                | (refine Runs.append (ihr _ _ _ _ hrt v hv _ (hA.same hB h2)
                     (hB.mono (by omega)) hr2) fun l3 ⟨h3, hw3⟩ hr3 => ?_
                   exact Runs.mov hr3 hw3
                     ⟨(h2.trans (h3.mono (by omega))).trans (Same.set64 (by omega) l3 _),
                      by simp⟩)
  | ite c t e ihc iht ihe | iteF32 c t e ihc iht ihe =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ht : trExpr F t (n1 + 1) with
        | none => simp [hc, ht] at h
        | some rt =>
          obtain ⟨st, vt, n2⟩ := rt
          cases he : trExpr F e n2 with
          | none => simp [hc, ht, he] at h
          | some re =>
            obtain ⟨se, ve, n3⟩ := re
            simp only [hc, ht, he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have mc := trExpr_mono F _ _ _ _ _ hc
            have mt := trExpr_mono F _ _ _ _ _ ht
            have me := trExpr_mono F _ _ _ _ _ he
            simp only [Source.Expr.denote, Option.bind_eq_bind] at hv
            cases hdc : c.denote L arrays with
            | none => simp [hdc] at hv
            | some bc =>
              simp only [hdc, Option.bind_some] at hv
              refine Runs.append (ihc _ _ _ _ hc bc hdc l hA hB hr) fun l1 ⟨h1, hw1⟩ hr1 => ?_
              refine Runs.append (P := (· = l1.setp n1 bc))
                (Runs.setp hr1 hw1 rfl (by cases bc <;> simp [Cmp.apply, wordOf])) ?_
              rintro l2 rfl hr2
              have h2 : Same next l (l1.setp n1 bc) := h1.trans fun _ _ => rfl
              cases bc with
              | true =>
                  simp only [↓reduceIte] at hv
                  refine Runs.ite_true hr2 (by simp) ?_
                  refine Runs.append (iht _ _ _ _ ht v hv _ (hA.same hB h2)
                    (hB.mono (by omega)) hr2) fun l3 ⟨h3, hw3⟩ hr3 => ?_
                  exact Runs.mov hr3 hw3
                    ⟨(h2.trans (h3.mono (by omega))).trans (Same.set64 (by omega) l3 _),
                      by simp⟩
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at hv
                  refine Runs.ite_false hr2 (by simp) ?_
                  refine Runs.append (ihe _ _ _ _ he v hv _ (hA.same hB h2)
                    (hB.mono (by omega)) hr2) fun l3 ⟨h3, hw3⟩ hr3 => ?_
                  exact Runs.mov hr3 hw3
                    ⟨(h2.trans (h3.mono (by omega))).trans (Same.set64 (by omega) l3 _),
                      by simp⟩
  | read array position ih =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hF : F.array array with
      | none => simp [hF] at h
      | some bl =>
        obtain ⟨base, len⟩ := bl
        cases hp : trExpr F position next with
        | none => simp [hF, hp] at h
        | some rp =>
          obtain ⟨sp, vp, n1⟩ := rp
          simp only [hF, hp, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have mp := trExpr_mono F _ _ _ _ _ hp
          simp only [Source.Expr.denote, Option.bind_eq_bind] at hv
          cases hxs : arrays array with
          | none => simp [hxs] at hv
          | some xs =>
            cases hk : position.denote L arrays with
            | none => simp [hxs, hk] at hv
            | some k =>
              simp only [hxs, hk, Option.bind_some, Option.pure_def, Option.some.injEq] at hv
              subst hv
              obtain ⟨hsz, base', len', b, hF', hbase, hlen, hsize, ho⟩ := hA.array array xs hxs
              rw [hF] at hF'
              simp only [Option.some.injEq, Prod.mk.injEq] at hF'
              obtain ⟨rfl, rfl⟩ := hF'
              have hbl := hB.array array base len hF
              have hvp := mp.2 hB
              refine Runs.append (ih _ _ _ _ hp k hk l hA hB hr) fun l1 ⟨h1, hw1⟩ hr1 => ?_
              have hb1 : l1.r64 base = some (.ptr b 0) := (h1 base hbl.1).trans hbase
              have hl1 : l1.r64 len = some (.word (UInt64.ofNat xs.size)) :=
                (h1 len hbl.2).trans hlen
              refine Runs.append (P := (· = l1.set64 n1 (.word 0))) (Runs.mov hr1 rfl rfl) ?_
              rintro l2 rfl hr2
              refine Runs.append
                (P := (· = (l1.set64 n1 (.word 0)).setp n1
                  (Cmp.apply .lt k (UInt64.ofNat xs.size))))
                (Runs.setp hr2 (by rw [Local.set64_r64_ne _ _ (by omega)]; exact hw1)
                  (by simp [Src64.word, Src64.get,
                    Local.set64_r64_ne _ _ (show len ≠ n1 by omega),
                    hl1]) rfl) ?_
              rintro l3 rfl hr3
              have hs : (UInt64.ofNat xs.size).toNat = xs.size := by simp; omega
              by_cases hkn : k.toNat < xs.size
              · have hlt : Cmp.apply .lt k (UInt64.ofNat xs.size) = true := by
                  simp only [Cmp.apply, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hs]
                  exact hkn
                refine Runs.ite_true hr3 (by simp [hlt]) ?_
                have hw : (0 + Shift.apply .shl k 3).toNat = 8 * k.toNat := by
                  have h3 : (3 : UInt32).toNat < 64 := by decide
                  simp only [Shift.apply, h3, ↓reduceIte, UInt64.zero_add, UInt64.toNat_shiftLeft]
                  simp [Nat.shiftLeft_eq]
                  omega
                have hword : wordAt (xs.size + 1) (0 + Shift.apply .shl k 3) 8 =
                    some (k.toNat + 1) := by
                  have h8 : (8 : UInt64).toNat = 8 := rfl
                  simp only [wordAt, hw, h8]
                  have : (8 * k.toNat + 8) / 8 = k.toNat + 1 := by omega
                  simp [this]
                  omega
                refine Runs.append (Runs.shift hr3 (x := k) (n := 3)
                  (by simp [Local.set64_r64_ne _ _ (show vp ≠ n1 by omega), hw1, wordOf]) rfl
                  (P := (· = ((l1.set64 n1 (.word 0)).setp n1
                    (Cmp.apply .lt k (UInt64.ofNat xs.size))).set64 (n1 + 1)
                      (.word (Shift.apply .shl k 3)))) rfl) ?_
                rintro l4 rfl hr4
                refine Runs.append (Runs.bin hr4 (x := .ptr b 0) (y := .word (Shift.apply .shl k 3))
                  (by simp [Local.set64_r64_ne _ _ (show base ≠ n1 + 1 by omega),
                    Local.set64_r64_ne _ _ (show base ≠ n1 by omega), hb1])
                  (by simp [Src64.get]) rfl rfl) ?_
                rintro l5 rfl hr5
                refine Runs.load hr5 (by simp) hsize hword (fun c => ho c k.toNat hkn) ⟨?_, ?_⟩
                · intro r hr'
                  simp [Local.set64_r64_ne _ _ (show r ≠ n1 by omega),
                    Local.set64_r64_ne _ _ (show r ≠ n1 + 1 by omega), h1 r hr']
                · simp [wordOf, getElem!_pos xs k.toNat hkn]
              · have hlt : Cmp.apply .lt k (UInt64.ofNat xs.size) = false := by
                  simp only [Cmp.apply, decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, hs]
                  exact hkn
                refine Runs.ite_false hr3 (by simp [hlt]) (Runs.nil hr3 ⟨?_, ?_⟩)
                · intro r hr'
                  simp [Local.set64_r64_ne _ _ (show r ≠ n1 by omega), h1 r hr']
                · simp [wordOf, getElem!_neg xs k.toNat hkn, show (default : UInt64) = 0 from rfl]
  | getF32 j =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨r, hrj, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hL : L j = some (.f32 v) := by
        simp only [Source.Expr.denote] at hv
        split at hv <;> simp_all
      obtain ⟨r', hr', hw⟩ := hA.float j v hL
      rw [hrj] at hr'
      cases hr'
      exact Runs.nil hr ⟨Same.refl _ _, hw⟩
  | constF32 c =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Source.Expr.denote, Option.some.injEq] at hv
      subst hv
      exact Runs.mov hr rfl ⟨Same.set64 (le_refl _) l _, by simp [wordOf]⟩
  | binF32 op left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => binFCode_sets op hr2 h2l h2r)
  | eqF32 left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpFCode_sets .eq hr2 h2l h2r)
  | ltF32 left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpFCode_sets .lt hr2 h2l h2r)
  | leF32 left right ihl ihr =>
      intro next code res next' h v hv l hA hB hr
      obtain ⟨sl, vl, n1, sr, vr, hl, hrt, rfl, rfl⟩ := joinCode_eq_some h
      simp only [Source.Expr.denote] at hv
      obtain ⟨lv, rv, hdl, hdr, rfl⟩ := Source.denote_two hv
      have ml := trExpr_mono F _ _ _ _ _ hl
      have mr := trExpr_mono F _ _ _ _ _ hrt
      exact ExprRuns.two ml.1 (ml.2 hB) mr.1 (ihl _ _ _ _ hl lv hdl l hA hB hr)
        (fun l1 h1 hr1 => ihr _ _ _ _ hrt rv hdr l1 (hA.same hB h1) (hB.mono ml.1) hr1)
        (fun l2 hr2 h2l h2r => cmpFCode_sets .le hr2 h2l h2r)
  | unF32 op operand ih =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨⟨so, vo, n1⟩, ho, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Source.Expr.denote, Option.map_eq_some_iff] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      have mo := trExpr_mono F _ _ _ _ _ ho
      refine Runs.append (ih _ _ _ _ ho b hb l hA hB hr) fun l1 ⟨h1, hw⟩ hr1 => ?_
      exact (unFCode_sets op hr1 hw).mono fun l2 ⟨h2, hv2⟩ =>
        ⟨h1.trans (h2.mono mo.1), hv2⟩
  | ofBits32 operand ih =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨⟨so, vo, n1⟩, ho, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Source.Expr.denote, Option.map_eq_some_iff] at hv
      obtain ⟨w, hw', rfl⟩ := hv
      have mo := trExpr_mono F _ _ _ _ _ ho
      have hlow : w &&& 0xffffffff = w.toUInt32.toUInt64 := by
        apply UInt64.toNat_inj.mp
        have h32 : ∀ n : Nat, n &&& 4294967295 = n % 4294967296 := fun n =>
          Nat.and_two_pow_sub_one_eq_mod n 32
        simp [UInt64.toNat_and, h32]
      refine Runs.append (ih _ _ _ _ ho w hw' l hA hB hr) fun l1 ⟨h1, hw⟩ hr1 => ?_
      exact Runs.bin hr1 hw rfl rfl ⟨h1.trans (Same.set64 mo.1 l1 _), by simp [wordOf, hlow]⟩
  | toBits32 operand ih =>
      intro next code res next' h v hv l hA hB hr
      simp only [trExpr] at h
      simp only [Source.Expr.denote, Option.map_eq_some_iff] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      exact ih next code res next' h b hb l hA hB hr
  | _ =>
      intro next code res next' h
      simp [trExpr] at h

/-! ### Statements -/

/-- The `.b64` registers below `n`, other than the registers of assigned locals, hold the same
values in `l` and `l'`. -/
def Layout.Keeps (F : Layout) (n : Nat) (l l' : Local) : Prop :=
  ∀ r, r < n → (∀ j t, F.assigned j = some t → F.scalar j ≠ some r) → l'.r64 r = l.r64 r

theorem Layout.Keeps.trans {F : Layout} {n : Nat} {a b c : Local} (h1 : F.Keeps n a b)
    (h2 : F.Keeps n b c) : F.Keeps n a c :=
  fun r hr ha => (h2 r hr ha).trans (h1 r hr ha)

theorem Layout.Keeps.mono {F : Layout} {n n' : Nat} {a b : Local} (h : F.Keeps n' a b)
    (hle : n ≤ n') : F.Keeps n a b :=
  fun r hr ha => h r (by omega) ha

theorem Same.keeps {F : Layout} {n : Nat} {a b : Local} (h : Same n a b) : F.Keeps n a b :=
  fun r hr _ => h r hr

/-- The agreement after a store of word `w` to the register `r` of assigned local `j`, where `w`
represents the local's new value `val`. -/
theorem Layout.Agrees.assign {F : Layout} (hD : F.Distinct) {L : Nat → Option Wasm.Value}
    {arrays : Nat → Option (Array UInt64)} {s : Shape} {o : Oracle} {l l1 : Local} {n j r : Nat}
    {t : Source.ScalarType} {val : Wasm.Value} {w : UInt64}
    (hA : F.Agrees L arrays s o l) (hB : F.Below n) (h1 : Same n l l1)
    (hrj : F.scalar j = some r) (hasg : F.assigned j = some t)
    (hword : ∀ v, val = .i64 v → w = v) (hfloat : ∀ b, val = .f32 b → w = b.toUInt64) :
    F.Agrees (fun i => if i = j then some val else L i) arrays s o (l1.set64 r (.word w)) ∧
      F.Keeps n l (l1.set64 r (.word w)) := by
  refine ⟨⟨fun i u hi => ?_, fun i b hi => ?_, fun a xs ha => ?_⟩, fun r' hr' hna => ?_⟩
  · by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Option.some.injEq] at hi
      exact ⟨r, hrj, by rw [hword u hi]; simp⟩
    · simp only [hij, ↓reduceIte] at hi
      obtain ⟨ri, hri, hu⟩ := hA.word i u hi
      have hne : ri ≠ r := fun heq => hij (hD.scalar i j r (heq ▸ hri) hrj)
      exact ⟨ri, hri, by rw [Local.set64_r64_ne _ _ hne, h1 ri (hB.scalar i ri hri), hu]⟩
  · by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Option.some.injEq] at hi
      exact ⟨r, hrj, by rw [hfloat b hi]; simp⟩
    · simp only [hij, ↓reduceIte] at hi
      obtain ⟨ri, hri, hu⟩ := hA.float i b hi
      have hne : ri ≠ r := fun heq => hij (hD.scalar i j r (heq ▸ hri) hrj)
      exact ⟨ri, hri, by rw [Local.set64_r64_ne _ _ hne, h1 ri (hB.scalar i ri hri), hu]⟩
  · obtain ⟨hsz, base, len, b, hF, hb, hl, hsize, ho⟩ := hA.array a xs ha
    have hbl := hB.array a base len hF
    have hne := hD.assigned j t r a base len hasg hrj hF
    exact ⟨hsz, base, len, b, hF,
      by rw [Local.set64_r64_ne _ _ (Ne.symm hne.1), h1 base hbl.1, hb],
      by rw [Local.set64_r64_ne _ _ (Ne.symm hne.2), h1 len hbl.2, hl], hsize, ho⟩
  · have hne : r' ≠ r := fun heq => hna j t hasg (heq ▸ hrj)
    rw [Local.set64_r64_ne _ _ hne, h1 r' hr']

theorem trStmt_mono (F : Layout) : ∀ (st : Source.Stmt) (next : Nat) (code : List Stmt)
    (next' : Nat), trStmt F st next = some (code, next') → next ≤ next' := by
  intro st
  induction st with
  | skip =>
      intro next code next' h
      simp only [trStmt, Option.some.injEq, Prod.mk.injEq] at h
      omega
  | @assign type j e =>
      intro next code next' h
      cases type <;> simp only [trStmt, Option.bind_eq_bind] at h
      all_goals try (simp at h; done)
      all_goals
        cases hr : F.scalar j with
        | none => simp [hr] at h
        | some r =>
          simp only [hr, Option.bind_some] at h
          split at h
          · cases he : trExpr F e next with
            | none => simp [he] at h
            | some re =>
              obtain ⟨se, v, n1⟩ := re
              simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact (trExpr_mono F e next se v n1 he).1
          · cases h
  | seq a b iha ihb =>
      intro next code next' h
      simp only [trStmt, Option.bind_eq_bind] at h
      cases ha : trStmt F a next with
      | none => simp [ha] at h
      | some ra =>
        obtain ⟨sa, n1⟩ := ra
        cases hb : trStmt F b n1 with
        | none => simp [ha, hb] at h
        | some rb =>
          obtain ⟨sb, n2⟩ := rb
          simp only [ha, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have := iha _ _ _ ha
          have := ihb _ _ _ hb
          omega
  | ite c a b iha ihb =>
      intro next code next' h
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ha : trStmt F a (n1 + 1) with
        | none => simp [hc, ha] at h
        | some ra =>
          obtain ⟨sa, n2⟩ := ra
          cases hb : trStmt F b (n1 + 1) with
          | none => simp [hc, ha, hb] at h
          | some rb =>
            obtain ⟨sb, n3⟩ := rb
            simp only [hc, ha, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            have := (trExpr_mono F c next sc vc n1 hc).1
            have := iha _ _ _ ha
            omega
  | «while» c body ih =>
      intro next code next' h
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases hb : trStmt F body (n1 + 1) with
        | none => simp [hc, hb] at h
        | some rb =>
          obtain ⟨sb, n2⟩ := rb
          simp only [hc, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have := (trExpr_mono F c next sc vc n1 hc).1
          have := ih _ _ _ hb
          omega
  | _ =>
      intro next code next' h
      simp [trStmt] at h

/-- The code of a condition followed by the `setp` of its predicate. -/
theorem cond_runs {F : Layout} {L : Nat → Option Wasm.Value}
    {arrays : Nat → Option (Array UInt64)} {s : Shape} {o : Oracle} {c : Source.Expr .bool}
    {next : Nat} {sc : List Stmt} {vc n1 : Nat} {b : Bool} {l : Local}
    (hc : trExpr F c next = some (sc, vc, n1)) (hd : c.denote L arrays = some b)
    (hA : F.Agrees L arrays s o l) (hB : F.Below next) (hr : l.returned = false) :
    Runs s o l (sc ++ [inst (.setp .ne n1 vc (.imm 0))])
      fun l' => Same next l l' ∧ l'.rp n1 = some b :=
  Runs.append (trExpr_sim F L arrays s o c next sc vc n1 hc b hd l hA hB hr)
    fun _ ⟨h1, hw1⟩ hr1 => Runs.setp hr1 hw1 rfl
      ⟨fun r hr' => h1 r hr', by cases b <;> simp [Cmp.apply, wordOf]⟩

theorem loop_sim (F : Layout) (arrays : Nat → Option (Array UInt64)) (s : Shape) (o : Oracle)
    {c : Source.Expr .bool} {next : Nat} {sc sb : List Stmt} {vc n1 : Nat}
    {bodyDenote : (Nat → Option Wasm.Value) → Option (Nat → Option Wasm.Value)}
    (hc : trExpr F c next = some (sc, vc, n1)) (hB : F.Below next)
    (hbody : ∀ L L', bodyDenote L = some L' → ∀ l, F.Agrees L arrays s o l →
      l.returned = false →
        Runs s o l sb fun l' => F.Agrees L' arrays s o l' ∧ F.Keeps (n1 + 1) l l') :
    ∀ fuel L L' l evs,
      Source.loopIter (fun L => c.denote L arrays) bodyDenote fuel L = some L' →
      F.Agrees L arrays s o l → l.returned = false →
      ∃ added l', loopRuns (fun l evs => Stmt.execList s o l evs
          (sc ++ [inst (.setp .ne n1 vc (.imm 0))]))
          (fun l evs => Stmt.execList s o l evs sb) n1 fuel l evs = (evs ++ added, some l') ∧
        writesOf added = [] ∧ l'.returned = false ∧ F.Agrees L' arrays s o l' ∧
        F.Keeps next l l' := by
  have hn1 := (trExpr_mono F c next sc vc n1 hc).1
  intro fuel
  induction fuel with
  | zero => intro L L' l evs h; cases h
  | succ fuel ih =>
      intro L L' l evs h hA hr
      rw [Source.loopIter_succ] at h
      cases hcd : c.denote L arrays with
      | none => simp [hcd] at h
      | some b =>
        simp only [hcd, Option.bind_some] at h
        obtain ⟨a1, l1, he1, hw1, hr1, h1, hp1⟩ := cond_runs hc hcd hA hB hr evs
        have hA1 := hA.same hB h1
        cases b with
        | true =>
            simp only [↓reduceIte, Option.bind_eq_some_iff] at h
            obtain ⟨L1, hb1, hL⟩ := h
            obtain ⟨a2, l2, he2, hw2, hr2, hA2, hk2⟩ := hbody L L1 hb1 l1 hA1 hr1 (evs ++ a1)
            obtain ⟨a3, l3, he3, hw3, hr3, hA3, hk3⟩ := ih L1 L' l2 (evs ++ a1 ++ a2) hL hA2 hr2
            simp only [List.append_assoc] at he2 he3
            refine ⟨a1 ++ a2 ++ a3, l3, ?_, by simp [hw1, hw2, hw3], hr3, hA3,
              (h1.keeps.trans (hk2.mono (by omega))).trans hk3⟩
            simp [loopRuns, hr, he1, Res.andThen, hr1, hp1, he2, he3]
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
            subst h
            refine ⟨a1, l1, ?_, hw1, hr1, hA1, h1.keeps⟩
            simp [loopRuns, hr, he1, Res.andThen, hr1, hp1]

/-- From registers that agree with the source locals and arrays, the code of a statement runs
without stopping or storing, keeps the registers below `next` other than those of assigned
locals, and leaves registers that agree with the statement's new locals. -/
theorem trStmt_sim (F : Layout) (hD : F.Distinct) (arrays : Nat → Option (Array UInt64))
    (s : Shape) (o : Oracle) :
    ∀ (st : Source.Stmt) (next : Nat) (code : List Stmt) (next' : Nat),
      trStmt F st next = some (code, next') → F.Below next →
      ∀ L L', st.denote arrays L = some L' → ∀ l, F.Agrees L arrays s o l →
        l.returned = false → Runs s o l code fun l' => F.Agrees L' arrays s o l' ∧
          F.Keeps next l l' := by
  intro st
  induction st with
  | skip =>
      intro next code next' h hB L L' hd l hA hr
      simp only [trStmt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Source.Stmt.denote, Option.some.injEq] at hd
      subst hd
      exact Runs.nil hr ⟨hA, fun _ _ _ => rfl⟩
  | @assign type j e =>
      intro next code next' h hB L L' hd l hA hr
      cases type <;> simp only [trStmt, Option.bind_eq_bind] at h
      all_goals try (simp at h; done)
      all_goals
        cases hrj : F.scalar j with
        | none => simp [hrj] at h
        | some r =>
          simp only [hrj, Option.bind_some] at h
          split at h
          · rename_i hasg
            cases he : trExpr F e next with
            | none => simp [he] at h
            | some re =>
              obtain ⟨se, v, n1⟩ := re
              simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [Source.Stmt.denote] at hd
              split at hd
              · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hd
                exact Runs.append (trExpr_sim F L arrays s o e next se v n1 he w hw l hA hB hr)
                  fun l1 ⟨h1, hw1⟩ hr1 => Runs.mov hr1 hw1
                    (Layout.Agrees.assign hD hA hB h1 hrj hasg (fun _ h => by cases h <;> rfl)
                      (fun _ h => by cases h <;> rfl))
              · cases hd
          · cases h
  | seq a b iha ihb =>
      intro next code next' h hB L L' hd l hA hr
      simp only [trStmt, Option.bind_eq_bind] at h
      cases ha : trStmt F a next with
      | none => simp [ha] at h
      | some ra =>
        obtain ⟨sa, n1⟩ := ra
        cases hb : trStmt F b n1 with
        | none => simp [ha, hb] at h
        | some rb =>
          obtain ⟨sb, n2⟩ := rb
          simp only [ha, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hn1 := trStmt_mono F a next sa n1 ha
          simp only [Source.Stmt.denote, Option.bind_eq_some_iff] at hd
          obtain ⟨L1, hd1, hd2⟩ := hd
          exact Runs.append (iha _ _ _ ha hB L L1 hd1 l hA hr) fun l1 ⟨hA1, hk1⟩ hr1 =>
            (ihb _ _ _ hb (hB.mono hn1) L1 L' hd2 l1 hA1 hr1).mono fun l2 ⟨hA2, hk2⟩ =>
              ⟨hA2, hk1.trans (hk2.mono hn1)⟩
  | ite c a b iha ihb =>
      intro next code next' h hB L L' hd l hA hr
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ha : trStmt F a (n1 + 1) with
        | none => simp [hc, ha] at h
        | some ra =>
          obtain ⟨sa, n2⟩ := ra
          cases hb : trStmt F b (n1 + 1) with
          | none => simp [hc, ha, hb] at h
          | some rb =>
            obtain ⟨sb, n3⟩ := rb
            simp only [hc, ha, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hn1 := (trExpr_mono F c next sc vc n1 hc).1
            simp only [Source.Stmt.denote, Option.bind_eq_bind] at hd
            cases hcd : c.denote L arrays with
            | none => simp [hcd] at hd
            | some bc =>
              simp only [hcd, Option.bind_some] at hd
              have hcond := cond_runs hc hcd hA hB hr
              rw [show sc ++ [inst (.setp .ne n1 vc (.imm 0)), .ite n1 sa sb] =
                (sc ++ [inst (.setp .ne n1 vc (.imm 0))]) ++ [.ite n1 sa sb] by simp]
              refine Runs.append hcond fun l1 ⟨h1, hp1⟩ hr1 => ?_
              have hA1 := hA.same hB h1
              cases bc with
              | true =>
                  simp only [↓reduceIte] at hd
                  exact Runs.ite_true hr1 hp1
                    ((iha _ _ _ ha (hB.mono (by omega)) L L' hd l1 hA1 hr1).mono
                      fun l2 ⟨hA2, hk2⟩ => ⟨hA2, h1.keeps.trans (hk2.mono (by omega))⟩)
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at hd
                  exact Runs.ite_false hr1 hp1
                    ((ihb _ _ _ hb (hB.mono (by omega)) L L' hd l1 hA1 hr1).mono
                      fun l2 ⟨hA2, hk2⟩ => ⟨hA2, h1.keeps.trans (hk2.mono (by omega))⟩)
  | «while» c body ih =>
      intro next code next' h hB L L' hd l hA hr
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases hb : trStmt F body (n1 + 1) with
        | none => simp [hc, hb] at h
        | some rb =>
          obtain ⟨sb, n2⟩ := rb
          simp only [hc, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hn1 := (trExpr_mono F c next sc vc n1 hc).1
          simp only [Source.Stmt.denote] at hd
          intro evs
          obtain ⟨added, l', he, hw, hr', hA', hk'⟩ := loop_sim F arrays s o hc hB
            (fun L L' hd l hA hr => ih _ _ _ hb (hB.mono (by omega)) L L' hd l hA hr)
            Source.loopBound L L' l evs hd hA hr
          have hlb : loopBound = Source.loopBound := rfl
          have hex : Stmt.exec s o l evs (.while_ (sc ++ [inst (.setp .ne n1 vc (.imm 0))]) n1 sb) =
              (evs ++ added, some l') := by
            rw [Stmt.exec, hlb]
            exact he
          refine ⟨added, l', ?_, hw, hr', hA', hk'⟩
          simp only [Stmt.execList, hr, Bool.false_eq_true, ↓reduceIte, hex, Res.andThen]
  | _ =>
      intro next code next' h
      simp [trStmt] at h

end LeanExe.PTX
