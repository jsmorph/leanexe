import LeanExe.WGSL.Semantics

/-!
The memory operations of one invocation.  This semantics runs the statements of `Semantics.lean`
with two changes.  A read of a buffer word takes its value from an oracle instead of the initial
buffer and records a read event, and a store records a write event.  A result keeps the events
produced before the invocation stops, so the memory model of `MemoryModel.lean` constrains the
reads of runs that end and of runs that stop.  An invocation stops where `Semantics.lean` fails: at
an ill-typed operation, an access outside a buffer, a read of the output, or a loop past
`loopBound` tests.

Operands are evaluated from left to right (WGSL 15.1), the arguments of `select` in order (WGSL
11.2), and a store `b[i] = e` evaluates `i` before `e` (WGSL 9.2.1).  `&&` and `||` evaluate their
right operand only when it determines the result.
-/

namespace LeanExe.WGSL

/-- A memory operation of an invocation: a read of word `word` of buffer `buffer` that returned
`value`, or a write of `value` to word `word` of the output buffer. -/
inductive Event where
  | read (buffer word : Nat) (value : UInt32)
  | write (word : Nat) (value : UInt32)
  deriving Repr, DecidableEq

/-- The value of a read, given the number of the invocation's earlier events, the buffer, and
the word.  Since the first argument differs for every read of a run, an oracle can give the reads
of a run any values. -/
abbrev Oracle := Nat → Nat → Nat → UInt32

/-- What an invocation uses besides the buffers' contents: its index, the sizes in words of the
read-only buffers, and the size of the output. -/
structure Shape where
  gid : UInt32
  sizes : List Nat
  outputSize : Nat

/-- A result: the events so far, and a value, or `none` when the invocation stops. -/
abbrev Res (α : Type) := List Event × Option α

/-- Continue with `k` after a result that has a value. -/
def Res.andThen (r : Res α) (k : List Event → α → Res β) : Res β :=
  match r with
  | (evs, some x) => k evs x
  | (evs, none) => (evs, none)

/-- The value of an expression, after the events `evs`. -/
def Expr.evalE (s : Shape) (o : Oracle) (env : Env) : Expr → List Event → Res Value
  | .lit v, evs => (evs, some (.u32 v))
  | .bool b, evs => (evs, some (.bool b))
  | .var n, evs => (evs, (env.find n).map (·.1))
  | .gidX, evs => (evs, some (.u32 s.gid))
  | .fst n, evs => (evs, match env.find n with
    | some (.vec2 low _, _) => some (.u32 low)
    | _ => none)
  | .snd n, evs => (evs, match env.find n with
    | some (.vec2 _ high, _) => some (.u32 high)
    | _ => none)
  | .vec2 a b, evs => (a.evalE s o env evs).andThen fun evs x =>
      (b.evalE s o env evs).andThen fun evs y => (evs, match x, y with
        | .u32 low, .u32 high => some (.vec2 low high)
        | _, _ => none)
  | .bin .and a b, evs => (a.evalE s o env evs).andThen fun evs x => match x with
    | .bool true => (b.evalE s o env evs).andThen fun evs y => (evs, match y with
      | .bool v => some (.bool v)
      | _ => none)
    | .bool false => (evs, some (.bool false))
    | _ => (evs, none)
  | .bin .or a b, evs => (a.evalE s o env evs).andThen fun evs x => match x with
    | .bool false => (b.evalE s o env evs).andThen fun evs y => (evs, match y with
      | .bool v => some (.bool v)
      | _ => none)
    | .bool true => (evs, some (.bool true))
    | _ => (evs, none)
  | .bin op a b, evs => (a.evalE s o env evs).andThen fun evs x =>
      (b.evalE s o env evs).andThen fun evs y => (evs, op.apply x y)
  | .not a, evs => (a.evalE s o env evs).andThen fun evs x => (evs, match x with
    | .bool v => some (.bool !v)
    | _ => none)
  | .toF32 a, evs => (a.evalE s o env evs).andThen fun evs x => (evs, match x with
    | .u32 v => some (.f32 v)
    | _ => none)
  | .toU32 a, evs => (a.evalE s o env evs).andThen fun evs x => (evs, match x with
    | .f32 v => some (.u32 v)
    | _ => none)
  | .sqrt a, evs => (a.evalE s o env evs).andThen fun evs x => (evs, match x with
    | .f32 v => some (.f32 (Wasm.IEEE32.sqrt v))
    | _ => none)
  | .round a, evs => (a.evalE s o env evs).andThen fun evs x => (evs, match x with
    | .f32 v => some (.f32 (Wasm.IEEE32.nearest v))
    | _ => none)
  | .abs a, evs => (a.evalE s o env evs).andThen fun evs x => (evs, match x with
    | .f32 v => some (.f32 (Wasm.IEEE32.abs v))
    | _ => none)
  | .select f t c, evs => (f.evalE s o env evs).andThen fun evs fv =>
      (t.evalE s o env evs).andThen fun evs tv =>
        (c.evalE s o env evs).andThen fun evs cv => (evs, match cv with
          | .bool cv => if fv.sameType tv then some (if cv then tv else fv) else none
          | _ => none)
  | .min a b, evs => (a.evalE s o env evs).andThen fun evs x =>
      (b.evalE s o env evs).andThen fun evs y => (evs, match x, y with
        | .u32 x, .u32 y => some (.u32 (if x ≤ y then x else y))
        | _, _ => none)
  | .length b, evs => (evs, (s.sizes[b]?).map fun size => .u32 (UInt32.ofNat size))
  | .index b p, evs => (p.evalE s o env evs).andThen fun evs x => match x, s.sizes[b]? with
    | .u32 i, some size =>
        if i.toNat < size then
          let v := o evs.length b i.toNat
          (evs ++ [.read b i.toNat v], some (.u32 v))
        else (evs, none)
    | _, _ => (evs, none)

/-- An invocation's state besides its events: the variables in scope and whether it has
returned. -/
structure Local where
  env : Env
  returned : Bool

/-- At most `fuel` tests of a loop's condition, each followed, while the condition holds, by a
run of the body; a `return` in the body ends the loop. -/
def loopRunsE (test : Local → List Event → Res Bool) (body : Local → List Event → Res Local) :
    Nat → Local → List Event → Res Local
  | 0, _, evs => (evs, none)
  | fuel + 1, l, evs =>
      if l.returned then (evs, some l)
      else (test l evs).andThen fun evs c =>
        if c then (body l evs).andThen fun evs l => loopRunsE test body fuel l evs
        else (evs, some l)

mutual
  /-- One statement. -/
  def Stmt.execE (s : Shape) (o : Oracle) (l : Local) (evs : List Event) : Stmt → Res Local
    | .let_ n ty e => (e.evalE s o l.env evs).andThen fun evs v =>
        (evs, if ty.holds v && (l.env.find n).isNone then
          some { l with env := (n, v, false) :: l.env } else none)
    | .var n ty e => (e.evalE s o l.env evs).andThen fun evs v =>
        (evs, if ty.holds v && (l.env.find n).isNone then
          some { l with env := (n, v, true) :: l.env } else none)
    | .assign n e => (e.evalE s o l.env evs).andThen fun evs v => (evs, match l.env.find n with
      | some (old, true) => if old.sameType v then some { l with env := l.env.set n v } else none
      | _ => none)
    | .store b p e => (p.evalE s o l.env evs).andThen fun evs x =>
        (e.evalE s o l.env evs).andThen fun evs y => match x, y with
          | .u32 i, .u32 v =>
              if b = s.sizes.length ∧ i.toNat < s.outputSize then
                (evs ++ [.write i.toNat v], some l)
              else (evs, none)
          | _, _ => (evs, none)
    | .ite c ts es => (c.evalE s o l.env evs).andThen fun evs x => match x with
      | .bool cv =>
          (if cv then Stmt.execListE s o l evs ts else Stmt.execListE s o l evs es).andThen
            -- Declarations inside the block go out of scope; assignments to outer variables stay.
            fun evs inner =>
              (evs, some { inner with env := inner.env.drop (inner.env.length - l.env.length) })
      | _ => (evs, none)
    | .while_ c body =>
        loopRunsE
          (fun l evs => (c.evalE s o l.env evs).andThen fun evs x => (evs, match x with
            | .bool b => some b
            | _ => none))
          (fun l evs => (Stmt.execListE s o l evs body).andThen fun evs inner =>
            (evs, some { inner with env := inner.env.drop (inner.env.length - l.env.length) }))
          loopBound l evs
    | .ret => (evs, some { l with returned := true })

  /-- Statements in order; those after a `return` do nothing. -/
  def Stmt.execListE (s : Shape) (o : Oracle) (l : Local) (evs : List Event) :
      List Stmt → Res Local
    | [] => (evs, some l)
    | st :: rest =>
        if l.returned then (evs, some l)
        else (Stmt.execE s o l evs st).andThen fun evs l => Stmt.execListE s o l evs rest
end

/-- The events of invocation `gid` in program order, up to its end or to the point where it
stops, and whether it ended. -/
def Module.invokeE (m : Module) (sizes : List Nat) (outputSize : Nat) (o : Oracle)
    (gid : UInt32) : List Event × Bool :=
  if sizes.length = m.inputs then
    let r := Stmt.execListE { gid, sizes, outputSize } o { env := [], returned := false } [] m.body
    (r.1, r.2.isSome)
  else ([], false)

end LeanExe.WGSL
