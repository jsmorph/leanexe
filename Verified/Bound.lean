import Verified.Compile

/-! The allocation bound: the bytes by which the code of an expression can raise the allocator's
`top`, as a Lean function of the values of its variables.  An allocation of `b` payload bytes
either reuses a free block, which leaves `top`, or raises `top` by `48 + b`, and the code requests
only multiples of 8 of at least 8 bytes, so `allocCost b = 48 + b`.  The bound follows
`Expr.code` with the modes of the variables and the same live sets: it counts each copy that the
modes and the live sets call for, each array that `build` makes, and each block of `push`, `++`,
and `insertAt`.  An owned array that dies grows into a block of less than twice the bytes of its
new length, which the code requests only when its block lacks room, and the bound charges that
block even when the array extends in place.  The bound ignores the reuse of freed blocks. -/

namespace Verified

/-- The growth of `top` for an allocation of `bytes` payload bytes that no free block supplies. -/
def allocCost (bytes : Nat) : Nat := 48 + bytes

/-- The bytes that a copy of a value of type `t` costs: a block for each of its arrays, whose
length word counts words. -/
def Ty.copyCost : (t : Ty) → t.denote → Nat
  | .elem _, _ => 0
  | .pair a b, v => a.copyCost v.1 + b.copyCost v.2
  | .array e, xs => allocCost ((xs.size * e.width + 1) * 8)

/-- The bytes of `coerceCode`: a copy when a borrowed value must be owned. -/
def coerceCost (t : Ty) (source target : Mode) (v : t.denote) : Nat :=
  if source = .borrowed ∧ target = .owned then t.copyCost v else 0

/-- The mode of variable `i` among the modes `modes`. -/
def modeAt (modes : List Mode) (i : Nat) : Mode := modes.getD i .borrowed

/-- The bytes of `Var.code`: a copy of an owned variable that stays live. -/
def Var.cost (modes : List Mode) (live : Nat → Bool) {Γ : List Ty} {t : Ty} (x : Var Γ t)
    (v : t.denote) : Nat :=
  if modeAt modes x.index = .owned ∧ live x.index = true then t.copyCost v else 0

/-- The bytes of `Var.ownedCode`: the copy of `Var.code`, or a copy of a borrowed variable. -/
def Var.ownedCost (modes : List Mode) (live : Nat → Bool) {Γ : List Ty} {t : Ty} (x : Var Γ t)
    (v : t.denote) : Nat :=
  x.cost modes live v + coerceCost t (modeAt modes x.index) .owned v

/-- The bytes of `Var.roomCode` for an extension by `ext` words of the array `xs` of `x`: a block
of less than twice the new length's bytes for an owned array that dies, and a copy at the new
length otherwise. -/
def Var.roomCost (modes : List Mode) (live : Nat → Bool) {Γ : List Ty} {e : Elem}
    (x : Var Γ (.array e)) (xs : Array e.denote) (ext : Nat) : Nat :=
  let len := xs.size * e.width + ext
  if modeAt modes x.index = .owned ∧ live x.index = false then allocCost (16 * (len + 1))
  else allocCost ((len + 1) * 8)

/-- The sum of `f k` for `k` below `n`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + f n

/-- The bytes of a loop's iterations from index `i`, with `n` indices left, from the state `s`:
the condition's at each state it tests, and the body's at each state that passes it, until the
first state that fails it, where the code leaves the loop. -/
def loopCost {α : Type} (condCost : α → Nat) (cond : α → Bool) (bodyCost : UInt64 → α → Nat)
    (step : UInt64 → α → α) : Nat → UInt64 → α → Nat
  | 0, _, _ => 0
  | n + 1, i, s =>
    condCost s +
      if cond s then bodyCost i s + loopCost condCost cond bodyCost step n (i + 1) (step i s)
      else 0

/-- The sum of `b i` for the indices `i` of a function's parameters. -/
def argsSum : {n : Nat} → ((i : Fin n) → Nat) → Nat
  | 0, _ => 0
  | _ + 1, b => b 0 + argsSum fun i => b i.succ

/-- Bounds for the functions with the signatures `S`, as `Funs S` holds their meanings. -/
inductive Bounds : List Sig → Type where
  | nil : Bounds []
  | cons (b : Env g.params → Nat) (rest : Bounds S) : Bounds (g :: S)

def Bounds.get : {S : List Sig} → {g : Sig} → Bounds S → FVar S g → Env g.params → Nat
  | _, _, .cons b _, .here => b
  | _, _, .cons _ rest, .there h => rest.get h

/-- `callMoves` on the modes of the slots. -/
def callMovesAt (modes : List Mode) (live : Nat → Bool) {S : List Sig} {Γ : List Ty} {g : Sig}
    (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) (i : Fin g.params.length) :
    Bool :=
  g.mode i == .owned &&
    match (args i).varIndex? with
    | some k => modeAt modes k == .owned && !live k &&
        !(argsAny fun j => j != i && !(g.params.get j).scalar && (args j).uses k)
    | none => false

/-- The bytes of `Expr.ownedCode`: those of `Var.ownedCode` for a variable, and none otherwise. -/
def Expr.ownedCost (modes : List Mode) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → Nat
  | _, _, .var x, env => x.ownedCost modes live (env.get x)
  | _, _, _, _ => 0

/-- The allocation bound of the code of an expression with the variables' modes `modes` and the
variables `live` live after it, for the functions `funs` with the bounds `bounds` and the values
`env` of its variables. -/
def Expr.allocs (funs : Funs S) (bounds : Bounds S) (modes : List Mode) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → Nat
  | _, _, .word _, _ | _, _, .bool _, _ | _, _, .float _, _ => 0
  | _, _, .var x, env => x.cost modes live (env.get x)
  | _, _, .bin _ left right, env | _, _, .cmp _ left right, env
  | _, _, .fbin _ left right, env | _, _, .fcmp _ left right, env
  | _, _, .and left right, env | _, _, .or left right, env
  | _, _, .mk left right, env =>
    left.allocs funs bounds modes (fun i => live i || right.uses i) env +
      right.allocs funs bounds modes live env
  | _, _, .not e, env | _, _, .funary _ e, env | _, _, .toFloat _ e, env
  | _, _, .toWord _ e, env => e.allocs funs bounds modes live env
  | _, _, .ite (t := t) c thenE elseE, env =>
    let mode := (thenE.mode modes).join (elseE.mode modes)
    c.allocs funs bounds modes (fun i => live i || thenE.uses i || elseE.uses i) env +
      if c.denote funs env then
        thenE.allocs funs bounds modes live env +
          coerceCost t (thenE.mode modes) mode (thenE.denote funs env)
      else
        elseE.allocs funs bounds modes live env +
          coerceCost t (elseE.mode modes) mode (elseE.denote funs env)
  | _, _, .letE value body, env =>
    value.allocs funs bounds modes (fun i => live i || body.uses (i + 1)) env +
      body.allocs funs bounds (value.mode modes :: modes) (shift 1 live)
        (.cons (value.denote funs env) env)
  | _, _, .call (g := g) f args, env =>
    let all := fun i => live i || argsAny fun j => (args j).uses i
    let kept := fun i =>
      all i && !(argsAny fun j => callMovesAt modes live args j && (args j).uses i)
    (argsSum fun i =>
      if (g.params.get i).scalar then (args i).allocs funs bounds modes all env
      else if g.mode i = .owned then (args i).ownedCost modes kept env else 0) +
      bounds.get f (Env.ofFn fun i => (args i).denote funs env)
  | _, _, .pair (s := s) (t := t) first second, env =>
    let mode := (first.mode modes).join (second.mode modes)
    first.allocs funs bounds modes (fun i => live i || second.uses i) env +
      coerceCost s (first.mode modes) mode (first.denote funs env) +
      second.allocs funs bounds modes live env +
      coerceCost t (second.mode modes) mode (second.denote funs env)
  | _, _, .letPair e body, env =>
    let mode := e.mode modes
    let p := e.denote funs env
    e.allocs funs bounds modes (fun i => live i || body.uses (i + 2)) env +
      body.allocs funs bounds (mode :: mode :: modes) (shift 2 live) (.cons p.2 (.cons p.1 env))
  | _, _, .loop (t := t) count init cond body, env =>
    let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
    let all := fun i => live i || cond.uses (i + 1) || body.uses (i + 2)
    count.allocs funs bounds modes (fun i => all i || init.uses i) env +
      init.allocs funs bounds modes all env +
      coerceCost t (init.mode modes) mode (init.denote funs env) +
      loopCost
        (fun s => cond.allocs funs bounds (.borrowed :: modes) (fun j => j == 0 || shift 1 all j)
          (.cons s env))
        (fun s => cond.denote funs (.cons s env))
        (fun i s =>
          body.allocs funs bounds (mode :: .borrowed :: modes) (shift 2 all)
              (.cons s (.cons i env)) +
            coerceCost t (body.mode (mode :: .borrowed :: modes)) mode
              (body.denote funs (.cons s (.cons i env))))
        (fun i s => body.denote funs (.cons s (.cons i env)))
        (count.denote funs env).toNat 0 (init.denote funs env)
  | _, _, .size _, _ | _, _, .proj _ _, _ => 0
  | _, _, .get x i, env => i.allocs funs bounds modes (fun j => live j || j == x.index) env
  | _, _, .set x i v, env =>
    i.allocs funs bounds modes (fun j => live j || j == x.index || v.uses j) env +
      v.allocs funs bounds modes (fun j => live j || j == x.index) env +
      x.ownedCost modes live (env.get x)
  | _, _, .push (e := e) x v, env =>
    v.allocs funs bounds modes (fun j => live j || j == x.index) env +
      x.roomCost modes live (env.get x) (wordCount e.width).toNat
  | _, _, .append (e := e) x y, env =>
    x.roomCost modes (fun k => live k || k == y.index) (env.get x) ((env.get y).size * e.width)
  | _, _, .insertAt (e := e) x i v, env =>
    i.allocs funs bounds modes (fun j => live j || j == x.index || v.uses j) env +
      v.allocs funs bounds modes (fun j => live j || j == x.index) env +
      x.roomCost modes live (env.get x) (wordCount e.width).toNat
  | _, _, .eraseAt x i, env =>
    i.allocs funs bounds modes (fun j => live j || j == x.index) env +
      x.ownedCost modes live (env.get x)
  | _, _, .build (e := e) count elem, env =>
    let all := fun i => live i || elem.uses (i + 1)
    let n := (count.denote funs env).toNat
    count.allocs funs bounds modes all env + allocCost ((n * e.width + 1) * 8) +
      sumBelow (fun k => elem.allocs funs bounds (.borrowed :: modes) (shift 1 all)
        (.cons (UInt64.ofNat k) env)) n

/-- The modes of a function's parameters at entry. -/
def entryModes (params : List Ty) (modes : List Mode) : List Mode :=
  (paramSlots params modes 0).map Slot.mode

/-- The allocation bound of a function: its body's, with nothing live after it, and the copy of
a borrowed result. -/
def Func.bound (func : Func S) (funs : Funs S) (bounds : Bounds S) (args : Env func.params) :
    Nat :=
  let modes := entryModes func.params func.modes
  func.body.allocs funs bounds modes (fun _ => false) args +
    coerceCost func.result (func.body.mode modes) .owned (func.body.denote funs args)

/-- The bounds of a program's functions, for the meanings `funs`.  A recursive function's code
takes the call depth, which the bound does not cover, and gets 0. -/
def Prog.bounds : {S : List Sig} → Prog S → Funs S → Bounds S
  | _, .nil, .nil => .nil
  | _, .cons f rest, .cons _ funs => .cons (f.bound funs (rest.bounds funs)) (rest.bounds funs)
  | _, .consRec _ rest, .cons _ funs => .cons (fun _ => 0) (rest.bounds funs)

end Verified
