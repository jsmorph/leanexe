import Verified.Compile
import Verified.TailRun

/-! The allocation bound: the bytes by which the code of an expression can raise the allocator's
`top`, as a Lean function of the values of its variables.  An allocation of `b` payload bytes
either reuses a free block, which leaves `top`, or raises `top` by `48 + b`, and the code requests
only multiples of 8 of at least 8 bytes, so `allocCost b = 48 + b`.  The bound follows
`Expr.code` with the modes of the variables, the same live sets, and flags that state which
variables are paid: it counts each copy that the modes and the live sets call for, each array that
`build` makes, and each block of `push`, `++`, and `insertAt`.  An owned array that dies and is not
paid is charged a block of twice the bytes of its new length and twice the added bytes, even when
it extends in place.  A paid one is charged a header and four times the added bytes, which with
its potential pay for its growth.  The bound ignores the reuse of freed blocks. -/

namespace Verified

/-- The growth of `top` for an allocation of `bytes` payload bytes that no free block supplies. -/
def allocCost (bytes : Nat) : Nat := 48 + bytes

/-- The bytes that a copy of a value of type `t` costs: a block for each of its arrays, whose
length word counts words. -/
def Ty.copyCost : (t : Ty) → t.denote → Nat
  | .elem _, _ => 0
  | .pair a b, v => a.copyCost v.1 + b.copyCost v.2
  | .array e, xs => allocCost ((xs.size * e.width + 1) * 8)

/-- The most potential that a value held in owned mode can have: twice the bytes of each array's
length word and words. -/
def Ty.credit : (t : Ty) → t.denote → Nat
  | .elem _, _ => 0
  | .pair a b, v => a.credit v.1 + b.credit v.2
  | .array e, xs => 16 * (xs.size * e.width + 1)

/-- The credits of the arguments that `sel` picks. -/
def Env.credit (sel : Nat → Bool) : {Γ : List Ty} → Env Γ → Nat
  | _, .nil => 0
  | _, .cons (t := t) v env => (if sel 0 then t.credit v else 0) + Env.credit (fun i => sel (i + 1))
      env

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

/-- Whether variable `i` is paid, among the flags `paid`: whether the potential of its arrays is
counted. -/
def paidAt (paid : List Bool) (i : Nat) : Bool := paid.getD i false

/-- The charge of `Var.roomCode` for an extension by `ext` words of the array `xs` of `x`: for an
owned array that dies, a header and four times the added bytes when it is paid, which with its
potential cover the bytes of the code and the result's potential, and a block of twice the new
length's bytes and twice the added bytes when it is not, which cover both alone, and a copy at the
new length otherwise. -/
def Var.roomCost (modes : List Mode) (paid : List Bool) (live : Nat → Bool) {Γ : List Ty}
    {e : Elem} (x : Var Γ (.array e)) (xs : Array e.denote) (ext : Nat) : Nat :=
  let len := xs.size * e.width + ext
  if modeAt modes x.index = .owned ∧ live x.index = false then
    if paidAt paid x.index then allocCost (32 * ext) else allocCost (16 * (len + 1)) + 16 * ext
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

theorem argsSum_le : {n : Nat} → {f g : Fin n → Nat} → (∀ i, f i ≤ g i) →
    argsSum f ≤ argsSum g
  | 0, _, _, _ => Nat.le_refl 0
  | _ + 1, _, _, h => Nat.add_le_add (h 0) (argsSum_le fun i => h i.succ)

theorem argsSum_add : {n : Nat} → (f g : Fin n → Nat) →
    argsSum (fun i => f i + g i) = argsSum f + argsSum g
  | 0, _, _ => rfl
  | _ + 1, f, g => by
    simp only [argsSum, argsSum_add (fun i => f i.succ) (fun i => g i.succ)]
    omega

/-- Bounds for the functions with the signatures `S`, as `Funs S` holds their meanings. -/
inductive Bounds : List Sig → Type where
  | nil : Bounds []
  | cons (b : Env g.params → Nat) (rest : Bounds S) : Bounds (g :: S)

def Bounds.get : {S : List Sig} → {g : Sig} → Bounds S → FVar S g → Env g.params → Nat
  | _, _, .cons b _, .here => b
  | _, _, .cons _ rest, .there h => rest.get h

/-- The paid flags of the functions with the signatures `S`: for each, whether each of its
parameters is paid and whether its result is. -/
inductive Flags : List Sig → Type where
  | nil : Flags []
  | cons (params : List Bool) (result : Bool) (rest : Flags S) : Flags (g :: S)

/-- The flags of the functions, in the order of `S`. -/
def Flags.toList : {S : List Sig} → Flags S → List (List Bool × Bool)
  | _, .nil => []
  | _, .cons ps r rest => (ps, r) :: rest.toList

/-- The flags of the parameters of function `f`.  The lookup goes by `f`'s index: the kernel
reduces a match on `Flags S` and `FVar S g` together in tens of milliseconds per step of `f`, and
the reflector evaluates these flags at every argument of every call. -/
def Flags.params {S : List Sig} {g : Sig} (flags : Flags S) (f : FVar S g) : List Bool :=
  (flags.toList.getD f.index ([], false)).1

/-- Whether the result of function `f` is paid. -/
def Flags.result {S : List Sig} {g : Sig} (flags : Flags S) (f : FVar S g) : Bool :=
  (flags.toList.getD f.index ([], false)).2

/-- `callMoves` on the modes of the slots. -/
def callMovesAt (modes : List Mode) (live : Nat → Bool) {S : List Sig} {Γ : List Ty} {g : Sig}
    (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) (i : Fin g.params.length) :
    Bool :=
  g.mode i == .owned &&
    match (args i).varIndex? with
    | some k => modeAt modes k == .owned && !live k &&
        !(argsAny fun j => j != i && !(g.params.get j).scalar && (args j).uses k)
    | none => false

/-- Whether an expression is a paid variable. -/
def Expr.paidVar (paid : List Bool) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .var x => paidAt paid x.index
  | _, _, _ => false

/-- The bytes of `Expr.ownedCode`: those of `Var.ownedCode` for a variable, and none otherwise. -/
def Expr.ownedCost (modes : List Mode) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → Nat
  | _, _, .var x, env => x.ownedCost modes live (env.get x)
  | _, _, _, _ => 0

/-- Whether an expression extends an array: whether it holds `push`, `++`, `insertAt`, or a call
of a function with a paid parameter, given the flags `flags`. -/
def Expr.grows (flags : Flags S) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .push _ _ | _, _, .append _ _ | _, _, .insertAt _ _ _ => true
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right | _, _, .and left right | _, _, .or left right
  | _, _, .mk left right | _, _, .pair left right => left.grows flags || right.grows flags
  | _, _, .not e | _, _, .funary _ e | _, _, .toFloat _ e | _, _, .toWord _ e => e.grows flags
  | _, _, .ite c thenE elseE => c.grows flags || thenE.grows flags || elseE.grows flags
  | _, _, .letE value body | _, _, .letPair value body => value.grows flags || body.grows flags
  | _, _, .call f args =>
    (argsAny fun i => (args i).grows flags) || (flags.params f).any id
  | _, _, .loop count init cond body =>
    count.grows flags || init.grows flags || cond.grows flags || body.grows flags
  | _, _, .fold _ init body => init.grows flags || body.grows flags
  | _, _, .build count elem => count.grows flags || elem.grows flags
  | _, _, .get _ i | _, _, .eraseAt _ i => i.grows flags
  | _, _, .set _ i v => i.grows flags || v.grows flags
  | _, _, _ => false

/-- Whether parameter `i` of a function with signature `g` and parameter flags `pf` is paid and
owned, so that its potential counts. -/
def Sig.paidSel (g : Sig) (pf : List Bool) (i : Nat) : Bool := paidAt pf i && g.mode i == .owned

/-- The selection `sel` of a function's arguments, for its code that takes the call depth first:
position 0, the depth word, is never picked, and position `i + 1` is picked when `sel i` holds. -/
def depthSelOf (sel : Nat → Bool) : Nat → Bool
  | 0 => false
  | i + 1 => sel i

/-- `Sig.paidSel` for the arguments of a function's code that takes the call depth first. -/
def Sig.depthSel (g : Sig) (pf : List Bool) : Nat → Bool := depthSelOf (g.paidSel pf)

/-- The credits that a call of `f` charges: that of each argument at a paid owned parameter, unless
the argument is a paid variable that the call moves, whose potential the caller holds. -/
def callCredits (funs : Funs S) (flags : Flags S) (modes : List Mode) (paid : List Bool)
    (live : Nat → Bool) {Γ : List Ty} {g : Sig} (f : FVar S g)
    (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) (env : Env Γ) : Nat :=
  argsSum fun i =>
    if g.paidSel (flags.params f) i && !(callMovesAt modes live args i && (args i).paidVar paid) then
      (g.params.get i).credit ((args i).denote funs env)
    else 0

/-- Whether the potential of an expression's value is counted, given the variables' modes and
flags and the variables live after it: for the growth of an owned array that dies, for a moved
variable that is paid, for an `if` whose branches are both paid, for a `let` whose body's value is
paid, for a loop whose state is paid, as `Expr.statePaid` states, and for a call of a function
whose result holds arrays and is paid, given the functions' flags `flags`. -/
def Expr.paid (flags : Flags S) (modes : List Mode) (paid : List Bool) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .var x => modeAt modes x.index == .owned && !live x.index && paidAt paid x.index
  | _, _, .push x _ | _, _, .insertAt x _ _ => modeAt modes x.index == .owned && !live x.index
  | _, _, .append x y => modeAt modes x.index == .owned && !(live x.index || x.index == y.index)
  | _, _, .ite _ thenE elseE =>
    thenE.paid flags modes paid live && elseE.paid flags modes paid live
  | _, _, .letE value body =>
    body.paid flags (value.mode modes :: modes)
      (value.paid flags modes paid (fun i => live i || body.uses (i + 1)) :: paid) (shift 1 live)
  | _, _, .loop _ init cond body =>
    let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
    mode == .owned && body.grows flags &&
      body.paid flags (mode :: .borrowed :: modes) (true :: false :: paid)
        (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2))
  | _, _, .fold x init body =>
    let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: .borrowed :: modes))
    let all := fun i => live i || false || (Expr.foldStep x body).uses (i + 2)
    mode == .owned && body.grows flags &&
      body.paid flags (.borrowed :: mode :: .borrowed :: modes) (false :: true :: false :: paid)
        (shift 1 (shift 2 all))
  | _, _, .call (g := g) f _ => !g.result.scalar && flags.result f
  | _, _, _ => false

/-- Whether a loop's state is paid: the loop's mode is owned, its body extends an array, and the
body's value is paid when the state is, so that each state passes its potential to the next. -/
def Expr.statePaid {Γ : List Ty} {t : Ty} (flags : Flags S) (modes : List Mode) (paid : List Bool)
    (live : Nat → Bool) (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool)
    (body : Expr S (t :: .word :: Γ) t) : Bool :=
  let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
  mode == .owned && body.grows flags &&
    body.paid flags (mode :: .borrowed :: modes) (true :: false :: paid)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2))

/-- A paid value is owned. -/
theorem Expr.mode_of_paid {flags : Flags S} {Γ : List Ty} {t : Ty} (e : Expr S Γ t) :
    ∀ {modes : List Mode} {paid : List Bool} {live : Nat → Bool},
      e.paid flags modes paid live = true → e.mode modes = .owned := by
  induction e <;> intro modes paid live h
  case var x =>
    simp only [Expr.paid, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1
  case ite c thenE elseE _ thenIh _ =>
    simp only [Expr.paid, Bool.and_eq_true] at h
    simp [Expr.mode, Mode.join, thenIh h.1]
  case letE value body _ bodyIh => exact bodyIh h
  case loop count init cond body _ _ _ _ =>
    simp only [Expr.paid, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1
  case fold x init body _ _ =>
    simp only [Expr.paid, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1
  case call g f args _ =>
    simp only [Expr.paid, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [Expr.mode, h.1]
  all_goals first | rfl | simp [Expr.paid] at h

theorem Expr.paid_loop {Γ : List Ty} {t : Ty} (flags : Flags S) (modes : List Mode)
    (paid : List Bool) (live : Nat → Bool) (count : Expr S Γ .word) (init : Expr S Γ t)
    (cond : Expr S (t :: Γ) .bool) (body : Expr S (t :: .word :: Γ) t) :
    (Expr.loop count init cond body).paid flags modes paid live =
      Expr.statePaid flags modes paid live init cond body := by
  simp only [Expr.paid, Expr.statePaid]

/-- The allocation bound of the code of an expression with the variables' modes `modes` and flags
`paid` and the variables `live` live after it, for the functions `funs` with the flags `flags` and
the bounds `bounds` and the values `env` of its variables, together with the potential of a paid
value. -/
def loopAlloc (funs : Funs S) (flags : Flags S) (modes : List Mode) (paid : List Bool)
    (live : Nat → Bool) {Γ : List Ty} {t : Ty} (count : Expr S Γ .word) (init : Expr S Γ t)
    (cond : Expr S (t :: Γ) .bool) (body : Expr S (t :: .word :: Γ) t)
    (countAlloc initAlloc : (Nat → Bool) → Env Γ → Nat)
    (condAlloc : List Mode → List Bool → (Nat → Bool) → Env (t :: Γ) → Nat)
    (bodyAlloc : List Mode → List Bool → (Nat → Bool) → Env (t :: .word :: Γ) → Nat)
    (env : Env Γ) : Nat :=
  let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
  let all := fun i => live i || cond.uses (i + 1) || body.uses (i + 2)
  let ps := Expr.statePaid flags modes paid live init cond body
  countAlloc (fun i => all i || init.uses i) env +
    initAlloc all env +
    coerceCost t (init.mode modes) mode (init.denote funs env) +
    (if ps && !init.paid flags modes paid all then t.credit (init.denote funs env) else 0) +
    loopCost
      (fun s => condAlloc (.borrowed :: modes) (false :: paid)
        (fun j => j == 0 || shift 1 all j)
        (.cons s env))
      (fun s => cond.denote funs (.cons s env))
      (fun i s =>
        bodyAlloc (mode :: .borrowed :: modes) (ps :: false :: paid)
          (shift 2 all)
            (.cons s (.cons i env)) +
          coerceCost t (body.mode (mode :: .borrowed :: modes)) mode
            (body.denote funs (.cons s (.cons i env))))
      (fun i s => body.denote funs (.cons s (.cons i env)))
      (count.denote funs env).toNat 0 (init.denote funs env)

def Expr.allocs (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (modes : List Mode)
    (paid : List Bool)
    (live : Nat → Bool) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → Nat
  | _, _, .word _, _ | _, _, .bool _, _ | _, _, .float _, _ | _, _, .float32 _, _ => 0
  | _, _, .var x, env => x.cost modes live (env.get x)
  | _, _, .bin _ left right, env | _, _, .cmp _ left right, env
  | _, _, .fbin _ left right, env | _, _, .fcmp _ left right, env
  | _, _, .and left right, env | _, _, .or left right, env
  | _, _, .mk left right, env =>
    left.allocs funs flags bounds modes paid (fun i => live i || right.uses i) env +
      right.allocs funs flags bounds modes paid live env
  | _, _, .not e, env | _, _, .funary _ e, env | _, _, .toFloat _ e, env
  | _, _, .toWord _ e, env => e.allocs funs flags bounds modes paid live env
  | _, _, .ite (t := t) c thenE elseE, env =>
    let mode := (thenE.mode modes).join (elseE.mode modes)
    c.allocs funs flags bounds modes paid (fun i => live i || thenE.uses i || elseE.uses i) env +
      if c.denote funs env then
        thenE.allocs funs flags bounds modes paid live env +
          coerceCost t (thenE.mode modes) mode (thenE.denote funs env)
      else
        elseE.allocs funs flags bounds modes paid live env +
          coerceCost t (elseE.mode modes) mode (elseE.denote funs env)
  | _, _, .letE value body, env =>
    value.allocs funs flags bounds modes paid (fun i => live i || body.uses (i + 1)) env +
      body.allocs funs flags bounds (value.mode modes :: modes)
        (value.paid flags modes paid (fun i => live i || body.uses (i + 1)) :: paid) (shift 1 live)
        (.cons (value.denote funs env) env)
  | _, _, .call (g := g) f args, env =>
    let all := fun i => live i || argsAny fun j => (args j).uses i
    let kept := fun i =>
      all i && !(argsAny fun j => callMovesAt modes live args j && (args j).uses i)
    (argsSum fun i =>
      if (g.params.get i).scalar then (args i).allocs funs flags bounds modes paid all env
      else if g.mode i = .owned then (args i).ownedCost modes kept env else 0) +
      callCredits funs flags modes paid live f args env +
      bounds.get f (Env.ofFn fun i => (args i).denote funs env)
  | _, _, .pair (s := s) (t := t) first second, env =>
    let mode := (first.mode modes).join (second.mode modes)
    first.allocs funs flags bounds modes paid (fun i => live i || second.uses i) env +
      coerceCost s (first.mode modes) mode (first.denote funs env) +
      second.allocs funs flags bounds modes paid live env +
      coerceCost t (second.mode modes) mode (second.denote funs env)
  | _, _, .letPair e body, env =>
    let mode := e.mode modes
    let p := e.denote funs env
    e.allocs funs flags bounds modes paid (fun i => live i || body.uses (i + 2)) env +
      body.allocs funs flags bounds (mode :: mode :: modes) (false :: false :: paid) (shift 2 live)
        (.cons p.2 (.cons p.1 env))
  | _, _, .loop count init cond body, env =>
    loopAlloc funs flags modes paid live count init cond body
      (fun live env => count.allocs funs flags bounds modes paid live env)
      (fun live env => init.allocs funs flags bounds modes paid live env)
      (fun modes paid live env => cond.allocs funs flags bounds modes paid live env)
      (fun modes paid live env => body.allocs funs flags bounds modes paid live env) env
  | _, _, .fold x init body, env =>
    loopAlloc funs flags modes paid live (.size x) init (.bool true) (Expr.foldStep x body)
      (fun _ _ => 0)
      (fun live env => init.allocs funs flags bounds modes paid live env)
      (fun _ _ _ _ => 0)
      (fun modes paid live env =>
        body.allocs funs flags bounds (.borrowed :: modes) (false :: paid) (shift 1 live)
          (.cons ((env.get (.there (.there x)))[(env.get (.there .here)).toNat]!) env)) env
  | _, _, .size _, _ | _, _, .leSize _ _, _ | _, _, .proj _ _, _ => 0
  | _, _, .get x i, env => i.allocs funs flags bounds modes paid (fun j => live j || j == x.index) env
  | _, _, .set x i v, env =>
    i.allocs funs flags bounds modes paid (fun j => live j || j == x.index || v.uses j) env +
      v.allocs funs flags bounds modes paid (fun j => live j || j == x.index) env +
      x.ownedCost modes live (env.get x)
  | _, _, .push (e := e) x v, env =>
    v.allocs funs flags bounds modes paid (fun j => live j || j == x.index) env +
      x.roomCost modes paid live (env.get x) (wordCount e.width).toNat
  | _, _, .append (e := e) x y, env =>
    x.roomCost modes paid (fun k => live k || k == y.index) (env.get x) ((env.get y).size * e.width)
  | _, _, .insertAt (e := e) x i v, env =>
    i.allocs funs flags bounds modes paid (fun j => live j || j == x.index || v.uses j) env +
      v.allocs funs flags bounds modes paid (fun j => live j || j == x.index) env +
      x.roomCost modes paid live (env.get x) (wordCount e.width).toNat
  | _, _, .eraseAt x i, env =>
    i.allocs funs flags bounds modes paid (fun j => live j || j == x.index) env +
      x.ownedCost modes live (env.get x)
  | _, _, .build (e := e) count elem, env =>
    let all := fun i => live i || elem.uses (i + 1)
    let n := (count.denote funs env).toNat
    count.allocs funs flags bounds modes paid all env + allocCost ((n * e.width + 1) * 8) +
      sumBelow (fun k => elem.allocs funs flags bounds (.borrowed :: modes) (false :: paid)
        (shift 1 all)
        (.cons (UInt64.ofNat k) env)) n

/-- The modes of a function's parameters at entry. -/
def entryModes (params : List Ty) (modes : List Mode) : List Mode :=
  (paramSlots params modes 0).map Slot.mode

/-- The flags of a function's parameters: an owned parameter, which holds an array, is paid when
`grows` holds, that is, when the body extends an array. -/
def paramFlags (params : List Ty) (modes : List Mode) (grows : Bool) : List Bool :=
  (entryModes params modes).map fun m => m == .owned && grows

/-- The allocation bound of a function with the parameter modes `modes`, the parameter flags `pf`,
and the body `body`: the body's, with nothing live after it, and the copy of a borrowed result. -/
def bodyBound {params : List Ty} {result : Ty} (modes : List Mode) (pf : List Bool)
    (body : Expr S params result) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (args : Env params) : Nat :=
  let ms := entryModes params modes
  body.allocs funs flags bounds ms pf (fun _ => false) args +
    coerceCost result (body.mode ms) .owned (body.denote funs args)

/-- The flags of a function's parameters, given the flags `flags` of the functions it calls. -/
def Func.paidParams (func : Func S) (flags : Flags S) : List Bool :=
  paramFlags func.params func.modes (func.body.grows flags)

/-- Whether a function's result is paid: whether it holds arrays and the body's value is paid with
the parameters' flags. -/
def Func.paidResult (func : Func S) (flags : Flags S) : Bool :=
  !func.result.scalar &&
    func.body.paid flags (entryModes func.params func.modes) (func.paidParams flags)
      (fun _ => false)

/-- The allocation bound of a function, without the credits of its paid parameters. -/
def Func.bound (func : Func S) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (args : Env func.params) : Nat :=
  bodyBound func.modes (func.paidParams flags) func.body funs flags bounds args

/-- The flags of a recursive function's parameters, with its calls of itself counted as extending
nothing. -/
def RecFunc.paidParams (func : RecFunc S) (flags : Flags S) : List Bool :=
  paramFlags func.params func.modes (func.body.grows (.cons [] false flags))

/-- Whether a recursive function's result is paid: whether it holds arrays and the body's value is
paid when the function's calls of itself return paid values, a flag that the check confirms. -/
def RecFunc.paidResult (func : RecFunc S) (flags : Flags S) : Bool :=
  !func.result.scalar &&
    func.body.paid (.cons (func.paidParams flags) true flags)
      (entryModes func.params func.modes) (func.paidParams flags) (fun _ => false)

/-- The flags of a recursive function and of the functions it calls. -/
def RecFunc.flags (func : RecFunc S) (flags : Flags S) : Flags (func.sig :: S) :=
  .cons (func.paidParams flags) (func.paidResult flags) flags

def TailBody.grows (flags : Flags S) : {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.grows flags
  | _, .next args => argsAny fun i => (args i).grows flags
  | _, .ite cond yes no => cond.grows flags || yes.grows flags || no.grows flags
  | _, .letE value body | _, .letPair value body => value.grows flags || body.grows flags

def TailFunc.paidParams (func : TailFunc S) (flags : Flags S) : List Bool :=
  paramFlags func.params func.modes (func.body.grows flags)

def TailBody.paidResult (flags : Flags S) (modes : List Mode) (paid : List Bool) :
    {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.paid flags modes paid (fun _ => false)
  | _, .next _ => true
  | _, .ite _ yes no => yes.paidResult flags modes paid && no.paidResult flags modes paid
  | _, .letE value body =>
    body.paidResult flags (value.mode modes :: modes)
      (value.paid flags modes paid (fun i => body.uses (i + 1)) :: paid)
  | _, .letPair value body =>
    body.paidResult flags (value.mode modes :: value.mode modes :: modes) (false :: false :: paid)

def TailFunc.paidResult (func : TailFunc S) (flags : Flags S) : Bool :=
  !func.result.scalar && func.body.paidResult flags (entryModes func.params func.modes)
    (func.paidParams flags)

def TailFunc.flags (func : TailFunc S) (flags : Flags S) : Flags (func.sig :: S) :=
  .cons (func.paidParams flags) (func.paidResult flags) flags

/-- The flags of a program's functions. -/
def Prog.flags : {S : List Sig} → Prog S → Flags S
  | _, .nil => .nil
  | _, .cons f rest => .cons (f.paidParams rest.flags) (f.paidResult rest.flags) rest.flags
  | _, .consRec f rest => f.flags rest.flags
  | _, .consTail f rest => f.flags rest.flags

/-- Whether a call of each function with the signatures `S` finds the frames it needs, as
`Bounds S` holds their bounds. -/
inductive Fits : List Sig → Type where
  | nil : Fits []
  | cons (b : Env g.params → Bool) (rest : Fits S) : Fits (g :: S)

def Fits.get : {S : List Sig} → {g : Sig} → Fits S → FVar S g → Env g.params → Bool
  | _, _, .cons b _, .here => b
  | _, _, .cons _ rest, .there h => rest.get h

/-- Whether `b i` holds for every index `i` of a function's parameters. -/
def argsAll : {n : Nat} → ((i : Fin n) → Bool) → Bool
  | 0, _ => true
  | _ + 1, b => b 0 && argsAll fun i => b i.succ

theorem argsAll_false : {n : Nat} → (b : Fin n → Bool) → (i : Fin n) → b i = false →
    argsAll b = false
  | _ + 1, b, ⟨0, _⟩, h => by
    have h0 : b 0 = false := h
    simp [argsAll, h0]
  | _ + 1, b, ⟨i + 1, hi⟩, h => by
    simp only [argsAll, Bool.and_eq_false_iff]
    exact Or.inr (argsAll_false (fun j => b j.succ) ⟨i, by omega⟩ h)

/-- Whether `f k` holds for every `k` below `n`. -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow f n && f n

theorem allBelow_get {f : Nat → Bool} : {n : Nat} → allBelow f n = true → ∀ k, k < n →
    f k = true
  | n + 1, h, k, hk => by
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact allBelow_get h.1 k hk
    · exact h.2

/-- Whether a loop's iterations from index `i`, with `n` indices left, from the state `s`, find
their frames: the condition at each state it tests, and the body at each state that passes it,
until the first state that fails it. -/
def loopFits {α : Type} (condFits : α → Bool) (cond : α → Bool) (bodyFits : UInt64 → α → Bool)
    (step : UInt64 → α → α) : Nat → UInt64 → α → Bool
  | 0, _, _ => true
  | n + 1, i, s =>
    condFits s &&
      if cond s then bodyFits i s && loopFits condFits cond bodyFits step n (i + 1) (step i s)
      else true

/-- Whether the code of an expression finds the frames it needs, for the functions `funs` whose
calls find theirs as `fits` states: whether every call that the run makes of a function whose code
takes the call depth finds its frames.  It follows `Expr.allocs`, with `&&` in place of `+`. -/
def Expr.fits (funs : Funs S) (fits : Fits S) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → Bool
  | _, _, .word _, _ | _, _, .bool _, _ | _, _, .float _, _ | _, _, .float32 _, _ | _, _, .var _, _ => true
  | _, _, .bin _ left right, env | _, _, .cmp _ left right, env
  | _, _, .fbin _ left right, env | _, _, .fcmp _ left right, env
  | _, _, .and left right, env | _, _, .or left right, env
  | _, _, .mk left right, env | _, _, .pair left right, env =>
    left.fits funs fits env && right.fits funs fits env
  | _, _, .not e, env | _, _, .funary _ e, env | _, _, .toFloat _ e, env
  | _, _, .toWord _ e, env => e.fits funs fits env
  | _, _, .ite c thenE elseE, env =>
    c.fits funs fits env &&
      if c.denote funs env then thenE.fits funs fits env else elseE.fits funs fits env
  | _, _, .letE value body, env =>
    value.fits funs fits env && body.fits funs fits (.cons (value.denote funs env) env)
  | _, _, .call (g := g) f args, env =>
    (argsAll fun i => (args i).fits funs fits env) &&
      if g.depth then fits.get f (Env.ofFn fun i => (args i).denote funs env) else true
  | _, _, .letPair e body, env =>
    let p := e.denote funs env
    e.fits funs fits env && body.fits funs fits (.cons p.2 (.cons p.1 env))
  | _, _, .loop count init cond body, env =>
    count.fits funs fits env && init.fits funs fits env &&
      loopFits (fun s => cond.fits funs fits (.cons s env)) (fun s => cond.denote funs (.cons s env))
        (fun i s => body.fits funs fits (.cons s (.cons i env)))
        (fun i s => body.denote funs (.cons s (.cons i env)))
        (count.denote funs env).toNat 0 (init.denote funs env)
  | _, _, .fold x init body, env =>
    init.fits funs fits env &&
      loopFits (fun _ => true) (fun _ => true)
        (fun i s => body.fits funs fits (.cons ((env.get x)[i.toNat]!) (.cons s (.cons i env))))
        (fun i s => body.denote funs (.cons ((env.get x)[i.toNat]!) (.cons s (.cons i env))))
        (env.get x).size.toUInt64.toNat 0 (init.denote funs env)
  | _, _, .size _, _ | _, _, .leSize _ _, _ | _, _, .proj _ _, _
  | _, _, .append _ _, _ => true
  | _, _, .get _ i, env | _, _, .eraseAt _ i, env => i.fits funs fits env
  | _, _, .set _ i v, env | _, _, .insertAt _ i v, env =>
    i.fits funs fits env && v.fits funs fits env
  | _, _, .push _ v, env => v.fits funs fits env
  | _, _, .build count elem, env =>
    count.fits funs fits env &&
      allBelow (fun k => elem.fits funs fits (.cons (UInt64.ofNat k) env))
        (count.denote funs env).toNat

theorem argsAny_eq_false : {n : Nat} → {b : Fin n → Bool} → argsAny b = false → ∀ i, b i = false
  | _ + 1, b, h, ⟨0, _⟩ => by
    simp only [argsAny, Bool.or_eq_false_iff] at h; exact h.1
  | _ + 1, b, h, ⟨i + 1, hi⟩ => by
    simp only [argsAny, Bool.or_eq_false_iff] at h
    exact argsAny_eq_false (b := fun j => b j.succ) h.2 ⟨i, by omega⟩

theorem argsAll_true : {n : Nat} → {b : Fin n → Bool} → (∀ i, b i = true) → argsAll b = true
  | 0, _, _ => rfl
  | _ + 1, b, h => by
    simp only [argsAll, Bool.and_eq_true]
    exact ⟨h 0, argsAll_true fun i => h i.succ⟩

theorem allBelow_true {f : Nat → Bool} (h : ∀ k, f k = true) : ∀ n, allBelow f n = true
  | 0 => rfl
  | n + 1 => by simp [allBelow, allBelow_true h n, h n]

theorem loopFits_true {α : Type} {cf : α → Bool} {cond : α → Bool} {bf : UInt64 → α → Bool}
    {step : UInt64 → α → α} (hc : ∀ s, cf s = true) (hb : ∀ i s, bf i s = true) :
    ∀ n i s, loopFits cf cond bf step n i s = true
  | 0, _, _ => rfl
  | n + 1, i, s => by
    simp only [loopFits, hc, hb, loopFits_true hc hb n, Bool.true_and]
    split <;> rfl

/-- An expression whose code calls no function that takes the call depth finds its frames. -/
theorem Expr.fits_of_depthCalls (funs : Funs S) (fits : Fits S) {Γ : List Ty} {t : Ty}
    (e : Expr S Γ t) : e.depthCalls = false → ∀ env, e.fits funs fits env = true := by
  induction e with
  | call f args ih =>
    intro hd env
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd
    simp only [Expr.fits, hd.1, Bool.false_eq_true, ↓reduceIte, Bool.and_true]
    exact argsAll_true fun i => ih i (argsAny_eq_false hd.2 i) env
  | loop count init cond body hc hi hcd hb =>
    intro hd env
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd
    simp only [Expr.fits, hc hd.1.1.1, hi hd.1.1.2, Bool.true_and]
    exact loopFits_true (fun s => hcd hd.1.2 _) (fun i s => hb hd.2 _) _ _ _
  | fold x init body hi hb =>
    intro hd env
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd
    simp only [Expr.fits, hi hd.1, Bool.true_and]
    exact loopFits_true (fun _ => rfl) (fun i s => hb hd.2 _) _ _ _
  | build count elem hc he =>
    intro hd env
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd
    simp only [Expr.fits, hc hd.1, Bool.true_and]
    exact allBelow_true (fun k => he hd.2 _) _
  | _ =>
    intro hd env
    simp_all [Expr.depthCalls, Expr.fits]

def tailCredits {params : List Ty} {result : Ty} (funs : Funs S)
    (targetModes : List Mode) (targetPaid : List Bool)
    (modes : List Mode) (paid : List Bool) {Γ : List Ty}
    (args : (i : Fin params.length) → Expr S Γ (params.get i)) (env : Env Γ) : Nat :=
  let g := tailSig params result targetModes
  argsSum fun i =>
    if g.paidSel targetPaid i &&
        !(callMovesAt modes (fun _ => false) (g := g) args i && (args i).paidVar paid) then
      (params.get i).credit ((args i).denote funs env)
    else 0

def TailBody.allocs (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (targetModes : List Mode) (targetPaid : List Bool) :
    {Γ : List Ty} → TailBody S params result Γ → List Mode → List Bool → Env Γ → Nat
  | _, .ret value, modes, paid, env =>
    value.allocs funs flags bounds modes paid (fun _ => false) env +
      coerceCost result (value.mode modes) .owned (value.denote funs env)
  | _, .next args, modes, paid, env =>
    let g := tailSig params result targetModes
    let all := fun i => argsAny fun j => (args j).uses i
    let kept := fun i =>
      all i && !(argsAny fun j => callMovesAt modes (fun _ => false) (g := g) args j &&
        (args j).uses i)
    (argsSum fun i =>
      if (params.get i).scalar then (args i).allocs funs flags bounds modes paid all env
      else if paramMode params targetModes i = .owned then (args i).ownedCost modes kept env
      else 0) + tailCredits (result := result) funs targetModes targetPaid modes paid args env
  | _, .ite cond yes no, modes, paid, env =>
    cond.allocs funs flags bounds modes paid (fun i => yes.uses i || no.uses i) env +
      if cond.denote funs env then yes.allocs funs flags bounds targetModes targetPaid modes paid env
      else no.allocs funs flags bounds targetModes targetPaid modes paid env
  | _, .letE value body, modes, paid, env =>
    value.allocs funs flags bounds modes paid (fun i => body.uses (i + 1)) env +
      body.allocs funs flags bounds targetModes targetPaid (value.mode modes :: modes)
        (value.paid flags modes paid (fun i => body.uses (i + 1)) :: paid)
        (.cons (value.denote funs env) env)
  | _, .letPair value body, modes, paid, env =>
    let mode := value.mode modes
    let pair := value.denote funs env
    value.allocs funs flags bounds modes paid (fun i => body.uses (i + 2)) env +
      body.allocs funs flags bounds targetModes targetPaid (mode :: mode :: modes)
        (false :: false :: paid) (.cons pair.2 (.cons pair.1 env))

def TailBody.fits (funs : Funs S) (fits : Fits S) :
    {Γ : List Ty} → TailBody S params result Γ → Env Γ → Bool
  | _, .ret value, env => value.fits funs fits env
  | _, .next args, env => argsAll fun i => (args i).fits funs fits env
  | _, .ite cond yes no, env =>
    cond.fits funs fits env &&
      if cond.denote funs env then yes.fits funs fits env else no.fits funs fits env
  | _, .letE value body, env =>
    value.fits funs fits env && body.fits funs fits (.cons (value.denote funs env) env)
  | _, .letPair value body, env =>
    let pair := value.denote funs env
    value.fits funs fits env && body.fits funs fits (.cons pair.2 (.cons pair.1 env))

def TailFunc.bound (func : TailFunc S) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (state : Env func.params) : Nat :=
  let paid := func.paidParams flags
  Tail.costAt (func.body.denote funs)
    (func.body.allocs funs flags bounds func.modes paid (entryModes func.params func.modes) paid)
    (func.rank funs state + 1) state

def TailFunc.fits (func : TailFunc S) (funs : Funs S) (fits : Fits S)
    (state : Env func.params) : Bool :=
  Tail.fitsAt (func.body.denote funs) (func.body.fits funs fits) (func.rank funs state + 1) state

def TailFunc.boundAt (func : TailFunc S) (funs : Funs S) (flags : Flags S)
    (rest : Nat → Bounds S) : Nat → Env func.params → Nat
  | 0 => fun _ => 0
  | k + 1 => func.bound funs flags (rest k)

def TailFunc.fitsAt (func : TailFunc S) (funs : Funs S) (rest : Nat → Fits S) :
    Nat → Env func.params → Bool
  | 0 => fun _ => false
  | k + 1 => func.fits funs (rest k)

/-- The bound of a function whose code takes the call depth, with `k` frames available: none at
0, where the guard traps, and otherwise its body's with its callees at `k - 1` frames, from their
bounds `rest` at each number of frames. -/
def Func.boundAt (func : Func S) (funs : Funs S) (flags : Flags S) (rest : Nat → Bounds S) :
    Nat → Env func.params → Nat
  | 0 => fun _ => 0
  | k + 1 => func.bound funs flags (rest k)

/-- The bound of a recursive function with `k` frames available: none at 0, and otherwise its
body's, with itself and its callees at `k - 1` frames. -/
def RecFunc.boundAt (func : RecFunc S) (funs : Funs (func.sig :: S)) (flags : Flags S)
    (rest : Nat → Bounds S) : Nat → Env func.params → Nat
  | 0 => fun _ => 0
  | k + 1 => bodyBound func.modes (func.paidParams flags) func.body funs (func.flags flags)
    (.cons (func.boundAt funs flags rest k) (rest k))

/-- Whether a function whose code takes the call depth finds its frames with `k` frames
available: not at 0, and otherwise whether its body does, with its callees at `k - 1` frames. -/
def Func.fitsAt (func : Func S) (funs : Funs S) (rest : Nat → Fits S) :
    Nat → Env func.params → Bool
  | 0 => fun _ => false
  | k + 1 => func.body.fits funs (rest k)

/-- Whether a recursive function finds its frames with `k` frames available: not at 0, and
otherwise whether its body does, with itself and its callees at `k - 1` frames. -/
def RecFunc.fitsAt (func : RecFunc S) (funs : Funs (func.sig :: S)) (rest : Nat → Fits S) :
    Nat → Env func.params → Bool
  | 0 => fun _ => false
  | k + 1 => func.body.fits funs (.cons (func.fitsAt funs rest k) (rest k))

/-- Whether the calls of a program's functions find their frames when they have `k` frames
available.  A call of a function whose code takes no call depth always does. -/
def Prog.fitsAt : {S : List Sig} → Prog S → Funs S → Nat → Fits S
  | _, .nil, .nil, _ => .nil
  | _, .cons f rest, .cons _ funs, k =>
    .cons (if f.depth then f.fitsAt funs (rest.fitsAt funs) k else fun _ => true)
      (rest.fitsAt funs k)
  | _, .consRec f rest, .cons M funs, k =>
    .cons (f.fitsAt (.cons M funs) (rest.fitsAt funs) k) (rest.fitsAt funs k)
  | _, .consTail f rest, .cons _ funs, k =>
    .cons (if f.depth then f.fitsAt funs (rest.fitsAt funs) k else fun _ => true)
      (rest.fitsAt funs k)

/-- The bounds of a program's functions, for the meanings `funs`, when their calls have `k`
frames available.  A function whose code takes no call depth calls no function that does, so its
bound, with its callees at 0 frames, is the same at every `k`. -/
def Prog.boundsAt : {S : List Sig} → Prog S → Funs S → Nat → Bounds S
  | _, .nil, .nil, _ => .nil
  | _, .cons f rest, .cons _ funs, k =>
    .cons (if f.depth then f.boundAt funs rest.flags (rest.boundsAt funs) k
      else f.bound funs rest.flags (rest.boundsAt funs 0)) (rest.boundsAt funs k)
  | _, .consRec f rest, .cons M funs, k =>
    .cons (f.boundAt (.cons M funs) rest.flags (rest.boundsAt funs) k) (rest.boundsAt funs k)
  | _, .consTail f rest, .cons _ funs, k =>
    .cons (if f.depth then f.boundAt funs rest.flags (rest.boundsAt funs) k
      else f.bound funs rest.flags (rest.boundsAt funs 0)) (rest.boundsAt funs k)

theorem Prog.boundsAt_cons_here (f : Func S) (rest : Prog S) (F : Env f.params → f.result.denote)
    (funs : Funs S) (k : Nat) :
    (Prog.boundsAt (.cons f rest) (.cons F funs) k).get .here =
      if f.depth then f.boundAt funs rest.flags (rest.boundsAt funs) k
      else f.bound funs rest.flags (rest.boundsAt funs 0) := rfl

theorem Prog.fitsAt_cons_here (f : Func S) (rest : Prog S) (F : Env f.params → f.result.denote)
    (funs : Funs S) (k : Nat) :
    (Prog.fitsAt (.cons f rest) (.cons F funs) k).get .here =
      if f.depth then f.fitsAt funs (rest.fitsAt funs) k else fun _ => true := rfl

theorem Prog.boundsAt_consTail_here (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (funs : Funs S) (k : Nat) :
    (Prog.boundsAt (.consTail f rest) (.cons F funs) k).get .here =
      if f.depth then f.boundAt funs rest.flags (rest.boundsAt funs) k
      else f.bound funs rest.flags (rest.boundsAt funs 0) := rfl

theorem Prog.fitsAt_consTail_here (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (funs : Funs S) (k : Nat) :
    (Prog.fitsAt (.consTail f rest) (.cons F funs) k).get .here =
      if f.depth then f.fitsAt funs (rest.fitsAt funs) k else fun _ => true := rfl

end Verified
