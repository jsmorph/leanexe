import Verified.Compile

/-! The modes that the reflector chooses for a function's parameters.  The choice is not trusted:
the correctness theorem holds for every choice of modes.  An array parameter is owned when the
body consumes it where it dies, where a borrowed parameter would be copied: as the array of an
update or an extension, at a call that moves it into an owned parameter, as the function's
result, or through a binding, a branch, a pair, or a loop's state into one of these.  Every other
parameter is borrowed, so that a caller need not copy an array that the function only reads.
The live sets follow those of `Expr.code`. -/

namespace Verified

/-- Whether an expression consumes variable `k` where it dies, given the variables `live` live
after the expression and whether its value is consumed, `owned`.  A value is consumed when it
is the function's result, a value that a binding's body consumes, a branch or a component of a
value that is consumed or owned, or a loop's state when its body consumes the state or returns
an owned value. -/
def Expr.demands : {Γ : List Ty} → {t : Ty} → Expr S Γ t → (Nat → Bool) → Bool → Nat → Bool
  | _, _, .var x, live, owned, k => owned && k == x.index && !live k
  | _, _, .word _, _, _, _ | _, _, .bool _, _, _, _ | _, _, .size _, _, _, _
  | _, _, .float _, _, _, _ => false
  | _, _, .bin _ left right, live, _, k | _, _, .cmp _ left right, live, _, k
  | _, _, .and left right, live, _, k | _, _, .or left right, live, _, k
  | _, _, .fbin _ left right, live, _, k | _, _, .fcmp _ left right, live, _, k =>
    left.demands (fun i => live i || right.uses i) false k || right.demands live false k
  | _, _, .not e, live, _, k | _, _, .funary _ e, live, _, k => e.demands live false k
  | _, _, .toFloat _ e, live, _, k => e.demands live false k
  | _, _, .toWord _ e, live, _, k => e.demands live false k
  | _, _, .ite c thenE elseE, live, owned, k =>
    let branch := owned || thenE.mode [] == .owned || elseE.mode [] == .owned
    c.demands (fun i => live i || thenE.uses i || elseE.uses i) false k ||
      thenE.demands live branch k || elseE.demands live branch k
  | _, _, .letE value body, live, owned, k =>
    value.demands (fun i => live i || body.uses (i + 1)) (body.demands (shift 1 live) owned 0) k ||
      body.demands (shift 1 live) owned (k + 1)
  | _, _, .call (g := g) _ args, live, _, k =>
    argsAny fun i =>
      if (g.params.get i).scalar then
        (args i).demands (fun j => live j || argsAny fun j' => (args j').uses j) false k
      else
        g.mode i == .owned && (args i).varIndex? == some k && !live k &&
          !(argsAny fun j => j != i && !(g.params.get j).scalar && (args j).uses k)
  | _, _, .pair first second, live, owned, k =>
    let component := owned || first.mode [] == .owned || second.mode [] == .owned
    first.demands (fun i => live i || second.uses i) component k ||
      second.demands live component k
  | _, _, .letPair e body, live, owned, k =>
    let inner := shift 2 live
    e.demands (fun i => live i || body.uses (i + 2))
        (body.demands inner owned 0 || body.demands inner owned 1) k ||
      body.demands inner owned (k + 2)
  | _, _, .loop count init body, live, owned, k =>
    let inner := shift 2 fun i => live i || body.uses (i + 2)
    let state := owned || body.demands inner false 0 || body.mode [] == .owned
    count.demands (fun i => live i || init.uses i || body.uses (i + 2)) false k ||
      init.demands (fun i => live i || body.uses (i + 2)) state k ||
      body.demands inner state (k + 2)
  | _, _, .get x i, live, _, k => i.demands (fun j => live j || j == x.index) false k
  | _, _, .build count elem, live, _, k =>
    let all := fun i => live i || elem.uses (i + 1)
    count.demands all false k || elem.demands (shift 1 all) false (k + 1)
  | _, _, .set x i v, live, _, k =>
    (k == x.index && !live k) || i.demands (fun j => live j || v.uses j || j == x.index) false k ||
      v.demands (fun j => live j || j == x.index) false k
  | _, _, .push x v, live, _, k =>
    (k == x.index && !live k) || v.demands (fun j => live j || j == x.index) false k
  | _, _, .append x y, live, _, k => k == x.index && !live k && x.index != y.index

/-- The modes chosen for the parameters of types `params` of a function with body `body`: owned
for an array parameter that the body consumes where it dies, and borrowed otherwise. -/
def Expr.paramChoice {params : List Ty} {result : Ty} (body : Expr S params result) :
    List Mode :=
  (List.range params.length).map fun i =>
    match params[i]? with
    | some Ty.array => if body.demands (fun _ => false) true i then .owned else .borrowed
    | _ => .borrowed

end Verified
