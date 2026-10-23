import Verified.TailSource
import Verified.Reflect.Modes

namespace Verified

def TailBody.demands (targetModes : List Mode) (modes : List Mode) :
    {Γ : List Ty} → TailBody S params result Γ → Nat → Bool
  | _, .ret value, k => value.demands (fun _ => false) true k
  | _, .next args, k =>
    argsAny fun i =>
      if (params.get i).scalar then
        (args i).demands (fun j => argsAny fun i' => (args i').uses j) false k
      else
        paramMode params targetModes i == .owned && (args i).varIndex? == some k &&
          !(argsAny fun j => j != i && !(params.get j).scalar && (args j).uses k)
  | _, .ite cond yes no, k =>
    cond.demands (fun i => yes.uses i || no.uses i) false k ||
      yes.demands targetModes modes k || no.demands targetModes modes k
  | _, .letE value body, k =>
    let inner := value.mode modes :: modes
    value.demands (fun i => body.uses (i + 1)) (body.demands targetModes inner 0) k ||
      body.demands targetModes inner (k + 1)
  | _, .letPair value body, k =>
    let inner := value.mode modes :: value.mode modes :: modes
    value.demands (fun i => body.uses (i + 2))
        (body.demands targetModes inner 0 || body.demands targetModes inner 1) k ||
      body.demands targetModes inner (k + 2)
  | _, .treeCase (shape := shape) x empty node, k =>
    let inner := shape.modes (modes.getD x.index .borrowed) modes
    let fields := node.demands targetModes inner 0 ||
      argsAny (fun i : Fin shape.children =>
        node.demands targetModes inner (1 + shape.words + i.val))
    (k == x.index && !node.uses (k + shape.bindCount) && fields) ||
      empty.demands targetModes modes k ||
      node.demands targetModes inner (k + shape.bindCount)

def TailBody.receivesOwned (modes : List Mode) (i : Fin params.length) :
    {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret _ => false
  | _, .next args => (args i).mode modes == .owned
  | _, .ite _ yes no => yes.receivesOwned modes i || no.receivesOwned modes i
  | _, .letE value body => body.receivesOwned (value.mode modes :: modes) i
  | _, .letPair value body => body.receivesOwned (value.mode modes :: value.mode modes :: modes) i
  | _, .treeCase (shape := shape) x empty node =>
    empty.receivesOwned modes i ||
      node.receivesOwned (shape.modes (modes.getD x.index .borrowed) modes) i

def TailBody.paramChoice (body : TailBody S params result params) (modes : List Mode) :
    List Mode :=
  (List.finRange params.length).map fun i =>
    match params.get i with
    | .array _ | .tree _ | .treeHeader _ | .bytes =>
      if modes.getD i .borrowed == .owned || body.demands modes (paramModes params modes) i ||
          body.receivesOwned (paramModes params modes) i then .owned else .borrowed
    | _ => .borrowed

def TailBody.inferModes (body : TailBody S params result params) : List Mode :=
  Nat.fold params.length (fun _ _ modes => body.paramChoice modes)
    (params.map fun _ => .borrowed)

end Verified
