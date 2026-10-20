import Verified.Reflect.Command

namespace Verified.Examples.Lists

def empty : List UInt64 := []

def cons (x : UInt64) (xs : List UInt64) : List UInt64 := x :: xs

def keep (xs : List UInt64) : List UInt64 := xs

def duplicate (xs : List UInt64) : List UInt64 × List UInt64 := (xs, xs)

def keepViaCall (xs : List UInt64) : List UInt64 := keep xs

def consTwice (x y : UInt64) (xs : List UInt64) : List UInt64 := cons x (cons y xs)

def first (xs : List UInt64) : UInt64 :=
  match xs with
  | [] => 0
  | x :: _ => x

def rest (xs : List UInt64) : List UInt64 :=
  match xs with
  | [] => []
  | _ :: ys => ys

def rebuild (xs : List UInt64) : List UInt64 :=
  match xs with
  | [] => []
  | x :: ys => x :: ys

def change (add : UInt64) (xs : List UInt64) : List UInt64 :=
  match xs with
  | [] => []
  | x :: ys => (x + add) :: ys

def foldWord (xs : List UInt64) (init : UInt64) : UInt64 :=
  xs.foldl (fun acc value => acc * 3 + value) init

def foldLookup (xs : List UInt64) (values : Array UInt64) (init : UInt64) : UInt64 :=
  xs.foldl (fun acc value => acc + values[value.toNat]!) init

def foldBuild (xs : List UInt64) (init : UInt64) : UInt64 :=
  xs.foldl (fun acc value =>
    let values := LeanExe.build 2 (fun i => value + i)
    acc + values[(1 : UInt64).toNat]!) init

def foldBool (xs : List UInt64) (init : Bool) : Bool :=
  xs.foldl (fun acc value => acc != (value == 0)) init

def foldTuple (xs : List UInt64) (init : UInt64) : UInt64 × Bool :=
  xs.foldl (fun (acc, flag) value => (acc + value, flag != (value == 0))) (init, false)

def foldNested (xs ys : List UInt64) (init : UInt64) : UInt64 :=
  xs.foldl (fun acc x => ys.foldl (fun acc y => acc + x * y) acc) init

inductive Choice where
  | absent
  | present (value : UInt64)
  deriving Inhabited

instance : LeanExe.Pipeline.Flat Choice (UInt64 × UInt64) := ⟨fun
  | .absent => (0, 0)
  | .present value => (1, value)⟩

def foldChoice (xs : List UInt64) (bias : UInt64) : UInt64 :=
  let choice : Choice := if bias == 0 then .absent else .present bias
  xs.foldl (fun acc value => acc + value +
    (match choice with | .absent => 7 | .present x => x)) 0

def foldFloat (xs : List UInt64) (init : Float) : Float :=
  xs.foldl (fun acc value => if value == 0 then acc + 1.5 else acc - 0.25) init

def foldFloat32 (xs : List UInt64) (init : Float32) : Float32 :=
  xs.foldl (fun acc value => if value == 0 then acc + 1.5 else acc - 0.25) init

def foldCons (value : UInt64) (xs : List UInt64) : UInt64 :=
  (value :: xs).foldl (fun acc x => acc + x) 0

def recursive (value : UInt64) : UInt64 :=
  if value = 0 then 0 else 1 + recursive (value - 1)
termination_by value.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def foldCalls (xs : List UInt64) (init : UInt64) : UInt64 :=
  xs.foldl (fun acc value => acc + recursive value) init

verified_compile compiled :=
  [empty, cons, keep, duplicate, keepViaCall, consTwice, first, rest, rebuild, change,
    foldWord, foldLookup, foldBuild, foldBool, foldTuple, foldNested, foldChoice,
    foldFloat, foldFloat32, foldCons, recursive, foldCalls]

example : compiled.cons.func.modes = [.borrowed, .owned] := rfl
example : compiled.keep.func.modes = [.owned] := rfl
example : compiled.duplicate.func.modes = [.owned] := rfl
example : compiled.keepViaCall.func.modes = [.owned] := rfl
example : compiled.consTwice.func.modes = [.borrowed, .borrowed, .owned] := rfl
example : compiled.first.func.modes = [.borrowed] := rfl
example : compiled.rest.func.modes = [.owned] := rfl
example : compiled.rebuild.func.modes = [.owned] := rfl
example : compiled.change.func.modes = [.borrowed, .owned] := rfl
example : compiled.foldWord.func.modes = [.borrowed, .borrowed] := rfl
example : compiled.foldCons.func.modes = [.borrowed, .owned] := rfl

theorem foldWord_bound (xs : List UInt64) (init : UInt64) :
    compiled.foldWord.bound (xs, init) = 0 := compiled.foldWord.bound_eq xs init

#print axioms compiled.empty.implements
#print axioms compiled.cons.implements
#print axioms compiled.keep.implements
#print axioms compiled.duplicate.implements
#print axioms compiled.keepViaCall.implements
#print axioms compiled.consTwice.implements
#print axioms compiled.first.implements
#print axioms compiled.rest.implements
#print axioms compiled.rebuild.implements
#print axioms compiled.change.implements
#print axioms compiled.foldWord.implements
#print axioms compiled.foldLookup.implements
#print axioms compiled.foldBuild.implements
#print axioms compiled.foldBool.implements
#print axioms compiled.foldTuple.implements
#print axioms compiled.foldNested.implements
#print axioms compiled.foldChoice.implements
#print axioms compiled.foldFloat.implements
#print axioms compiled.foldFloat32.implements
#print axioms compiled.foldCons.implements
#print axioms compiled.foldCalls.implements
#print axioms compiled.foldCalls.fits_eq
#print axioms foldWord_bound

end Verified.Examples.Lists
