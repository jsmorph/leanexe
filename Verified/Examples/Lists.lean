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

verified_compile compiled :=
  [empty, cons, keep, duplicate, keepViaCall, consTwice, first, rest, rebuild, change]

example : compiled.cons.func.modes = [.borrowed, .owned] := rfl
example : compiled.keep.func.modes = [.owned] := rfl
example : compiled.duplicate.func.modes = [.owned] := rfl
example : compiled.keepViaCall.func.modes = [.owned] := rfl
example : compiled.consTwice.func.modes = [.borrowed, .borrowed, .owned] := rfl
example : compiled.first.func.modes = [.borrowed] := rfl
example : compiled.rest.func.modes = [.owned] := rfl
example : compiled.rebuild.func.modes = [.owned] := rfl
example : compiled.change.func.modes = [.borrowed, .owned] := rfl

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

end Verified.Examples.Lists
