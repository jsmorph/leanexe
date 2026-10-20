import Verified.Reflect.Command

namespace Verified.Examples.Lists

def empty : List UInt64 := []

def cons (x : UInt64) (xs : List UInt64) : List UInt64 := x :: xs

def keep (xs : List UInt64) : List UInt64 := xs

def duplicate (xs : List UInt64) : List UInt64 × List UInt64 := (xs, xs)

def keepViaCall (xs : List UInt64) : List UInt64 := keep xs

def consTwice (x y : UInt64) (xs : List UInt64) : List UInt64 := cons x (cons y xs)

verified_compile compiled := [empty, cons, keep, duplicate, keepViaCall, consTwice]

example : compiled.cons.func.modes = [.borrowed, .owned] := rfl
example : compiled.keep.func.modes = [.owned] := rfl
example : compiled.duplicate.func.modes = [.owned] := rfl
example : compiled.keepViaCall.func.modes = [.owned] := rfl
example : compiled.consTwice.func.modes = [.borrowed, .borrowed, .owned] := rfl

#print axioms compiled.empty.implements
#print axioms compiled.cons.implements
#print axioms compiled.keep.implements
#print axioms compiled.duplicate.implements
#print axioms compiled.keepViaCall.implements
#print axioms compiled.consTwice.implements

end Verified.Examples.Lists
