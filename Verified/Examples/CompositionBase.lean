import Verified.Reflect.Command

namespace Verified.Examples.CompositionBase

def add (x y : UInt64) : UInt64 := x + y

def scale (x : Float) : Float := x * 1.5

verified_compile compiled := [add, scale]

end Verified.Examples.CompositionBase
