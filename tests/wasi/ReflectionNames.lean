import Verified.Wasi

namespace Verified.Wasi.ReflectionNames

open LeanExe.Wasi

namespace First
def same : Action UInt64 := pure 0
end First

namespace Second
def same : Action UInt64 := pure 1
end Second

/-- error: verified_compile_wasi: definitions share the generated name same -/
#guard_msgs in
verified_compile_wasi collision := [First.same, Second.same]

def memory : Action UInt64 := pure 0

/-- error: verified_compile_wasi: memory is a reserved module export -/
#guard_msgs in
verified_compile_wasi reserved := [memory]

end Verified.Wasi.ReflectionNames
