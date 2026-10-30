import Examples.Bucket.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `bucket`.  The function allocates nothing, so the generated
`compiled.bucket.implements` states that function 2 computes `bucket` without a trap. -/

namespace Examples.Bucket

verified_compile compiled := [bucket]

end Examples.Bucket
