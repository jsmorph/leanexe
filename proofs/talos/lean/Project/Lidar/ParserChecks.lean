import LeanExe.WGSL.UIntCertificate

open LeanExe.WGSL.UInt

-- A typo, forged reference, wrap-prone literal or wrong output ownership must
-- not acquire the meaning of the intended program merely by being generated.
example : lineStep [] "let v0 : u32 = 4294967296u;" = none := by decide +kernel
example : lineStep [] "let v0 : u32 = scene[16u];" = none := by decide +kernel
example : lineStep [] "let v0 : u32 = params[4u];" = none := by decide +kernel
example : lineStep [] "let v0 : u32 = unknown + unknown;" = none := by decide +kernel
example : lineStep [("v0", .lit 1)] "let v0 : u32 = 2u;" = none := by decide +kernel
example : rhs? [("v0", .lit 1), ("v1", .lit 2)]
    ["max", "(", "v0", ",", "v1", ")", "-", "v0"] = none := by decide +kernel
example : body? 2 [("v0", .lit 1)]
    ["results", "[", "0u", "]", "=", "v0", ";", "}"] = none := by decide +kernel
