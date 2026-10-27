import Demos.RunningSumFp.Program

private def words (text : String) : Array UInt64 := text.toUTF8.data.map UInt8.toUInt64

private def check (input : String) (bits : UInt64) (output : String) : IO Unit := do
  let (accepted, number) := Demos.RunningSumFp.parse (words input)
  unless accepted && number.toBits == bits do
    throw (IO.userError s!"Parse {repr input}: expected {bits}, observed {accepted}, {number.toBits}")
  let rendered := Demos.RunningSumFp.render number
  unless rendered.data == output.toUTF8 do
    throw (IO.userError s!"Render {repr input}: expected {repr output}, observed bytes {repr rendered.data.data.toList}")

def main : IO Unit := do
  check "1.25\r" 0x3ff4000000000000 "1.25e0\n"
  check "-0\r" 0x8000000000000000 "-0e0\n"
  check "5e-324" 1 "5e-324\n"
  check "Infinity" 0x7ff0000000000000 "Infinity\n"
  check "-Infinity" 0xfff0000000000000 "-Infinity\n"
  check "-NaN" 0x7ff8000000000000 "NaN\n"
  check "0x1.8p1" 0x4008000000000000 "3e0\n"
  check "9007199254740993" 0x4340000000000000 "9.007199254740992e15\n"
  check "1e400" 0x7ff0000000000000 "Infinity\n"
  check "1e-400" 0 "0e0\n"
  for input in ["", "+", ".", "1e", "0x10", "1\r\r", " 1", "1 ", "1\x00"] do
    if (Demos.RunningSumFp.parse (words input)).1 then
      throw (IO.userError s!"Parser accepted {repr input}")
  IO.println "Running sumfp parse/render: 19 cases passed"
