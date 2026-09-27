import LeanExe.Float64

namespace LeanExe.Examples.SpectralKL

/-- Binary64 coefficients (-1)^k/((k+1)(k+2)), k = 0,...,40. -/
def coefficients40 : Array UInt64 := Id.run do
  let mut cs : Array UInt64 := #[]
  cs := cs.push 0x3FE0000000000000
  cs := cs.push 0xBFC5555555555555
  cs := cs.push 0x3FB5555555555555
  cs := cs.push 0xBFA999999999999A
  cs := cs.push 0x3FA1111111111111
  cs := cs.push 0xBF98618618618618
  cs := cs.push 0x3F92492492492492
  cs := cs.push 0xBF8C71C71C71C71C
  cs := cs.push 0x3F86C16C16C16C17
  cs := cs.push 0xBF829E4129E4129E
  cs := cs.push 0x3F7F07C1F07C1F08
  cs := cs.push 0xBF7A41A41A41A41A
  cs := cs.push 0x3F76816816816817
  cs := cs.push 0xBF73813813813814
  cs := cs.push 0x3F71111111111111
  cs := cs.push 0xBF6E1E1E1E1E1E1E
  cs := cs.push 0x3F6AC5701AC5701B
  cs := cs.push 0xBF67F405FD017F40
  cs := cs.push 0x3F658ED2308158ED
  cs := cs.push 0xBF63813813813814
  cs := cs.push 0x3F61BB4A4046ED29
  cs := cs.push 0xBF603091B51F5E1A
  cs := cs.push 0x3F5DAE6076B981DB
  cs := cs.push 0xBF5B4E81B4E81B4F
  cs := cs.push 0x3F5934C67F9B2CE6
  cs := cs.push 0xBF5756CAC201756D
  cs := cs.push 0x3F55AC056B015AC0
  cs := cs.push 0xBF542D6625D51F87
  cs := cs.push 0x3F52D50A012D50A0
  cs := cs.push 0xBF519E0119E0119E
  cs := cs.push 0x3F50842108421084
  cs := cs.push 0xBF4F07C1F07C1F08
  cs := cs.push 0x3F4D347A4BC01D34
  cs := cs.push 0xBF4B89401B89401C
  cs := cs.push 0x3F4A01A01A01A01A
  cs := cs.push 0xBF4899C0F601899C
  cs := cs.push 0x3F474E4B040174E5
  cs := cs.push 0xBF461C544C0161C5
  cs := cs.push 0x3F45015015015015
  cs := cs.push 0xBF43FB013FB013FB
  cs := cs.push 0x3F43076EE7525C2C
  return cs

end LeanExe.Examples.SpectralKL
