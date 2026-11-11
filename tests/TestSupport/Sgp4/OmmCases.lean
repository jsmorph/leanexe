import Demos.Sgp4.Omm
import TestSupport.Host

/-! Cases of the module `sgp4omm`: `Omm.field` on decimal values in the forms of an Orbit
Mean-Elements Message and on texts that are no numbers. -/

namespace TestSupport.Sgp4.OmmCases

open TestSupport.Host Demos.Sgp4

def texts : List String :=
  ["15.50103472", ".0030035", "0.0030035", "58.0579", "221.1854", ".12808E-3", "0.12808E-3",
    "-.11606E-4", "1.2808e-4", "0", "-0", "+3.5", "1e400", "-1e400", "abc", "", "1.2.3", "12 ",
    "0x1p-3", "nan", "inf", "16.05824518", "0.00000000000000000000000000001"]

def cases : IO Unit := do
  for text in texts do
    let words := (text.toUTF8.toList.map fun b => b.toUInt64)
    let i := Omm.field words.toArray
    line "sgp4omm" "field" "list:i64,f64,f64" [arrU words] s!"{i.status} {i.lo.toBits} {i.hi.toBits}"
    let j := Omm.fieldNonneg words.toArray
    line "sgp4omm" "fieldNonneg" "list:i64,f64,f64" [arrU words]
      s!"{j.status} {j.lo.toBits} {j.hi.toBits}"

end TestSupport.Sgp4.OmmCases
