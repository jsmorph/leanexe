namespace LeanExe.Examples.ScaledHypot

/-- `sqrt (x * x + y * y) / s` in binary64. -/
def scaledHypot (x y s : Float) : Float := (x * x + y * y).sqrt / s

end LeanExe.Examples.ScaledHypot
