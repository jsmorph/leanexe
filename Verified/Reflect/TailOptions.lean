import Lean

register_option verified.tailLoops : Bool := {
  defValue := true
  descr := "Compile recognized tail recursion as a loop"
}
