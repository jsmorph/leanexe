module

public import LeanExe.Base
public import Lean

@[expose] public section

register_option verified.tailLoops : Bool := {
  defValue := true
  descr := "Compile recognized tail recursion as a loop"
}
