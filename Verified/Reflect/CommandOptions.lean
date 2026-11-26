module

public import LeanExe.Base
public import Lean

@[expose] public section

/-! The option of `verified_compile`, in a module of its own, which `Verified.Reflect.Command`
imports for its elaborator's meta code and for its users' `set_option`. -/

register_option verified_compile.alignedNative : Bool := {
  defValue := false
  descr := "verified_compile also translates the module to C without the test of alignment and \
    states p.f.nativeAligned for each function and wrapper of a program without byte literals"
}
