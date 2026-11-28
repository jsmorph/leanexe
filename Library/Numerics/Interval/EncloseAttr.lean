module

public import LeanExe.Base
public import Lean.LabelAttribute

@[expose] public section

/-! The label of the theorems that the `enclose` tactic applies. -/

register_label_attr enclose
