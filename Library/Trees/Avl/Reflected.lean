module

public import Library.Trees.Avl.Encoding
public import Verified.Reflect.RecursiveTypes

@[expose] public section

/-! The declarations through which the verified compiler compiles programs over `AvlTree`, derived
once, so that any number of modules that compile such programs can be imported together. -/

verified_recursive_type Library.Trees.Avl.AvlTree
