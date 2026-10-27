import Examples.Words.Encode
import Verified.Reflect.RecursiveTypes

/-! The declarations through which the verified compiler compiles programs over `Words`, derived
once, so that any number of modules that compile such programs can be imported together. -/

verified_recursive_type Examples.Words.Words
