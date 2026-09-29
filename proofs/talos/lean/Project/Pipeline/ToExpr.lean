import Lean
import Interpreter.Wasm.Syntax

open Lean

deriving instance ToExpr for Wasm.Simd.Shape
deriving instance ToExpr for Wasm.Simd.ICmp
deriving instance ToExpr for Wasm.Simd.FCmp
deriving instance ToExpr for Wasm.Simd.UnOp
deriving instance ToExpr for Wasm.Simd.BinOp
deriving instance ToExpr for Wasm.Simd.TestOp
deriving instance ToExpr for Wasm.Simd.ShiftOp
deriving instance ToExpr for Wasm.GcHeapType
deriving instance ToExpr for Wasm.ValueType
deriving instance ToExpr for Wasm.AnyRef
deriving instance ToExpr for Wasm.StorageType
deriving instance ToExpr for Wasm.FieldType
deriving instance ToExpr for Wasm.Value
deriving instance ToExpr for Wasm.CatchClause
deriving instance ToExpr for Wasm.GcOp
deriving instance ToExpr for Wasm.Instruction
deriving instance ToExpr for Wasm.Function
deriving instance ToExpr for Wasm.Export
deriving instance ToExpr for Wasm.DataSegment
deriving instance ToExpr for Wasm.MemDecl
deriving instance ToExpr for Wasm.GlobalDecl
deriving instance ToExpr for Wasm.FuncType
deriving instance ToExpr for Wasm.CompositeType
deriving instance ToExpr for Wasm.GcTypeDef
deriving instance ToExpr for Wasm.TableDecl
deriving instance ToExpr for Wasm.ImportDecl
deriving instance ToExpr for Wasm.ElementSegment
deriving instance ToExpr for Wasm.Module
