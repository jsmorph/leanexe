import Interpreter.Wasm.IEEE64

namespace Project.IEEE64Source

def addBits (left right : UInt64) : UInt64 := Wasm.IEEE64.add left right

def subBits (left right : UInt64) : UInt64 := Wasm.IEEE64.sub left right

def mulBits (left right : UInt64) : UInt64 := Wasm.IEEE64.mul left right

def divBits (left right : UInt64) : UInt64 := Wasm.IEEE64.div left right

def sqrtBits (value : UInt64) : UInt64 := Wasm.IEEE64.sqrt value

def sqrtDivBits (left right : UInt64) : UInt64 :=
  Wasm.IEEE64.sqrt (Wasm.IEEE64.div left right)

end Project.IEEE64Source
