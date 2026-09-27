/- Generated from LeanExe.Examples.EncodingGcd by GenerateProgram.lean. -/

import Project.TalosPrelude

set_option maxRecDepth 1048576

namespace Project.EncodingGcd

open Wasm

def func0 : Wasm.Program :=
[Wasm.Instruction.localGet 0,
 Wasm.Instruction.localSet 2,
 Wasm.Instruction.localGet 1,
 Wasm.Instruction.localSet 3,
 Wasm.Instruction.localGet 2,
 Wasm.Instruction.localSet 4,
 Wasm.Instruction.localGet 3,
 Wasm.Instruction.localSet 5,
 Wasm.Instruction.block
   0
   0
   [Wasm.Instruction.loop
      0
      0
      [Wasm.Instruction.localGet 4,
       Wasm.Instruction.localSet 6,
       Wasm.Instruction.localGet 5,
       Wasm.Instruction.localSet 7,
       Wasm.Instruction.localGet 7,
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 1] [Wasm.Instruction.constI64 0] [] [Wasm.ValueType.i64],
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.eqz,
       Wasm.Instruction.eqz,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 1] [Wasm.Instruction.constI64 0] [] [Wasm.ValueType.i64],
       Wasm.Instruction.constI64 1,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 1] [Wasm.Instruction.constI64 0] [] [Wasm.ValueType.i64],
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.eqz,
       Wasm.Instruction.iff
         0
         0
         [Wasm.Instruction.localGet 6,
          Wasm.Instruction.localSet 16,
          Wasm.Instruction.localGet 7,
          Wasm.Instruction.localSet 17,
          Wasm.Instruction.localGet 17,
          Wasm.Instruction.constI64 0,
          Wasm.Instruction.eqI64,
          Wasm.Instruction.iff
            0
            1
            [Wasm.Instruction.localGet 16]
            [Wasm.Instruction.localGet 16, Wasm.Instruction.localGet 17, Wasm.Instruction.remUI64]
            []
            [Wasm.ValueType.i64],
          Wasm.Instruction.localSet 8,
          Wasm.Instruction.localGet 7,
          Wasm.Instruction.localSet 9,
          Wasm.Instruction.localGet 8,
          Wasm.Instruction.localSet 10,
          Wasm.Instruction.localGet 9,
          Wasm.Instruction.localSet 11,
          Wasm.Instruction.localGet 10,
          Wasm.Instruction.localSet 12]
         [Wasm.Instruction.localGet 6,
          Wasm.Instruction.localSet 11,
          Wasm.Instruction.localGet 7,
          Wasm.Instruction.localSet 12]
         []
         [],
       Wasm.Instruction.localGet 11,
       Wasm.Instruction.localSet 19,
       Wasm.Instruction.localGet 12,
       Wasm.Instruction.localSet 20,
       Wasm.Instruction.localGet 5,
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 1] [Wasm.Instruction.constI64 0] [] [Wasm.ValueType.i64],
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.eqz,
       Wasm.Instruction.eqz,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 1] [Wasm.Instruction.constI64 0] [] [Wasm.ValueType.i64],
       Wasm.Instruction.constI64 1,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 1] [Wasm.Instruction.constI64 0] [] [Wasm.ValueType.i64],
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.eqI64,
       Wasm.Instruction.eqz,
       Wasm.Instruction.iff 0 1 [Wasm.Instruction.constI64 0] [Wasm.Instruction.constI64 1] [] [Wasm.ValueType.i64],
       Wasm.Instruction.localSet 18,
       Wasm.Instruction.localGet 19,
       Wasm.Instruction.localSet 4,
       Wasm.Instruction.localGet 20,
       Wasm.Instruction.localSet 5,
       Wasm.Instruction.localGet 18,
       Wasm.Instruction.constI64 0,
       Wasm.Instruction.neI64,
       Wasm.Instruction.br_if 1,
       Wasm.Instruction.br 0]
      []
      []]
   []
   [],
 Wasm.Instruction.localGet 4,
 Wasm.Instruction.localSet 13,
 Wasm.Instruction.localGet 5,
 Wasm.Instruction.localSet 14,
 Wasm.Instruction.localGet 13,
 Wasm.Instruction.localSet 15,
 Wasm.Instruction.localGet 15]

def func0Def : Wasm.Function :=
{ params := [Wasm.ValueType.i64, Wasm.ValueType.i64], locals := [Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64,  Wasm.ValueType.i64], body := func0, results := [Wasm.ValueType.i64], typeIdx := some 0 }

def func1Def : Wasm.Function :=
{ params := [Wasm.ValueType.i64],
  locals := [Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64],
  body := [Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 7,
           Wasm.Instruction.addI64,
           Wasm.Instruction.constI64 8,
           Wasm.Instruction.divUI64,
           Wasm.Instruction.constI64 8,
           Wasm.Instruction.mulI64,
           Wasm.Instruction.localSet 1,
           Wasm.Instruction.localGet 1,
           Wasm.Instruction.constI64 8,
           Wasm.Instruction.ltUI64,
           Wasm.Instruction.iff 0 0 [Wasm.Instruction.constI64 8, Wasm.Instruction.localSet 1] [] [] [],
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.localSet 6,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.localSet 2,
           Wasm.Instruction.globalGet 1,
           Wasm.Instruction.localSet 3,
           Wasm.Instruction.block
             0
             0
             [Wasm.Instruction.loop
                0
                0
                [Wasm.Instruction.localGet 3,
                 Wasm.Instruction.constI64 0,
                 Wasm.Instruction.eqI64,
                 Wasm.Instruction.br_if 1,
                 Wasm.Instruction.localGet 6,
                 Wasm.Instruction.constI64 0,
                 Wasm.Instruction.neI64,
                 Wasm.Instruction.br_if 1,
                 Wasm.Instruction.localGet 3,
                 Wasm.Instruction.constI64 32,
                 Wasm.Instruction.subI64,
                 Wasm.Instruction.wrapI64,
                 Wasm.Instruction.load64 0,
                 Wasm.Instruction.localSet 4,
                 Wasm.Instruction.localGet 3,
                 Wasm.Instruction.constI64 8,
                 Wasm.Instruction.subI64,
                 Wasm.Instruction.wrapI64,
                 Wasm.Instruction.load64 0,
                 Wasm.Instruction.localSet 5,
                 Wasm.Instruction.localGet 4,
                 Wasm.Instruction.localGet 1,
                 Wasm.Instruction.geUI64,
                 Wasm.Instruction.iff
                   0
                   0
                   [Wasm.Instruction.localGet 2,
                    Wasm.Instruction.constI64 0,
                    Wasm.Instruction.eqI64,
                    Wasm.Instruction.iff
                      0
                      0
                      [Wasm.Instruction.localGet 5, Wasm.Instruction.globalSet 1]
                      [Wasm.Instruction.localGet 2,
                       Wasm.Instruction.constI64 8,
                       Wasm.Instruction.subI64,
                       Wasm.Instruction.wrapI64,
                       Wasm.Instruction.localGet 5,
                       Wasm.Instruction.store64 0]
                      []
                      [],
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.constI64 48,
                    Wasm.Instruction.subI64,
                    Wasm.Instruction.wrapI64,
                    Wasm.Instruction.constI64 5501223100278326855,
                    Wasm.Instruction.store64 0,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.constI64 40,
                    Wasm.Instruction.subI64,
                    Wasm.Instruction.wrapI64,
                    Wasm.Instruction.constI64 1,
                    Wasm.Instruction.store64 0,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.constI64 32,
                    Wasm.Instruction.subI64,
                    Wasm.Instruction.wrapI64,
                    Wasm.Instruction.localGet 4,
                    Wasm.Instruction.store64 0,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.constI64 24,
                    Wasm.Instruction.subI64,
                    Wasm.Instruction.wrapI64,
                    Wasm.Instruction.constI64 0,
                    Wasm.Instruction.store64 0,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.constI64 16,
                    Wasm.Instruction.subI64,
                    Wasm.Instruction.wrapI64,
                    Wasm.Instruction.constI64 0,
                    Wasm.Instruction.store64 0,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.constI64 8,
                    Wasm.Instruction.subI64,
                    Wasm.Instruction.wrapI64,
                    Wasm.Instruction.constI64 0,
                    Wasm.Instruction.store64 0,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.localSet 6]
                   [Wasm.Instruction.localGet 3,
                    Wasm.Instruction.localSet 2,
                    Wasm.Instruction.localGet 5,
                    Wasm.Instruction.localSet 3]
                   []
                   [],
                 Wasm.Instruction.br 0]
                []
                []]
             []
             [],
           Wasm.Instruction.localGet 6,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.eqI64,
           Wasm.Instruction.iff
             0
             0
             [Wasm.Instruction.globalGet 0,
              Wasm.Instruction.constI64 48,
              Wasm.Instruction.addI64,
              Wasm.Instruction.localGet 1,
              Wasm.Instruction.addI64,
              Wasm.Instruction.localTee 4,
              Wasm.Instruction.globalGet 0,
              Wasm.Instruction.ltUI64,
              Wasm.Instruction.iff 0 0 [Wasm.Instruction.unreachable] [] [] [],
              Wasm.Instruction.localGet 4,
              Wasm.Instruction.constI64 1,
              Wasm.Instruction.subI64,
              Wasm.Instruction.constI64 65536,
              Wasm.Instruction.divUI64,
              Wasm.Instruction.constI64 1,
              Wasm.Instruction.addI64,
              Wasm.Instruction.localSet 5,
              Wasm.Instruction.memorySize,
              Wasm.Instruction.extendUI32,
              Wasm.Instruction.localGet 5,
              Wasm.Instruction.ltUI64,
              Wasm.Instruction.iff
                0
                0
                [Wasm.Instruction.localGet 5,
                 Wasm.Instruction.memorySize,
                 Wasm.Instruction.extendUI32,
                 Wasm.Instruction.subI64,
                 Wasm.Instruction.wrapI64,
                 Wasm.Instruction.memoryGrow,
                 Wasm.Instruction.const 4294967295,
                 Wasm.Instruction.eq,
                 Wasm.Instruction.iff 0 0 [Wasm.Instruction.unreachable] [] [] []]
                []
                []
                [],
              Wasm.Instruction.globalGet 0,
              Wasm.Instruction.constI64 48,
              Wasm.Instruction.addI64,
              Wasm.Instruction.localSet 6,
              Wasm.Instruction.localGet 4,
              Wasm.Instruction.globalSet 0,
              Wasm.Instruction.localGet 6,
              Wasm.Instruction.constI64 48,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.constI64 5501223100278326855,
              Wasm.Instruction.store64 0,
              Wasm.Instruction.localGet 6,
              Wasm.Instruction.constI64 40,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.constI64 1,
              Wasm.Instruction.store64 0,
              Wasm.Instruction.localGet 6,
              Wasm.Instruction.constI64 32,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.localGet 1,
              Wasm.Instruction.store64 0,
              Wasm.Instruction.localGet 6,
              Wasm.Instruction.constI64 24,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.constI64 0,
              Wasm.Instruction.store64 0,
              Wasm.Instruction.localGet 6,
              Wasm.Instruction.constI64 16,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.constI64 0,
              Wasm.Instruction.store64 0,
              Wasm.Instruction.localGet 6,
              Wasm.Instruction.constI64 8,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.constI64 0,
              Wasm.Instruction.store64 0]
             []
             []
             [],
           Wasm.Instruction.globalGet 2,
           Wasm.Instruction.constI64 1,
           Wasm.Instruction.addI64,
           Wasm.Instruction.globalSet 2,
           Wasm.Instruction.localGet 6],
  results := [Wasm.ValueType.i64],
  typeIdx := some 1 }

def func2Def : Wasm.Function :=
{ params := [],
  locals := [],
  body := [Wasm.Instruction.constI64 4096,
           Wasm.Instruction.globalSet 0,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.globalSet 1,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.globalSet 2,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.globalSet 3,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.globalSet 4,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.globalSet 5],
  results := [],
  typeIdx := some 2 }

def func3Def : Wasm.Function :=
{ params := [Wasm.ValueType.i64],
  locals := [Wasm.ValueType.i64],
  body := [Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.neI64,
           Wasm.Instruction.iff
             0
             0
             [Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 48,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.constI64 5501223100278326855,
              Wasm.Instruction.neI64,
              Wasm.Instruction.iff 0 0 [Wasm.Instruction.unreachable] [] [] [],
              Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 40,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.localSet 1,
              Wasm.Instruction.localGet 1,
              Wasm.Instruction.constI64 0,
              Wasm.Instruction.eqI64,
              Wasm.Instruction.iff 0 0 [Wasm.Instruction.unreachable] [] [] [],
              Wasm.Instruction.globalGet 3,
              Wasm.Instruction.constI64 1,
              Wasm.Instruction.addI64,
              Wasm.Instruction.globalSet 3,
              Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 40,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.localGet 1,
              Wasm.Instruction.constI64 1,
              Wasm.Instruction.addI64,
              Wasm.Instruction.store64 0]
             []
             []
             [],
           Wasm.Instruction.localGet 0],
  results := [Wasm.ValueType.i64],
  typeIdx := some 3 }

def func4Def : Wasm.Function :=
{ params := [Wasm.ValueType.i64],
  locals := [Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64,
             Wasm.ValueType.i64],
  body := [Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.eqI64,
           Wasm.Instruction.iff 0 0 [Wasm.Instruction.ret] [] [] [],
           Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 48,
           Wasm.Instruction.subI64,
           Wasm.Instruction.wrapI64,
           Wasm.Instruction.load64 0,
           Wasm.Instruction.constI64 5501223100278326855,
           Wasm.Instruction.neI64,
           Wasm.Instruction.iff 0 0 [Wasm.Instruction.unreachable] [] [] [],
           Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 40,
           Wasm.Instruction.subI64,
           Wasm.Instruction.wrapI64,
           Wasm.Instruction.load64 0,
           Wasm.Instruction.localSet 1,
           Wasm.Instruction.localGet 1,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.eqI64,
           Wasm.Instruction.iff 0 0 [Wasm.Instruction.unreachable] [] [] [],
           Wasm.Instruction.globalGet 4,
           Wasm.Instruction.constI64 1,
           Wasm.Instruction.addI64,
           Wasm.Instruction.globalSet 4,
           Wasm.Instruction.constI64 1,
           Wasm.Instruction.localGet 1,
           Wasm.Instruction.ltUI64,
           Wasm.Instruction.iff
             0
             0
             [Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 40,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.localGet 1,
              Wasm.Instruction.constI64 1,
              Wasm.Instruction.subI64,
              Wasm.Instruction.store64 0,
              Wasm.Instruction.ret]
             []
             []
             [],
           Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 24,
           Wasm.Instruction.subI64,
           Wasm.Instruction.wrapI64,
           Wasm.Instruction.load64 0,
           Wasm.Instruction.localSet 2,
           Wasm.Instruction.localGet 2,
           Wasm.Instruction.constI64 1,
           Wasm.Instruction.eqI64,
           Wasm.Instruction.iff
             0
             0
             [Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 16,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.localSet 3,
              Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 8,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.localSet 5,
              Wasm.Instruction.constI64 0,
              Wasm.Instruction.localSet 6,
              Wasm.Instruction.block
                0
                0
                [Wasm.Instruction.loop
                   0
                   0
                   [Wasm.Instruction.localGet 6,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.geUI64,
                    Wasm.Instruction.br_if 1,
                    Wasm.Instruction.localGet 5,
                    Wasm.Instruction.localGet 6,
                    Wasm.Instruction.shrUI64,
                    Wasm.Instruction.constI64 1,
                    Wasm.Instruction.andI64,
                    Wasm.Instruction.constI64 0,
                    Wasm.Instruction.neI64,
                    Wasm.Instruction.iff
                      0
                      0
                      [Wasm.Instruction.localGet 0,
                       Wasm.Instruction.localGet 6,
                       Wasm.Instruction.constI64 8,
                       Wasm.Instruction.mulI64,
                       Wasm.Instruction.addI64,
                       Wasm.Instruction.wrapI64,
                       Wasm.Instruction.load64 0,
                       Wasm.Instruction.localSet 8,
                       Wasm.Instruction.localGet 8,
                       Wasm.Instruction.call 4]
                      []
                      []
                      [],
                    Wasm.Instruction.localGet 6,
                    Wasm.Instruction.constI64 1,
                    Wasm.Instruction.addI64,
                    Wasm.Instruction.localSet 6,
                    Wasm.Instruction.br 0]
                   []
                   []]
                []
                []]
             []
             []
             [],
           Wasm.Instruction.localGet 2,
           Wasm.Instruction.constI64 2,
           Wasm.Instruction.eqI64,
           Wasm.Instruction.iff
             0
             0
             [Wasm.Instruction.localGet 0,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.localSet 3,
              Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 16,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.localSet 4,
              Wasm.Instruction.localGet 0,
              Wasm.Instruction.constI64 8,
              Wasm.Instruction.subI64,
              Wasm.Instruction.wrapI64,
              Wasm.Instruction.load64 0,
              Wasm.Instruction.localSet 5,
              Wasm.Instruction.constI64 0,
              Wasm.Instruction.localSet 7,
              Wasm.Instruction.block
                0
                0
                [Wasm.Instruction.loop
                   0
                   0
                   [Wasm.Instruction.localGet 7,
                    Wasm.Instruction.localGet 3,
                    Wasm.Instruction.geUI64,
                    Wasm.Instruction.br_if 1,
                    Wasm.Instruction.constI64 0,
                    Wasm.Instruction.localSet 6,
                    Wasm.Instruction.block
                      0
                      0
                      [Wasm.Instruction.loop
                         0
                         0
                         [Wasm.Instruction.localGet 6,
                          Wasm.Instruction.localGet 4,
                          Wasm.Instruction.geUI64,
                          Wasm.Instruction.br_if 1,
                          Wasm.Instruction.localGet 5,
                          Wasm.Instruction.localGet 6,
                          Wasm.Instruction.shrUI64,
                          Wasm.Instruction.constI64 1,
                          Wasm.Instruction.andI64,
                          Wasm.Instruction.constI64 0,
                          Wasm.Instruction.neI64,
                          Wasm.Instruction.iff
                            0
                            0
                            [Wasm.Instruction.localGet 0,
                             Wasm.Instruction.constI64 8,
                             Wasm.Instruction.addI64,
                             Wasm.Instruction.localGet 7,
                             Wasm.Instruction.localGet 4,
                             Wasm.Instruction.mulI64,
                             Wasm.Instruction.localGet 6,
                             Wasm.Instruction.addI64,
                             Wasm.Instruction.constI64 8,
                             Wasm.Instruction.mulI64,
                             Wasm.Instruction.addI64,
                             Wasm.Instruction.wrapI64,
                             Wasm.Instruction.load64 0,
                             Wasm.Instruction.localSet 8,
                             Wasm.Instruction.localGet 8,
                             Wasm.Instruction.call 4]
                            []
                            []
                            [],
                          Wasm.Instruction.localGet 6,
                          Wasm.Instruction.constI64 1,
                          Wasm.Instruction.addI64,
                          Wasm.Instruction.localSet 6,
                          Wasm.Instruction.br 0]
                         []
                         []]
                      []
                      [],
                    Wasm.Instruction.localGet 7,
                    Wasm.Instruction.constI64 1,
                    Wasm.Instruction.addI64,
                    Wasm.Instruction.localSet 7,
                    Wasm.Instruction.br 0]
                   []
                   []]
                []
                []]
             []
             []
             [],
           Wasm.Instruction.globalGet 5,
           Wasm.Instruction.constI64 1,
           Wasm.Instruction.addI64,
           Wasm.Instruction.globalSet 5,
           Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 40,
           Wasm.Instruction.subI64,
           Wasm.Instruction.wrapI64,
           Wasm.Instruction.constI64 0,
           Wasm.Instruction.store64 0,
           Wasm.Instruction.localGet 0,
           Wasm.Instruction.constI64 8,
           Wasm.Instruction.subI64,
           Wasm.Instruction.wrapI64,
           Wasm.Instruction.globalGet 1,
           Wasm.Instruction.store64 0,
           Wasm.Instruction.localGet 0,
           Wasm.Instruction.globalSet 1],
  results := [],
  typeIdx := some 4 }

def «module» : Wasm.Module :=
{ funcs := [func0Def, func1Def, func2Def, func3Def, func4Def],
  exports := [{ name := "gcd", funcIdx := 0 },  { name := "alloc", funcIdx := 1 },  { name := "reset", funcIdx := 2 },  { name := "retain", funcIdx := 3 },  { name := "release", funcIdx := 4 },  { name := "free", funcIdx := 4 }],
  memory := (some { pagesMin := 16, pagesMax := none, data := [], is64 := false }),
  globals := [{ init := Wasm.Value.i64 4096,    declaredType := some (Wasm.ValueType.i64),    isMut := true,    sourceInit := some [Wasm.Instruction.constI64 4096],    initExpr := [] },  { init := Wasm.Value.i64 0,    declaredType := some (Wasm.ValueType.i64),    isMut := true,    sourceInit := some [Wasm.Instruction.constI64 0],    initExpr := [] },  { init := Wasm.Value.i64 0,    declaredType := some (Wasm.ValueType.i64),    isMut := true,    sourceInit := some [Wasm.Instruction.constI64 0],    initExpr := [] },  { init := Wasm.Value.i64 0,    declaredType := some (Wasm.ValueType.i64),    isMut := true,    sourceInit := some [Wasm.Instruction.constI64 0],    initExpr := [] },  { init := Wasm.Value.i64 0,    declaredType := some (Wasm.ValueType.i64),    isMut := true,    sourceInit := some [Wasm.Instruction.constI64 0],    initExpr := [] },  { init := Wasm.Value.i64 0,    declaredType := some (Wasm.ValueType.i64),    isMut := true,    sourceInit := some [Wasm.Instruction.constI64 0],    initExpr := [] }],
  types := [{ params := [Wasm.ValueType.i64, Wasm.ValueType.i64], results := [Wasm.ValueType.i64] },  { params := [Wasm.ValueType.i64], results := [Wasm.ValueType.i64] },  { params := [], results := [] },  { params := [Wasm.ValueType.i64], results := [Wasm.ValueType.i64] },  { params := [Wasm.ValueType.i64], results := [] }],
  gcTypes := [{ comp := Wasm.CompositeType.func              { params := [Wasm.ValueType.i64, Wasm.ValueType.i64], results := [Wasm.ValueType.i64] },    sourceName := none,    super := none,    final := true,    recGroup := none },  { comp := Wasm.CompositeType.func { params := [Wasm.ValueType.i64], results := [Wasm.ValueType.i64] },    sourceName := none,    super := none,    final := true,    recGroup := none },  { comp := Wasm.CompositeType.func { params := [], results := [] },    sourceName := none,    super := none,    final := true,    recGroup := none },  { comp := Wasm.CompositeType.func { params := [Wasm.ValueType.i64], results := [Wasm.ValueType.i64] },    sourceName := none,    super := none,    final := true,    recGroup := none },  { comp := Wasm.CompositeType.func { params := [Wasm.ValueType.i64], results := [] },    sourceName := none,    super := none,    final := true,    recGroup := none }],
  globalExports := [("allocCount", 2), ("retainCount", 3), ("releaseCount", 4), ("freeCount", 5)],
  memoryExports := [("memory", 0)] }

end Project.EncodingGcd
