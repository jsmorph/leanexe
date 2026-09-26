import Project.ClobFindBest.Program
import Project.ClobPostOnly.Program
import Project.ClobMatchFuel.Program

/-! Checked instruction slices shared by the standalone and post-only search.
The two generated functions differ only in their eligibility and release call
indices. Tag and payload decisions share the same control flow. -/
namespace Project.ClobFindBest.SearchProgram
open Wasm
set_option maxRecDepth 16384

def readCandidate : Program := [
.localGet 2,
.localSet 64,
.localGet 8,
.localSet 65,
.localGet 65,
.localGet 64,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 64,
      .localGet 65,
      .constI64 5,
      .mulI64,
      .constI64 1,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 15,
.localGet 2,
.localSet 64,
.localGet 8,
.localSet 65,
.localGet 65,
.localGet 64,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 64,
      .localGet 65,
      .constI64 5,
      .mulI64,
      .constI64 2,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 16,
.localGet 2,
.localSet 64,
.localGet 8,
.localSet 65,
.localGet 65,
.localGet 64,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 64,
      .localGet 65,
      .constI64 5,
      .mulI64,
      .constI64 3,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 17,
.localGet 2,
.localSet 64,
.localGet 8,
.localSet 65,
.localGet 65,
.localGet 64,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 64,
      .localGet 65,
      .constI64 5,
      .mulI64,
      .constI64 4,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 18,
.localGet 2,
.localSet 64,
.localGet 8,
.localSet 65,
.localGet 65,
.localGet 64,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 64,
      .localGet 65,
      .constI64 5,
      .mulI64,
      .constI64 5,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 19
]

def decision (tag : Bool) (eligibleId : Nat) : Program := [
.localGet 9,
.constI64 0,
.eqI64,
.iff 0 1 [
      .localGet 3,
      .localSet 20,
      .localGet 4,
      .localSet 21,
      .localGet 5,
      .localSet 22,
      .localGet 6,
      .localSet 23,
      .localGet 7,
      .localSet 24,
      .localGet 15,
      .localSet 25,
      .localGet 16,
      .localSet 26,
      .localGet 17,
      .localSet 27,
      .localGet 18,
      .localSet 28,
      .localGet 19,
      .localSet 29,
      .localGet 20,
      .localGet 21,
      .localGet 22,
      .localGet 23,
      .localGet 24,
      .localGet 25,
      .localGet 26,
      .localGet 27,
      .localGet 28,
      .localGet 29,
      .call eligibleId,
      .localSet 30,
      .localGet 30,
      .constI64 1,
      .eqI64,
      .iff 0 1 [
       .constI64 1
      ] [
       .constI64 0
      ] [] [.i64],
      .constI64 0,
      .eqI64,
      .eqz,
      .iff 0 1 [
(if tag then Instruction.constI64 1 else .localGet 8)
      ] [
       .constI64 0
      ] [] [.i64]
     ] [
      .localGet 3,
      .localSet 31,
      .localGet 4,
      .localSet 32,
      .localGet 5,
      .localSet 33,
      .localGet 6,
      .localSet 34,
      .localGet 7,
      .localSet 35,
      .localGet 15,
      .localSet 36,
      .localGet 16,
      .localSet 37,
      .localGet 17,
      .localSet 38,
      .localGet 18,
      .localSet 39,
      .localGet 19,
      .localSet 40,
      .localGet 31,
      .localGet 32,
      .localGet 33,
      .localGet 34,
      .localGet 35,
      .localGet 36,
      .localGet 37,
      .localGet 38,
      .localGet 39,
      .localGet 40,
      .call eligibleId,
      .constI64 0,
      .eqI64,
      .eqz,
      .iff 0 1 [
       .localGet 5,
       .constI64 0,
       .eqI64,
       .iff 0 1 [
        .constI64 1
       ] [
        .constI64 0
       ] [] [.i64],
       .constI64 0,
       .eqI64,
       .eqz,
       .iff 0 1 [
        .constI64 1
       ] [
        .constI64 0
       ] [] [.i64],
       .constI64 1,
       .eqI64,
       .iff 0 1 [
        .constI64 1
       ] [
        .constI64 0
       ] [] [.i64],
       .constI64 0,
       .eqI64,
       .eqz,
       .iff 0 1 [
        .localGet 18,
        .localGet 2,
        .localSet 64,
        .localGet 10,
        .localSet 65,
        .localGet 65,
        .localGet 64,
        .wrapI64,
        .load64 0,
        .ltUI64,
        .iff 0 1 [
         .localGet 64,
         .localGet 65,
         .constI64 5,
         .mulI64,
         .constI64 4,
         .addI64,
         .constI64 8,
         .mulI64,
         .addI64,
         .wrapI64,
         .load64 0
        ] [
         .unreachable
        ] [] [.i64],
        .ltUI64,
        .iff 0 1 [
         .constI64 1
        ] [
         .constI64 0
        ] [] [.i64]
       ] [
        .localGet 2,
        .localSet 64,
        .localGet 10,
        .localSet 65,
        .localGet 65,
        .localGet 64,
        .wrapI64,
        .load64 0,
        .ltUI64,
        .iff 0 1 [
         .localGet 64,
         .localGet 65,
         .constI64 5,
         .mulI64,
         .constI64 4,
         .addI64,
         .constI64 8,
         .mulI64,
         .addI64,
         .wrapI64,
         .load64 0
        ] [
         .unreachable
        ] [] [.i64],
        .localGet 18,
        .ltUI64,
        .iff 0 1 [
         .constI64 1
        ] [
         .constI64 0
        ] [] [.i64]
       ] [] [.i64],
       .constI64 0,
       .eqI64,
       .eqz
      ] [
       .const 0
      ] [] [.i32],
      .iff 0 1 [
       .constI64 1
      ] [
       .constI64 0
      ] [] [.i64],
      .constI64 1,
      .eqI64,
      .iff 0 1 [
       .constI64 1
      ] [
       .constI64 0
      ] [] [.i64],
      .constI64 0,
      .eqI64,
      .eqz,
      .iff 0 1 [
(if tag then Instruction.constI64 1 else .localGet 8)
      ] [
(if tag then Instruction.constI64 1 else .localGet 10)
      ] [] [.i64]
     ] [] [.i64]
]

def advance (releaseId : Nat) : Program := [
.localGet 1,
.localSet 43,
.localGet 2,
.localSet 44,
.localGet 3,
.localSet 45,
.localGet 4,
.localSet 46,
.localGet 5,
.localSet 47,
.localGet 6,
.localSet 48,
.localGet 7,
.localSet 49,
.localGet 8,
.localSet 64,
.constI64 1,
.localSet 65,
.localGet 64,
.localGet 65,
.addI64,
.localTee 66,
.localGet 64,
.ltUI64,
.iff 0 1 [
      .unreachable
     ] [
      .localGet 66
     ] [] [.i64],
.localSet 50,
.localGet 41,
.localSet 51,
.localGet 42,
.localSet 52,
.localGet 11,
.constI64 0,
.eqI64,
.eqz,
.iff 0 1 [
      .localGet 11,
      .localGet 43,
      .eqI64,
      .eqz
     ] [
      .const 0
     ] [] [.i32],
.iff 0 0 [
      .localGet 11,
      .call releaseId
     ] [],
.localGet 43,
.localSet 53,
.localGet 44,
.localSet 54,
.localGet 45,
.localSet 55,
.localGet 46,
.localSet 56,
.localGet 47,
.localSet 57,
.localGet 48,
.localSet 58,
.localGet 49,
.localSet 59,
.localGet 50,
.localSet 60,
.localGet 51,
.localSet 61,
.localGet 52,
.localSet 62,
.localGet 43,
.localGet 11,
.eqI64,
.iff 0 1 [
      .localGet 43
     ] [
      .constI64 0
     ] [] [.i64],
.localSet 63,
.localGet 53,
.localSet 1,
.localGet 54,
.localSet 2,
.localGet 55,
.localSet 3,
.localGet 56,
.localSet 4,
.localGet 57,
.localSet 5,
.localGet 58,
.localSet 6,
.localGet 59,
.localSet 7,
.localGet 60,
.localSet 8,
.localGet 61,
.localSet 9,
.localGet 62,
.localSet 10,
.localGet 63,
.localSet 11,
.localGet 0,
.constI64 1,
.subI64,
.localSet 0
]

def done : Program := [
.localGet 9,
.localSet 12,
.localGet 10,
.localSet 13,
.constI64 1,
.localSet 14
]

def guard : Program := [
.localGet 0,
.constI64 0,
.eqI64,
.eqz,
.iff 0 1 [
     .localGet 14,
     .constI64 0,
     .eqI64
    ] [
     .const 0
    ] [] [.i32],
.eqz,
.br_if 1,
.localGet 8,
.localGet 2,
.localSet 64,
.localGet 64,
.wrapI64,
.load64 0,
.ltUI64
]

def loop (eligibleId releaseId : Nat) : Program := guard ++
  [.iff 0 0 (readCandidate ++ decision true eligibleId ++ [.localSet 41] ++
    decision false eligibleId ++ [.localSet 42] ++ advance releaseId) done, .br 0]

def finish : Program := [
.localGet 14,
.constI64 0,
.eqI64,
.iff 0 0 [
   .localGet 9,
   .localSet 12,
   .localGet 10,
   .localSet 13
  ] [],
.localGet 12,
.localGet 13
]

def program (eligibleId releaseId : Nat) : Program :=
  [.constI64 0, .localSet 11, .constI64 0, .localSet 14,
    .block 0 0 [.loop 0 0 (loop eligibleId releaseId)]] ++ finish

theorem standalone : Project.ClobFindBest.func7 = program 5 12 := by rfl
theorem postOnly : Project.ClobPostOnly.func12 = program 10 21 := by rfl

theorem matchFuel : Project.ClobMatchFuel.func8 = program 6 18 := by rfl

#print axioms standalone
#print axioms postOnly
#print axioms matchFuel
end Project.ClobFindBest.SearchProgram
