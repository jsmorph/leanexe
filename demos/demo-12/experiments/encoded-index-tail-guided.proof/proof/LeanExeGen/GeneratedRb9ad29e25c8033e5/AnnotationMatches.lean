import LeanExeGen.GeneratedRb9ad29e25c8033e5.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayFindIdxEq

import Project.ProofKit.EncodedIndexDecoder

import Project.ProofKit.FixedArrayCopy





import Project.ProofKit.FixedArrayLengthDispatch

import Project.ProofKit.FixedArrayCapacity






set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches

def function_0_encoded_index_0_program : Wasm.Program :=
  Project.ProofKit.EncodedIndexDecoder.program
    2 8 4

theorem function_0_encoded_index_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 20, field := .elseBranch }] 2
      8 = some function_0_encoded_index_0_program := by
  rfl

theorem function_0_encoded_index_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve LeanExeGen.GeneratedRb9ad29e25c8033e5.func0 [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 20, field := .elseBranch }]).getD []).drop 2 =
      function_0_encoded_index_0_program ++ ((Project.ProofKit.Annotation.resolve LeanExeGen.GeneratedRb9ad29e25c8033e5.func0 [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 20, field := .elseBranch }]).getD []).drop 8 := by
  rfl

def function_0_length_dispatch_0_valid_branch_program : Wasm.Program :=
  [
  .localGet 0,
  .localSet 8,
  .localGet 8,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 9,
  .constI64 (0 : UInt64),
  .localSet 10,
  .constI64 (0 : UInt64),
  .localSet 11,
  .block 0 0 [
    .loop 0 0 [
      .localGet 10,
      .localGet 9,
      .geUI64,
      .br_if 1,
      .localGet 8,
      .localGet 10,
      .constI64 (1 : UInt64),
      .mulI64,
      .constI64 (1 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 1,
      .localGet 1,
      .constI64 (0 : UInt64),
      .eqI64,
      .iff 0 1 [
        .constI64 (1 : UInt64)
      ] [
        .constI64 (0 : UInt64)
      ],
      .constI64 (0 : UInt64),
      .neI64,
      .iff 0 0 [
        .localGet 10,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 11,
        .br 2
      ] [],
      .localGet 10,
      .constI64 (1 : UInt64),
      .addI64,
      .localSet 10,
      .br 0
    ]
  ],
  .localGet 11,
  .localSet 2,
  .localGet 2,
  .constI64 (0 : UInt64),
  .eqI64,
  .eqz,
  .iff 0 1 [
    .constI64 (1 : UInt64)
  ] [
    .constI64 (0 : UInt64)
  ],
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .localGet 0,
    .localSet 7
  ] [
    .localGet 0,
    .localSet 3,
    .localGet 2,
    .constI64 (0 : UInt64),
    .eqI64,
    .eqz,
    .iff 0 1 [
      .localGet 2,
      .localSet 8,
      .constI64 (1 : UInt64),
      .localSet 9,
      .localGet 8,
      .localGet 9,
      .ltUI64,
      .iff 0 1 [
        .constI64 (0 : UInt64)
      ] [
        .localGet 8,
        .localGet 9,
        .subI64
      ]
    ] [
      .constI64 (0 : UInt64)
    ],
    .localSet 4,
    .localGet 4,
    .localGet 3,
    .localSet 8,
    .localGet 8,
    .wrapI64,
    .load64 (0 : UInt32),
    .ltUI64,
    .iff 0 1 [
      .localGet 3,
      .localSet 8,
      .localGet 4,
      .localSet 9,
      .localGet 8,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 10,
      .localGet 9,
      .localGet 10,
      .ltUI64,
      .iff 0 1 [
        .localGet 10,
        .constI64 (1 : UInt64),
        .subI64,
        .localSet 13,
        .localGet 9,
        .constI64 (1 : UInt64),
        .mulI64,
        .localSet 11,
        .localGet 13,
        .localGet 9,
        .subI64,
        .constI64 (1 : UInt64),
        .mulI64,
        .localSet 12,
        .constI64 (8 : UInt64),
        .localGet 13,
        .constI64 (1 : UInt64),
        .mulI64,
        .constI64 (8 : UInt64),
        .mulI64,
        .addI64,
        .constI64 (7 : UInt64),
        .addI64,
        .constI64 (8 : UInt64),
        .divUI64,
        .constI64 (8 : UInt64),
        .mulI64,
        .localSet 18,
        .localGet 18,
        .constI64 (8 : UInt64),
        .ltUI64,
        .iff 0 0 [
          .constI64 (8 : UInt64),
          .localSet 18
        ] [],
        .constI64 (0 : UInt64),
        .localSet 23,
        .constI64 (0 : UInt64),
        .localSet 19,
        .globalGet 1,
        .localSet 20,
        .block 0 0 [
          .loop 0 0 [
            .localGet 20,
            .constI64 (0 : UInt64),
            .eqI64,
            .br_if 1,
            .localGet 23,
            .constI64 (0 : UInt64),
            .neI64,
            .br_if 1,
            .localGet 20,
            .constI64 (32 : UInt64),
            .subI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .localSet 21,
            .localGet 20,
            .constI64 (8 : UInt64),
            .subI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .localSet 22,
            .localGet 21,
            .localGet 18,
            .geUI64,
            .iff 0 0 [
              .localGet 19,
              .constI64 (0 : UInt64),
              .eqI64,
              .iff 0 0 [
                .localGet 22,
                .globalSet 1
              ] [
                .localGet 19,
                .constI64 (8 : UInt64),
                .subI64,
                .wrapI64,
                .localGet 22,
                .store64 (0 : UInt32)
              ],
              .localGet 20,
              .constI64 (48 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (5501223100278326855 : UInt64),
              .store64 (0 : UInt32),
              .localGet 20,
              .constI64 (40 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (1 : UInt64),
              .store64 (0 : UInt32),
              .localGet 20,
              .constI64 (32 : UInt64),
              .subI64,
              .wrapI64,
              .localGet 21,
              .store64 (0 : UInt32),
              .localGet 20,
              .constI64 (24 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (2 : UInt64),
              .store64 (0 : UInt32),
              .localGet 20,
              .constI64 (16 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (1 : UInt64),
              .store64 (0 : UInt32),
              .localGet 20,
              .constI64 (8 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 20,
              .localSet 23
            ] [
              .localGet 20,
              .localSet 19,
              .localGet 22,
              .localSet 20
            ],
            .br 0
          ]
        ],
        .localGet 23,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .globalGet 0,
          .constI64 (48 : UInt64),
          .addI64,
          .localGet 18,
          .addI64,
          .localSet 21,
          .localGet 21,
          .globalGet 0,
          .ltUI64,
          .iff 0 0 [
            .unreachable
          ] [],
          .localGet 21,
          .constI64 (1 : UInt64),
          .subI64,
          .constI64 (65536 : UInt64),
          .divUI64,
          .constI64 (1 : UInt64),
          .addI64,
          .localSet 22,
          .memorySize,
          .extendUI32,
          .localGet 22,
          .ltUI64,
          .iff 0 0 [
            .localGet 22,
            .memorySize,
            .extendUI32,
            .subI64,
            .wrapI64,
            .memoryGrow,
            .const (4294967295 : UInt32),
            .eq,
            .iff 0 0 [
              .unreachable
            ] []
          ] [],
          .globalGet 0,
          .constI64 (48 : UInt64),
          .addI64,
          .localSet 23,
          .localGet 21,
          .globalSet 0,
          .localGet 23,
          .constI64 (48 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (5501223100278326855 : UInt64),
          .store64 (0 : UInt32),
          .localGet 23,
          .constI64 (40 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (1 : UInt64),
          .store64 (0 : UInt32),
          .localGet 23,
          .constI64 (32 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 18,
          .store64 (0 : UInt32),
          .localGet 23,
          .constI64 (24 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (2 : UInt64),
          .store64 (0 : UInt32),
          .localGet 23,
          .constI64 (16 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (1 : UInt64),
          .store64 (0 : UInt32),
          .localGet 23,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (0 : UInt64),
          .store64 (0 : UInt32)
        ] [],
        .globalGet 2,
        .constI64 (1 : UInt64),
        .addI64,
        .globalSet 2,
        .localGet 23,
        .localSet 14,
        .localGet 14,
        .wrapI64,
        .localGet 13,
        .store64 (0 : UInt32),
        .constI64 (0 : UInt64),
        .localSet 15,
        .block 0 0 [
          .loop 0 0 [
            .localGet 15,
            .localGet 11,
            .geUI64,
            .br_if 1,
            .localGet 14,
            .localGet 15,
            .constI64 (1 : UInt64),
            .addI64,
            .constI64 (8 : UInt64),
            .mulI64,
            .addI64,
            .wrapI64,
            .localGet 8,
            .localGet 15,
            .constI64 (1 : UInt64),
            .addI64,
            .constI64 (8 : UInt64),
            .mulI64,
            .addI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .store64 (0 : UInt32),
            .localGet 15,
            .constI64 (1 : UInt64),
            .addI64,
            .localSet 15,
            .br 0
          ]
        ],
        .constI64 (0 : UInt64),
        .localSet 15,
        .block 0 0 [
          .loop 0 0 [
            .localGet 15,
            .localGet 12,
            .geUI64,
            .br_if 1,
            .localGet 14,
            .localGet 11,
            .localGet 15,
            .addI64,
            .constI64 (1 : UInt64),
            .addI64,
            .constI64 (8 : UInt64),
            .mulI64,
            .addI64,
            .wrapI64,
            .localGet 8,
            .localGet 11,
            .constI64 (1 : UInt64),
            .addI64,
            .localGet 15,
            .addI64,
            .constI64 (1 : UInt64),
            .addI64,
            .constI64 (8 : UInt64),
            .mulI64,
            .addI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .store64 (0 : UInt32),
            .localGet 15,
            .constI64 (1 : UInt64),
            .addI64,
            .localSet 15,
            .br 0
          ]
        ],
        .localGet 14
      ] [
        .localGet 8
      ]
    ] [
      .unreachable
    ],
    .localSet 5,
    .localGet 5,
    .localSet 7
  ]
]

def function_0_length_dispatch_0_invalid_branch_program : Wasm.Program :=
  [
  .constI64 (8 : UInt64),
  .constI64 (0 : UInt64),
  .constI64 (1 : UInt64),
  .mulI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .constI64 (7 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .divUI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .localSet 12,
  .localGet 12,
  .constI64 (8 : UInt64),
  .ltUI64,
  .iff 0 0 [
    .constI64 (8 : UInt64),
    .localSet 12
  ] [],
  .constI64 (0 : UInt64),
  .localSet 17,
  .constI64 (0 : UInt64),
  .localSet 13,
  .globalGet 1,
  .localSet 14,
  .block 0 0 [
    .loop 0 0 [
      .localGet 14,
      .constI64 (0 : UInt64),
      .eqI64,
      .br_if 1,
      .localGet 17,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 14,
      .constI64 (32 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 15,
      .localGet 14,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 16,
      .localGet 15,
      .localGet 12,
      .geUI64,
      .iff 0 0 [
        .localGet 13,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .localGet 16,
          .globalSet 1
        ] [
          .localGet 13,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 16,
          .store64 (0 : UInt32)
        ],
        .localGet 14,
        .constI64 (48 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (5501223100278326855 : UInt64),
        .store64 (0 : UInt32),
        .localGet 14,
        .constI64 (40 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 14,
        .constI64 (32 : UInt64),
        .subI64,
        .wrapI64,
        .localGet 15,
        .store64 (0 : UInt32),
        .localGet 14,
        .constI64 (24 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (2 : UInt64),
        .store64 (0 : UInt32),
        .localGet 14,
        .constI64 (16 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 14,
        .constI64 (8 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 14,
        .localSet 17
      ] [
        .localGet 14,
        .localSet 13,
        .localGet 16,
        .localSet 14
      ],
      .br 0
    ]
  ],
  .localGet 17,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 12,
    .addI64,
    .localSet 15,
    .localGet 15,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 15,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 16,
    .memorySize,
    .extendUI32,
    .localGet 16,
    .ltUI64,
    .iff 0 0 [
      .localGet 16,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const (4294967295 : UInt32),
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localSet 17,
    .localGet 15,
    .globalSet 0,
    .localGet 17,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 17,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 17,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 12,
    .store64 (0 : UInt32),
    .localGet 17,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 17,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 17,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32)
  ] [],
  .globalGet 2,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 2,
  .localGet 17,
  .localSet 8,
  .localGet 8,
  .wrapI64,
  .constI64 (0 : UInt64),
  .store64 (0 : UInt32),
  .localGet 8,
  .localSet 6,
  .localGet 6,
  .localSet 7
]

def function_0_length_dispatch_0_dispatch_program : Wasm.Program :=
  Project.ProofKit.FixedArrayLengthDispatch.leProgram
    8 8
    function_0_length_dispatch_0_valid_branch_program function_0_length_dispatch_0_invalid_branch_program

def function_0_length_dispatch_0_suffix_program : Wasm.Program :=
  [
  .localGet 7
]

theorem function_0_length_dispatch_0_dispatch_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [] 0
      8 = some function_0_length_dispatch_0_dispatch_program := by
  rfl

theorem function_0_length_dispatch_0_function_eq :
    LeanExeGen.GeneratedRb9ad29e25c8033e5.func0 =
      function_0_length_dispatch_0_dispatch_program ++ function_0_length_dispatch_0_suffix_program := by
  rfl

def function_0_length_dispatch_0_invalid_capacity_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    0 1 12

theorem function_0_length_dispatch_0_invalid_capacity_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [{ instructionIndex := 7, field := .elseBranch }] 0
      18 = some function_0_length_dispatch_0_invalid_capacity_program := by
  rfl

def function_0_find_idx_eq_0_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFindIdxEq.program
    8 0

theorem function_0_find_idx_eq_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [{ instructionIndex := 7, field := .thenBranch }] 0
      12 = some function_0_find_idx_eq_0_program := by
  rfl

def function_0_erase_copy_0_prefix_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.prefixProgram
    8 14
    11 15

def function_0_erase_copy_0_suffix_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.suffixProgram
    1 8 14
    11 12
    15

def function_0_erase_copy_0_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.program
    1 8 14
    11 12
    15

theorem function_0_erase_copy_0_prefix_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 20, field := .elseBranch }, { instructionIndex := 15, field := .thenBranch }, { instructionIndex := 11, field := .thenBranch }] 53
      56 = some function_0_erase_copy_0_prefix_program := by
  rfl

theorem function_0_erase_copy_0_suffix_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 20, field := .elseBranch }, { instructionIndex := 15, field := .thenBranch }, { instructionIndex := 11, field := .thenBranch }] 56
      59 = some function_0_erase_copy_0_suffix_program := by
  rfl

theorem function_0_erase_copy_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRb9ad29e25c8033e5.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 20, field := .elseBranch }, { instructionIndex := 15, field := .thenBranch }, { instructionIndex := 11, field := .thenBranch }] 53
      59 = some function_0_erase_copy_0_program := by
  rfl

end LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches
