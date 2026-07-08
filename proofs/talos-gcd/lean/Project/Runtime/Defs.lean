/-
  The runtime function suite the compiler appends to every module: allocate,
  reset, retain, and release.  The bodies below are the decoded instruction
  streams, shared verbatim by every generated module; release takes its own
  function index as a parameter because its recursion calls itself.
  `Checks.lean` pins each generated module's runtime functions to these
  definitions by `rfl`.
-/

import CodeLib

set_option maxRecDepth 1048576

namespace Project.Runtime

open Wasm

def allocBody : Wasm.Program :=
  [
  .localGet 0,
  .constI64 (7 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .divUI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .localSet 1,
  .localGet 1,
  .constI64 (8 : UInt64),
  .ltUI64,
  .iff 0 0 [
    .constI64 (8 : UInt64),
    .localSet 1
  ] [],
  .constI64 (0 : UInt64),
  .localSet 6,
  .constI64 (0 : UInt64),
  .localSet 2,
  .globalGet 1,
  .localSet 3,
  .block 0 0 [
    .loop 0 0 [
      .localGet 3,
      .constI64 (0 : UInt64),
      .eqI64,
      .br_if 1,
      .localGet 6,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 3,
      .constI64 (32 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 4,
      .localGet 3,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 5,
      .localGet 4,
      .localGet 1,
      .geUI64,
      .iff 0 0 [
        .localGet 2,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .localGet 5,
          .globalSet 1
        ] [
          .localGet 2,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 5,
          .store64 (0 : UInt32)
        ],
        .localGet 3,
        .constI64 (48 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (5501223100278326855 : UInt64),
        .store64 (0 : UInt32),
        .localGet 3,
        .constI64 (40 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 3,
        .constI64 (32 : UInt64),
        .subI64,
        .wrapI64,
        .localGet 4,
        .store64 (0 : UInt32),
        .localGet 3,
        .constI64 (24 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 3,
        .constI64 (16 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 3,
        .constI64 (8 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 3,
        .localSet 6
      ] [
        .localGet 3,
        .localSet 2,
        .localGet 5,
        .localSet 3
      ],
      .br 0
    ]
  ],
  .localGet 6,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 1,
    .addI64,
    .localSet 4,
    .localGet 4,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 4,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 5,
    .memorySize,
    .extendUI32,
    .localGet 5,
    .ltUI64,
    .iff 0 0 [
      .localGet 5,
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
    .localSet 6,
    .localGet 4,
    .globalSet 0,
    .localGet 6,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 6,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 6,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 1,
    .store64 (0 : UInt32),
    .localGet 6,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32),
    .localGet 6,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32),
    .localGet 6,
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
  .localGet 6
]

def allocFuncDef : Wasm.Function :=
  { params := [.i64], locals := [.i64, .i64, .i64, .i64, .i64, .i64], body := allocBody, results := [.i64] }

def resetBody : Wasm.Program :=
  [
  .constI64 (4096 : UInt64),
  .globalSet 0,
  .constI64 (0 : UInt64),
  .globalSet 1,
  .constI64 (0 : UInt64),
  .globalSet 2,
  .constI64 (0 : UInt64),
  .globalSet 3,
  .constI64 (0 : UInt64),
  .globalSet 4,
  .constI64 (0 : UInt64),
  .globalSet 5
]

def resetFuncDef : Wasm.Function :=
  { params := [], locals := [], body := resetBody, results := [] }

def retainBody : Wasm.Program :=
  [
  .localGet 0,
  .constI64 (0 : UInt64),
  .neI64,
  .iff 0 0 [
    .localGet 0,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .load64 (0 : UInt32),
    .constI64 (5501223100278326855 : UInt64),
    .neI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 0,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .load64 (0 : UInt32),
    .localSet 1,
    .localGet 1,
    .constI64 (0 : UInt64),
    .eqI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .globalGet 3,
    .constI64 (1 : UInt64),
    .addI64,
    .globalSet 3,
    .localGet 0,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 1,
    .constI64 (1 : UInt64),
    .addI64,
    .store64 (0 : UInt32)
  ] [],
  .localGet 0
]

def retainFuncDef : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := retainBody, results := [.i64] }

def releaseBody (self : Nat) : Wasm.Program :=
  [
  .localGet 0,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .ret
  ] [],
  .localGet 0,
  .constI64 (48 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .constI64 (5501223100278326855 : UInt64),
  .neI64,
  .iff 0 0 [
    .unreachable
  ] [],
  .localGet 0,
  .constI64 (40 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 1,
  .localGet 1,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .unreachable
  ] [],
  .globalGet 4,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 4,
  .constI64 (1 : UInt64),
  .localGet 1,
  .ltUI64,
  .iff 0 0 [
    .localGet 0,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 1,
    .constI64 (1 : UInt64),
    .subI64,
    .store64 (0 : UInt32),
    .ret
  ] [],
  .localGet 0,
  .constI64 (24 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 2,
  .localGet 2,
  .constI64 (1 : UInt64),
  .eqI64,
  .iff 0 0 [
    .localGet 0,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .load64 (0 : UInt32),
    .localSet 3,
    .localGet 0,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .load64 (0 : UInt32),
    .localSet 5,
    .constI64 (0 : UInt64),
    .localSet 6,
    .block 0 0 [
      .loop 0 0 [
        .localGet 6,
        .localGet 3,
        .geUI64,
        .br_if 1,
        .localGet 5,
        .localGet 6,
        .shrUI64,
        .constI64 (1 : UInt64),
        .andI64,
        .constI64 (0 : UInt64),
        .neI64,
        .iff 0 0 [
          .localGet 0,
          .localGet 6,
          .constI64 (8 : UInt64),
          .mulI64,
          .addI64,
          .wrapI64,
          .load64 (0 : UInt32),
          .localSet 8,
          .localGet 8,
          .call self
        ] [],
        .localGet 6,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 6,
        .br 0
      ]
    ]
  ] [],
  .localGet 2,
  .constI64 (2 : UInt64),
  .eqI64,
  .iff 0 0 [
    .localGet 0,
    .wrapI64,
    .load64 (0 : UInt32),
    .localSet 3,
    .localGet 0,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .load64 (0 : UInt32),
    .localSet 4,
    .localGet 0,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .load64 (0 : UInt32),
    .localSet 5,
    .constI64 (0 : UInt64),
    .localSet 7,
    .block 0 0 [
      .loop 0 0 [
        .localGet 7,
        .localGet 3,
        .geUI64,
        .br_if 1,
        .constI64 (0 : UInt64),
        .localSet 6,
        .block 0 0 [
          .loop 0 0 [
            .localGet 6,
            .localGet 4,
            .geUI64,
            .br_if 1,
            .localGet 5,
            .localGet 6,
            .shrUI64,
            .constI64 (1 : UInt64),
            .andI64,
            .constI64 (0 : UInt64),
            .neI64,
            .iff 0 0 [
              .localGet 0,
              .constI64 (8 : UInt64),
              .addI64,
              .localGet 7,
              .localGet 4,
              .mulI64,
              .localGet 6,
              .addI64,
              .constI64 (8 : UInt64),
              .mulI64,
              .addI64,
              .wrapI64,
              .load64 (0 : UInt32),
              .localSet 8,
              .localGet 8,
              .call self
            ] [],
            .localGet 6,
            .constI64 (1 : UInt64),
            .addI64,
            .localSet 6,
            .br 0
          ]
        ],
        .localGet 7,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 7,
        .br 0
      ]
    ]
  ] [],
  .globalGet 5,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 5,
  .localGet 0,
  .constI64 (40 : UInt64),
  .subI64,
  .wrapI64,
  .constI64 (0 : UInt64),
  .store64 (0 : UInt32),
  .localGet 0,
  .constI64 (8 : UInt64),
  .subI64,
  .wrapI64,
  .globalGet 1,
  .store64 (0 : UInt32),
  .localGet 0,
  .globalSet 1
]

def releaseFuncDef (self : Nat) : Wasm.Function :=
  { params := [.i64], locals := [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64], body := releaseBody self, results := [] }

end Project.Runtime
