import Project.TinyGpt2Hidden.HiddenCodeData5
namespace Project.TinyGpt2Hidden.HiddenCode
set_option maxRecDepth 8192

noncomputable def tail6 : Wasm.Program :=
  [
  .localSet 65,
  .localSet 64,
  .localSet 63,
  .localSet 62,
  .localGet 62,
  .localSet 102,
  .localGet 63,
  .localSet 103,
  .localGet 64,
  .localSet 104,
  .localGet 65,
  .localSet 105,
  .constI64 0,
  .localSet 66,
  .localGet 0,
  .localSet 67,
  .call 18
  ] ++ tail7

noncomputable def tail5 : Wasm.Program :=
  [
  .localSet 56,
  .localGet 56,
  .localSet 57,
  .localGet 38,
  .localSet 58,
  .localGet 39,
  .localSet 59,
  .localGet 40,
  .localSet 60,
  .localGet 41,
  .localSet 61,
  .localGet 54,
  .localGet 55,
  .localGet 57,
  .localGet 58,
  .localGet 59,
  .localGet 60,
  .localGet 61,
  .call 17
  ] ++ tail6

noncomputable def tail4 : Wasm.Program :=
  [
  .localSet 37,
  .localSet 36,
  .localSet 35,
  .localSet 34,
  .localGet 34,
  .localSet 50,
  .localGet 35,
  .localSet 51,
  .localGet 36,
  .localSet 52,
  .localGet 37,
  .localSet 53,
  .constI64 0,
  .localSet 54,
  .localGet 0,
  .localSet 55,
  .call 18
  ] ++ tail5

noncomputable def tail3 : Wasm.Program :=
  [
  .localSet 29,
  .localSet 28,
  .localSet 27,
  .localSet 26,
  .localGet 26,
  .localSet 46,
  .localGet 27,
  .localSet 47,
  .localGet 28,
  .localSet 48,
  .localGet 29,
  .localSet 49,
  .constI64 0,
  .localSet 30,
  .localGet 0,
  .localSet 31,
  .localGet 4,
  .localSet 32,
  .constI64 3,
  .localSet 33,
  .localGet 30,
  .localGet 31,
  .localGet 32,
  .localGet 33,
  .call 8
  ] ++ tail4

noncomputable def tail2 : Wasm.Program :=
  [
  .localSet 21,
  .localSet 20,
  .localSet 19,
  .localSet 18,
  .localGet 18,
  .localSet 42,
  .localGet 19,
  .localSet 43,
  .localGet 20,
  .localSet 44,
  .localGet 21,
  .localSet 45,
  .constI64 0,
  .localSet 22,
  .localGet 0,
  .localSet 23,
  .localGet 3,
  .localSet 24,
  .constI64 2,
  .localSet 25,
  .localGet 22,
  .localGet 23,
  .localGet 24,
  .localGet 25,
  .call 8
  ] ++ tail3

noncomputable def tail1 : Wasm.Program :=
  [
  .localSet 13,
  .localSet 12,
  .localSet 11,
  .localSet 10,
  .localGet 10,
  .localSet 38,
  .localGet 11,
  .localSet 39,
  .localGet 12,
  .localSet 40,
  .localGet 13,
  .localSet 41,
  .constI64 0,
  .localSet 14,
  .localGet 0,
  .localSet 15,
  .localGet 2,
  .localSet 16,
  .constI64 1,
  .localSet 17,
  .localGet 14,
  .localGet 15,
  .localGet 16,
  .localGet 17,
  .call 8
  ] ++ tail2

noncomputable def tail0 : Wasm.Program :=
  [
  .constI64 0,
  .localSet 6,
  .localGet 0,
  .localSet 7,
  .localGet 1,
  .localSet 8,
  .constI64 0,
  .localSet 9,
  .localGet 6,
  .localGet 7,
  .localGet 8,
  .localGet 9,
  .call 8
  ] ++ tail1

end Project.TinyGpt2Hidden.HiddenCode
