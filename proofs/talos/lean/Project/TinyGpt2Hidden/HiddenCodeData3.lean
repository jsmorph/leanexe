import Project.TinyGpt2Hidden.HiddenCodeData2
namespace Project.TinyGpt2Hidden.HiddenCode
set_option maxRecDepth 8192

noncomputable def tail48 : Wasm.Program :=
  [
  .localSet 479,
  .localGet 479,
  .localSet 480,
  .localGet 421,
  .localSet 481,
  .localGet 422,
  .localSet 482,
  .localGet 423,
  .localSet 483,
  .localGet 424,
  .localSet 484,
  .localGet 477,
  .localGet 478,
  .localGet 480,
  .localGet 481,
  .localGet 482,
  .localGet 483,
  .localGet 484,
  .call 17
  ] ++ tail49

noncomputable def tail47 : Wasm.Program :=
  [
  .localSet 473,
  .localGet 473,
  .localSet 474,
  .constI64 8,
  .localSet 475,
  .constI64 2,
  .localSet 476,
  .constI64 0,
  .localSet 477,
  .localGet 0,
  .localSet 478,
  .call 58
  ] ++ tail48

noncomputable def tail46 : Wasm.Program :=
  [
  .localSet 470,
  .localGet 470,
  .localSet 518,
  .constI64 0,
  .localSet 471,
  .localGet 0,
  .localSet 472,
  .call 55
  ] ++ tail47

noncomputable def tail45 : Wasm.Program :=
  [
  .localSet 465,
  .localSet 464,
  .localSet 463,
  .localSet 462,
  .localGet 462,
  .localSet 466,
  .localGet 463,
  .localSet 467,
  .localGet 464,
  .localSet 468,
  .localGet 465,
  .localSet 469,
  .localGet 448,
  .localGet 449,
  .localGet 451,
  .localGet 452,
  .localGet 453,
  .localGet 466,
  .localGet 467,
  .localGet 468,
  .localGet 469,
  .call 25
  ] ++ tail46

noncomputable def tail44 : Wasm.Program :=
  [
  .localSet 456,
  .localGet 456,
  .localSet 457,
  .localGet 421,
  .localSet 458,
  .localGet 422,
  .localSet 459,
  .localGet 423,
  .localSet 460,
  .localGet 424,
  .localSet 461,
  .localGet 454,
  .localGet 455,
  .localGet 457,
  .localGet 458,
  .localGet 459,
  .localGet 460,
  .localGet 461,
  .call 17
  ] ++ tail45

noncomputable def tail43 : Wasm.Program :=
  [
  .localSet 450,
  .localGet 450,
  .localSet 451,
  .constI64 8,
  .localSet 452,
  .constI64 1,
  .localSet 453,
  .constI64 0,
  .localSet 454,
  .localGet 0,
  .localSet 455,
  .call 58
  ] ++ tail44

noncomputable def tail42 : Wasm.Program :=
  [
  .localSet 447,
  .localGet 447,
  .localSet 517,
  .constI64 0,
  .localSet 448,
  .localGet 0,
  .localSet 449,
  .call 55
  ] ++ tail43

noncomputable def tail41 : Wasm.Program :=
  [
  .localSet 442,
  .localSet 441,
  .localSet 440,
  .localSet 439,
  .localGet 439,
  .localSet 443,
  .localGet 440,
  .localSet 444,
  .localGet 441,
  .localSet 445,
  .localGet 442,
  .localSet 446,
  .localGet 425,
  .localGet 426,
  .localGet 428,
  .localGet 429,
  .localGet 430,
  .localGet 443,
  .localGet 444,
  .localGet 445,
  .localGet 446,
  .call 25
  ] ++ tail42

noncomputable def tail40 : Wasm.Program :=
  [
  .localSet 433,
  .localGet 433,
  .localSet 434,
  .localGet 421,
  .localSet 435,
  .localGet 422,
  .localSet 436,
  .localGet 423,
  .localSet 437,
  .localGet 424,
  .localSet 438,
  .localGet 431,
  .localGet 432,
  .localGet 434,
  .localGet 435,
  .localGet 436,
  .localGet 437,
  .localGet 438,
  .call 17
  ] ++ tail41

noncomputable def tail39 : Wasm.Program :=
  [
  .localSet 427,
  .localGet 427,
  .localSet 428,
  .constI64 8,
  .localSet 429,
  .constI64 0,
  .localSet 430,
  .constI64 0,
  .localSet 431,
  .localGet 0,
  .localSet 432,
  .call 58
  ] ++ tail40

noncomputable def tail38 : Wasm.Program :=
  [
  .localSet 420,
  .localSet 419,
  .localSet 418,
  .localSet 417,
  .localGet 417,
  .localSet 421,
  .localGet 418,
  .localSet 422,
  .localGet 419,
  .localSet 423,
  .localGet 420,
  .localSet 424,
  .constI64 0,
  .localSet 425,
  .localGet 0,
  .localSet 426,
  .call 55
  ] ++ tail39

noncomputable def tail37 : Wasm.Program :=
  [
  .localSet 408,
  .localSet 407,
  .localSet 406,
  .localSet 405,
  .localGet 405,
  .localSet 409,
  .localGet 406,
  .localSet 410,
  .localGet 407,
  .localSet 411,
  .localGet 408,
  .localSet 412,
  .localGet 384,
  .localSet 413,
  .localGet 385,
  .localSet 414,
  .localGet 386,
  .localSet 415,
  .localGet 387,
  .localSet 416,
  .localGet 409,
  .localGet 410,
  .localGet 411,
  .localGet 412,
  .localGet 413,
  .localGet 414,
  .localGet 415,
  .localGet 416,
  .call 4
  ] ++ tail38

noncomputable def tail36 : Wasm.Program :=
  [
  .localSet 383,
  .localSet 382,
  .localSet 381,
  .localSet 380,
  .localGet 383,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 387,
  .localGet 38,
  .localSet 388,
  .localGet 39,
  .localSet 389,
  .localGet 40,
  .localSet 390,
  .localGet 41,
  .localSet 391,
  .localGet 42,
  .localSet 392,
  .localGet 43,
  .localSet 393,
  .localGet 44,
  .localSet 394,
  .localGet 45,
  .localSet 395,
  .localGet 46,
  .localSet 396,
  .localGet 47,
  .localSet 397,
  .localGet 48,
  .localSet 398,
  .localGet 49,
  .localSet 399,
  .localGet 50,
  .localSet 400,
  .localGet 51,
  .localSet 401,
  .localGet 52,
  .localSet 402,
  .localGet 53,
  .localSet 403,
  .localGet 5,
  .localSet 404,
  .localGet 388,
  .localGet 389,
  .localGet 390,
  .localGet 391,
  .localGet 392,
  .localGet 393,
  .localGet 394,
  .localGet 395,
  .localGet 396,
  .localGet 397,
  .localGet 398,
  .localGet 399,
  .localGet 400,
  .localGet 401,
  .localGet 402,
  .localGet 403,
  .localGet 404,
  .call 28
  ] ++ tail37

noncomputable def tail35 : Wasm.Program :=
  [
  .localSet 378,
  .localGet 378,
  .localSet 379,
  .localGet 376,
  .localGet 377,
  .localGet 379,
  .call 5
  ] ++ tail36

end Project.TinyGpt2Hidden.HiddenCode
