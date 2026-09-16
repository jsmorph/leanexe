import Project.TinyGpt2Infer.Program

namespace Project.TinyGpt2Infer.HiddenCode

set_option maxRecDepth 8192

noncomputable def tail90 : Wasm.Program :=
  [
  .localSet 781,
  .localSet 780,
  .localSet 779,
  .localSet 778,
  .localGet 778,
  .localSet 782,
  .localGet 779,
  .localSet 783,
  .localGet 780,
  .localSet 784,
  .localGet 781,
  .localSet 785,
  .localGet 782,
  .localGet 783,
  .localGet 784,
  .localGet 785
  ]

noncomputable def tail89 : Wasm.Program :=
  [
  .localSet 772,
  .localGet 772,
  .localSet 773,
  .localGet 766,
  .localSet 774,
  .localGet 767,
  .localSet 775,
  .localGet 768,
  .localSet 776,
  .localGet 769,
  .localSet 777,
  .localGet 770,
  .localGet 771,
  .localGet 773,
  .localGet 774,
  .localGet 775,
  .localGet 776,
  .localGet 777,
  .call 17
  ] ++ tail90

noncomputable def tail88 : Wasm.Program :=
  [
  .localSet 765,
  .localSet 764,
  .localSet 763,
  .localSet 762,
  .localGet 765,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 769,
  .localGet 0,
  .localSet 770,
  .localGet 1,
  .localSet 771,
  .call 70
  ] ++ tail89

noncomputable def tail87 : Wasm.Program :=
  [
  .localSet 751,
  .localSet 750,
  .localSet 749,
  .localSet 748,
  .localGet 750,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 768,
  .localGet 425,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 752,
  .localGet 1,
  .localSet 753,
  .localGet 702,
  .localSet 754,
  .localGet 703,
  .localSet 755,
  .localGet 704,
  .localSet 756,
  .localGet 705,
  .localSet 757,
  .localGet 706,
  .localSet 758,
  .localGet 707,
  .localSet 759,
  .localGet 708,
  .localSet 760,
  .localGet 709,
  .localSet 761,
  .localGet 752,
  .localGet 753,
  .localGet 754,
  .localGet 755,
  .localGet 756,
  .localGet 757,
  .localGet 758,
  .localGet 759,
  .localGet 760,
  .localGet 761,
  .call 69
  ] ++ tail88

noncomputable def tail86 : Wasm.Program :=
  [
  .localSet 737,
  .localSet 736,
  .localSet 735,
  .localSet 734,
  .localGet 735,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 767,
  .localGet 424,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 738,
  .localGet 1,
  .localSet 739,
  .localGet 702,
  .localSet 740,
  .localGet 703,
  .localSet 741,
  .localGet 704,
  .localSet 742,
  .localGet 705,
  .localSet 743,
  .localGet 706,
  .localSet 744,
  .localGet 707,
  .localSet 745,
  .localGet 708,
  .localSet 746,
  .localGet 709,
  .localSet 747,
  .localGet 738,
  .localGet 739,
  .localGet 740,
  .localGet 741,
  .localGet 742,
  .localGet 743,
  .localGet 744,
  .localGet 745,
  .localGet 746,
  .localGet 747,
  .call 69
  ] ++ tail87

noncomputable def tail85 : Wasm.Program :=
  [
  .localSet 723,
  .localSet 722,
  .localSet 721,
  .localSet 720,
  .localGet 720,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 766,
  .localGet 423,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 724,
  .localGet 1,
  .localSet 725,
  .localGet 702,
  .localSet 726,
  .localGet 703,
  .localSet 727,
  .localGet 704,
  .localSet 728,
  .localGet 705,
  .localSet 729,
  .localGet 706,
  .localSet 730,
  .localGet 707,
  .localSet 731,
  .localGet 708,
  .localSet 732,
  .localGet 709,
  .localSet 733,
  .localGet 724,
  .localGet 725,
  .localGet 726,
  .localGet 727,
  .localGet 728,
  .localGet 729,
  .localGet 730,
  .localGet 731,
  .localGet 732,
  .localGet 733,
  .call 69
  ] ++ tail86

noncomputable def tail84 : Wasm.Program :=
  [
  .localSet 701,
  .localSet 700,
  .localSet 699,
  .localSet 698,
  .localGet 698,
  .localSet 706,
  .localGet 699,
  .localSet 707,
  .localGet 700,
  .localSet 708,
  .localGet 701,
  .localSet 709,
  .localGet 422,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 710,
  .localGet 1,
  .localSet 711,
  .localGet 702,
  .localSet 712,
  .localGet 703,
  .localSet 713,
  .localGet 704,
  .localSet 714,
  .localGet 705,
  .localSet 715,
  .localGet 706,
  .localSet 716,
  .localGet 707,
  .localSet 717,
  .localGet 708,
  .localSet 718,
  .localGet 709,
  .localSet 719,
  .localGet 710,
  .localGet 711,
  .localGet 712,
  .localGet 713,
  .localGet 714,
  .localGet 715,
  .localGet 716,
  .localGet 717,
  .localGet 718,
  .localGet 719,
  .call 69
  ] ++ tail85

noncomputable def tail83 : Wasm.Program :=
  [
  .localSet 693,
  .localSet 692,
  .localSet 691,
  .localSet 690,
  .localGet 690,
  .localSet 702,
  .localGet 691,
  .localSet 703,
  .localGet 692,
  .localSet 704,
  .localGet 693,
  .localSet 705,
  .localGet 682,
  .localSet 694,
  .localGet 683,
  .localSet 695,
  .localGet 684,
  .localSet 696,
  .localGet 685,
  .localSet 697,
  .localGet 694,
  .localGet 695,
  .localGet 696,
  .localGet 697,
  .call 62
  ] ++ tail84

noncomputable def tail82 : Wasm.Program :=
  [
  .localSet 677,
  .localSet 676,
  .localSet 675,
  .localSet 674,
  .localGet 677,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 685,
  .localGet 678,
  .localSet 686,
  .localGet 679,
  .localSet 687,
  .localGet 680,
  .localSet 688,
  .localGet 681,
  .localSet 689,
  .localGet 686,
  .localGet 687,
  .localGet 688,
  .localGet 689,
  .call 62
  ] ++ tail83

noncomputable def tail81 : Wasm.Program :=
  [
  .localSet 670,
  .localSet 669,
  .localSet 668,
  .localSet 667,
  .localGet 669,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 684,
  .localGet 617,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 671,
  .localGet 1,
  .localSet 672,
  .constI64 1140,
  .localSet 786,
  .constI64 4,
  .localSet 787,
  .localGet 786,
  .localGet 787,
  .addI64,
  .localTee 788,
  .localGet 786,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 788
  ] [] [.i64],
  .localSet 673,
  .localGet 671,
  .localGet 672,
  .localGet 673,
  .call 5
  ] ++ tail82

noncomputable def tail80 : Wasm.Program :=
  [
  .localSet 663,
  .localSet 662,
  .localSet 661,
  .localSet 660,
  .localGet 661,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 683,
  .localGet 616,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 664,
  .localGet 1,
  .localSet 665,
  .constI64 1140,
  .localSet 786,
  .constI64 4,
  .localSet 787,
  .localGet 786,
  .localGet 787,
  .addI64,
  .localTee 788,
  .localGet 786,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 788
  ] [] [.i64],
  .localSet 666,
  .localGet 664,
  .localGet 665,
  .localGet 666,
  .call 5
  ] ++ tail81

noncomputable def tail79 : Wasm.Program :=
  [
  .localSet 656,
  .localSet 655,
  .localSet 654,
  .localSet 653,
  .localGet 653,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 682,
  .localGet 615,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 657,
  .localGet 1,
  .localSet 658,
  .constI64 1140,
  .localSet 786,
  .constI64 4,
  .localSet 787,
  .localGet 786,
  .localGet 787,
  .addI64,
  .localTee 788,
  .localGet 786,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 788
  ] [] [.i64],
  .localSet 659,
  .localGet 657,
  .localGet 658,
  .localGet 659,
  .call 5
  ] ++ tail80

noncomputable def tail78 : Wasm.Program :=
  [
  .localSet 649,
  .localSet 648,
  .localSet 647,
  .localSet 646,
  .localGet 649,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 681,
  .localGet 614,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 650,
  .localGet 1,
  .localSet 651,
  .constI64 1140,
  .localSet 786,
  .constI64 4,
  .localSet 787,
  .localGet 786,
  .localGet 787,
  .addI64,
  .localTee 788,
  .localGet 786,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 788
  ] [] [.i64],
  .localSet 652,
  .localGet 650,
  .localGet 651,
  .localGet 652,
  .call 5
  ] ++ tail79

noncomputable def tail77 : Wasm.Program :=
  [
  .localSet 644,
  .localGet 644,
  .localSet 645,
  .localGet 642,
  .localGet 643,
  .localGet 645,
  .call 5
  ] ++ tail78

noncomputable def tail76 : Wasm.Program :=
  [
  .localSet 641,
  .localSet 640,
  .localSet 639,
  .localSet 638,
  .localGet 640,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 680,
  .localGet 521,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 642,
  .localGet 1,
  .localSet 643,
  .call 52
  ] ++ tail77

noncomputable def tail75 : Wasm.Program :=
  [
  .localSet 636,
  .localGet 636,
  .localSet 637,
  .localGet 634,
  .localGet 635,
  .localGet 637,
  .call 5
  ] ++ tail76

noncomputable def tail74 : Wasm.Program :=
  [
  .localSet 633,
  .localSet 632,
  .localSet 631,
  .localSet 630,
  .localGet 631,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 679,
  .localGet 520,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 634,
  .localGet 1,
  .localSet 635,
  .call 52
  ] ++ tail75

noncomputable def tail73 : Wasm.Program :=
  [
  .localSet 628,
  .localGet 628,
  .localSet 629,
  .localGet 626,
  .localGet 627,
  .localGet 629,
  .call 5
  ] ++ tail74

noncomputable def tail72 : Wasm.Program :=
  [
  .localSet 625,
  .localSet 624,
  .localSet 623,
  .localSet 622,
  .localGet 622,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 678,
  .localGet 519,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 626,
  .localGet 1,
  .localSet 627,
  .call 52
  ] ++ tail73

noncomputable def tail71 : Wasm.Program :=
  [
  .localSet 620,
  .localGet 620,
  .localSet 621,
  .localGet 618,
  .localGet 619,
  .localGet 621,
  .call 5
  ] ++ tail72

noncomputable def tail70 : Wasm.Program :=
  [
  .localSet 613,
  .localGet 613,
  .localSet 617,
  .localGet 518,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 618,
  .localGet 1,
  .localSet 619,
  .call 52
  ] ++ tail71

noncomputable def tail69 : Wasm.Program :=
  [
  .localSet 608,
  .localSet 607,
  .localSet 606,
  .localSet 605,
  .localGet 605,
  .localSet 609,
  .localGet 606,
  .localSet 610,
  .localGet 607,
  .localSet 611,
  .localGet 608,
  .localSet 612,
  .localGet 591,
  .localGet 592,
  .localGet 594,
  .localGet 595,
  .localGet 596,
  .localGet 609,
  .localGet 610,
  .localGet 611,
  .localGet 612,
  .call 25
  ] ++ tail70

noncomputable def tail68 : Wasm.Program :=
  [
  .localSet 599,
  .localGet 599,
  .localSet 600,
  .localGet 422,
  .localSet 601,
  .localGet 423,
  .localSet 602,
  .localGet 424,
  .localSet 603,
  .localGet 425,
  .localSet 604,
  .localGet 597,
  .localGet 598,
  .localGet 600,
  .localGet 601,
  .localGet 602,
  .localGet 603,
  .localGet 604,
  .call 17
  ] ++ tail69

noncomputable def tail67 : Wasm.Program :=
  [
  .localSet 593,
  .localGet 593,
  .localSet 594,
  .constI64 8,
  .localSet 595,
  .constI64 7,
  .localSet 596,
  .localGet 0,
  .localSet 597,
  .localGet 1,
  .localSet 598,
  .call 54
  ] ++ tail68

noncomputable def tail66 : Wasm.Program :=
  [
  .localSet 590,
  .localGet 590,
  .localSet 616,
  .localGet 0,
  .localSet 591,
  .localGet 1,
  .localSet 592,
  .call 51
  ] ++ tail67

noncomputable def tail65 : Wasm.Program :=
  [
  .localSet 585,
  .localSet 584,
  .localSet 583,
  .localSet 582,
  .localGet 582,
  .localSet 586,
  .localGet 583,
  .localSet 587,
  .localGet 584,
  .localSet 588,
  .localGet 585,
  .localSet 589,
  .localGet 568,
  .localGet 569,
  .localGet 571,
  .localGet 572,
  .localGet 573,
  .localGet 586,
  .localGet 587,
  .localGet 588,
  .localGet 589,
  .call 25
  ] ++ tail66

noncomputable def tail64 : Wasm.Program :=
  [
  .localSet 576,
  .localGet 576,
  .localSet 577,
  .localGet 422,
  .localSet 578,
  .localGet 423,
  .localSet 579,
  .localGet 424,
  .localSet 580,
  .localGet 425,
  .localSet 581,
  .localGet 574,
  .localGet 575,
  .localGet 577,
  .localGet 578,
  .localGet 579,
  .localGet 580,
  .localGet 581,
  .call 17
  ] ++ tail65

noncomputable def tail63 : Wasm.Program :=
  [
  .localSet 570,
  .localGet 570,
  .localSet 571,
  .constI64 8,
  .localSet 572,
  .constI64 6,
  .localSet 573,
  .localGet 0,
  .localSet 574,
  .localGet 1,
  .localSet 575,
  .call 54
  ] ++ tail64

noncomputable def tail62 : Wasm.Program :=
  [
  .localSet 567,
  .localGet 567,
  .localSet 615,
  .localGet 0,
  .localSet 568,
  .localGet 1,
  .localSet 569,
  .call 51
  ] ++ tail63

noncomputable def tail61 : Wasm.Program :=
  [
  .localSet 562,
  .localSet 561,
  .localSet 560,
  .localSet 559,
  .localGet 559,
  .localSet 563,
  .localGet 560,
  .localSet 564,
  .localGet 561,
  .localSet 565,
  .localGet 562,
  .localSet 566,
  .localGet 545,
  .localGet 546,
  .localGet 548,
  .localGet 549,
  .localGet 550,
  .localGet 563,
  .localGet 564,
  .localGet 565,
  .localGet 566,
  .call 25
  ] ++ tail62

noncomputable def tail60 : Wasm.Program :=
  [
  .localSet 553,
  .localGet 553,
  .localSet 554,
  .localGet 422,
  .localSet 555,
  .localGet 423,
  .localSet 556,
  .localGet 424,
  .localSet 557,
  .localGet 425,
  .localSet 558,
  .localGet 551,
  .localGet 552,
  .localGet 554,
  .localGet 555,
  .localGet 556,
  .localGet 557,
  .localGet 558,
  .call 17
  ] ++ tail61

noncomputable def tail59 : Wasm.Program :=
  [
  .localSet 547,
  .localGet 547,
  .localSet 548,
  .constI64 8,
  .localSet 549,
  .constI64 5,
  .localSet 550,
  .localGet 0,
  .localSet 551,
  .localGet 1,
  .localSet 552,
  .call 54
  ] ++ tail60

noncomputable def tail58 : Wasm.Program :=
  [
  .localSet 544,
  .localGet 544,
  .localSet 614,
  .localGet 0,
  .localSet 545,
  .localGet 1,
  .localSet 546,
  .call 51
  ] ++ tail59

noncomputable def tail57 : Wasm.Program :=
  [
  .localSet 539,
  .localSet 538,
  .localSet 537,
  .localSet 536,
  .localGet 536,
  .localSet 540,
  .localGet 537,
  .localSet 541,
  .localGet 538,
  .localSet 542,
  .localGet 539,
  .localSet 543,
  .localGet 522,
  .localGet 523,
  .localGet 525,
  .localGet 526,
  .localGet 527,
  .localGet 540,
  .localGet 541,
  .localGet 542,
  .localGet 543,
  .call 25
  ] ++ tail58

noncomputable def tail56 : Wasm.Program :=
  [
  .localSet 530,
  .localGet 530,
  .localSet 531,
  .localGet 422,
  .localSet 532,
  .localGet 423,
  .localSet 533,
  .localGet 424,
  .localSet 534,
  .localGet 425,
  .localSet 535,
  .localGet 528,
  .localGet 529,
  .localGet 531,
  .localGet 532,
  .localGet 533,
  .localGet 534,
  .localGet 535,
  .call 17
  ] ++ tail57

noncomputable def tail55 : Wasm.Program :=
  [
  .localSet 524,
  .localGet 524,
  .localSet 525,
  .constI64 8,
  .localSet 526,
  .constI64 4,
  .localSet 527,
  .localGet 0,
  .localSet 528,
  .localGet 1,
  .localSet 529,
  .call 54
  ] ++ tail56

noncomputable def tail54 : Wasm.Program :=
  [
  .localSet 517,
  .localGet 517,
  .localSet 521,
  .localGet 0,
  .localSet 522,
  .localGet 1,
  .localSet 523,
  .call 51
  ] ++ tail55

noncomputable def tail53 : Wasm.Program :=
  [
  .localSet 512,
  .localSet 511,
  .localSet 510,
  .localSet 509,
  .localGet 509,
  .localSet 513,
  .localGet 510,
  .localSet 514,
  .localGet 511,
  .localSet 515,
  .localGet 512,
  .localSet 516,
  .localGet 495,
  .localGet 496,
  .localGet 498,
  .localGet 499,
  .localGet 500,
  .localGet 513,
  .localGet 514,
  .localGet 515,
  .localGet 516,
  .call 25
  ] ++ tail54

noncomputable def tail52 : Wasm.Program :=
  [
  .localSet 503,
  .localGet 503,
  .localSet 504,
  .localGet 422,
  .localSet 505,
  .localGet 423,
  .localSet 506,
  .localGet 424,
  .localSet 507,
  .localGet 425,
  .localSet 508,
  .localGet 501,
  .localGet 502,
  .localGet 504,
  .localGet 505,
  .localGet 506,
  .localGet 507,
  .localGet 508,
  .call 17
  ] ++ tail53

noncomputable def tail51 : Wasm.Program :=
  [
  .localSet 497,
  .localGet 497,
  .localSet 498,
  .constI64 8,
  .localSet 499,
  .constI64 3,
  .localSet 500,
  .localGet 0,
  .localSet 501,
  .localGet 1,
  .localSet 502,
  .call 54
  ] ++ tail52

noncomputable def tail50 : Wasm.Program :=
  [
  .localSet 494,
  .localGet 494,
  .localSet 520,
  .localGet 0,
  .localSet 495,
  .localGet 1,
  .localSet 496,
  .call 51
  ] ++ tail51

noncomputable def tail49 : Wasm.Program :=
  [
  .localSet 489,
  .localSet 488,
  .localSet 487,
  .localSet 486,
  .localGet 486,
  .localSet 490,
  .localGet 487,
  .localSet 491,
  .localGet 488,
  .localSet 492,
  .localGet 489,
  .localSet 493,
  .localGet 472,
  .localGet 473,
  .localGet 475,
  .localGet 476,
  .localGet 477,
  .localGet 490,
  .localGet 491,
  .localGet 492,
  .localGet 493,
  .call 25
  ] ++ tail50

noncomputable def tail48 : Wasm.Program :=
  [
  .localSet 480,
  .localGet 480,
  .localSet 481,
  .localGet 422,
  .localSet 482,
  .localGet 423,
  .localSet 483,
  .localGet 424,
  .localSet 484,
  .localGet 425,
  .localSet 485,
  .localGet 478,
  .localGet 479,
  .localGet 481,
  .localGet 482,
  .localGet 483,
  .localGet 484,
  .localGet 485,
  .call 17
  ] ++ tail49

noncomputable def tail47 : Wasm.Program :=
  [
  .localSet 474,
  .localGet 474,
  .localSet 475,
  .constI64 8,
  .localSet 476,
  .constI64 2,
  .localSet 477,
  .localGet 0,
  .localSet 478,
  .localGet 1,
  .localSet 479,
  .call 54
  ] ++ tail48

noncomputable def tail46 : Wasm.Program :=
  [
  .localSet 471,
  .localGet 471,
  .localSet 519,
  .localGet 0,
  .localSet 472,
  .localGet 1,
  .localSet 473,
  .call 51
  ] ++ tail47

noncomputable def tail45 : Wasm.Program :=
  [
  .localSet 466,
  .localSet 465,
  .localSet 464,
  .localSet 463,
  .localGet 463,
  .localSet 467,
  .localGet 464,
  .localSet 468,
  .localGet 465,
  .localSet 469,
  .localGet 466,
  .localSet 470,
  .localGet 449,
  .localGet 450,
  .localGet 452,
  .localGet 453,
  .localGet 454,
  .localGet 467,
  .localGet 468,
  .localGet 469,
  .localGet 470,
  .call 25
  ] ++ tail46

noncomputable def tail44 : Wasm.Program :=
  [
  .localSet 457,
  .localGet 457,
  .localSet 458,
  .localGet 422,
  .localSet 459,
  .localGet 423,
  .localSet 460,
  .localGet 424,
  .localSet 461,
  .localGet 425,
  .localSet 462,
  .localGet 455,
  .localGet 456,
  .localGet 458,
  .localGet 459,
  .localGet 460,
  .localGet 461,
  .localGet 462,
  .call 17
  ] ++ tail45

noncomputable def tail43 : Wasm.Program :=
  [
  .localSet 451,
  .localGet 451,
  .localSet 452,
  .constI64 8,
  .localSet 453,
  .constI64 1,
  .localSet 454,
  .localGet 0,
  .localSet 455,
  .localGet 1,
  .localSet 456,
  .call 54
  ] ++ tail44

noncomputable def tail42 : Wasm.Program :=
  [
  .localSet 448,
  .localGet 448,
  .localSet 518,
  .localGet 0,
  .localSet 449,
  .localGet 1,
  .localSet 450,
  .call 51
  ] ++ tail43

noncomputable def tail41 : Wasm.Program :=
  [
  .localSet 443,
  .localSet 442,
  .localSet 441,
  .localSet 440,
  .localGet 440,
  .localSet 444,
  .localGet 441,
  .localSet 445,
  .localGet 442,
  .localSet 446,
  .localGet 443,
  .localSet 447,
  .localGet 426,
  .localGet 427,
  .localGet 429,
  .localGet 430,
  .localGet 431,
  .localGet 444,
  .localGet 445,
  .localGet 446,
  .localGet 447,
  .call 25
  ] ++ tail42

noncomputable def tail40 : Wasm.Program :=
  [
  .localSet 434,
  .localGet 434,
  .localSet 435,
  .localGet 422,
  .localSet 436,
  .localGet 423,
  .localSet 437,
  .localGet 424,
  .localSet 438,
  .localGet 425,
  .localSet 439,
  .localGet 432,
  .localGet 433,
  .localGet 435,
  .localGet 436,
  .localGet 437,
  .localGet 438,
  .localGet 439,
  .call 17
  ] ++ tail41

noncomputable def tail39 : Wasm.Program :=
  [
  .localSet 428,
  .localGet 428,
  .localSet 429,
  .constI64 8,
  .localSet 430,
  .constI64 0,
  .localSet 431,
  .localGet 0,
  .localSet 432,
  .localGet 1,
  .localSet 433,
  .call 54
  ] ++ tail40

noncomputable def tail38 : Wasm.Program :=
  [
  .localSet 421,
  .localSet 420,
  .localSet 419,
  .localSet 418,
  .localGet 418,
  .localSet 422,
  .localGet 419,
  .localSet 423,
  .localGet 420,
  .localSet 424,
  .localGet 421,
  .localSet 425,
  .localGet 0,
  .localSet 426,
  .localGet 1,
  .localSet 427,
  .call 51
  ] ++ tail39

noncomputable def tail37 : Wasm.Program :=
  [
  .localSet 409,
  .localSet 408,
  .localSet 407,
  .localSet 406,
  .localGet 406,
  .localSet 410,
  .localGet 407,
  .localSet 411,
  .localGet 408,
  .localSet 412,
  .localGet 409,
  .localSet 413,
  .localGet 385,
  .localSet 414,
  .localGet 386,
  .localSet 415,
  .localGet 387,
  .localSet 416,
  .localGet 388,
  .localSet 417,
  .localGet 410,
  .localGet 411,
  .localGet 412,
  .localGet 413,
  .localGet 414,
  .localGet 415,
  .localGet 416,
  .localGet 417,
  .call 4
  ] ++ tail38

noncomputable def tail36 : Wasm.Program :=
  [
  .localSet 384,
  .localSet 383,
  .localSet 382,
  .localSet 381,
  .localGet 384,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
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
  .localGet 54,
  .localSet 404,
  .localGet 6,
  .localSet 405,
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
  .localGet 405,
  .call 28
  ] ++ tail37

noncomputable def tail35 : Wasm.Program :=
  [
  .localSet 379,
  .localGet 379,
  .localSet 380,
  .localGet 377,
  .localGet 378,
  .localGet 380,
  .call 5
  ] ++ tail36

noncomputable def tail34 : Wasm.Program :=
  [
  .localSet 376,
  .localSet 375,
  .localSet 374,
  .localSet 373,
  .localGet 376,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 377,
  .localGet 1,
  .localSet 378,
  .call 50
  ] ++ tail35

noncomputable def tail33 : Wasm.Program :=
  [
  .localSet 367,
  .localGet 367,
  .localSet 368,
  .localGet 301,
  .localSet 369,
  .localGet 302,
  .localSet 370,
  .localGet 303,
  .localSet 371,
  .localGet 304,
  .localSet 372,
  .localGet 365,
  .localGet 366,
  .localGet 368,
  .localGet 369,
  .localGet 370,
  .localGet 371,
  .localGet 372,
  .call 26
  ] ++ tail34

noncomputable def tail32 : Wasm.Program :=
  [
  .localSet 364,
  .localSet 363,
  .localSet 362,
  .localSet 361,
  .localGet 363,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 387,
  .localGet 0,
  .localSet 365,
  .localGet 1,
  .localSet 366,
  .call 49
  ] ++ tail33

noncomputable def tail31 : Wasm.Program :=
  [
  .localSet 359,
  .localGet 359,
  .localSet 360,
  .localGet 357,
  .localGet 358,
  .localGet 360,
  .call 5
  ] ++ tail32

noncomputable def tail30 : Wasm.Program :=
  [
  .localSet 356,
  .localSet 355,
  .localSet 354,
  .localSet 353,
  .localGet 355,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 357,
  .localGet 1,
  .localSet 358,
  .call 50
  ] ++ tail31

noncomputable def tail29 : Wasm.Program :=
  [
  .localSet 347,
  .localGet 347,
  .localSet 348,
  .localGet 301,
  .localSet 349,
  .localGet 302,
  .localSet 350,
  .localGet 303,
  .localSet 351,
  .localGet 304,
  .localSet 352,
  .localGet 345,
  .localGet 346,
  .localGet 348,
  .localGet 349,
  .localGet 350,
  .localGet 351,
  .localGet 352,
  .call 26
  ] ++ tail30

noncomputable def tail28 : Wasm.Program :=
  [
  .localSet 344,
  .localSet 343,
  .localSet 342,
  .localSet 341,
  .localGet 342,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 386,
  .localGet 0,
  .localSet 345,
  .localGet 1,
  .localSet 346,
  .call 49
  ] ++ tail29

noncomputable def tail27 : Wasm.Program :=
  [
  .localSet 339,
  .localGet 339,
  .localSet 340,
  .localGet 337,
  .localGet 338,
  .localGet 340,
  .call 5
  ] ++ tail28

noncomputable def tail26 : Wasm.Program :=
  [
  .localSet 336,
  .localSet 335,
  .localSet 334,
  .localSet 333,
  .localGet 334,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 337,
  .localGet 1,
  .localSet 338,
  .call 50
  ] ++ tail27

noncomputable def tail25 : Wasm.Program :=
  [
  .localSet 327,
  .localGet 327,
  .localSet 328,
  .localGet 301,
  .localSet 329,
  .localGet 302,
  .localSet 330,
  .localGet 303,
  .localSet 331,
  .localGet 304,
  .localSet 332,
  .localGet 325,
  .localGet 326,
  .localGet 328,
  .localGet 329,
  .localGet 330,
  .localGet 331,
  .localGet 332,
  .call 26
  ] ++ tail26

noncomputable def tail24 : Wasm.Program :=
  [
  .localSet 324,
  .localSet 323,
  .localSet 322,
  .localSet 321,
  .localGet 321,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 385,
  .localGet 0,
  .localSet 325,
  .localGet 1,
  .localSet 326,
  .call 49
  ] ++ tail25

noncomputable def tail23 : Wasm.Program :=
  [
  .localSet 319,
  .localGet 319,
  .localSet 320,
  .localGet 317,
  .localGet 318,
  .localGet 320,
  .call 5
  ] ++ tail24

noncomputable def tail22 : Wasm.Program :=
  [
  .localSet 316,
  .localSet 315,
  .localSet 314,
  .localSet 313,
  .localGet 313,
  .f64ReinterpretI64,
  .localGet 0,
  .localSet 317,
  .localGet 1,
  .localSet 318,
  .call 50
  ] ++ tail23

noncomputable def tail21 : Wasm.Program :=
  [
  .localSet 307,
  .localGet 307,
  .localSet 308,
  .localGet 301,
  .localSet 309,
  .localGet 302,
  .localSet 310,
  .localGet 303,
  .localSet 311,
  .localGet 304,
  .localSet 312,
  .localGet 305,
  .localGet 306,
  .localGet 308,
  .localGet 309,
  .localGet 310,
  .localGet 311,
  .localGet 312,
  .call 26
  ] ++ tail22

noncomputable def tail20 : Wasm.Program :=
  [
  .localSet 300,
  .localSet 299,
  .localSet 298,
  .localSet 297,
  .localGet 297,
  .localSet 301,
  .localGet 298,
  .localSet 302,
  .localGet 299,
  .localSet 303,
  .localGet 300,
  .localSet 304,
  .localGet 0,
  .localSet 305,
  .localGet 1,
  .localSet 306,
  .call 49
  ] ++ tail21

noncomputable def tail19 : Wasm.Program :=
  [
  .localSet 243,
  .localSet 242,
  .localSet 241,
  .localSet 240,
  .localSet 239,
  .localSet 238,
  .localSet 237,
  .localSet 236,
  .localSet 235,
  .localSet 234,
  .localSet 233,
  .localSet 232,
  .localSet 231,
  .localSet 230,
  .localSet 229,
  .localSet 228,
  .localGet 228,
  .localSet 244,
  .localGet 229,
  .localSet 245,
  .localGet 230,
  .localSet 246,
  .localGet 231,
  .localSet 247,
  .localGet 232,
  .localSet 248,
  .localGet 233,
  .localSet 249,
  .localGet 234,
  .localSet 250,
  .localGet 235,
  .localSet 251,
  .localGet 236,
  .localSet 252,
  .localGet 237,
  .localSet 253,
  .localGet 238,
  .localSet 254,
  .localGet 239,
  .localSet 255,
  .localGet 240,
  .localSet 256,
  .localGet 241,
  .localSet 257,
  .localGet 242,
  .localSet 258,
  .localGet 243,
  .localSet 259,
  .localGet 6,
  .constI64 1,
  .addI64,
  .localSet 260,
  .localGet 152,
  .localSet 261,
  .localGet 153,
  .localSet 262,
  .localGet 154,
  .localSet 263,
  .localGet 155,
  .localSet 264,
  .localGet 192,
  .localSet 265,
  .localGet 193,
  .localSet 266,
  .localGet 194,
  .localSet 267,
  .localGet 195,
  .localSet 268,
  .localGet 196,
  .localSet 269,
  .localGet 197,
  .localSet 270,
  .localGet 198,
  .localSet 271,
  .localGet 199,
  .localSet 272,
  .localGet 200,
  .localSet 273,
  .localGet 201,
  .localSet 274,
  .localGet 202,
  .localSet 275,
  .localGet 203,
  .localSet 276,
  .localGet 204,
  .localSet 277,
  .localGet 205,
  .localSet 278,
  .localGet 206,
  .localSet 279,
  .localGet 207,
  .localSet 280,
  .localGet 244,
  .localSet 281,
  .localGet 245,
  .localSet 282,
  .localGet 246,
  .localSet 283,
  .localGet 247,
  .localSet 284,
  .localGet 248,
  .localSet 285,
  .localGet 249,
  .localSet 286,
  .localGet 250,
  .localSet 287,
  .localGet 251,
  .localSet 288,
  .localGet 252,
  .localSet 289,
  .localGet 253,
  .localSet 290,
  .localGet 254,
  .localSet 291,
  .localGet 255,
  .localSet 292,
  .localGet 256,
  .localSet 293,
  .localGet 257,
  .localSet 294,
  .localGet 258,
  .localSet 295,
  .localGet 259,
  .localSet 296,
  .localGet 260,
  .localGet 261,
  .localGet 262,
  .localGet 263,
  .localGet 264,
  .localGet 265,
  .localGet 266,
  .localGet 267,
  .localGet 268,
  .localGet 269,
  .localGet 270,
  .localGet 271,
  .localGet 272,
  .localGet 273,
  .localGet 274,
  .localGet 275,
  .localGet 276,
  .localGet 277,
  .localGet 278,
  .localGet 279,
  .localGet 280,
  .localGet 281,
  .localGet 282,
  .localGet 283,
  .localGet 284,
  .localGet 285,
  .localGet 286,
  .localGet 287,
  .localGet 288,
  .localGet 289,
  .localGet 290,
  .localGet 291,
  .localGet 292,
  .localGet 293,
  .localGet 294,
  .localGet 295,
  .localGet 296,
  .call 48
  ] ++ tail20

noncomputable def tail18 : Wasm.Program :=
  [
  .localSet 210,
  .localGet 210,
  .localSet 211,
  .localGet 103,
  .localSet 212,
  .localGet 104,
  .localSet 213,
  .localGet 105,
  .localSet 214,
  .localGet 106,
  .localSet 215,
  .localGet 107,
  .localSet 216,
  .localGet 108,
  .localSet 217,
  .localGet 109,
  .localSet 218,
  .localGet 110,
  .localSet 219,
  .localGet 111,
  .localSet 220,
  .localGet 112,
  .localSet 221,
  .localGet 113,
  .localSet 222,
  .localGet 114,
  .localSet 223,
  .localGet 115,
  .localSet 224,
  .localGet 116,
  .localSet 225,
  .localGet 117,
  .localSet 226,
  .localGet 118,
  .localSet 227,
  .localGet 208,
  .localGet 209,
  .localGet 211,
  .localGet 212,
  .localGet 213,
  .localGet 214,
  .localGet 215,
  .localGet 216,
  .localGet 217,
  .localGet 218,
  .localGet 219,
  .localGet 220,
  .localGet 221,
  .localGet 222,
  .localGet 223,
  .localGet 224,
  .localGet 225,
  .localGet 226,
  .localGet 227,
  .call 29
  ] ++ tail19

noncomputable def tail17 : Wasm.Program :=
  [
  .localSet 191,
  .localSet 190,
  .localSet 189,
  .localSet 188,
  .localSet 187,
  .localSet 186,
  .localSet 185,
  .localSet 184,
  .localSet 183,
  .localSet 182,
  .localSet 181,
  .localSet 180,
  .localSet 179,
  .localSet 178,
  .localSet 177,
  .localSet 176,
  .localGet 176,
  .localSet 192,
  .localGet 177,
  .localSet 193,
  .localGet 178,
  .localSet 194,
  .localGet 179,
  .localSet 195,
  .localGet 180,
  .localSet 196,
  .localGet 181,
  .localSet 197,
  .localGet 182,
  .localSet 198,
  .localGet 183,
  .localSet 199,
  .localGet 184,
  .localSet 200,
  .localGet 185,
  .localSet 201,
  .localGet 186,
  .localSet 202,
  .localGet 187,
  .localSet 203,
  .localGet 188,
  .localSet 204,
  .localGet 189,
  .localSet 205,
  .localGet 190,
  .localSet 206,
  .localGet 191,
  .localSet 207,
  .localGet 0,
  .localSet 208,
  .localGet 1,
  .localSet 209,
  .call 31
  ] ++ tail18

noncomputable def tail16 : Wasm.Program :=
  [
  .localSet 158,
  .localGet 158,
  .localSet 159,
  .localGet 103,
  .localSet 160,
  .localGet 104,
  .localSet 161,
  .localGet 105,
  .localSet 162,
  .localGet 106,
  .localSet 163,
  .localGet 107,
  .localSet 164,
  .localGet 108,
  .localSet 165,
  .localGet 109,
  .localSet 166,
  .localGet 110,
  .localSet 167,
  .localGet 111,
  .localSet 168,
  .localGet 112,
  .localSet 169,
  .localGet 113,
  .localSet 170,
  .localGet 114,
  .localSet 171,
  .localGet 115,
  .localSet 172,
  .localGet 116,
  .localSet 173,
  .localGet 117,
  .localSet 174,
  .localGet 118,
  .localSet 175,
  .localGet 156,
  .localGet 157,
  .localGet 159,
  .localGet 160,
  .localGet 161,
  .localGet 162,
  .localGet 163,
  .localGet 164,
  .localGet 165,
  .localGet 166,
  .localGet 167,
  .localGet 168,
  .localGet 169,
  .localGet 170,
  .localGet 171,
  .localGet 172,
  .localGet 173,
  .localGet 174,
  .localGet 175,
  .call 29
  ] ++ tail17

noncomputable def tail15 : Wasm.Program :=
  [
  .localSet 151,
  .localSet 150,
  .localSet 149,
  .localSet 148,
  .localGet 148,
  .localSet 152,
  .localGet 149,
  .localSet 153,
  .localGet 150,
  .localSet 154,
  .localGet 151,
  .localSet 155,
  .localGet 0,
  .localSet 156,
  .localGet 1,
  .localSet 157,
  .call 30
  ] ++ tail16

noncomputable def tail14 : Wasm.Program :=
  [
  .localSet 143,
  .localSet 142,
  .localSet 141,
  .localSet 140,
  .localGet 140,
  .localSet 144,
  .localGet 141,
  .localSet 145,
  .localGet 142,
  .localSet 146,
  .localGet 143,
  .localSet 147,
  .localGet 119,
  .localGet 120,
  .localGet 122,
  .localGet 144,
  .localGet 145,
  .localGet 146,
  .localGet 147,
  .call 26
  ] ++ tail15

noncomputable def tail13 : Wasm.Program :=
  [
  .localSet 121,
  .localGet 121,
  .localSet 122,
  .localGet 103,
  .localSet 123,
  .localGet 104,
  .localSet 124,
  .localGet 105,
  .localSet 125,
  .localGet 106,
  .localSet 126,
  .localGet 107,
  .localSet 127,
  .localGet 108,
  .localSet 128,
  .localGet 109,
  .localSet 129,
  .localGet 110,
  .localSet 130,
  .localGet 111,
  .localSet 131,
  .localGet 112,
  .localSet 132,
  .localGet 113,
  .localSet 133,
  .localGet 114,
  .localSet 134,
  .localGet 115,
  .localSet 135,
  .localGet 116,
  .localSet 136,
  .localGet 117,
  .localSet 137,
  .localGet 118,
  .localSet 138,
  .localGet 6,
  .localSet 139,
  .localGet 123,
  .localGet 124,
  .localGet 125,
  .localGet 126,
  .localGet 127,
  .localGet 128,
  .localGet 129,
  .localGet 130,
  .localGet 131,
  .localGet 132,
  .localGet 133,
  .localGet 134,
  .localGet 135,
  .localGet 136,
  .localGet 137,
  .localGet 138,
  .localGet 139,
  .call 28
  ] ++ tail14

noncomputable def tail12 : Wasm.Program :=
  [
  .localSet 102,
  .localSet 101,
  .localSet 100,
  .localSet 99,
  .localGet 99,
  .localSet 115,
  .localGet 100,
  .localSet 116,
  .localGet 101,
  .localSet 117,
  .localGet 102,
  .localSet 118,
  .localGet 0,
  .localSet 119,
  .localGet 1,
  .localSet 120,
  .call 27
  ] ++ tail13

noncomputable def tail11 : Wasm.Program :=
  [
  .localSet 93,
  .localGet 93,
  .localSet 94,
  .localGet 51,
  .localSet 95,
  .localGet 52,
  .localSet 96,
  .localGet 53,
  .localSet 97,
  .localGet 54,
  .localSet 98,
  .localGet 91,
  .localGet 92,
  .localGet 94,
  .localGet 95,
  .localGet 96,
  .localGet 97,
  .localGet 98,
  .call 17
  ] ++ tail12

noncomputable def tail10 : Wasm.Program :=
  [
  .localSet 90,
  .localSet 89,
  .localSet 88,
  .localSet 87,
  .localGet 87,
  .localSet 111,
  .localGet 88,
  .localSet 112,
  .localGet 89,
  .localSet 113,
  .localGet 90,
  .localSet 114,
  .localGet 0,
  .localSet 91,
  .localGet 1,
  .localSet 92,
  .call 18
  ] ++ tail11

noncomputable def tail9 : Wasm.Program :=
  [
  .localSet 81,
  .localGet 81,
  .localSet 82,
  .localGet 47,
  .localSet 83,
  .localGet 48,
  .localSet 84,
  .localGet 49,
  .localSet 85,
  .localGet 50,
  .localSet 86,
  .localGet 79,
  .localGet 80,
  .localGet 82,
  .localGet 83,
  .localGet 84,
  .localGet 85,
  .localGet 86,
  .call 17
  ] ++ tail10

noncomputable def tail8 : Wasm.Program :=
  [
  .localSet 78,
  .localSet 77,
  .localSet 76,
  .localSet 75,
  .localGet 75,
  .localSet 107,
  .localGet 76,
  .localSet 108,
  .localGet 77,
  .localSet 109,
  .localGet 78,
  .localSet 110,
  .localGet 0,
  .localSet 79,
  .localGet 1,
  .localSet 80,
  .call 18
  ] ++ tail9

noncomputable def tail7 : Wasm.Program :=
  [
  .localSet 69,
  .localGet 69,
  .localSet 70,
  .localGet 43,
  .localSet 71,
  .localGet 44,
  .localSet 72,
  .localGet 45,
  .localSet 73,
  .localGet 46,
  .localSet 74,
  .localGet 67,
  .localGet 68,
  .localGet 70,
  .localGet 71,
  .localGet 72,
  .localGet 73,
  .localGet 74,
  .call 17
  ] ++ tail8

noncomputable def tail6 : Wasm.Program :=
  [
  .localSet 66,
  .localSet 65,
  .localSet 64,
  .localSet 63,
  .localGet 63,
  .localSet 103,
  .localGet 64,
  .localSet 104,
  .localGet 65,
  .localSet 105,
  .localGet 66,
  .localSet 106,
  .localGet 0,
  .localSet 67,
  .localGet 1,
  .localSet 68,
  .call 18
  ] ++ tail7

noncomputable def tail5 : Wasm.Program :=
  [
  .localSet 57,
  .localGet 57,
  .localSet 58,
  .localGet 39,
  .localSet 59,
  .localGet 40,
  .localSet 60,
  .localGet 41,
  .localSet 61,
  .localGet 42,
  .localSet 62,
  .localGet 55,
  .localGet 56,
  .localGet 58,
  .localGet 59,
  .localGet 60,
  .localGet 61,
  .localGet 62,
  .call 17
  ] ++ tail6

noncomputable def tail4 : Wasm.Program :=
  [
  .localSet 38,
  .localSet 37,
  .localSet 36,
  .localSet 35,
  .localGet 35,
  .localSet 51,
  .localGet 36,
  .localSet 52,
  .localGet 37,
  .localSet 53,
  .localGet 38,
  .localSet 54,
  .localGet 0,
  .localSet 55,
  .localGet 1,
  .localSet 56,
  .call 18
  ] ++ tail5

noncomputable def tail3 : Wasm.Program :=
  [
  .localSet 30,
  .localSet 29,
  .localSet 28,
  .localSet 27,
  .localGet 27,
  .localSet 47,
  .localGet 28,
  .localSet 48,
  .localGet 29,
  .localSet 49,
  .localGet 30,
  .localSet 50,
  .localGet 0,
  .localSet 31,
  .localGet 1,
  .localSet 32,
  .localGet 5,
  .localSet 33,
  .constI64 3,
  .localSet 34,
  .localGet 31,
  .localGet 32,
  .localGet 33,
  .localGet 34,
  .call 8
  ] ++ tail4

noncomputable def tail2 : Wasm.Program :=
  [
  .localSet 22,
  .localSet 21,
  .localSet 20,
  .localSet 19,
  .localGet 19,
  .localSet 43,
  .localGet 20,
  .localSet 44,
  .localGet 21,
  .localSet 45,
  .localGet 22,
  .localSet 46,
  .localGet 0,
  .localSet 23,
  .localGet 1,
  .localSet 24,
  .localGet 4,
  .localSet 25,
  .constI64 2,
  .localSet 26,
  .localGet 23,
  .localGet 24,
  .localGet 25,
  .localGet 26,
  .call 8
  ] ++ tail3

noncomputable def tail1 : Wasm.Program :=
  [
  .localSet 14,
  .localSet 13,
  .localSet 12,
  .localSet 11,
  .localGet 11,
  .localSet 39,
  .localGet 12,
  .localSet 40,
  .localGet 13,
  .localSet 41,
  .localGet 14,
  .localSet 42,
  .localGet 0,
  .localSet 15,
  .localGet 1,
  .localSet 16,
  .localGet 3,
  .localSet 17,
  .constI64 1,
  .localSet 18,
  .localGet 15,
  .localGet 16,
  .localGet 17,
  .localGet 18,
  .call 8
  ] ++ tail2

noncomputable def tail0 : Wasm.Program :=
  [
  .localGet 0,
  .localSet 7,
  .localGet 1,
  .localSet 8,
  .localGet 2,
  .localSet 9,
  .constI64 0,
  .localSet 10,
  .localGet 7,
  .localGet 8,
  .localGet 9,
  .localGet 10,
  .call 8
  ] ++ tail1

theorem program_eq : func71 = tail0 := by rfl

end Project.TinyGpt2Infer.HiddenCode
