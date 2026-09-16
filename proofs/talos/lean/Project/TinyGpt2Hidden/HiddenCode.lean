import Project.TinyGpt2Hidden.Program

namespace Project.TinyGpt2Hidden.HiddenCode

set_option maxRecDepth 8192

noncomputable def tail90 : Wasm.Program :=
  [
  .localSet 780,
  .localSet 779,
  .localSet 778,
  .localSet 777,
  .localGet 777,
  .localSet 781,
  .localGet 778,
  .localSet 782,
  .localGet 779,
  .localSet 783,
  .localGet 780,
  .localSet 784,
  .localGet 781,
  .localGet 782,
  .localGet 783,
  .localGet 784
  ]

noncomputable def tail89 : Wasm.Program :=
  [
  .localSet 771,
  .localGet 771,
  .localSet 772,
  .localGet 765,
  .localSet 773,
  .localGet 766,
  .localSet 774,
  .localGet 767,
  .localSet 775,
  .localGet 768,
  .localSet 776,
  .localGet 769,
  .localGet 770,
  .localGet 772,
  .localGet 773,
  .localGet 774,
  .localGet 775,
  .localGet 776,
  .call 17
  ] ++ tail90

noncomputable def tail88 : Wasm.Program :=
  [
  .localSet 764,
  .localSet 763,
  .localSet 762,
  .localSet 761,
  .localGet 764,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 768,
  .constI64 0,
  .localSet 769,
  .localGet 0,
  .localSet 770,
  .call 70
  ] ++ tail89

noncomputable def tail87 : Wasm.Program :=
  [
  .localSet 750,
  .localSet 749,
  .localSet 748,
  .localSet 747,
  .localGet 749,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 767,
  .localGet 424,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 751,
  .localGet 0,
  .localSet 752,
  .localGet 701,
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
  .localGet 751,
  .localGet 752,
  .localGet 753,
  .localGet 754,
  .localGet 755,
  .localGet 756,
  .localGet 757,
  .localGet 758,
  .localGet 759,
  .localGet 760,
  .call 69
  ] ++ tail88

noncomputable def tail86 : Wasm.Program :=
  [
  .localSet 736,
  .localSet 735,
  .localSet 734,
  .localSet 733,
  .localGet 734,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 766,
  .localGet 423,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 737,
  .localGet 0,
  .localSet 738,
  .localGet 701,
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
  .localGet 737,
  .localGet 738,
  .localGet 739,
  .localGet 740,
  .localGet 741,
  .localGet 742,
  .localGet 743,
  .localGet 744,
  .localGet 745,
  .localGet 746,
  .call 69
  ] ++ tail87

noncomputable def tail85 : Wasm.Program :=
  [
  .localSet 722,
  .localSet 721,
  .localSet 720,
  .localSet 719,
  .localGet 719,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 765,
  .localGet 422,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 723,
  .localGet 0,
  .localSet 724,
  .localGet 701,
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
  .localGet 723,
  .localGet 724,
  .localGet 725,
  .localGet 726,
  .localGet 727,
  .localGet 728,
  .localGet 729,
  .localGet 730,
  .localGet 731,
  .localGet 732,
  .call 69
  ] ++ tail86

noncomputable def tail84 : Wasm.Program :=
  [
  .localSet 700,
  .localSet 699,
  .localSet 698,
  .localSet 697,
  .localGet 697,
  .localSet 705,
  .localGet 698,
  .localSet 706,
  .localGet 699,
  .localSet 707,
  .localGet 700,
  .localSet 708,
  .localGet 421,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 709,
  .localGet 0,
  .localSet 710,
  .localGet 701,
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
  .localGet 710,
  .localGet 711,
  .localGet 712,
  .localGet 713,
  .localGet 714,
  .localGet 715,
  .localGet 716,
  .localGet 717,
  .localGet 718,
  .call 69
  ] ++ tail85

noncomputable def tail83 : Wasm.Program :=
  [
  .localSet 692,
  .localSet 691,
  .localSet 690,
  .localSet 689,
  .localGet 689,
  .localSet 701,
  .localGet 690,
  .localSet 702,
  .localGet 691,
  .localSet 703,
  .localGet 692,
  .localSet 704,
  .localGet 681,
  .localSet 693,
  .localGet 682,
  .localSet 694,
  .localGet 683,
  .localSet 695,
  .localGet 684,
  .localSet 696,
  .localGet 693,
  .localGet 694,
  .localGet 695,
  .localGet 696,
  .call 62
  ] ++ tail84

noncomputable def tail82 : Wasm.Program :=
  [
  .localSet 676,
  .localSet 675,
  .localSet 674,
  .localSet 673,
  .localGet 676,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 684,
  .localGet 677,
  .localSet 685,
  .localGet 678,
  .localSet 686,
  .localGet 679,
  .localSet 687,
  .localGet 680,
  .localSet 688,
  .localGet 685,
  .localGet 686,
  .localGet 687,
  .localGet 688,
  .call 62
  ] ++ tail83

noncomputable def tail81 : Wasm.Program :=
  [
  .localSet 669,
  .localSet 668,
  .localSet 667,
  .localSet 666,
  .localGet 668,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 683,
  .localGet 616,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 670,
  .localGet 0,
  .localSet 671,
  .constI64 1140,
  .localSet 785,
  .constI64 4,
  .localSet 786,
  .localGet 785,
  .localGet 786,
  .addI64,
  .localTee 787,
  .localGet 785,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 787
  ] [] [.i64],
  .localSet 672,
  .localGet 670,
  .localGet 671,
  .localGet 672,
  .call 5
  ] ++ tail82

noncomputable def tail80 : Wasm.Program :=
  [
  .localSet 662,
  .localSet 661,
  .localSet 660,
  .localSet 659,
  .localGet 660,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 682,
  .localGet 615,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 663,
  .localGet 0,
  .localSet 664,
  .constI64 1140,
  .localSet 785,
  .constI64 4,
  .localSet 786,
  .localGet 785,
  .localGet 786,
  .addI64,
  .localTee 787,
  .localGet 785,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 787
  ] [] [.i64],
  .localSet 665,
  .localGet 663,
  .localGet 664,
  .localGet 665,
  .call 5
  ] ++ tail81

noncomputable def tail79 : Wasm.Program :=
  [
  .localSet 655,
  .localSet 654,
  .localSet 653,
  .localSet 652,
  .localGet 652,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 681,
  .localGet 614,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 656,
  .localGet 0,
  .localSet 657,
  .constI64 1140,
  .localSet 785,
  .constI64 4,
  .localSet 786,
  .localGet 785,
  .localGet 786,
  .addI64,
  .localTee 787,
  .localGet 785,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 787
  ] [] [.i64],
  .localSet 658,
  .localGet 656,
  .localGet 657,
  .localGet 658,
  .call 5
  ] ++ tail80

noncomputable def tail78 : Wasm.Program :=
  [
  .localSet 648,
  .localSet 647,
  .localSet 646,
  .localSet 645,
  .localGet 648,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 680,
  .localGet 613,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 649,
  .localGet 0,
  .localSet 650,
  .constI64 1140,
  .localSet 785,
  .constI64 4,
  .localSet 786,
  .localGet 785,
  .localGet 786,
  .addI64,
  .localTee 787,
  .localGet 785,
  .ltUI64,
  .iff 0 1 [
   .unreachable
  ] [
   .localGet 787
  ] [] [.i64],
  .localSet 651,
  .localGet 649,
  .localGet 650,
  .localGet 651,
  .call 5
  ] ++ tail79

noncomputable def tail77 : Wasm.Program :=
  [
  .localSet 643,
  .localGet 643,
  .localSet 644,
  .localGet 641,
  .localGet 642,
  .localGet 644,
  .call 5
  ] ++ tail78

noncomputable def tail76 : Wasm.Program :=
  [
  .localSet 640,
  .localSet 639,
  .localSet 638,
  .localSet 637,
  .localGet 639,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 679,
  .localGet 520,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 641,
  .localGet 0,
  .localSet 642,
  .call 52
  ] ++ tail77

noncomputable def tail75 : Wasm.Program :=
  [
  .localSet 635,
  .localGet 635,
  .localSet 636,
  .localGet 633,
  .localGet 634,
  .localGet 636,
  .call 5
  ] ++ tail76

noncomputable def tail74 : Wasm.Program :=
  [
  .localSet 632,
  .localSet 631,
  .localSet 630,
  .localSet 629,
  .localGet 630,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 678,
  .localGet 519,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 633,
  .localGet 0,
  .localSet 634,
  .call 52
  ] ++ tail75

noncomputable def tail73 : Wasm.Program :=
  [
  .localSet 627,
  .localGet 627,
  .localSet 628,
  .localGet 625,
  .localGet 626,
  .localGet 628,
  .call 5
  ] ++ tail74

noncomputable def tail72 : Wasm.Program :=
  [
  .localSet 624,
  .localSet 623,
  .localSet 622,
  .localSet 621,
  .localGet 621,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 677,
  .localGet 518,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 625,
  .localGet 0,
  .localSet 626,
  .call 52
  ] ++ tail73

noncomputable def tail71 : Wasm.Program :=
  [
  .localSet 619,
  .localGet 619,
  .localSet 620,
  .localGet 617,
  .localGet 618,
  .localGet 620,
  .call 5
  ] ++ tail72

noncomputable def tail70 : Wasm.Program :=
  [
  .localSet 612,
  .localGet 612,
  .localSet 616,
  .localGet 517,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 617,
  .localGet 0,
  .localSet 618,
  .call 52
  ] ++ tail71

noncomputable def tail69 : Wasm.Program :=
  [
  .localSet 607,
  .localSet 606,
  .localSet 605,
  .localSet 604,
  .localGet 604,
  .localSet 608,
  .localGet 605,
  .localSet 609,
  .localGet 606,
  .localSet 610,
  .localGet 607,
  .localSet 611,
  .localGet 590,
  .localGet 591,
  .localGet 593,
  .localGet 594,
  .localGet 595,
  .localGet 608,
  .localGet 609,
  .localGet 610,
  .localGet 611,
  .call 25
  ] ++ tail70

noncomputable def tail68 : Wasm.Program :=
  [
  .localSet 598,
  .localGet 598,
  .localSet 599,
  .localGet 421,
  .localSet 600,
  .localGet 422,
  .localSet 601,
  .localGet 423,
  .localSet 602,
  .localGet 424,
  .localSet 603,
  .localGet 596,
  .localGet 597,
  .localGet 599,
  .localGet 600,
  .localGet 601,
  .localGet 602,
  .localGet 603,
  .call 17
  ] ++ tail69

noncomputable def tail67 : Wasm.Program :=
  [
  .localSet 592,
  .localGet 592,
  .localSet 593,
  .constI64 8,
  .localSet 594,
  .constI64 7,
  .localSet 595,
  .constI64 0,
  .localSet 596,
  .localGet 0,
  .localSet 597,
  .call 54
  ] ++ tail68

noncomputable def tail66 : Wasm.Program :=
  [
  .localSet 589,
  .localGet 589,
  .localSet 615,
  .constI64 0,
  .localSet 590,
  .localGet 0,
  .localSet 591,
  .call 51
  ] ++ tail67

noncomputable def tail65 : Wasm.Program :=
  [
  .localSet 584,
  .localSet 583,
  .localSet 582,
  .localSet 581,
  .localGet 581,
  .localSet 585,
  .localGet 582,
  .localSet 586,
  .localGet 583,
  .localSet 587,
  .localGet 584,
  .localSet 588,
  .localGet 567,
  .localGet 568,
  .localGet 570,
  .localGet 571,
  .localGet 572,
  .localGet 585,
  .localGet 586,
  .localGet 587,
  .localGet 588,
  .call 25
  ] ++ tail66

noncomputable def tail64 : Wasm.Program :=
  [
  .localSet 575,
  .localGet 575,
  .localSet 576,
  .localGet 421,
  .localSet 577,
  .localGet 422,
  .localSet 578,
  .localGet 423,
  .localSet 579,
  .localGet 424,
  .localSet 580,
  .localGet 573,
  .localGet 574,
  .localGet 576,
  .localGet 577,
  .localGet 578,
  .localGet 579,
  .localGet 580,
  .call 17
  ] ++ tail65

noncomputable def tail63 : Wasm.Program :=
  [
  .localSet 569,
  .localGet 569,
  .localSet 570,
  .constI64 8,
  .localSet 571,
  .constI64 6,
  .localSet 572,
  .constI64 0,
  .localSet 573,
  .localGet 0,
  .localSet 574,
  .call 54
  ] ++ tail64

noncomputable def tail62 : Wasm.Program :=
  [
  .localSet 566,
  .localGet 566,
  .localSet 614,
  .constI64 0,
  .localSet 567,
  .localGet 0,
  .localSet 568,
  .call 51
  ] ++ tail63

noncomputable def tail61 : Wasm.Program :=
  [
  .localSet 561,
  .localSet 560,
  .localSet 559,
  .localSet 558,
  .localGet 558,
  .localSet 562,
  .localGet 559,
  .localSet 563,
  .localGet 560,
  .localSet 564,
  .localGet 561,
  .localSet 565,
  .localGet 544,
  .localGet 545,
  .localGet 547,
  .localGet 548,
  .localGet 549,
  .localGet 562,
  .localGet 563,
  .localGet 564,
  .localGet 565,
  .call 25
  ] ++ tail62

noncomputable def tail60 : Wasm.Program :=
  [
  .localSet 552,
  .localGet 552,
  .localSet 553,
  .localGet 421,
  .localSet 554,
  .localGet 422,
  .localSet 555,
  .localGet 423,
  .localSet 556,
  .localGet 424,
  .localSet 557,
  .localGet 550,
  .localGet 551,
  .localGet 553,
  .localGet 554,
  .localGet 555,
  .localGet 556,
  .localGet 557,
  .call 17
  ] ++ tail61

noncomputable def tail59 : Wasm.Program :=
  [
  .localSet 546,
  .localGet 546,
  .localSet 547,
  .constI64 8,
  .localSet 548,
  .constI64 5,
  .localSet 549,
  .constI64 0,
  .localSet 550,
  .localGet 0,
  .localSet 551,
  .call 54
  ] ++ tail60

noncomputable def tail58 : Wasm.Program :=
  [
  .localSet 543,
  .localGet 543,
  .localSet 613,
  .constI64 0,
  .localSet 544,
  .localGet 0,
  .localSet 545,
  .call 51
  ] ++ tail59

noncomputable def tail57 : Wasm.Program :=
  [
  .localSet 538,
  .localSet 537,
  .localSet 536,
  .localSet 535,
  .localGet 535,
  .localSet 539,
  .localGet 536,
  .localSet 540,
  .localGet 537,
  .localSet 541,
  .localGet 538,
  .localSet 542,
  .localGet 521,
  .localGet 522,
  .localGet 524,
  .localGet 525,
  .localGet 526,
  .localGet 539,
  .localGet 540,
  .localGet 541,
  .localGet 542,
  .call 25
  ] ++ tail58

noncomputable def tail56 : Wasm.Program :=
  [
  .localSet 529,
  .localGet 529,
  .localSet 530,
  .localGet 421,
  .localSet 531,
  .localGet 422,
  .localSet 532,
  .localGet 423,
  .localSet 533,
  .localGet 424,
  .localSet 534,
  .localGet 527,
  .localGet 528,
  .localGet 530,
  .localGet 531,
  .localGet 532,
  .localGet 533,
  .localGet 534,
  .call 17
  ] ++ tail57

noncomputable def tail55 : Wasm.Program :=
  [
  .localSet 523,
  .localGet 523,
  .localSet 524,
  .constI64 8,
  .localSet 525,
  .constI64 4,
  .localSet 526,
  .constI64 0,
  .localSet 527,
  .localGet 0,
  .localSet 528,
  .call 54
  ] ++ tail56

noncomputable def tail54 : Wasm.Program :=
  [
  .localSet 516,
  .localGet 516,
  .localSet 520,
  .constI64 0,
  .localSet 521,
  .localGet 0,
  .localSet 522,
  .call 51
  ] ++ tail55

noncomputable def tail53 : Wasm.Program :=
  [
  .localSet 511,
  .localSet 510,
  .localSet 509,
  .localSet 508,
  .localGet 508,
  .localSet 512,
  .localGet 509,
  .localSet 513,
  .localGet 510,
  .localSet 514,
  .localGet 511,
  .localSet 515,
  .localGet 494,
  .localGet 495,
  .localGet 497,
  .localGet 498,
  .localGet 499,
  .localGet 512,
  .localGet 513,
  .localGet 514,
  .localGet 515,
  .call 25
  ] ++ tail54

noncomputable def tail52 : Wasm.Program :=
  [
  .localSet 502,
  .localGet 502,
  .localSet 503,
  .localGet 421,
  .localSet 504,
  .localGet 422,
  .localSet 505,
  .localGet 423,
  .localSet 506,
  .localGet 424,
  .localSet 507,
  .localGet 500,
  .localGet 501,
  .localGet 503,
  .localGet 504,
  .localGet 505,
  .localGet 506,
  .localGet 507,
  .call 17
  ] ++ tail53

noncomputable def tail51 : Wasm.Program :=
  [
  .localSet 496,
  .localGet 496,
  .localSet 497,
  .constI64 8,
  .localSet 498,
  .constI64 3,
  .localSet 499,
  .constI64 0,
  .localSet 500,
  .localGet 0,
  .localSet 501,
  .call 54
  ] ++ tail52

noncomputable def tail50 : Wasm.Program :=
  [
  .localSet 493,
  .localGet 493,
  .localSet 519,
  .constI64 0,
  .localSet 494,
  .localGet 0,
  .localSet 495,
  .call 51
  ] ++ tail51

noncomputable def tail49 : Wasm.Program :=
  [
  .localSet 488,
  .localSet 487,
  .localSet 486,
  .localSet 485,
  .localGet 485,
  .localSet 489,
  .localGet 486,
  .localSet 490,
  .localGet 487,
  .localSet 491,
  .localGet 488,
  .localSet 492,
  .localGet 471,
  .localGet 472,
  .localGet 474,
  .localGet 475,
  .localGet 476,
  .localGet 489,
  .localGet 490,
  .localGet 491,
  .localGet 492,
  .call 25
  ] ++ tail50

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
  .call 54
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
  .call 51
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
  .call 54
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
  .call 51
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
  .call 54
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
  .call 51
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

noncomputable def tail34 : Wasm.Program :=
  [
  .localSet 375,
  .localSet 374,
  .localSet 373,
  .localSet 372,
  .localGet 375,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 376,
  .localGet 0,
  .localSet 377,
  .call 50
  ] ++ tail35

noncomputable def tail33 : Wasm.Program :=
  [
  .localSet 366,
  .localGet 366,
  .localSet 367,
  .localGet 300,
  .localSet 368,
  .localGet 301,
  .localSet 369,
  .localGet 302,
  .localSet 370,
  .localGet 303,
  .localSet 371,
  .localGet 364,
  .localGet 365,
  .localGet 367,
  .localGet 368,
  .localGet 369,
  .localGet 370,
  .localGet 371,
  .call 26
  ] ++ tail34

noncomputable def tail32 : Wasm.Program :=
  [
  .localSet 363,
  .localSet 362,
  .localSet 361,
  .localSet 360,
  .localGet 362,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 386,
  .constI64 0,
  .localSet 364,
  .localGet 0,
  .localSet 365,
  .call 49
  ] ++ tail33

noncomputable def tail31 : Wasm.Program :=
  [
  .localSet 358,
  .localGet 358,
  .localSet 359,
  .localGet 356,
  .localGet 357,
  .localGet 359,
  .call 5
  ] ++ tail32

noncomputable def tail30 : Wasm.Program :=
  [
  .localSet 355,
  .localSet 354,
  .localSet 353,
  .localSet 352,
  .localGet 354,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 356,
  .localGet 0,
  .localSet 357,
  .call 50
  ] ++ tail31

noncomputable def tail29 : Wasm.Program :=
  [
  .localSet 346,
  .localGet 346,
  .localSet 347,
  .localGet 300,
  .localSet 348,
  .localGet 301,
  .localSet 349,
  .localGet 302,
  .localSet 350,
  .localGet 303,
  .localSet 351,
  .localGet 344,
  .localGet 345,
  .localGet 347,
  .localGet 348,
  .localGet 349,
  .localGet 350,
  .localGet 351,
  .call 26
  ] ++ tail30

noncomputable def tail28 : Wasm.Program :=
  [
  .localSet 343,
  .localSet 342,
  .localSet 341,
  .localSet 340,
  .localGet 341,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 385,
  .constI64 0,
  .localSet 344,
  .localGet 0,
  .localSet 345,
  .call 49
  ] ++ tail29

noncomputable def tail27 : Wasm.Program :=
  [
  .localSet 338,
  .localGet 338,
  .localSet 339,
  .localGet 336,
  .localGet 337,
  .localGet 339,
  .call 5
  ] ++ tail28

noncomputable def tail26 : Wasm.Program :=
  [
  .localSet 335,
  .localSet 334,
  .localSet 333,
  .localSet 332,
  .localGet 333,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 336,
  .localGet 0,
  .localSet 337,
  .call 50
  ] ++ tail27

noncomputable def tail25 : Wasm.Program :=
  [
  .localSet 326,
  .localGet 326,
  .localSet 327,
  .localGet 300,
  .localSet 328,
  .localGet 301,
  .localSet 329,
  .localGet 302,
  .localSet 330,
  .localGet 303,
  .localSet 331,
  .localGet 324,
  .localGet 325,
  .localGet 327,
  .localGet 328,
  .localGet 329,
  .localGet 330,
  .localGet 331,
  .call 26
  ] ++ tail26

noncomputable def tail24 : Wasm.Program :=
  [
  .localSet 323,
  .localSet 322,
  .localSet 321,
  .localSet 320,
  .localGet 320,
  .f64ReinterpretI64,
  .f64Add,
  .i64ReinterpretF64,
  .localSet 384,
  .constI64 0,
  .localSet 324,
  .localGet 0,
  .localSet 325,
  .call 49
  ] ++ tail25

noncomputable def tail23 : Wasm.Program :=
  [
  .localSet 318,
  .localGet 318,
  .localSet 319,
  .localGet 316,
  .localGet 317,
  .localGet 319,
  .call 5
  ] ++ tail24

noncomputable def tail22 : Wasm.Program :=
  [
  .localSet 315,
  .localSet 314,
  .localSet 313,
  .localSet 312,
  .localGet 312,
  .f64ReinterpretI64,
  .constI64 0,
  .localSet 316,
  .localGet 0,
  .localSet 317,
  .call 50
  ] ++ tail23

noncomputable def tail21 : Wasm.Program :=
  [
  .localSet 306,
  .localGet 306,
  .localSet 307,
  .localGet 300,
  .localSet 308,
  .localGet 301,
  .localSet 309,
  .localGet 302,
  .localSet 310,
  .localGet 303,
  .localSet 311,
  .localGet 304,
  .localGet 305,
  .localGet 307,
  .localGet 308,
  .localGet 309,
  .localGet 310,
  .localGet 311,
  .call 26
  ] ++ tail22

noncomputable def tail20 : Wasm.Program :=
  [
  .localSet 299,
  .localSet 298,
  .localSet 297,
  .localSet 296,
  .localGet 296,
  .localSet 300,
  .localGet 297,
  .localSet 301,
  .localGet 298,
  .localSet 302,
  .localGet 299,
  .localSet 303,
  .constI64 0,
  .localSet 304,
  .localGet 0,
  .localSet 305,
  .call 49
  ] ++ tail21

noncomputable def tail19 : Wasm.Program :=
  [
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
  .localSet 227,
  .localGet 227,
  .localSet 243,
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
  .localGet 5,
  .constI64 1,
  .addI64,
  .localSet 259,
  .localGet 151,
  .localSet 260,
  .localGet 152,
  .localSet 261,
  .localGet 153,
  .localSet 262,
  .localGet 154,
  .localSet 263,
  .localGet 191,
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
  .localGet 243,
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
  .call 48
  ] ++ tail20

noncomputable def tail18 : Wasm.Program :=
  [
  .localSet 209,
  .localGet 209,
  .localSet 210,
  .localGet 102,
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
  .localGet 207,
  .localGet 208,
  .localGet 210,
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
  .call 29
  ] ++ tail19

noncomputable def tail17 : Wasm.Program :=
  [
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
  .localSet 175,
  .localGet 175,
  .localSet 191,
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
  .constI64 0,
  .localSet 207,
  .localGet 0,
  .localSet 208,
  .call 31
  ] ++ tail18

noncomputable def tail16 : Wasm.Program :=
  [
  .localSet 157,
  .localGet 157,
  .localSet 158,
  .localGet 102,
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
  .localGet 155,
  .localGet 156,
  .localGet 158,
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
  .call 29
  ] ++ tail17

noncomputable def tail15 : Wasm.Program :=
  [
  .localSet 150,
  .localSet 149,
  .localSet 148,
  .localSet 147,
  .localGet 147,
  .localSet 151,
  .localGet 148,
  .localSet 152,
  .localGet 149,
  .localSet 153,
  .localGet 150,
  .localSet 154,
  .constI64 0,
  .localSet 155,
  .localGet 0,
  .localSet 156,
  .call 30
  ] ++ tail16

noncomputable def tail14 : Wasm.Program :=
  [
  .localSet 142,
  .localSet 141,
  .localSet 140,
  .localSet 139,
  .localGet 139,
  .localSet 143,
  .localGet 140,
  .localSet 144,
  .localGet 141,
  .localSet 145,
  .localGet 142,
  .localSet 146,
  .localGet 118,
  .localGet 119,
  .localGet 121,
  .localGet 143,
  .localGet 144,
  .localGet 145,
  .localGet 146,
  .call 26
  ] ++ tail15

noncomputable def tail13 : Wasm.Program :=
  [
  .localSet 120,
  .localGet 120,
  .localSet 121,
  .localGet 102,
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
  .localGet 5,
  .localSet 138,
  .localGet 122,
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
  .call 28
  ] ++ tail14

noncomputable def tail12 : Wasm.Program :=
  [
  .localSet 101,
  .localSet 100,
  .localSet 99,
  .localSet 98,
  .localGet 98,
  .localSet 114,
  .localGet 99,
  .localSet 115,
  .localGet 100,
  .localSet 116,
  .localGet 101,
  .localSet 117,
  .constI64 0,
  .localSet 118,
  .localGet 0,
  .localSet 119,
  .call 27
  ] ++ tail13

noncomputable def tail11 : Wasm.Program :=
  [
  .localSet 92,
  .localGet 92,
  .localSet 93,
  .localGet 50,
  .localSet 94,
  .localGet 51,
  .localSet 95,
  .localGet 52,
  .localSet 96,
  .localGet 53,
  .localSet 97,
  .localGet 90,
  .localGet 91,
  .localGet 93,
  .localGet 94,
  .localGet 95,
  .localGet 96,
  .localGet 97,
  .call 17
  ] ++ tail12

noncomputable def tail10 : Wasm.Program :=
  [
  .localSet 89,
  .localSet 88,
  .localSet 87,
  .localSet 86,
  .localGet 86,
  .localSet 110,
  .localGet 87,
  .localSet 111,
  .localGet 88,
  .localSet 112,
  .localGet 89,
  .localSet 113,
  .constI64 0,
  .localSet 90,
  .localGet 0,
  .localSet 91,
  .call 18
  ] ++ tail11

noncomputable def tail9 : Wasm.Program :=
  [
  .localSet 80,
  .localGet 80,
  .localSet 81,
  .localGet 46,
  .localSet 82,
  .localGet 47,
  .localSet 83,
  .localGet 48,
  .localSet 84,
  .localGet 49,
  .localSet 85,
  .localGet 78,
  .localGet 79,
  .localGet 81,
  .localGet 82,
  .localGet 83,
  .localGet 84,
  .localGet 85,
  .call 17
  ] ++ tail10

noncomputable def tail8 : Wasm.Program :=
  [
  .localSet 77,
  .localSet 76,
  .localSet 75,
  .localSet 74,
  .localGet 74,
  .localSet 106,
  .localGet 75,
  .localSet 107,
  .localGet 76,
  .localSet 108,
  .localGet 77,
  .localSet 109,
  .constI64 0,
  .localSet 78,
  .localGet 0,
  .localSet 79,
  .call 18
  ] ++ tail9

noncomputable def tail7 : Wasm.Program :=
  [
  .localSet 68,
  .localGet 68,
  .localSet 69,
  .localGet 42,
  .localSet 70,
  .localGet 43,
  .localSet 71,
  .localGet 44,
  .localSet 72,
  .localGet 45,
  .localSet 73,
  .localGet 66,
  .localGet 67,
  .localGet 69,
  .localGet 70,
  .localGet 71,
  .localGet 72,
  .localGet 73,
  .call 17
  ] ++ tail8

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

theorem program_eq : func71 = tail0 := by rfl

end Project.TinyGpt2Hidden.HiddenCode
