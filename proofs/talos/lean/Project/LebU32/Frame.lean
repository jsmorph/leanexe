import Project.LebU32.Defs
import Project.WpScaffold

/-!
# Folded frame for the LEB128 fuel loop

The LEB128 iteration uses thirty-seven scalar slots.  Keeping those slots behind
one named frame prevents instruction stepping from repeatedly reducing literal
parameter and local arrays.  The generated `frame_step` lemmas expose only the
slot read or update required by each instruction.
-/

namespace Project.LebU32.Spec

open Wasm

def lFrameFlat (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 : UInt64) : Locals :=
  { params := [.i64 l0, .i64 l1, .i64 l2, .i64 l3, .i64 l4],
    locals := [.i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18, .i64 l19, .i64 l20, .i64 l21, .i64 l22, .i64 l23, .i64 l24, .i64 l25, .i64 l26, .i64 l27, .i64 l28, .i64 l29, .i64 l30, .i64 l31, .i64 l32, .i64 l33, .i64 l34, .i64 l35, .i64 l36],
    values := [] }

theorem lFrame_eq_flat (l0 l1 l2 l3 l4 l5 l6 l7 l8 : UInt64)
    (e : Nat → UInt64) :
    lFrame l0 l1 l2 l3 l4 l5 l6 l7 l8 e =
      lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 (e 9) (e 10) (e 11)
        (e 12) (e 13) (e 14) (e 15) (e 16) (e 17) (e 18) (e 19) (e 20)
        (e 21) (e 22) (e 23) (e 24) (e 25) (e 26) (e 27) (e 28) (e 29)
        (e 30) (e 31) (e 32) (e 33) (e 34) (e 35) (e 36) := by
  rfl

theorem cFramePos_eq_flat (g0 v : UInt64) (k j : Nat)
    (e : Nat → UInt64) :
    cFramePos g0 v k j e =
      lFrameFlat (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
        (UInt64.ofNat k) 0 0 0 0 (v % 128 &&& 255) (bufPtr g0 k)
        (UInt64.ofNat k) (e 12) (e 13) (e 14) (e 15) (e 16) (e 17)
        (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
        (UInt64.ofNat k) (v % 128 &&& 255)
        (g0 + 56 * UInt64.ofNat k + 48) (UInt64.ofNat k + 1)
        (UInt64.ofNat j) 8 0 0 (g0 + 56 * UInt64.ofNat k + 48 + 8)
        ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1)
        (g0 + 56 * UInt64.ofNat k + 48) := by
  rfl

theorem cFrameNeg_eq_flat (g0 v : UInt64) (k j : Nat)
    (e : Nat → UInt64) :
    cFrameNeg g0 v k j e =
      lFrameFlat (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
        (UInt64.ofNat k) 0 0 0 0 (e 9) (e 10) (e 11) (e 12) (v / 128)
        (v % 128 + 128 &&& 255) (bufPtr g0 k) (UInt64.ofNat k) (e 17)
        (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
        (UInt64.ofNat k) (v % 128 + 128 &&& 255)
        (g0 + 56 * UInt64.ofNat k + 48) (UInt64.ofNat k + 1)
        (UInt64.ofNat j) 8 0 0 (g0 + 56 * UInt64.ofNat k + 48 + 8)
        ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1)
        (g0 + 56 * UInt64.ofNat k + 48) := by
  rfl

section lFrameFlatLemmas
variable (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 : UInt64)

@[frame_step] theorem lFrameFlat_get_0 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 0 = some (.i64 l0) := rfl
@[frame_step] theorem lFrameFlat_get_1 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 1 = some (.i64 l1) := rfl
@[frame_step] theorem lFrameFlat_get_2 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 2 = some (.i64 l2) := rfl
@[frame_step] theorem lFrameFlat_get_3 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 3 = some (.i64 l3) := rfl
@[frame_step] theorem lFrameFlat_get_4 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 4 = some (.i64 l4) := rfl
@[frame_step] theorem lFrameFlat_get_5 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 5 = some (.i64 l5) := rfl
@[frame_step] theorem lFrameFlat_get_6 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 6 = some (.i64 l6) := rfl
@[frame_step] theorem lFrameFlat_get_7 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 7 = some (.i64 l7) := rfl
@[frame_step] theorem lFrameFlat_get_8 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 8 = some (.i64 l8) := rfl
@[frame_step] theorem lFrameFlat_get_9 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 9 = some (.i64 l9) := rfl
@[frame_step] theorem lFrameFlat_get_10 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 10 = some (.i64 l10) := rfl
@[frame_step] theorem lFrameFlat_get_11 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 11 = some (.i64 l11) := rfl
@[frame_step] theorem lFrameFlat_get_12 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 12 = some (.i64 l12) := rfl
@[frame_step] theorem lFrameFlat_get_13 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 13 = some (.i64 l13) := rfl
@[frame_step] theorem lFrameFlat_get_14 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 14 = some (.i64 l14) := rfl
@[frame_step] theorem lFrameFlat_get_15 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 15 = some (.i64 l15) := rfl
@[frame_step] theorem lFrameFlat_get_16 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 16 = some (.i64 l16) := rfl
@[frame_step] theorem lFrameFlat_get_17 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 17 = some (.i64 l17) := rfl
@[frame_step] theorem lFrameFlat_get_18 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 18 = some (.i64 l18) := rfl
@[frame_step] theorem lFrameFlat_get_19 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 19 = some (.i64 l19) := rfl
@[frame_step] theorem lFrameFlat_get_20 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 20 = some (.i64 l20) := rfl
@[frame_step] theorem lFrameFlat_get_21 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 21 = some (.i64 l21) := rfl
@[frame_step] theorem lFrameFlat_get_22 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 22 = some (.i64 l22) := rfl
@[frame_step] theorem lFrameFlat_get_23 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 23 = some (.i64 l23) := rfl
@[frame_step] theorem lFrameFlat_get_24 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 24 = some (.i64 l24) := rfl
@[frame_step] theorem lFrameFlat_get_25 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 25 = some (.i64 l25) := rfl
@[frame_step] theorem lFrameFlat_get_26 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 26 = some (.i64 l26) := rfl
@[frame_step] theorem lFrameFlat_get_27 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 27 = some (.i64 l27) := rfl
@[frame_step] theorem lFrameFlat_get_28 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 28 = some (.i64 l28) := rfl
@[frame_step] theorem lFrameFlat_get_29 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 29 = some (.i64 l29) := rfl
@[frame_step] theorem lFrameFlat_get_30 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 30 = some (.i64 l30) := rfl
@[frame_step] theorem lFrameFlat_get_31 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 31 = some (.i64 l31) := rfl
@[frame_step] theorem lFrameFlat_get_32 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 32 = some (.i64 l32) := rfl
@[frame_step] theorem lFrameFlat_get_33 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 33 = some (.i64 l33) := rfl
@[frame_step] theorem lFrameFlat_get_34 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 34 = some (.i64 l34) := rfl
@[frame_step] theorem lFrameFlat_get_35 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 35 = some (.i64 l35) := rfl
@[frame_step] theorem lFrameFlat_get_36 :
    Wasm.Locals.get (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 36 = some (.i64 l36) := rfl

@[frame_step] theorem lFrameFlat_set_0 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 0 (.i64 w) = some (lFrameFlat w l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_1 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 1 (.i64 w) = some (lFrameFlat l0 w l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_2 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 2 (.i64 w) = some (lFrameFlat l0 l1 w l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_3 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 3 (.i64 w) = some (lFrameFlat l0 l1 l2 w l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_4 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 4 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 w l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_5 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 5 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 w l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_6 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 6 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 w l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_7 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 7 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 w l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_8 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 8 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 w l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_9 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 9 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 w l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_10 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 10 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 w l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_11 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 11 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 w l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_12 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 12 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 w l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_13 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 13 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 w l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_14 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 14 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 w l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_15 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 15 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 w l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_16 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 16 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 w l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_17 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 17 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 w l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_18 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 18 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 w l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_19 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 19 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 w l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_20 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 20 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 w l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_21 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 21 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 w l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_22 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 22 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 w l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_23 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 23 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 w l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_24 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 24 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 w l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_25 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 25 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 w l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_26 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 26 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 w l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_27 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 27 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 w l28 l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_28 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 28 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 w l29 l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_29 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 29 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 w l30 l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_30 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 30 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 w l31 l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_31 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 31 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 w l32 l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_32 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 32 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 w l33 l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_33 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 33 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 w l34 l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_34 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 34 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 w l35 l36) := rfl
@[frame_step] theorem lFrameFlat_set_35 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 35 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 w l36) := rfl
@[frame_step] theorem lFrameFlat_set_36 (w : UInt64) :
    Wasm.Locals.set? (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) 36 (.i64 w) = some (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 w) := rfl

@[frame_step] theorem lFrameFlat_params_length :
    (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params.length = 5 := rfl
@[frame_step] theorem lFrameFlat_locals_length :
    (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.length = 32 := rfl

@[frame_step] theorem lFrameFlat_setp_0 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params.set 0 (.i64 w),
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals,
        values := vs } : Wasm.Locals) =
      { lFrameFlat w l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setp_1 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params.set 1 (.i64 w),
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals,
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 w l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setp_2 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params.set 2 (.i64 w),
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals,
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 w l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setp_3 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params.set 3 (.i64 w),
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals,
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 w l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setp_4 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params.set 4 (.i64 w),
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals,
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 w l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl

@[frame_step] theorem lFrameFlat_setl_0 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 0 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 w l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_1 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 1 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 w l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_2 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 2 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 w l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_3 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 3 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 w l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_4 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 4 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 w l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_5 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 5 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 w l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_6 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 6 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 w l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_7 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 7 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 w l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_8 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 8 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 w l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_9 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 9 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 w l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_10 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 10 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 w l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_11 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 11 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 w l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_12 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 12 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 w l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_13 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 13 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 w l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_14 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 14 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 w l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_15 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 15 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 w l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_16 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 16 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 w l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_17 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 17 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 w l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_18 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 18 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 w l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_19 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 19 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 w l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_20 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 20 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 w l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_21 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 21 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 w l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_22 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 22 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 w l28 l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_23 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 23 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 w l29 l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_24 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 24 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 w l30 l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_25 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 25 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 w l31 l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_26 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 26 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 w l32 l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_27 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 27 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 w l33 l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_28 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 28 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 w l34 l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_29 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 29 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 w l35 l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_30 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 30 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 w l36 with values := vs } := rfl
@[frame_step] theorem lFrameFlat_setl_31 (w : UInt64) (vs : List Wasm.Value) :
    ({ params := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params,
        locals := (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals.set 31 (.i64 w),
        values := vs } : Wasm.Locals) =
      { lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 w with values := vs } := rfl

@[frame_step] theorem lFrameFlat_params :
    (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).params = [.i64 l0, .i64 l1, .i64 l2, .i64 l3, .i64 l4] := rfl
@[frame_step] theorem lFrameFlat_locals :
    (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).locals = [.i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18, .i64 l19, .i64 l20, .i64 l21, .i64 l22, .i64 l23, .i64 l24, .i64 l25, .i64 l26, .i64 l27, .i64 l28, .i64 l29, .i64 l30, .i64 l31, .i64 l32, .i64 l33, .i64 l34, .i64 l35, .i64 l36] := rfl
@[frame_step] theorem lFrameFlat_values :
    (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36).values = [] := rfl

@[frame_step] theorem lFrameFlat_validIndex (i : Nat) (h : i < 37) :
    Wasm.Locals.validIndex (lFrameFlat l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36) i := by
  simp only [lFrameFlat, Wasm.Locals.validIndex]
  simp
  omega

end lFrameFlatLemmas

end Project.LebU32.Spec
