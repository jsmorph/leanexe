import Project.LebU32.Program
import Project.Common
import Project.Runtime.Spec
import Project.Runtime.TreeSpec
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Shared definitions for the LEB128 artifact proof

The pure recursion, its length lemmas, the loop frames, the invariant,
and the two branch programs of the compiled fuel loop.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec


open Wasm Project.Common Project.Runtime

def lebList : Nat → UInt64 → List UInt8
  | 0, _ => []
  | fuel + 1, v =>
      let low := v % 128
      let rest := v / 128
      if rest == 0 then
        [low.toUInt8]
      else
        (low + 128).toUInt8 :: lebList fuel rest

theorem lebList_length_le (fuel : Nat) (v : UInt64) :
    (lebList fuel v).length ≤ fuel := by
  induction fuel generalizing v with
  | zero => simp [lebList]
  | succ fuel ih =>
      unfold lebList
      by_cases h : v / 128 == 0
      · simp [h]
      · simp [h]
        exact Nat.le_trans (ih _) (by omega)

theorem lebList_length_pos (fuel : Nat) (v : UInt64) (h : 0 < fuel) :
    0 < (lebList fuel v).length := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      unfold lebList
      by_cases hv : v / 128 == 0 <;> simp [hv]

/-- Small values encode within few bytes: each seven-bit group divides
the value by 128, so `fuel` groups cover `v < 128 ^ fuel`. -/
theorem lebList_length_of_lt (fuel bound : Nat) (v : UInt64)
    (hb : bound ≤ 10) (hv : v.toNat < 128 ^ bound) (hf : bound ≤ fuel)
    (h0 : 0 < bound) :
    (lebList fuel v).length ≤ bound := by
  induction fuel generalizing v bound with
  | zero => omega
  | succ fuel ih =>
      unfold lebList
      by_cases h : v / 128 == 0
      · simp [h]
        omega
      · simp [h]
        have hne : ¬ (v / 128).toNat = 0 := by
          intro hz
          have : v / 128 = 0 := by
            apply UInt64.toNat.inj
            simpa using hz
          simp [this] at h
        have hdiv : (v / 128).toNat = v.toNat / 128 := by
          rw [UInt64.toNat_div]
          rfl
        cases bound with
        | zero => omega
        | succ bound =>
            cases bound with
            | zero =>
                exfalso
                have : v.toNat < 128 := by simpa using hv
                omega
            | succ b =>
                have := ih (b + 1) (v / 128) (by omega)
                  (by
                    rw [hdiv]
                    rw [Nat.pow_succ] at hv
                    omega)
                  (by omega) (by omega)
                simpa using this
/-- One 8-byte-capacity heap object per emitted byte: 48-byte header
plus the rounded payload. -/
def objBase (g0 : UInt64) (i : Nat) : Nat :=
  g0.toNat + 56 * i

def lFrame (l0 l1 l2 l3 l4 l5 l6 l7 l8 : UInt64)
    (e : Nat → UInt64) : Locals :=
  { params := [.i64 l0, .i64 l1, .i64 l2, .i64 l3, .i64 l4],
    locals := [.i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 (e 9),
      .i64 (e 10), .i64 (e 11), .i64 (e 12), .i64 (e 13), .i64 (e 14),
      .i64 (e 15), .i64 (e 16), .i64 (e 17), .i64 (e 18), .i64 (e 19),
      .i64 (e 20), .i64 (e 21), .i64 (e 22), .i64 (e 23), .i64 (e 24),
      .i64 (e 25), .i64 (e 26), .i64 (e 27), .i64 (e 28), .i64 (e 29),
      .i64 (e 30), .i64 (e 31), .i64 (e 32), .i64 (e 33), .i64 (e 34),
      .i64 (e 35), .i64 (e 36)],
    values := [] }

def bufPtr (g0 : UInt64) (k : Nat) : UInt64 :=
  if k = 0 then 0 else UInt64.ofNat (objBase g0 (k - 1) + 48)

/-- The running/done loop invariant for the compiled fuel loop. -/
def lInv (st : Store Unit) (n g0 g2 : UInt64) :
    AssertionF Unit :=
  fun stL sL =>
    ∃ (k : Nat) (v : UInt64) (written : List UInt8) (done : Bool)
      (e : Nat → UInt64),
      lebList 10 n = written ++ (if done then [] else lebList (10 - k) v) ∧
      written.length = k ∧
      k ≤ (lebList 10 n).length ∧
      (if done then
        sL = lFrame (UInt64.ofNat (11 - k)) (e 1) (e 2) (e 3) (e 4)
          (bufPtr g0 k) (bufPtr g0 k) (UInt64.ofNat k) 1 e
       else
        sL = lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
          (UInt64.ofNat k) 0 0 0 0 e) ∧
      (∀ i : Nat, i < k →
        stL.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!) ∧
      stL.globals.globals.length = st.globals.globals.length ∧
      stL.globals.globals[0]? =
        some (.i64 (g0 + UInt64.ofNat (56 * k))) ∧
      stL.globals.globals[1]? = some (.i64 0) ∧
      stL.globals.globals[2]? = some (.i64 (g2 + UInt64.ofNat k)) ∧
      stL.globals.globals[3]? = st.globals.globals[3]? ∧
      stL.globals.globals[4]? = st.globals.globals[4]? ∧
      stL.globals.globals[5]? = st.globals.globals[5]? ∧
      stL.mem.pages = st.mem.pages ∧
      (∀ a : Nat, a < g0.toNat → stL.mem.bytes a = st.mem.bytes a)

def lMeasure (_ : Store Unit) (sL : Locals) : Nat :=
  match sL.params, sL.locals with
  | .i64 l0 :: _, _ :: _ :: _ :: .i64 l8 :: _ =>
      2 * l0.toNat + (if l8 = 0 then 1 else 0)
  | _, _ => 0

def posProg : Wasm.Program :=
  [
  .localGet 1,
        .localSet 25,
        .constI64 (128 : UInt64),
        .localSet 26,
        .localGet 26,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 1 [
          .localGet 25
        ] [
          .localGet 25,
          .localGet 26,
          .remUI64
        ],
        .constI64 (255 : UInt64),
        .andI64,
        .localSet 9,
        .localGet 3,
        .localSet 10,
        .localGet 4,
        .localSet 11,
        .localGet 10,
        .localSet 25,
        .localGet 11,
        .localSet 26,
        .localGet 9,
        .localSet 27,
        .localGet 26,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 29,
        .localGet 29,
        .constI64 (7 : UInt64),
        .addI64,
        .constI64 (8 : UInt64),
        .divUI64,
        .constI64 (8 : UInt64),
        .mulI64,
        .localSet 31,
        .localGet 31,
        .constI64 (8 : UInt64),
        .ltUI64,
        .iff 0 0 [
          .constI64 (8 : UInt64),
          .localSet 31
        ] [],
        .constI64 (0 : UInt64),
        .localSet 36,
        .constI64 (0 : UInt64),
        .localSet 32,
        .globalGet 1,
        .localSet 33,
        .block 0 0 [
          .loop 0 0 [
            .localGet 33,
            .constI64 (0 : UInt64),
            .eqI64,
            .br_if 1,
            .localGet 36,
            .constI64 (0 : UInt64),
            .neI64,
            .br_if 1,
            .localGet 33,
            .constI64 (32 : UInt64),
            .subI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .localSet 34,
            .localGet 33,
            .constI64 (8 : UInt64),
            .subI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .localSet 35,
            .localGet 34,
            .localGet 31,
            .geUI64,
            .iff 0 0 [
              .localGet 32,
              .constI64 (0 : UInt64),
              .eqI64,
              .iff 0 0 [
                .localGet 35,
                .globalSet 1
              ] [
                .localGet 32,
                .constI64 (8 : UInt64),
                .subI64,
                .wrapI64,
                .localGet 35,
                .store64 (0 : UInt32)
              ],
              .localGet 33,
              .constI64 (48 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (5501223100278326855 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (40 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (1 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (32 : UInt64),
              .subI64,
              .wrapI64,
              .localGet 34,
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (24 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (16 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (8 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .localSet 36
            ] [
              .localGet 33,
              .localSet 32,
              .localGet 35,
              .localSet 33
            ],
            .br 0
          ]
        ],
        .localGet 36,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .globalGet 0,
          .constI64 (48 : UInt64),
          .addI64,
          .localGet 31,
          .addI64,
          .localSet 34,
          .localGet 34,
          .globalGet 0,
          .ltUI64,
          .iff 0 0 [
            .unreachable
          ] [],
          .localGet 34,
          .constI64 (1 : UInt64),
          .subI64,
          .constI64 (65536 : UInt64),
          .divUI64,
          .constI64 (1 : UInt64),
          .addI64,
          .localSet 35,
          .memorySize,
          .extendUI32,
          .localGet 35,
          .ltUI64,
          .iff 0 0 [
            .localGet 35,
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
          .localSet 36,
          .localGet 34,
          .globalSet 0,
          .localGet 36,
          .constI64 (48 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (5501223100278326855 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (40 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (1 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (32 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 31,
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (24 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (0 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (16 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (0 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
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
        .localGet 36,
        .localSet 28,
        .constI64 (0 : UInt64),
        .localSet 30,
        .block 0 0 [
          .loop 0 0 [
            .localGet 30,
            .localGet 26,
            .geUI64,
            .br_if 1,
            .localGet 28,
            .localGet 30,
            .addI64,
            .wrapI64,
            .localGet 25,
            .localGet 30,
            .addI64,
            .wrapI64,
            .load8U (0 : UInt32),
            .store8 (0 : UInt32),
            .localGet 30,
            .constI64 (1 : UInt64),
            .addI64,
            .localSet 30,
            .br 0
          ]
        ],
        .localGet 28,
        .localGet 26,
        .addI64,
        .wrapI64,
        .localGet 27,
        .wrapI64,
        .store8 (0 : UInt32),
        .localGet 28,
        .localSet 12,
        .localGet 12,
        .localSet 5,
        .localGet 12,
        .localSet 6,
        .localGet 11,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 7,
        .constI64 (1 : UInt64),
        .localSet 8
]

def negProg : Wasm.Program :=
  [
  .localGet 1,
        .localSet 25,
        .constI64 (128 : UInt64),
        .localSet 26,
        .localGet 26,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 1 [
          .constI64 (0 : UInt64)
        ] [
          .localGet 25,
          .localGet 26,
          .divUI64
        ],
        .localSet 13,
        .localGet 1,
        .localSet 25,
        .constI64 (128 : UInt64),
        .localSet 26,
        .localGet 26,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 1 [
          .localGet 25
        ] [
          .localGet 25,
          .localGet 26,
          .remUI64
        ],
        .constI64 (128 : UInt64),
        .addI64,
        .constI64 (255 : UInt64),
        .andI64,
        .localSet 14,
        .localGet 3,
        .localSet 15,
        .localGet 4,
        .localSet 16,
        .localGet 15,
        .localSet 25,
        .localGet 16,
        .localSet 26,
        .localGet 14,
        .localSet 27,
        .localGet 26,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 29,
        .localGet 29,
        .constI64 (7 : UInt64),
        .addI64,
        .constI64 (8 : UInt64),
        .divUI64,
        .constI64 (8 : UInt64),
        .mulI64,
        .localSet 31,
        .localGet 31,
        .constI64 (8 : UInt64),
        .ltUI64,
        .iff 0 0 [
          .constI64 (8 : UInt64),
          .localSet 31
        ] [],
        .constI64 (0 : UInt64),
        .localSet 36,
        .constI64 (0 : UInt64),
        .localSet 32,
        .globalGet 1,
        .localSet 33,
        .block 0 0 [
          .loop 0 0 [
            .localGet 33,
            .constI64 (0 : UInt64),
            .eqI64,
            .br_if 1,
            .localGet 36,
            .constI64 (0 : UInt64),
            .neI64,
            .br_if 1,
            .localGet 33,
            .constI64 (32 : UInt64),
            .subI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .localSet 34,
            .localGet 33,
            .constI64 (8 : UInt64),
            .subI64,
            .wrapI64,
            .load64 (0 : UInt32),
            .localSet 35,
            .localGet 34,
            .localGet 31,
            .geUI64,
            .iff 0 0 [
              .localGet 32,
              .constI64 (0 : UInt64),
              .eqI64,
              .iff 0 0 [
                .localGet 35,
                .globalSet 1
              ] [
                .localGet 32,
                .constI64 (8 : UInt64),
                .subI64,
                .wrapI64,
                .localGet 35,
                .store64 (0 : UInt32)
              ],
              .localGet 33,
              .constI64 (48 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (5501223100278326855 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (40 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (1 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (32 : UInt64),
              .subI64,
              .wrapI64,
              .localGet 34,
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (24 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (16 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .constI64 (8 : UInt64),
              .subI64,
              .wrapI64,
              .constI64 (0 : UInt64),
              .store64 (0 : UInt32),
              .localGet 33,
              .localSet 36
            ] [
              .localGet 33,
              .localSet 32,
              .localGet 35,
              .localSet 33
            ],
            .br 0
          ]
        ],
        .localGet 36,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .globalGet 0,
          .constI64 (48 : UInt64),
          .addI64,
          .localGet 31,
          .addI64,
          .localSet 34,
          .localGet 34,
          .globalGet 0,
          .ltUI64,
          .iff 0 0 [
            .unreachable
          ] [],
          .localGet 34,
          .constI64 (1 : UInt64),
          .subI64,
          .constI64 (65536 : UInt64),
          .divUI64,
          .constI64 (1 : UInt64),
          .addI64,
          .localSet 35,
          .memorySize,
          .extendUI32,
          .localGet 35,
          .ltUI64,
          .iff 0 0 [
            .localGet 35,
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
          .localSet 36,
          .localGet 34,
          .globalSet 0,
          .localGet 36,
          .constI64 (48 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (5501223100278326855 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (40 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (1 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (32 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 31,
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (24 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (0 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
          .constI64 (16 : UInt64),
          .subI64,
          .wrapI64,
          .constI64 (0 : UInt64),
          .store64 (0 : UInt32),
          .localGet 36,
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
        .localGet 36,
        .localSet 28,
        .constI64 (0 : UInt64),
        .localSet 30,
        .block 0 0 [
          .loop 0 0 [
            .localGet 30,
            .localGet 26,
            .geUI64,
            .br_if 1,
            .localGet 28,
            .localGet 30,
            .addI64,
            .wrapI64,
            .localGet 25,
            .localGet 30,
            .addI64,
            .wrapI64,
            .load8U (0 : UInt32),
            .store8 (0 : UInt32),
            .localGet 30,
            .constI64 (1 : UInt64),
            .addI64,
            .localSet 30,
            .br 0
          ]
        ],
        .localGet 28,
        .localGet 26,
        .addI64,
        .wrapI64,
        .localGet 27,
        .wrapI64,
        .store8 (0 : UInt32),
        .localGet 28,
        .localSet 17,
        .localGet 17,
        .localSet 18,
        .localGet 17,
        .localSet 19,
        .localGet 16,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 20,
        .localGet 13,
        .localSet 21,
        .localGet 18,
        .localSet 22,
        .localGet 19,
        .localSet 23,
        .localGet 20,
        .localSet 24,
        .localGet 21,
        .localSet 1,
        .localGet 22,
        .localSet 2,
        .localGet 23,
        .localSet 3,
        .localGet 24,
        .localSet 4,
        .localGet 0,
        .constI64 (1 : UInt64),
        .subI64,
        .localSet 0
]

def tailProgPos : Wasm.Program :=
  [.localGet 28, .localGet 26, .addI64, .wrapI64,
   .localGet 27, .wrapI64, .store8 (0 : UInt32),
   .localGet 28, .localSet 12, .localGet 12, .localSet 5,
   .localGet 12, .localSet 6, .localGet 11, .constI64 (1 : UInt64),
   .addI64, .localSet 7, .constI64 (1 : UInt64), .localSet 8,
   .br 0]

/-- The continuation step: when the rest is nonzero the encoder emits the
low seven bits with the high bit set and recurses on `v / 128`. -/
theorem lebList_cont (fuel : Nat) (v : UInt64) (h : ¬ v / 128 = 0) :
    lebList (fuel + 1) v = (v % 128 + 128).toUInt8 :: lebList fuel (v / 128) := by
  have hb : ¬ ((v / 128) == 0) = true := by simpa using h
  conv_lhs => unfold lebList
  simp only [hb]
  simp

/-- The final step: when the rest is zero the encoder emits the low seven
bits and stops. -/
theorem lebList_final (fuel : Nat) (v : UInt64) (h : v / 128 = 0) :
    lebList (fuel + 1) v = [(v % 128).toUInt8] := by
  have hb : ((v / 128) == 0) = true := by simpa using h
  conv_lhs => unfold lebList
  simp only [hb]
  simp

/-- The copy-loop frame for the continuation branch: `negProg` holds the
rest in local 13 and the byte in local 14, shifting locals 9 through 16. -/
def cFrameNeg (g0 v : UInt64) (k j : Nat)
    (e : Nat → UInt64) : Locals :=
  { params := [.i64 (UInt64.ofNat (10 - k)), .i64 v,
        .i64 (bufPtr g0 k), .i64 (bufPtr g0 k),
        .i64 (UInt64.ofNat k)],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0,
        .i64 (e 9), .i64 (e 10),
        .i64 (e 11), .i64 (e 12), .i64 (v / 128),
        .i64 (v % 128 + 128 &&& 255), .i64 (bufPtr g0 k),
        .i64 (UInt64.ofNat k), .i64 (e 17),
        .i64 (e 18), .i64 (e 19), .i64 (e 20), .i64 (e 21),
        .i64 (e 22), .i64 (e 23), .i64 (e 24),
        .i64 (bufPtr g0 k), .i64 (UInt64.ofNat k),
        .i64 (v % 128 + 128 &&& 255),
        .i64 (g0 + 56 * UInt64.ofNat k + 48),
        .i64 (UInt64.ofNat k + 1), .i64 (UInt64.ofNat j),
        .i64 8, .i64 0, .i64 0,
        .i64 (g0 + 56 * UInt64.ofNat k + 48 + 8),
        .i64 ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) /
          65536 + 1),
        .i64 (g0 + 56 * UInt64.ofNat k + 48)],
      values := [] }

def cFramePos (g0 v : UInt64) (k j : Nat)
    (e : Nat → UInt64) : Locals :=
  { params := [.i64 (UInt64.ofNat (10 - k)), .i64 v,
        .i64 (bufPtr g0 k), .i64 (bufPtr g0 k),
        .i64 (UInt64.ofNat k)],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0,
        .i64 (v % 128 &&& 255), .i64 (bufPtr g0 k),
        .i64 (UInt64.ofNat k), .i64 (e 12), .i64 (e 13),
        .i64 (e 14), .i64 (e 15), .i64 (e 16), .i64 (e 17),
        .i64 (e 18), .i64 (e 19), .i64 (e 20), .i64 (e 21),
        .i64 (e 22), .i64 (e 23), .i64 (e 24),
        .i64 (bufPtr g0 k), .i64 (UInt64.ofNat k),
        .i64 (v % 128 &&& 255),
        .i64 (g0 + 56 * UInt64.ofNat k + 48),
        .i64 (UInt64.ofNat k + 1), .i64 (UInt64.ofNat j),
        .i64 8, .i64 0, .i64 0,
        .i64 (g0 + 56 * UInt64.ofNat k + 48 + 8),
        .i64 ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) /
          65536 + 1),
        .i64 (g0 + 56 * UInt64.ofNat k + 48)],
      values := [] }


end Project.LebU32.Spec
