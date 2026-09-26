import Project.Beck.ExecutionRead
import Project.Beck.Counting
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

abbrev CountScratch := Fin 25 → Value

def counted (input : Input) (point : Point) (category index : Nat) : Bool :=
  !frozen point index && input.incidence[index * input.categories + category]! == 1

def countFrame (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category index count : Nat) (scratch : CountScratch) : Locals :=
  { params := (inputValues input inputOwner inputPointer).reverse ++
      (pointValues point pointOwner pointPointer).reverse ++ [.i64 category.toUInt64]
    locals := [.i64 0, .i64 count.toUInt64,
      scratch 0, scratch 1, scratch 2, scratch 3, scratch 4, scratch 5, scratch 6,
      scratch 7, scratch 8, scratch 9, scratch 10, scratch 11, scratch 12, scratch 13, scratch 14,
      .i64 index.toUInt64, .i64 input.jobs.toUInt64, .i64 1,
      scratch 15, scratch 16, scratch 17, scratch 18, scratch 19, scratch 20,
      scratch 21, scratch 22, scratch 23, scratch 24] }

def countScratch (input : Input) (point : Point) (pointOwner pointPointer : UInt64)
    (category index count : Nat) (isFrozen contributes : Bool) (scratch : CountScratch) : CountScratch := fun k =>
  match k.val with
  | 0 | 5 | 11 | 15 => .i64 index.toUInt64
  | 1 => .i64 count.toUInt64
  | 2 | 8 => .i64 point.denominator
  | 3 | 9 => .i64 pointOwner
  | 4 | 10 => .i64 pointPointer
  | 6 => if contributes then .i64 (count + 1).toUInt64 else scratch k
  | 7 | 23 => .i64 (if contributes then (count + 1).toUInt64 else count.toUInt64)
  | 16 => .i64 1
  | 17 => .i64 (index + 1).toUInt64
  | 18 => if isFrozen then scratch k else .i64 category.toUInt64
  | 19 => if isFrozen then scratch k else .i64 (index * input.categories + category).toUInt64
  | 20 => if isFrozen then scratch k else .i64 index.toUInt64
  | 21 => if isFrozen then scratch k else .i64 input.categories.toUInt64
  | 22 => .i64 0
  | _ => scratch k

def countBody : Wasm.Program :=
  match (func17[10]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

set_option maxHeartbeats 1000000 in
theorem countStep_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category index count : Nat) (scratch : CountScratch)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (pointSize : input.jobs ≤ point.numerators.size)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8)
    (categoryBound : category < input.categories) (indexBound : index < input.jobs) (countBound : count ≤ index)
    (Q : Assertion Unit)
    (next : Q (.Break 0 initial (countFrame input point inputOwner inputPointer pointOwner pointPointer
      category (index + 1) (if counted input point category index then count + 1 else count)
      (countScratch input point pointOwner pointPointer category index count (frozen point index)
        (counted input point category index) scratch)))) :
    wp «module» (countBody.drop 4) Q initial
      (countFrame input point inputOwner inputPointer pointOwner pointPointer category index count scratch) env := by
  have indexFit : index < UInt64.size := by change index < 18446744073709551616; omega
  have categoryFit : input.categories < UInt64.size := by change input.categories < 18446744073709551616; omega
  have productFit : index * input.categories < UInt64.size := by
    change index * input.categories < 18446744073709551616
    nlinarith
  have addressBound : index * input.categories + category < input.incidence.size := by
    rw [inputSize]
    nlinarith
  have addressFit := lt_trans addressBound inputArray.size_lt
  have indexGuard : ¬UInt64.ofNat index + 1 < UInt64.ofNat index :=
    CheckedNatAdd.guard_of_fits index 1 (by change index + 1 < 18446744073709551616; omega)
  have countGuard : ¬UInt64.ofNat count + 1 < UInt64.ofNat count :=
    CheckedNatAdd.guard_of_fits count 1 (by change count + 1 < 18446744073709551616; omega)
  have addressGuard := CheckedNatAdd.guard_of_fits (index * input.categories) category addressFit
  have productWord : UInt64.ofNat index * UInt64.ofNat input.categories = UInt64.ofNat (index * input.categories) :=
    (UInt64.ofNat_mul _ _).symm
  have addressWord : UInt64.ofNat (index * input.categories) + UInt64.ofNat category =
      UInt64.ofNat (index * input.categories + category) := (UInt64.ofNat_add _ _).symm
  have hFrozen := frozen_exact env initial point pointOwner pointPointer index pointArray
    (lt_of_lt_of_le indexBound pointSize)
  have mulFit : (UInt64.ofNat index).toNat * (UInt64.ofNat input.categories).toNat < UInt64.size := by
    rw [UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' categoryFit]
    exact productFit
  cases hf : frozen point index <;> by_cases member : input.incidence[index * input.categories + category] = 1
  all_goals
    simp only [countBody, func17, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop,
      countFrame, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append]
    repeat' (first
      | (refine wp_call_tw hFrozen ?_; rintro final values ⟨same, rfl⟩; subst final)
      | (refine CheckedNatMul.program_spec 35 36 «module» env initial _
          (UInt64.ofNat index) (UInt64.ofNat input.categories) [] rfl rfl rfl mulFit _ _ ?_)
      | (refine CheckedArrayGet.checkedGetCore_spec 30 31 «module» env initial _ inputPointer
          input.incidence (index * input.categories + category) [] rfl (by simp [Locals.get])
          rfl inputArray addressBound _ _ ?_)
      | wp_fixed_frame_step
      | ((first
          | rw [wp_eqI64_cons] | rw [wp_eqz_cons] | rw [wp_neI64_cons]
          | rw [wp_ltUI64_cons] | rw [wp_addI64_cons] | rw [wp_const_cons]
          | rw [wp_localTee_cons] | rw [wp_br_if_cons] | rw [wp_br_cons] | rw [wp_nil]) <;>
        simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
          List.take, List.drop, List.append_nil, Nat.toUInt64, boolWord, hf, member,
          productWord, countGuard, addressGuard, ↓reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  all_goals
    try repeat' ((try wp_fixed_frame [indexGuard]) <;> (refine wp_iff_cons rfl ?_; simp))
    simpa [countFrame, countScratch, inputValues, pointValues, counted, hf,
      getElem!_pos input.incidence (index * input.categories + category) addressBound, member, addressWord] using next

end Project.Beck.Execution
