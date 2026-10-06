import Project.Smalltalk.Frame
import Project.Smalltalk.Loops

namespace Project.Smalltalk.Unwind
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Frame Project.Smalltalk.Loops

/-- The actual caller links from current through stop, including stop.
Each frame has a valid handle and appears at most once in this prefix. -/
inductive Prefix (s : Array UInt64) (cap : Nat) (stop : UInt64) :
    UInt64 → List UInt64 → UInt64 → Prop
  | done {caller} : Handle cap stop → kind s stop = 5 → field s stop 4 = caller →
      Prefix s cap stop stop [stop] caller
  | next {head tail nodes caller} : Handle cap head → kind s head = 5 → head ≠ stop →
      field s head 4 = tail → head ∉ nodes → Prefix s cap stop tail nodes caller →
      Prefix s cap stop head (head :: nodes) caller

def retireMany (s : Array UInt64) (frames : List UInt64) : Array UInt64 := frames.foldl retire s

@[simp] theorem retireMany_nil (s : Array UInt64) : retireMany s [] = s := rfl
@[simp] theorem retireMany_cons (s : Array UInt64) (head : UInt64) (rest : List UInt64) :
    retireMany s (head :: rest) = retireMany (retire s head) rest := rfl

theorem retireMany_shape {s : Array UInt64} {cap : Nat} {frames : List UInt64}
    (shape : Shape s cap) (handles : ∀ h ∈ frames, Handle cap h) : Shape (retireMany s frames) cap := by
  induction frames generalizing s with
  | nil => exact shape
  | cons head rest ih =>
    rw [retireMany_cons]
    exact ih (retire_shape shape (handles head (by simp)))
      (fun h mem => handles h (List.mem_cons_of_mem _ mem))

theorem retireMany_register {s : Array UInt64} {cap : Nat} {frames : List UInt64} {r : UInt64}
    (shape : Shape s cap) (handles : ∀ h ∈ frames, Handle cap h) (bound : r.toNat < 24) :
    read (retireMany s frames) r = read s r := by
  induction frames generalizing s with
  | nil => rfl
  | cons head rest ih =>
    rw [retireMany_cons, ih (retire_shape shape (handles head (by simp)))
      (fun h mem => handles h (List.mem_cons_of_mem _ mem)), retire_register shape (handles head (by simp)) bound]

theorem retireMany_field {s : Array UInt64} {cap : Nat} {frames : List UInt64} {h k : UInt64}
    (shape : Shape s cap) (handles : ∀ g ∈ frames, Handle cap g) (handle : Handle cap h)
    (bound : k.toNat < 8) :
    field (retireMany s frames) h k =
      if h ∈ frames then if k = 7 ∨ k = 4 then 0 else if k = 3 then dead else field s h k
      else field s h k := by
  induction frames generalizing s with
  | nil => simp only [retireMany_nil, List.not_mem_nil, ite_false]
  | cons head rest ih =>
    have hh := handles head (by simp)
    rw [retireMany_cons, ih (retire_shape shape hh) (fun h mem => handles h (List.mem_cons_of_mem _ mem)),
      retire_field shape hh handle bound]
    by_cases tailMember : h ∈ rest <;> by_cases same : h = head <;>
      by_cases cleared : k = 7 ∨ k = 4 <;> by_cases pc : k = 3 <;>
      simp only [List.mem_cons, tailMember, same, cleared, pc, true_or, false_or, ite_true, ite_false, ite_self]

theorem prefix_handles {s cap stop current frames caller} (path : Prefix s cap stop current frames caller)
    {h : UInt64} (member : h ∈ frames) : Handle cap h := by
  induction path with
  | done handle _ _ => simpa using (show ∀ h ∈ [stop], Handle cap h from by simpa using handle) h member
  | next handle _ _ _ _ _ ih =>
    rcases List.mem_cons.mp member with eq | mem
    · subst h; exact handle
    · exact ih mem

theorem prefix_nonempty {s cap stop current frames caller} (path : Prefix s cap stop current frames caller) :
    frames ≠ [] := by cases path <;> simp

theorem prefix_transfer {s t cap stop current frames caller}
    (path : Prefix s cap stop current frames caller)
    (same : ∀ h ∈ frames, kind t h = kind s h ∧ field t h 4 = field s h 4) :
    Prefix t cap stop current frames caller := by
  induction path with
  | done handle tag link =>
    have words := same stop (by simp)
    exact .done handle (words.1.trans tag) (words.2.trans link)
  | @next head tail nodes caller handle tag different link absent path ih =>
    have words := same head (by simp)
    exact .next handle (words.1.trans tag) different (words.2.trans link) absent
      (ih (fun h mem => same h (List.mem_cons_of_mem _ mem)))

theorem prefix_after_retire {s : Array UInt64} {cap : Nat} {stop head tail caller : UInt64}
    {nodes : List UInt64} (shape : Shape s cap) (handle : Handle cap head)
    (absent : head ∉ nodes) (path : Prefix s cap stop tail nodes caller) :
    Prefix (retire s head) cap stop tail nodes caller := by
  have post := retire_shape shape handle
  apply prefix_transfer path
  intro h member
  have hh := prefix_handles path member
  have different : h ≠ head := by intro eq; subst h; exact absent member
  constructor
  · rw [kind_eq_field post hh, retire_field shape handle hh (show (0 : UInt64).toNat < 8 by decide),
      kind_eq_field shape hh]
    simp only [different, ite_false]
  · rw [retire_field shape handle hh (show (4 : UInt64).toNat < 8 by decide)]
    simp only [different, ite_false]

theorem unwind_go_prefix {s : Array UInt64} {cap : Nat} {stop current caller : UInt64}
    {frames : List UInt64} (shape : Shape s cap) (path : Prefix s cap stop current frames caller)
    (fuel : Nat) (room : frames.length ≤ fuel) :
    LeanExe.repeatWhile.go (fun (cursor, _) => cursor != (0 : UInt64))
      (fun (cursor, s) => unwindNext s stop cursor) fuel (current, s) = (0, retireMany s frames) := by
  induction fuel generalizing s current frames with
  | zero =>
    have empty : frames = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact False.elim (prefix_nonempty path empty)
  | succ fuel ih =>
    cases path with
    | done handle tag link =>
      have nonzero : stop ≠ 0 := by
        intro zero
        have bound := handle.1
        rw [zero] at bound
        contradiction
      have test : (stop != 0) = true := bne_iff_ne.mpr nonzero
      rw [LeanExe.repeatWhile.go]
      simp only [test, ite_true]
      rw [show unwindNext s stop stop = (0, retire s stop) by simp [unwindNext]]
      rw [go_stop _ _ _ (by simp)]
      rfl
    | @next head tail nodes caller handle tag different link absent path =>
      have nonzero : current ≠ 0 := by
        intro zero
        have bound := handle.1
        rw [zero] at bound
        contradiction
      have test : (current != 0) = true := bne_iff_ne.mpr nonzero
      have miss : (current == stop) = false := beq_eq_false_iff_ne.mpr different
      rw [LeanExe.repeatWhile.go]
      simp only [test, ite_true]
      rw [show unwindNext s stop current = (tail, retire s current) by
        simp only [unwindNext, miss, Bool.false_eq_true, ite_false, link]]
      rw [ih (retire_shape shape handle) (prefix_after_retire shape handle absent path)
        (by simp only [List.length_cons] at room; omega)]
      rfl

/-- The bounded concrete loop retires exactly the represented prefix through
the return target, then passes its state to returnCaller. -/
theorem returnReady_prefix {s : Array UInt64} {cap : Nat} {stop caller value : UInt64}
    {frames : List UInt64} (shape : Shape s cap)
    (path : Prefix s cap stop (read s 2) frames caller) (room : frames.length ≤ cap) :
    returnReady s stop caller value = returnCaller (retireMany s frames) caller value := by
  simp only [returnReady, LeanExe.repeatWhile]
  rw [unwind_go_prefix shape path _ (by rw [shape.2.2.2]; exact room)]

end Project.Smalltalk.Unwind
