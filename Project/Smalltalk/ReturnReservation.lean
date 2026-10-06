import Project.Smalltalk.ReturnValue
import Project.Smalltalk.Reservation
import Project.Smalltalk.ReturnChecks

namespace Project.Smalltalk.ReturnReservation
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Unwind Project.Smalltalk.Reservation Project.Smalltalk.ReturnValue

theorem handle_nonzero {cap : Nat} {h : UInt64} (handle : Handle cap h) : h ≠ 0 := by
  intro zero
  have bound := handle.1
  rw [zero] at bound
  contradiction

theorem prefix_current_handle {s cap stop current frames caller}
    (path : Prefix s cap stop current frames caller) : Handle cap current := by
  cases path <;> assumption

theorem prefix_target {s cap stop current frames caller}
    (path : Prefix s cap stop current frames caller) :
    stop ∈ frames ∧ Handle cap stop ∧ kind s stop = 5 ∧ field s stop 4 = caller := by
  induction path with
  | done handle tag link => exact ⟨by simp, handle, tag, link⟩
  | next _ _ _ _ _ _ ih => exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩

theorem caller_edge {s : Array UInt64} {cap : Nat} {parent child : UInt64}
    (shape : Shape s cap) (handle : Handle cap parent) (tag : kind s parent = 5)
    (link : field s parent 4 = child) (nonzero : child ≠ 0) : Edge s parent child := by
  refine ⟨nonzero, 4, by decide, ?_, link⟩
  rw [← kind_eq_field shape handle, tag]
  simp [PointerField]

theorem prefix_reachable {s : Array UInt64} {cap : Nat} {stop current caller : UInt64}
    {frames : List UInt64} (shape : Shape s cap) (path : Prefix s cap stop current frames caller)
    (reached : Reachable s current) : ∀ h ∈ frames, Reachable s h := by
  induction path with
  | done handle tag link =>
    intro h member
    have eq : h = stop := by simpa using member
    subst h
    exact reached
  | @next head tail nodes caller handle tag _ link _ path ih =>
    intro h member
    rcases List.mem_cons.mp member with eq | member
    · subst h; exact reached
    · exact ih (.next reached (caller_edge shape handle tag link
        (handle_nonzero (prefix_current_handle path)))) h member

theorem current_reachable {s : Array UInt64} {cap : Nat} {stop caller : UInt64} {frames : List UInt64}
    (path : Prefix s cap stop (read s 2) frames caller) : Reachable s (read s 2) :=
  .root ⟨handle_nonzero (prefix_current_handle path), by simp⟩

theorem reserve_prefix {s : Array UInt64} {cap : Nat} {stop caller : UInt64} {frames : List UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (path : Prefix s cap stop (read s 2) frames caller) (need : UInt64) :
    Prefix (reserve s need) cap stop (read (reserve s need) 2) frames caller := by
  have facts := reserve_correct valid phase need
  have reached := prefix_reachable valid.1.1 path (current_reachable path)
  rw [reserve_register valid phase need (show (2 : UInt64).toNat < 24 by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  apply prefix_transfer path
  intro h member
  have handle := prefix_handles path member
  constructor
  · rw [kind_eq_field facts.1.1.1 handle, facts.2.1 h (reached h member) 0 (by decide) (by decide),
      kind_eq_field valid.1.1 handle]
  · exact facts.2.1 h (reached h member) 4 (by decide) (by decide)

theorem returnReserved_eq (s : Array UInt64) (stop caller value : UInt64) (nonzero : caller ≠ 0) :
    returnReserved s stop caller value =
      if read (reserve s 1) 0 == 4 then reserve s 1 else returnReady (reserve s 1) stop caller value := by
  have test : (caller == 0) = false := beq_eq_false_iff_ne.mpr nonzero
  simp only [returnReserved, test, Bool.false_eq_true, ite_false]

theorem free_head {t : Array UInt64} {cap : Nat} {nodes : List UInt64}
    (free : Project.Smalltalk.FreeList.Valid t cap nodes) (enough : (1 : UInt64) ≤ read t 9) :
    ∃ h rest, nodes = h :: rest := by
  cases nodes with
  | nil =>
    have count : (read t 9).toNat = 0 := free.2.1
    have positive : 1 ≤ (read t 9).toNat := UInt64.le_iff_toNat_le.mp enough
    omega
  | cons h rest => exact ⟨h, rest, rfl⟩

/-- Reservation may collect before return. A successful reservation preserves
the represented unwind prefix and caller's data, then delivers the value.
An unsuccessful reservation reports error 9 without unwinding. -/
theorem returnReserved_delivers {s : Array UInt64} {cap : Nat} {stop caller value : UInt64}
    {frames : List UInt64} (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (path : Prefix s cap stop (read s 2) frames caller) (room : frames.length ≤ cap)
    (callerHandle : Handle cap caller) (callerTag : field s caller 0 = 5)
    (callerOutside : caller ∉ frames) :
    (read (returnReserved s stop caller value) 0 = 4 ∧ read (returnReserved s stop caller value) 15 = 9) ∨
    ∃ h, Handle cap h ∧ read (returnReserved s stop caller value) 2 = caller ∧
      field (returnReserved s stop caller value) caller 3 = field s caller 3 ∧
      field (returnReserved s stop caller value) caller 7 = h ∧
      field (returnReserved s stop caller value) h 0 = 7 ∧
      field (returnReserved s stop caller value) h 2 = value ∧
      field (returnReserved s stop caller value) h 3 = field s caller 7 := by
  have facts := reserve_correct valid phase 1
  have preserved := reserve_prefix valid phase path 1
  have target := prefix_target path
  have stopReach := prefix_reachable valid.1.1 path (current_reachable path) stop target.1
  have callerReach := Reachable.next stopReach
    (caller_edge valid.1.1 target.2.1 target.2.2.1 target.2.2.2 (handle_nonzero callerHandle))
  rw [returnReserved_eq s stop caller value (handle_nonzero callerHandle)]
  by_cases error : read (reserve s 1) 0 = 4
  · have reason : read (reserve s 1) 15 = 9 := by
      rcases facts.2.2.2 with ready | failed
      · exact False.elim (phase (ready.1.symm.trans error))
      · exact failed.2
    simp only [error, BEq.rfl, ite_true]
    exact Or.inl ⟨True.intro, reason⟩
  · have enough : (1 : UInt64) ≤ read (reserve s 1) 9 := by
      rcases facts.2.2.2 with ready | failed
      · exact ready.2
      · exact False.elim (error failed.1)
    have readyBool : (read (reserve s 1) 0 == 4) = false := beq_eq_false_iff_ne.mpr error
    simp only [readyBool, Bool.false_eq_true, ite_false]
    rcases facts.1.2 with ⟨nodes, free⟩
    rcases free_head free enough with ⟨h, rest, eq⟩
    subst nodes
    have delivered := returnReady_delivers facts.1.1.1 preserved room free callerHandle
      ((facts.2.1 caller callerReach 0 (by decide) (by decide)).trans callerTag) callerOutside (value := value)
    rw [facts.2.1 caller callerReach 3 (by decide) (by decide),
      facts.2.1 caller callerReach 7 (by decide) (by decide)] at delivered
    exact Or.inr ⟨h, Project.Smalltalk.FreeList.chain_handle free.1 (by simp), delivered⟩

theorem returnReserved_zero (s : Array UInt64) (stop value : UInt64) (phase : read s 0 ≠ 4) :
    returnReserved s stop 0 value = returnReady s stop 0 value := by
  have test : (read s 0 == 4) = false := beq_eq_false_iff_ne.mpr phase
  simp only [returnReserved, BEq.rfl, ite_true, reserve_zero, test, Bool.false_eq_true, ite_false]

theorem returnReserved_finished {s : Array UInt64} {cap : Nat} {stop value : UInt64}
    {frames : List UInt64} (shape : Shape s cap) (phase : read s 0 ≠ 4)
    (path : Prefix s cap stop (read s 2) frames 0) (room : frames.length ≤ cap) :
    read (returnReserved s stop 0 value) 0 = 3 ∧ read (returnReserved s stop 0 value) 2 = 0 ∧
    read (returnReserved s stop 0 value) 7 = value := by
  rw [returnReserved_zero s stop value phase]
  exact returnReady_finished shape path room

open Project.Smalltalk.ReturnChecks Project.Smalltalk.Traversal

theorem ret_delivers {p s : Array UInt64} {cap : Nat} {nonlocal caller : UInt64}
    {nodes frames : List UInt64} (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (chain : Path s 5 4 (read s 2) nodes) (bound : nodes.length ≤ (read s 14).toNat)
    (stack : kind s (field s (read s 2) 7) = 7)
    (tag : kind s (selected p s nonlocal) = 5) (live : field s (selected p s nonlocal) 3 ≠ dead)
    (member : selected p s nonlocal ∈ nodes)
    (unwindPath : Prefix s cap (selected p s nonlocal) (read s 2) frames caller)
    (room : frames.length ≤ cap) (callerHandle : Handle cap caller)
    (callerTag : field s caller 0 = 5) (callerOutside : caller ∉ frames) :
    (read (ret p s nonlocal) 0 = 4 ∧ read (ret p s nonlocal) 15 = 9) ∨
    ∃ h, Handle cap h ∧ read (ret p s nonlocal) 2 = caller ∧
      field (ret p s nonlocal) caller 3 = field s caller 3 ∧
      field (ret p s nonlocal) caller 7 = h ∧ field (ret p s nonlocal) h 0 = 7 ∧
      field (ret p s nonlocal) h 2 = field s (field s (read s 2) 7) 2 ∧
      field (ret p s nonlocal) h 3 = field s caller 7 := by
  rw [ret_accepted chain bound nonlocal stack tag live member, (prefix_target unwindPath).2.2.2]
  exact returnReserved_delivers valid phase unwindPath room callerHandle callerTag callerOutside

theorem ret_finished {p s : Array UInt64} {cap : Nat} {nonlocal : UInt64}
    {nodes frames : List UInt64} (shape : Shape s cap) (phase : read s 0 ≠ 4)
    (chain : Path s 5 4 (read s 2) nodes) (bound : nodes.length ≤ (read s 14).toNat)
    (stack : kind s (field s (read s 2) 7) = 7)
    (tag : kind s (selected p s nonlocal) = 5) (live : field s (selected p s nonlocal) 3 ≠ dead)
    (member : selected p s nonlocal ∈ nodes)
    (unwindPath : Prefix s cap (selected p s nonlocal) (read s 2) frames 0) (room : frames.length ≤ cap) :
    read (ret p s nonlocal) 0 = 3 ∧ read (ret p s nonlocal) 2 = 0 ∧
      read (ret p s nonlocal) 7 = field s (field s (read s 2) 7) 2 := by
  rw [ret_accepted chain bound nonlocal stack tag live member, (prefix_target unwindPath).2.2.2]
  exact returnReserved_finished shape phase unwindPath room

end Project.Smalltalk.ReturnReservation
