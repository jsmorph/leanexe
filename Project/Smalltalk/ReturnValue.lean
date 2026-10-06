import Project.Smalltalk.FreeList
import Project.Smalltalk.Unwind

namespace Project.Smalltalk.ReturnValue
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Allocation Project.Smalltalk.FreeList
open Project.Smalltalk.Unwind

theorem returnCallerReady_eq {s : Array UInt64} {cap : Nat} {h caller value : UInt64}
    {rest : List UInt64} (shape : Shape s cap) (free : FreeList.Valid s cap (h :: rest)) :
    returnCallerReady s caller value =
      write (write (allocateCell s 7 value (field s caller 7) 0 0 0 0) 2 caller)
        (address caller + 7) (read s 8) := by
  have head := chain_cons free.1
  have hh : Handle cap (read s 8) := head.1 ▸ head.2.1
  simp only [returnCallerReady, allocate_success free]
  rw [allocateCell_register shape hh (show (10 : UInt64).toNat < 24 by decide)]
  rfl

theorem returnCallerReady_shape {s : Array UInt64} {cap : Nat} {h caller value : UInt64}
    {rest : List UInt64} (shape : Shape s cap) (free : FreeList.Valid s cap (h :: rest))
    (callerHandle : Handle cap caller) : Shape (returnCallerReady s caller value) cap := by
  rw [returnCallerReady_eq shape free]
  have head := chain_cons free.1
  have hh : Handle cap (read s 8) := head.1 ▸ head.2.1
  exact write_shape (write_shape (allocateCell_shape shape hh ..) (by decide))
    (cell_index_not_register shape.2.1 callerHandle (show (7 : UInt64).toNat < 8 by decide) (by decide))

theorem returnCallerReady_field {s : Array UInt64} {cap : Nat} {h caller value g k : UInt64}
    {rest : List UInt64} (shape : Shape s cap) (free : FreeList.Valid s cap (h :: rest))
    (callerHandle : Handle cap caller) (handle : Handle cap g) (bound : k.toNat < 8) :
    field (returnCallerReady s caller value) g k =
      if g = caller ∧ k = 7 then read s 8 else
      if g = read s 8 then allocatedWord 7 value (field s caller 7) 0 0 0 0 k else field s g k := by
  rw [returnCallerReady_eq shape free]
  have head := chain_cons free.1
  have hh : Handle cap (read s 8) := head.1 ▸ head.2.1
  have allocated := allocateCell_shape shape hh 7 value (field s caller 7) 0 0 0 0
  rw [field_write_cell (write_shape allocated (show (2 : UInt64) ≠ 14 by decide))
      callerHandle handle (show (7 : UInt64).toNat < 8 by decide) bound,
    field_write_register allocated handle bound (show (2 : UInt64).toNat < 24 by decide),
    allocateCell_field shape hh handle bound]

theorem returnCallerReady_register {s : Array UInt64} {cap : Nat} {h caller value r : UInt64}
    {rest : List UInt64} (shape : Shape s cap) (free : FreeList.Valid s cap (h :: rest))
    (callerHandle : Handle cap caller) (bound : r.toNat < 24) :
    read (returnCallerReady s caller value) r =
      if r = 2 then caller else read (allocateCell s 7 value (field s caller 7) 0 0 0 0) r := by
  rw [returnCallerReady_eq shape free]
  have head := chain_cons free.1
  have hh : Handle cap (read s 8) := head.1 ▸ head.2.1
  have allocated := allocateCell_shape shape hh 7 value (field s caller 7) 0 0 0 0
  rw [read_write_other _ _ _ _ (cell_index_not_register shape.2.1 callerHandle
      (show (7 : UInt64).toNat < 8 by decide) bound),
    read_write _ _ _ _ (register_bound allocated (show (2 : UInt64).toNat < 24 by decide))]

/-- Delivery sets current to the caller without advancing its PC, and adds exactly
one fresh operand link containing the returned value above its old stack. -/
theorem returnCallerReady_delivers {s : Array UInt64} {cap : Nat} {h caller value : UInt64}
    {rest : List UInt64} (shape : Shape s cap) (free : FreeList.Valid s cap (h :: rest))
    (callerHandle : Handle cap caller) (callerTag : field s caller 0 = 5) :
    read (returnCallerReady s caller value) 2 = caller ∧
    field (returnCallerReady s caller value) caller 3 = field s caller 3 ∧
    field (returnCallerReady s caller value) caller 7 = h ∧
    field (returnCallerReady s caller value) h 0 = 7 ∧
    field (returnCallerReady s caller value) h 2 = value ∧
    field (returnCallerReady s caller value) h 3 = field s caller 7 := by
  have head := chain_cons free.1
  have different : caller ≠ h := by
    intro eq
    have zero := head.2.2.1
    rw [← eq, callerTag] at zero
    contradiction
  have current := returnCallerReady_register (value := value) shape free callerHandle (show (2 : UInt64).toNat < 24 by decide)
  have words := fun {g k : UInt64} (hg : Handle cap g) (hk : k.toNat < 8) =>
    returnCallerReady_field (value := value) shape free callerHandle hg hk
  refine ⟨by simpa only [ite_true] using current, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [head.1, different] using words callerHandle (show (3 : UInt64).toNat < 8 by decide)
  · simpa [head.1] using words callerHandle (show (7 : UInt64).toNat < 8 by decide)
  · simpa [head.1, Ne.symm different, allocatedWord] using words head.2.1 (show (0 : UInt64).toNat < 8 by decide)
  · simpa [head.1, Ne.symm different, allocatedWord] using words head.2.1 (show (2 : UInt64).toNat < 8 by decide)
  · simpa [head.1, Ne.symm different, allocatedWord] using words head.2.1 (show (3 : UInt64).toNat < 8 by decide)

theorem returnCaller_finished {s : Array UInt64} {cap : Nat} (shape : Shape s cap) (value : UInt64) :
    read (returnCaller s 0 value) 0 = 3 ∧ read (returnCaller s 0 value) 2 = 0 ∧
    read (returnCaller s 0 value) 7 = value := by
  have b0 := register_bound shape (show (0 : UInt64).toNat < 24 by decide)
  have b2 := register_bound shape (show (2 : UInt64).toNat < 24 by decide)
  have b7 := register_bound shape (show (7 : UInt64).toNat < 24 by decide)
  simp only [returnCaller, BEq.rfl, ite_true, read_write, write_size, b0, b2, b7]
  simp

theorem retireMany_free {s : Array UInt64} {cap : Nat} {frames nodes : List UInt64}
    (shape : Shape s cap) (handles : ∀ h ∈ frames, Handle cap h) (free : FreeList.Valid s cap nodes) :
    FreeList.Valid (retireMany s frames) cap nodes := by
  apply valid_transfer free (retireMany_register shape handles (show (8 : UInt64).toNat < 24 by decide))
    (retireMany_register shape handles (show (9 : UInt64).toNat < 24 by decide))
  intro g hg
  constructor
  · rw [retireMany_field shape handles hg (show (0 : UInt64).toNat < 8 by decide)]
    simp
  · rw [retireMany_field shape handles hg (show (2 : UInt64).toNat < 8 by decide)]
    simp

theorem returnReady_delivers {s : Array UInt64} {cap : Nat} {h stop caller value : UInt64}
    {frames rest : List UInt64} (shape : Shape s cap)
    (path : Prefix s cap stop (read s 2) frames caller) (room : frames.length ≤ cap)
    (free : FreeList.Valid s cap (h :: rest)) (callerHandle : Handle cap caller)
    (callerTag : field s caller 0 = 5) (callerOutside : caller ∉ frames) :
    read (returnReady s stop caller value) 2 = caller ∧
    field (returnReady s stop caller value) caller 3 = field s caller 3 ∧
    field (returnReady s stop caller value) caller 7 = h ∧
    field (returnReady s stop caller value) h 0 = 7 ∧
    field (returnReady s stop caller value) h 2 = value ∧
    field (returnReady s stop caller value) h 3 = field s caller 7 := by
  have handles := fun h member => prefix_handles path (h := h) member
  have retiredShape := retireMany_shape shape handles
  have retiredFree := retireMany_free shape handles free
  have same : ∀ k : UInt64, k.toNat < 8 →
      field (retireMany s frames) caller k = field s caller k := by
    intro k bound
    rw [retireMany_field shape handles callerHandle bound]
    simp only [callerOutside, ite_false]
  have facts := returnCallerReady_delivers retiredShape retiredFree callerHandle
    ((same 0 (by decide)).trans callerTag) (value := value)
  rw [same 3 (by decide), same 7 (by decide)] at facts
  have nonzero : caller ≠ 0 := by
    intro zero
    have bound := callerHandle.1
    rw [zero] at bound
    contradiction
  rw [returnReady_prefix shape path room]
  simp only [returnCaller, beq_iff_eq, nonzero, ite_false]
  exact facts

theorem returnReady_finished {s : Array UInt64} {cap : Nat} {stop value : UInt64}
    {frames : List UInt64} (shape : Shape s cap)
    (path : Prefix s cap stop (read s 2) frames 0) (room : frames.length ≤ cap) :
    read (returnReady s stop 0 value) 0 = 3 ∧ read (returnReady s stop 0 value) 2 = 0 ∧
    read (returnReady s stop 0 value) 7 = value := by
  rw [returnReady_prefix shape path room]
  exact returnCaller_finished (retireMany_shape shape (fun h member => prefix_handles path member)) value

end Project.Smalltalk.ReturnValue
