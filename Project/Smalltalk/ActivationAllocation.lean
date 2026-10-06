import Project.Smalltalk.BindingLoop

namespace Project.Smalltalk.ActivationAllocation
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.AllocationEffect
open Project.Smalltalk.ConstructionValues Project.Smalltalk.BindingPreservation

theorem frame_references {s : Array UInt64} {cap : Nat} {method pc caller lex slots : UInt64}
    (callerType : Matches s cap 5 caller) (lexType : Matches s cap 5 lex)
    (slotType : Matches s cap 7 slots) : HeapAllocation.References s cap 5 method pc caller lex slots 0 := by
  intro k _ pointer nonzero
  have offset : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by simpa [PointerField] using pointer
  rcases offset with rfl | rfl | rfl | rfl
  · exact StackPush.value_nonzero (matches_value callerType (by decide)) nonzero
  · exact StackPush.value_nonzero (matches_value lexType (by decide)) nonzero
  · exact StackPush.value_nonzero (matches_value slotType (by decide)) nonzero
  · exact False.elim (nonzero rfl)

theorem frame_typed_references {s : Array UInt64} {cap : Nat} {method pc caller lex slots : UInt64}
    (callerType : Matches s cap 5 caller) (lexType : Matches s cap 5 lex)
    (slotType : Matches s cap 7 slots) : TypedAllocation.References s cap 5 method pc caller lex slots 0 := by
  intro k _ expected required
  have offset : ((k = 4 ∨ k = 5) ∧ expected = 5) ∨ ((k = 6 ∨ k = 7) ∧ expected = 7) := by
    simpa [Required] using required
  rcases offset with ⟨offset, rfl⟩ | ⟨offset, rfl⟩
  · rcases offset with rfl | rfl
    · exact callerType
    · exact lexType
  · rcases offset with rfl | rfl
    · exact slotType
    · exact Or.inl rfl

def publish (s : Array UInt64) : Array UInt64 := write (write s 2 (read s 10)) 19 0

theorem publish_valid {s : Array UInt64} {cap : Nat}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (value : HeapWrite.Value s cap (read s 10)) :
    Heap.Valid (publish s) cap ∧ PointerTypes.Valid (publish s) cap := by
  have current := HeapWrite.write_register_valid valid (show (2 : UInt64).toNat < 24 by decide)
    (by decide) (by decide) (by decide) (by intro _; exact value)
  have currentTyped := PointerTypes.write_register_valid valid.1.1 typed (show (2 : UInt64).toNat < 24 by decide)
    (v := read s 10)
  exact ⟨HeapWrite.write_register_valid current (show (19 : UInt64).toNat < 24 by decide)
    (by decide) (by decide) (by decide) (by intro root; simp at root),
    PointerTypes.write_register_valid current.1.1 currentTyped (show (19 : UInt64).toNat < 24 by decide)⟩

theorem publish_field {s : Array UInt64} {cap : Nat} {h k : UInt64}
    (shape : Shape s cap) (handle : Handle cap h) (bound : k.toNat < 8) :
    field (publish s) h k = field s h k := by
  rw [publish, field_write_register (write_shape shape (show (2 : UInt64) ≠ 14 by decide)) handle bound
      (show (19 : UInt64).toNat < 24 by decide)]
  exact field_write_register shape handle bound (show (2 : UInt64).toNat < 24 by decide)

theorem publish_current {s : Array UInt64} {cap : Nat} (shape : Shape s cap) : read (publish s) 2 = read s 10 := by
  rw [publish, read_write_other _ _ _ _ (show (19 : UInt64) ≠ 2 by decide),
    read_write_same _ _ _ (register_bound shape (show (2 : UInt64).toNat < 24 by decide))]

theorem publish_register {s : Array UInt64} {r : UInt64} (notCurrent : r ≠ 2) (notScratch : r ≠ 19) :
    read (publish s) r = read s r := by
  rw [publish, read_write_other _ _ _ _ (Ne.symm notScratch), read_write_other _ _ _ _ (Ne.symm notCurrent)]

structure Effect (s t : Array UInt64) (cap : Nat) (method pc caller lex : UInt64) (values : List UInt64) : Prop where
  heap : Heap.Valid t cap
  typed : PointerTypes.Valid t cap
  handle : Handle cap (read t 2)
  last : read t 10 = read t 2
  tag : field t (read t 2) 0 = 5
  methodId : field t (read t 2) 2 = method
  entryPC : field t (read t 2) 3 = pc
  callerLink : field t (read t 2) 4 = caller
  lexicalLink : field t (read t 2) 5 = lex
  slots : Values t cap (field t (read t 2) 6) values
  stack : field t (read t 2) 7 = 0
  scratch : read t 19 = 0
  count : (read t 9).toNat + 1 = (read s 9).toNat
  previous : Preserved s t cap
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read t r = read s r

theorem allocate_effect {s : Array UInt64} {cap : Nat} {method pc caller lex : UInt64} {values : List UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (callerType : Matches s cap 5 caller) (lexType : Matches s cap 5 lex)
    (slots : Values s cap (read s 19) values) (enough : (1 : UInt64) ≤ read s 9) :
    Effect s (publish (allocate s 5 method pc caller lex (read s 19) 0)) cap method pc caller lex values := by
  have slotType := head_matches slots
  rcases valid.2 with ⟨nodes, free⟩
  rcases free_nonempty free enough with ⟨head, rest, eq⟩
  subst nodes
  let q := allocate s 5 method pc caller lex (read s 19) 0
  have refs := frame_references callerType lexType slotType (method := method) (pc := pc)
  have allocation : AllocationEffect.Effect s q cap 5 method pc caller lex (read s 19) 0 :=
    AllocationEffect.allocate_effect valid.1 free 5 method pc caller lex (read s 19) 0 (by simp [ValidTag]) refs
  have frameTyped := TypedAllocation.allocate_typed valid.1 typed free
    5 method pc caller lex (read s 19) 0 (by simp [ValidTag]) refs
    (frame_typed_references callerType lexType slotType)
  have remaining := (FreeList.allocate_valid valid.1.1 free 5 method pc caller lex (read s 19) 0 (by decide)).2
  have published := publish_valid allocation.heap frameTyped (last_value allocation (by decide))
  have currentRead : read (publish q) 2 = read s 8 := (publish_current allocation.heap.1.1).trans allocation.last
  have words := fun (k : UInt64) (bound : k.toNat < 8) =>
    show field (publish q) (read s 8) k = Allocation.allocatedWord 5 method pc caller lex (read s 19) 0 k from
      (publish_field allocation.heap.1.1 allocation.handle bound).trans (allocation.words k bound)
  refine ⟨published.1, published.2, currentRead ▸ allocation.handle,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [publish_register (by decide) (by decide), currentRead, allocation.last]
  · rw [currentRead, words 0 (by decide)]; rfl
  · rw [currentRead, words 2 (by decide)]; rfl
  · rw [currentRead, words 3 (by decide)]; rfl
  · rw [currentRead, words 4 (by decide)]; rfl
  · rw [currentRead, words 5 (by decide)]; rfl
  · rw [currentRead, words 6 (by decide)]
    apply transfer slots
    intro h handle tag k bound
    rw [publish_field allocation.heap.1.1 handle bound]
    exact allocation.previous h handle (by rw [tag]; decide) k bound
  · rw [currentRead, words 7 (by decide)]; rfl
  · exact read_write_same _ _ _ (register_bound
      (write_shape allocation.heap.1.1 (show (2 : UInt64) ≠ 14 by decide))
      (show (19 : UInt64).toNat < 24 by decide))
  · rw [publish_register (by decide) (by decide), remaining.2.1, free.2.1]
    rfl
  · intro h handle allocated k bound
    rw [publish_field allocation.heap.1.1 handle bound]
    exact allocation.previous h handle allocated k bound
  · intro r bound h2 h8 h9 h10 h13 h17 h19
    rw [publish_register h2 h19]
    exact allocation.registers r bound h8 h9 h10 h13 h17

end Project.Smalltalk.ActivationAllocation
