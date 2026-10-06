import Project.Smalltalk.FillLoop

namespace Project.Smalltalk.ObjectConstruction
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.AllocationEffect
open Project.Smalltalk.ConstructionValues

theorem newReady_eq (s : Array UInt64) (classId metaId fields : UInt64) :
    newReady s classId metaId fields =
      write (allocate (FillLoop.filling s fields).2 4 classId (read (FillLoop.filling s fields).2 19)
        metaId 0 0 0) 19 0 := by
  rw [FillLoop.filling_eq_pair]
  rfl

theorem object_references {s : Array UInt64} {cap : Nat} {classId metaId head : UInt64}
    (links : Matches s cap 7 head) : HeapAllocation.References s cap 4 classId head metaId 0 0 0 := by
  intro k _ pointer nonzero
  have offset : k = 3 := by simpa [PointerField] using pointer
  subst k
  exact StackPush.value_nonzero (matches_value links (by decide)) nonzero

theorem object_typed_references {s : Array UInt64} {cap : Nat} {classId metaId head : UInt64}
    (links : Matches s cap 7 head) : TypedAllocation.References s cap 4 classId head metaId 0 0 0 := by
  intro k _ expected required
  have both : k = 3 ∧ expected = 7 := by simpa [Required] using required
  rcases both with ⟨rfl, rfl⟩
  exact links

structure Effect (original t : Array UInt64) (cap : Nat) (classId metaId : UInt64) (fields : Nat) : Prop where
  heap : Heap.Valid t cap
  typed : PointerTypes.Valid t cap
  handle : Handle cap (read t 10)
  tag : field t (read t 10) 0 = 4
  classId : field t (read t 10) 2 = classId
  metaId : field t (read t 10) 4 = metaId
  fieldValues : Values t cap (field t (read t 10) 3) (List.replicate fields 1)
  scratch : read t 19 = 0
  count : (read t 9).toNat + fields + 1 = (read original 9).toNat
  previous : ∀ h, Handle cap h → field original h 0 ≠ 0 → ∀ k : UInt64, k.toNat < 8 → field t h k = field original h k
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read t r = read original r

theorem newReady_effect {s : Array UInt64} {cap : Nat} {classId metaId fields : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (budget : fields.toNat + 1 ≤ (read s 9).toNat) :
    Effect s (newReady s classId metaId fields) cap classId metaId fields.toNat := by
  let t := (FillLoop.filling s fields).2
  have filled := FillLoop.filling_progress valid typed budget
  have visits := FillLoop.filling_index valid budget
  have before : (read t 9).toNat + fields.toNat = (read s 9).toNat := by
    have count := filled.count
    rw [visits] at count
    exact count
  have enough : (1 : UInt64) ≤ read t 9 := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ (read t 9).toNat
    omega
  have values := FillLoop.filling_values valid typed budget
  have links : Matches t cap 7 (read t 19) := head_matches values
  rcases filled.heap.2 with ⟨nodes, free⟩
  rcases free_nonempty free enough with ⟨head, rest, eq⟩
  subst nodes
  let q := allocate t 4 classId (read t 19) metaId 0 0 0
  have refs := object_references links (classId := classId) (metaId := metaId)
  have allocation : AllocationEffect.Effect t q cap 4 classId (read t 19) metaId 0 0 0 :=
    allocate_effect filled.heap.1 free 4 classId (read t 19) metaId 0 0 0 (by simp [ValidTag]) refs
  have objectTyped := TypedAllocation.allocate_typed filled.heap.1 filled.typed free
    4 classId (read t 19) metaId 0 0 0 (by simp [ValidTag]) refs (object_typed_references links)
  have remaining := (FreeList.allocate_valid filled.heap.1.1 free 4 classId (read t 19) metaId 0 0 0 (by decide)).2
  have objectRead : read (write q 19 0) 10 = read t 8 := by
    rw [read_write_other _ _ _ _ (show (19 : UInt64) ≠ 10 by decide), allocation.last]
  have words := fun (k : UInt64) (bound : k.toNat < 8) =>
    show field (write q 19 0) (read t 8) k = Allocation.allocatedWord 4 classId (read t 19) metaId 0 0 0 k from by
      rw [field_write_register allocation.heap.1.1 allocation.handle bound (show (19 : UInt64).toNat < 24 by decide), allocation.words k bound]
  rw [newReady_eq]
  change Effect s (write q 19 0) cap classId metaId fields.toNat
  refine ⟨HeapWrite.write_register_valid allocation.heap (show (19 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (by intro root; simp at root),
    PointerTypes.write_register_valid allocation.heap.1.1 objectTyped (show (19 : UInt64).toNat < 24 by decide),
    objectRead ▸ allocation.handle, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [objectRead, words 0 (by decide)]; rfl
  · rw [objectRead, words 2 (by decide)]; rfl
  · rw [objectRead, words 4 (by decide)]; rfl
  · rw [objectRead, words 3 (by decide)]
    apply transfer values
    intro h handle tag k bound
    rw [field_write_register allocation.heap.1.1 handle bound (show (19 : UInt64).toNat < 24 by decide)]
    exact allocation.previous h handle (by rw [tag]; decide) k bound
  · exact read_write_same _ _ _ (register_bound allocation.heap.1.1 (show (19 : UInt64).toNat < 24 by decide))
  · rw [read_write_other _ _ _ _ (show (19 : UInt64) ≠ 9 by decide), remaining.2.1]
    rw [free.2.1, List.length_cons] at before
    omega
  · intro h handle allocated k bound
    have currentAllocated : field t h 0 ≠ 0 := by
      rw [filled.previous h handle allocated 0 (by decide)]
      exact allocated
    rw [field_write_register allocation.heap.1.1 handle bound (show (19 : UInt64).toNat < 24 by decide)]
    exact (allocation.previous h handle currentAllocated k bound).trans (filled.previous h handle allocated k bound)
  · intro r bound h8 h9 h10 h13 h17 h19
    rw [read_write_other _ _ _ _ (Ne.symm h19), allocation.registers r bound h8 h9 h10 h13 h17]
    exact filled.registers r bound h8 h9 h10 h13 h17 h19

end Project.Smalltalk.ObjectConstruction
