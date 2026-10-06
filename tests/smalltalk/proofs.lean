import Project.Smalltalk.Proofs
import Lean.Util.CollectAxioms

-- Reject admitted proofs and additional axioms in every Smalltalk theorem,
-- including the dependencies of the listed results.
run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if (`Project.Smalltalk).isPrefixOf name && info.isTheorem then
      for axiomName in ← Lean.collectAxioms name do
        unless axiomName == `propext || axiomName == `Quot.sound || axiomName == `Classical.choice do
          throwError "{name} depends on forbidden axiom {axiomName}"

#print axioms Project.Smalltalk.Memory.address_toNat
#print axioms Project.Smalltalk.Memory.cell_indices_distinct
#print axioms Project.Smalltalk.Memory.field_write_cell
#print axioms Project.Smalltalk.Allocation.allocateCell_read
#print axioms Project.Smalltalk.Allocation.allocateCell_field
#print axioms Project.Smalltalk.Allocation.allocateCell_preserves_other
#print axioms Project.Smalltalk.Allocation.allocateCell_register
#print axioms Project.Smalltalk.Allocation.allocateCell_shape
#print axioms Project.Smalltalk.FreeList.allocate_valid
#print axioms Project.Smalltalk.FreeList.allocate_empty_preserves_cells
#print axioms Project.Smalltalk.Sweep.finishCollection_preserves_marked
#print axioms Project.Smalltalk.SweepList.finishCollection_freeList
#print axioms Project.Smalltalk.MarkMemory.markReady_preserves_payload
#print axioms Project.Smalltalk.MarkMemory.markReady_work
#print axioms Project.Smalltalk.MarkMemory.mark_new
#print axioms Project.Smalltalk.Clear.cleared_marks
#print axioms Project.Smalltalk.Clear.cleared_payload
#print axioms Project.Smalltalk.Graph.sweep_correct
#print axioms Project.Smalltalk.Worklist.enqueue_room
#print axioms Project.Smalltalk.MarkInvariant.mark_holds
#print axioms Project.Smalltalk.MarkInvariant.roots_holds
#print axioms Project.Smalltalk.Worklist.top_word
#print axioms Project.Smalltalk.Worklist.pop_represents
#print axioms Project.Smalltalk.ScanMemory.scanCell_eq
#print axioms Project.Smalltalk.ScanInvariant.scan_holds
#print axioms Project.Smalltalk.Marking.marking_correct
#print axioms Project.Smalltalk.Collector.collect_correct
#print axioms Project.Smalltalk.Collector.collect_register
#print axioms Project.Smalltalk.CollectorPreservation.collect_valid
#print axioms Project.Smalltalk.CollectorPreservation.collect_reachable
#print axioms Project.Smalltalk.CollectorPreservation.collect_twice_payload
#print axioms Project.Smalltalk.Frame.retire_field
#print axioms Project.Smalltalk.Frame.advance_field
#print axioms Project.Smalltalk.Traversal.walk_path
#print axioms Project.Smalltalk.Traversal.lexical_path
#print axioms Project.Smalltalk.CallChain.onChain_correct
#print axioms Project.Smalltalk.Home.home_correct
#print axioms Project.Smalltalk.ReturnChecks.ret_dead
#print axioms Project.Smalltalk.ReturnChecks.ret_absent
#print axioms Project.Smalltalk.ReturnChecks.ret_accepted
#print axioms Project.Smalltalk.Unwind.unwind_go_prefix
#print axioms Project.Smalltalk.Unwind.returnReady_prefix
#print axioms Project.Smalltalk.Unwind.retireMany_field
#print axioms Project.Smalltalk.ReturnValue.returnCallerReady_delivers
#print axioms Project.Smalltalk.ReturnValue.returnReady_delivers
#print axioms Project.Smalltalk.ReturnValue.returnReady_finished
#print axioms Project.Smalltalk.Heap.fail_valid
#print axioms Project.Smalltalk.Reservation.reserve_correct
#print axioms Project.Smalltalk.Reservation.reserve_register
#print axioms Project.Smalltalk.ReturnReservation.reserve_prefix
#print axioms Project.Smalltalk.ReturnReservation.returnReserved_delivers
#print axioms Project.Smalltalk.ReturnReservation.ret_delivers
#print axioms Project.Smalltalk.ReturnReservation.ret_finished
#print axioms Project.Smalltalk.InitializationBase.capacity_bounds
#print axioms Project.Smalltalk.Seeding.init_cells
#print axioms Project.Smalltalk.InitializationGraph.init_graph_valid
#print axioms Project.Smalltalk.InitializationFree.init_free_list
#print axioms Project.Smalltalk.InitializationFree.init_valid
#print axioms Project.Smalltalk.InitializationFree.collect_init_valid
#print axioms Project.Smalltalk.HeapAllocation.allocate_valid
#print axioms Project.Smalltalk.HeapAllocation.allocateCell_reachable
#print axioms Project.Smalltalk.HeapAllocation.allocate_empty_valid
#print axioms Project.Smalltalk.HeapWrite.write_cell_valid
#print axioms Project.Smalltalk.HeapWrite.write_register_valid
#print axioms Project.Smalltalk.FrameHeap.advance_valid
#print axioms Project.Smalltalk.FrameHeap.retire_valid
#print axioms Project.Smalltalk.Reachability.localSlot_live
#print axioms Project.Smalltalk.Reachability.fieldSlot_live
#print axioms Project.Smalltalk.StackWrite.pop_valid
#print axioms Project.Smalltalk.StackWrite.storeSlot_valid
#print axioms Project.Smalltalk.StackPush.pushReady_delivers
#print axioms Project.Smalltalk.PushReservation.push_correct
#print axioms Project.Smalltalk.PushReservation.loadSlot_valid
#print axioms Project.Smalltalk.LiteralHeap.literalReady_valid
#print axioms Project.Smalltalk.LiteralHeap.literal_block_valid
#print axioms Project.Smalltalk.InstructionHeap.branch_valid
#print axioms Project.Smalltalk.ExecuteHeap.execute_covered_valid
#print axioms Project.Smalltalk.ExecuteHeap.step_covered_valid
#print axioms Project.Smalltalk.Execution.run_resume
#print axioms Project.Smalltalk.Execution.run_stopped
