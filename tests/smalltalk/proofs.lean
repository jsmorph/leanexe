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
