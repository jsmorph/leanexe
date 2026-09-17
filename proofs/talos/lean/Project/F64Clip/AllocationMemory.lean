import Project.ProofKit.UInt64ArrayAllocation

namespace Project.F64Clip.Spec

abbrev clipCapacity := Project.ProofKit.UInt64ArrayAllocation.capacity
abbrev clipAllocate := Project.ProofKit.UInt64ArrayAllocation.allocate
abbrev clipInitialize := Project.ProofKit.UInt64ArrayAllocation.initialized
abbrev clip_allocation_words := Project.ProofKit.UInt64ArrayAllocation.allocation_words
abbrev clip_capacity_normalized := Project.ProofKit.UInt64ArrayAllocation.capacity_normalized
abbrev clip_allocate_pages := Project.ProofKit.UInt64ArrayAllocation.allocate_pages
abbrev clip_initialize_pages := Project.ProofKit.UInt64ArrayAllocation.initialize_pages
abbrev clip_initialize_prefix := Project.ProofKit.UInt64ArrayAllocation.initialize_prefix
abbrev clip_initialize_input := Project.ProofKit.UInt64ArrayAllocation.initialize_input

end Project.F64Clip.Spec
