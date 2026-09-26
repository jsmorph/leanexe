import Project.ClobDepth.HeapLoop

/-! Compatibility import for the depth fold proof. The allocator-aware loop
in `HeapLoop` replaces the former bump-only invariant: the generated loop
releases superseded level buffers and can reuse those chunks. -/
