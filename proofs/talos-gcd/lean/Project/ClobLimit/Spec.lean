import Project.ClobLimit.Model
import Project.ClobLimit.Program
import Project.ClobLimit.ValidOrder
import Project.ClobLimit.Invalid
import Project.ClobLimit.FindBestWrapper
import Project.ClobLimit.InternalEarlyExit
import Project.ClobLimit.InternalIteration
import Project.ClobLimit.InternalBookBump
import Project.ClobLimit.InternalFullBookBump
import Project.ClobLimit.InternalTradeBump
import Project.ClobLimit.InternalPartialBookPrepare
import Project.ClobLimit.InternalPartialBookControl
import Project.ClobLimit.InternalPartialBookAllocPrepare
import Project.ClobLimit.InternalPartialBookAlloc

/-!
# Specification for `clob_limit`
-/

namespace Project.ClobLimit

open Wasm

/-!
The artifact proof will relate exported function 21 to `Model.limitL` for every
represented input.  Its branch theorems will state result ownership, allocator
counters, page preservation, and a budgeted memory frame.  The validity,
invalid-result, embedded search, and internal early-exit subsystems are
complete.  The internal iteration control is proved through selected-maker
quantity dispatch, and all three empty-free-list allocator layouts have exact
store theorems.  The partial-fill book prefix proves the maker reads and
replacement-book bounds guard, and its control theorem enters the opaque
one-result update branch.  The partial-book allocator prefix computes the
aligned capacity and initializes its free-list scan, and the empty-list
composition returns the exact bump store and result frame.  This module
remains outside `Project.lean` until the exported theorem is complete.
-/

end Project.ClobLimit
