import Project.ClobLimit.Model
import Project.ClobLimit.Program
import Project.ClobLimit.ValidOrder
import Project.ClobLimit.Invalid
import Project.ClobLimit.FindBestWrapper
import Project.ClobLimit.InternalEarlyExit
import Project.ClobLimit.InternalIteration
import Project.ClobLimit.InternalBookBump
import Project.ClobLimit.InternalFullBookBump
import Project.ClobLimit.InternalFullBookPrepare
import Project.ClobLimit.InternalTradeBump
import Project.ClobLimit.InternalPartialBookPrepare
import Project.ClobLimit.InternalPartialBookControl
import Project.ClobLimit.InternalPartialBookAllocPrepare
import Project.ClobLimit.InternalPartialBookAlloc
import Project.ClobLimit.InternalPartialBookCopy
import Project.ClobLimit.InternalPartialBookFinish
import Project.ClobLimit.InternalPartialBookUpdate
import Project.ClobLimit.InternalPartialTradePrepare
import Project.ClobLimit.InternalPartialTradeAllocPrepare
import Project.ClobLimit.InternalPartialTradeAlloc
import Project.ClobLimit.InternalPartialTradeCopy
import Project.ClobLimit.InternalPartialTradeFinish
import Project.ClobLimit.InternalPartialTradeUpdate
import Project.ClobLimit.InternalPartialFinish
import Project.ClobLimit.InternalPartialTradeBranch
import Project.ClobLimit.InternalPartialBranch

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
also proves the replacement-book length initialization and complete payload
copy, followed by the five maker-field stores and returned replacement pointer.
Their composition retains ownership of the source and replacement books and
the allocator memory frame.  The following trade prefix records the replacement
book, reads the maker trade fields, and computes the appended trade length.  It
also computes the aligned stride-four capacity and initializes the trade
free-list scan.  Its empty-list composition returns the exact stride-four bump
store and result frame.  The post-allocation loop initializes the extended
length and copies every old trade word, and the four append stores return the
represented extended array.  Their composition retains the old book, new book,
old trades, and new trades with exact allocator state.  The final partial-fill
assignments record the new trade pointer, zero remaining quantity, and a
completed result in the recursive locals.  Their composition with trade
preparation proves the complete continuation after replacement-book
construction.  The complete partial-fill branch preserves both source arrays,
returns the semantic replacement book and appended trades, and states the
two-allocation heap, counter, page, and below-heap memory facts.  The full-fill
book preparation proves both selected-index bounds checks and computes the
erased length and exact prefix and suffix copy ranges.  The proof remains
outside `Project.lean` until the exported theorem is complete.
-/

end Project.ClobLimit
