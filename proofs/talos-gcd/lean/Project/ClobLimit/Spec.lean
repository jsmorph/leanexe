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
import Project.ClobLimit.InternalFullBookAllocPrepare
import Project.ClobLimit.InternalFullBookAlloc
import Project.ClobLimit.InternalFullBookPrefix
import Project.ClobLimit.InternalFullBookSuffix
import Project.ClobLimit.InternalFullBookUpdate
import Project.ClobLimit.InternalFullTradePrepare
import Project.ClobLimit.InternalFullTradeFinish
import Project.ClobLimit.InternalFullTradeUpdate
import Project.ClobLimit.InternalFullBookTrade
import Project.ClobLimit.InternalFullTransition
import Project.ClobLimit.InternalFullBranch
import Project.ClobLimit.InternalLoopControl
import Project.ClobLimit.InternalLoopInvariant
import Project.ClobLimit.InternalLoopBounds
import Project.ClobLimit.InternalLoopProgress
import Project.ClobLimit.InternalLoopCompletion
import Project.ClobLimit.InternalLoopAdvance
import Project.ClobLimit.InternalLoopBranches
import Project.ClobLimit.InternalLoopIteration
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
erased length and exact prefix and suffix copy ranges.  Its allocator prefix
computes the aligned stride-five capacity, then composes the empty free-list
scan and bump fallback.  The following loop stores the smaller length and
copies every word before the erased maker, and the shifted-suffix loop
reconstructs the represented erased book.  Their composition retains both
owned books and the exact allocator state.  The following prefix reads the
full maker trade and prepares the shared trade append frame, and the following
suffix records the new trades and next remaining quantity.  Their composition
retains both books and both trade arrays while returning the semantic full-fill
trade, exact allocator state, and reduced remaining quantity.  The complete
book-and-trade composition carries both bump allocations through the generated
nested result branches and preserves bytes below the old heap top.  The
recursive transition copies that state into the loop parameters and decrements
the fuel parameter.  The complete full-fill branch composes those boundaries
and returns the recursive state with both semantic replacement arrays, both
source arrays, exact allocator counters, unchanged pages, and the below-heap
memory frame.  The outer loop guard and five-result epilogue have exact theorems
for completed and zero-fuel exits.  A separately compiled invariant states
source progress, owner-and-pointer locals, array ownership, exact allocator
globals, pages, below-initial-heap equality, and a fixed per-step budget for
running and completed states.  Its bound theorem derives every branch length,
byte, no-wrap, page-fit, and two-allocation budget premise from one nonzero-fuel
running state.  Source-progress theorems normalize stopped, partial-fill, and
full-fill outcomes against the residual list model and its allocation counter.
Completed-state constructors establish the invariant after stopped and
partial-fill outcomes while retaining exact memory and allocator facts.
The full-fill result and recursive transition also retain the four typed
allocator scratch locals and zero completion flag required by the next
iteration.
The full-fill successor constructor establishes the complete running invariant,
including source progress, heap monotonicity, counters, and remaining budget.
Branch-composition theorems connect both allocation-bearing dispatcher paths to
their completed or next-running invariant and prove strict measure decrease.
The complete dispatcher composition preserves the invariant through stopped,
partial-fill, and full-fill outcomes with the same decrease.
The proof remains outside `Project.lean` until the exported theorem is complete.
-/

end Project.ClobLimit
