import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

/-! Exact cover by Algorithm X with dancing links, TAOCP §7.2.2.1.  The input `x` holds the number
of items `N = x[0]` and then the options, each a run of nonzero item numbers, the runs separated by
zeros.  The program keeps Knuth's two tables in one array `t`.  Node `p` occupies the words `3p`,
`3p + 1`, and `3p + 2`, its `TOP`, `ULINK`, and `DLINK`, for the nodes 0 to `Z`.  Node 0 belongs
to no list, and its words start at 0.  Node `i` for `1 ≤ i ≤ N` is the header of item `i`'s
list and keeps the list's length `LEN` in `TOP`.  Node `N + 1` is a spacer, the nodes of each
option follow in order, and a spacer follows every option, the last at node `Z`.  The `TOP` of an
option's node is its item, and the `TOP` of a spacer is 0, where Knuth numbers the spacers with
nonpositive values, which his program DLX1 reads only to print an option.  A spacer's `ULINK` is
the first node of the option before it, and its `DLINK` is the last node of the option after it,
except that the first spacer's `ULINK` and the last spacer's `DLINK` are 0.  The links of the items
follow the nodes: `LLINK` and `RLINK` of item `i`, for `0 ≤ i ≤ N`, are the words `b + 2i` and
`b + 2i + 1`, where `b = 3(Z + 1)`, and item 0 heads the doubly linked list of the active items.

The search is the recursive `search(k)` of Knuth's paper "Dancing Links", where TAOCP writes steps
X1 to X8 with an explicit stack of choices.  The recursion takes one level for each chosen option,
so the compiler's limit of 1,000 nested calls bounds the number of items by 998.  One array, in
place of Knuth's two tables, keeps the frame of the recursive `search` within the 32 positions
that the compiler allows, since a tuple that holds two arrays takes a position for each of its
nested pairs.  Each traversal is a `repeatWhile` whose fuel is the size of `t`, more than the
length of any list.  The state of the traversals of `hide`, `unhide`, `hideColumn`, `unhideColumn`,
`coverOthers`, and `uncoverOthers` holds the current node and the array. -/

namespace Library.Combinatorics.DancingLinks

open LeanExe

/-- The largest number of items: `count` calls `search` at depth 1, the search at level `l` runs
at depth `l + 1`, and the levels run from 0 to `N`, so `N ≤ 998` keeps every call below the
compiler's depth limit of 1,000. -/
def itemLimit : UInt64 := 998

/-- Knuth's `hide(p)`: removes each other node `q` of the option of node `p` from its item's list,
from `p + 1` onward, by `DLINK(ULINK(q)) ← DLINK(q)` and `ULINK(DLINK(q)) ← ULINK(q)`, and
decreases that item's `LEN`.  At a spacer, `ULINK` leads back to the first node of the option, so
the traversal goes around the option and stops at `p`. -/
def hide (p : UInt64) (t : Array UInt64) : Array UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (p + 1, t) (fun s => s.1 ≠ p) fun s =>
    let x := s.2[(3 * s.1).toNat]!
    let u := s.2[(3 * s.1 + 1).toNat]!
    let d := s.2[(3 * s.1 + 2).toNat]!
    let len := s.2[(3 * x).toNat]!
    if x = 0 then (u, s.2)
    else (s.1 + 1, ((s.2.set! (3 * u + 2).toNat d).set! (3 * d + 1).toNat u).set! (3 * x).toNat
      (len - 1))).2

/-- Knuth's `unhide(p)`: puts back each other node `q` of the option of node `p`, from `p - 1`
backward, the reverse of the order of `hide`, by `DLINK(ULINK(q)) ← q` and `ULINK(DLINK(q)) ← q`,
and increases that item's `LEN`.  The node's own links still name the neighbors it had when `hide`
removed it.  At a spacer, `DLINK` leads forward to the last node of the option. -/
def unhide (p : UInt64) (t : Array UInt64) : Array UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (p - 1, t) (fun s => s.1 ≠ p) fun s =>
    let x := s.2[(3 * s.1).toNat]!
    let u := s.2[(3 * s.1 + 1).toNat]!
    let d := s.2[(3 * s.1 + 2).toNat]!
    let len := s.2[(3 * x).toNat]!
    if x = 0 then (d, s.2)
    else (s.1 - 1, ((s.2.set! (3 * u + 2).toNat s.1).set! (3 * d + 1).toNat s.1).set! (3 * x).toNat
      (len + 1))).2

/-- The loop of Knuth's `cover(i)`: hides each option in item `i`'s list, from the top down.  The
list of `i` itself does not change, since no option holds `i` twice. -/
def hideColumn (i : UInt64) (t : Array UInt64) : Array UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (t[(3 * i + 2).toNat]!, t) (fun s => s.1 ≠ i) fun s =>
    let u := hide s.1 s.2
    (u[(3 * s.1 + 2).toNat]!, u)).2

/-- The loop of Knuth's `uncover(i)`: unhides each option in item `i`'s list, from the bottom up,
the reverse of the order of `hideColumn`. -/
def unhideColumn (i : UInt64) (t : Array UInt64) : Array UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (t[(3 * i + 1).toNat]!, t) (fun s => s.1 ≠ i) fun s =>
    let u := unhide s.1 s.2
    (u[(3 * s.1 + 1).toNat]!, u)).2

/-- Removes item `i` from the list of active items: `RLINK(LLINK(i)) ← RLINK(i)` and
`LLINK(RLINK(i)) ← LLINK(i)`, in the item links at `b`. -/
def unlinkItem (b i : UInt64) (t : Array UInt64) : Array UInt64 :=
  let l := t[(b + 2 * i).toNat]!
  let r := t[(b + 2 * i + 1).toNat]!
  (t.set! (b + 2 * l + 1).toNat r).set! (b + 2 * r).toNat l

/-- Puts item `i` back into the list of active items between the neighbors that its own links
still name: `RLINK(LLINK(i)) ← i` and `LLINK(RLINK(i)) ← i`. -/
def relinkItem (b i : UInt64) (t : Array UInt64) : Array UInt64 :=
  let l := t[(b + 2 * i).toNat]!
  let r := t[(b + 2 * i + 1).toNat]!
  (t.set! (b + 2 * l + 1).toNat i).set! (b + 2 * r).toNat i

/-- Knuth's `cover(i)`: hides each option in the list of item `i`, and then removes `i` from the
list of active items. -/
def coverItem (b i : UInt64) (t : Array UInt64) : Array UInt64 := unlinkItem b i (hideColumn i t)

/-- Knuth's `uncover(i)`: puts item `i` back into the list of active items, and then unhides each
option in its list, the reverse of the order of `coverItem`. -/
def uncoverItem (b i : UInt64) (t : Array UInt64) : Array UInt64 :=
  unhideColumn i (relinkItem b i t)

/-- Step X5 for the option of node `r`: covers the items of the option's other nodes, from `r + 1`
onward around the option. -/
def coverOthers (b r : UInt64) (t : Array UInt64) : Array UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (r + 1, t) (fun s => s.1 ≠ r) fun s =>
    let j := s.2[(3 * s.1).toNat]!
    let u := s.2[(3 * s.1 + 1).toNat]!
    if j = 0 then (u, s.2) else (s.1 + 1, coverItem b j s.2)).2

/-- Step X6 for the option of node `r`: uncovers the items of the option's other nodes, from
`r - 1` backward around the option, the reverse of the order of `coverOthers`. -/
def uncoverOthers (b r : UInt64) (t : Array UInt64) : Array UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (r - 1, t) (fun s => s.1 ≠ r) fun s =>
    let j := s.2[(3 * s.1).toNat]!
    let d := s.2[(3 * s.1 + 2).toNat]!
    if j = 0 then (d, s.2) else (s.1 - 1, uncoverItem b j s.2)).2

/-- Step X3 with Knuth's minimum-remaining-values heuristic: the active item whose list is
shortest, the leftmost of those that tie, as DLX1 chooses.  The state holds the item `p` to
inspect, the best item so far, 0 before the first, and its length. -/
def choose (b : UInt64) (t : Array UInt64) : UInt64 :=
  let n := t.size.toUInt64
  (repeatWhile n (t[(b + 1).toNat]!, (0 : UInt64), (0 : UInt64)) (fun s => s.1 ≠ 0)
    fun s =>
      let len := t[(3 * s.1).toNat]!
      (t[(b + 2 * s.1 + 1).toNat]!, if s.2.1 = 0 ∨ len < s.2.2 then s.1 else s.2.1,
        if s.2.1 = 0 ∨ len < s.2.2 then len else s.2.2)).2.1

/-- The end of one pass of the search's loop over the column of the chosen item: step X6 for the
option of node `r`, by `uncoverOthers`, and then the next node `DLINK(r)` of the column, the count
`acc` increased by the option's covers `c`, and the array.  A separate function keeps these values
out of the frame of the recursive `search`. -/
def next (b r acc c : UInt64) (t : Array UInt64) : UInt64 × UInt64 × Array UInt64 :=
  let v := uncoverOthers b r t
  (v[(3 * r + 2).toNat]!, acc + c, v)

/-- The number of exact covers of the active items by the options that are not hidden, modulo
`2^64`, and the array, which the search restores.  `d` bounds the depth, and the item links begin
at `b`.  When no item is active, the empty set of options is the one cover, and the result is 1.
Otherwise the search chooses an item `i` by step X3, covers it, and for each option `r` in its
list covers the option's other items by step X5, counts the covers of the rest by recursion, and
uncovers them by step X6, and at the end uncovers `i`, as in Knuth's `search(k)`.  The loop's
state holds the node `r`, the count so far, and the array, and the loop starts at `DLINK(i)`,
which covering `i` leaves unchanged.  `d` starts at `N` and decreases at each level, so the
recursion terminates on any array, and on a valid input the active items never outnumber `d`, so
the branch `d = 0` with an active item, which returns 0, never runs. -/
def search (d b : UInt64) (t : Array UInt64) : UInt64 × Array UInt64 :=
  if _h : t[(b + 1).toNat]! = 0 ∨ d = 0 then (if t[(b + 1).toNat]! = 0 then 1 else 0, t)
  else
    let i := choose b t
    let s := repeatWhile t.size.toUInt64 (t[(3 * i + 2).toNat]!, (0 : UInt64), coverItem b i t)
      (fun s => s.1 ≠ i) fun s =>
        let u := search (d - 1) b (coverOthers b s.1 s.2.2)
        next b s.1 s.2.1 u.1 u.2
    (s.2.1, uncoverItem b i s.2.2)
termination_by d.toNat
decreasing_by
  have hd : d ≠ 0 := fun e => _h (Or.inr e)
  simp only [ne_eq, ← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hd ⊢
  omega

/-- The number of nodes after the first spacer: one for each nonzero word after `x[0]`, and one
spacer for each option, counted at the option's first word.  The loop's state is the count. -/
def nodeCount (x : Array UInt64) : UInt64 :=
  loop x.size.toUInt64 (0 : UInt64) fun k c =>
    let w := x[k.toNat]!
    let prev := x[(k - 1).toNat]!
    if k = 0 ∨ w = 0 then c else if k = 1 ∨ prev = 0 then c + 2 else c + 1

/-- Step X1: the array of `b + 2(N + 1)` words that holds the nodes and the item links for the
input `x`, with `b = 3(Z + 1)`.  It starts with each header's list empty, `LEN(i) = 0` and
`ULINK(i) = DLINK(i) = i`, the words of every other node 0, and the items linked in order from 0
to `N` and around.  The loop reads the words after `x[0]`, and its state holds the latest spacer,
the next node `p`, the first node of the current option, or 0 between options, and the array.  A
nonzero word `w` becomes node `p` with `TOP(p) = w`, at the bottom of item `w`'s list, and
increases `LEN(w)`.  A zero after an option's nodes makes node `p` the next spacer, with `ULINK(p)`
the option's first node, and sets the `DLINK` of the spacer before the option to the option's last
node `p - 1`, and any other zero changes nothing.  An input that ends inside an option gets the
same spacer after the loop. -/
def build (b : UInt64) (x : Array UInt64) : Array UInt64 :=
  let n := x[(0 : UInt64).toNat]!
  let t := LeanExe.build (b + 2 * (n + 1)) fun k =>
    if b ≤ k then
      (if (k - b) % 2 = 0 then (if k = b then n else (k - b) / 2 - 1)
       else (if (k - b) / 2 = n then 0 else (k - b) / 2 + 1))
    else if k % 3 = 0 ∨ n < k / 3 ∨ k / 3 = 0 then 0 else k / 3
  let s := loop x.size.toUInt64 (n + 1, n + 2, (0 : UInt64), t) fun k s =>
    let w := x[k.toNat]!
    let spacer := s.1
    let p := s.2.1
    let first := s.2.2.1
    let t := s.2.2.2
    let up := t[(3 * w + 1).toNat]!
    let len := t[(3 * w).toNat]!
    if k = 0 ∨ (w = 0 ∧ first = 0) then s
    else if w = 0 then
      (p, p + 1, 0, (t.set! (3 * p + 1).toNat first).set! (3 * spacer + 2).toNat (p - 1))
    else
      (spacer, p + 1, if first = 0 then p else first,
        ((((t.set! (3 * p).toNat w).set! (3 * p + 1).toNat up).set! (3 * p + 2).toNat w).set!
          (3 * up + 2).toNat p |>.set! (3 * w + 1).toNat p).set! (3 * w).toNat (len + 1))
  let t := s.2.2.2
  let p := s.2.1
  let first := s.2.2.1
  if first = 0 then t else (t.set! (3 * p + 1).toNat first).set! (3 * s.1 + 2).toNat (p - 1)

/-- The number of exact covers of the items `1..N` by the options of `x`, modulo `2^64`, for a
valid input: step X1 builds the array, with the item links at `b = 3(N + 2 + nodeCount x)`, and
`search` counts from depth bound `N`. -/
def count (x : Array UInt64) : UInt64 :=
  let n := x[(0 : UInt64).toNat]!
  let b := 3 * (n + 2 + nodeCount x)
  (search n b (build b x)).1

/-- 1 when `N ≤ 998`, every item of every option lies in `1..N`, and no option repeats an item,
and 0 otherwise.  It tests `N` before it allocates the mark array of `N + 1` words.  The loop's
state holds the number of the current option, which each zero increases, a flag that becomes 0 at
the first defect, and the marks, where `marks[w]` is the number of the last option that held `w`,
so that an item seen again in the same option finds its own option's number. -/
def valid (x : Array UInt64) : UInt64 :=
  let n := x[(0 : UInt64).toNat]!
  if itemLimit < n then 0
  else
    let marks := LeanExe.build (n + 1) fun _ => 0
    (loop x.size.toUInt64 ((1 : UInt64), (1 : UInt64), marks) fun k s =>
      let w := x[k.toNat]!
      let seen := s.2.2[w.toNat]!
      if k = 0 then s
      else if w = 0 then (s.1 + 1, s.2.1, s.2.2)
      else (s.1, if n < w ∨ seen = s.1 then 0 else s.2.1, s.2.2.set! w.toNat s.1)).2.1

end Library.Combinatorics.DancingLinks
