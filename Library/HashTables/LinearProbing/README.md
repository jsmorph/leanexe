# LinearProbing: Algorithms L and R of TAOCP §6.4

## Request and specification

[The request](request.txt) asks for a hash table of words with open addressing and linear probing, Knuth's Algorithm L, with deletion by Algorithm R.  The input is the number of slots `M` and then pairs of a code and a key: code 0 inserts, code 1 looks up, and any other code deletes.  The hash of a key is the key modulo `M`, and a table of `M` slots holds at most `M - 1` keys.  Each operation returns 1 when it adds, finds, or removes its key, and 0 otherwise.  [The specification](Spec.lean) runs the operations on a list of distinct keys: `runOps` adds an absent key while the list holds fewer than `M - 1` keys, tests membership, and erases a present key.  The specification fixes the outputs and leaves the hash function and the arrangement of the slots to the program.  A table of `M ≤ 1` slots holds no key, so for `M = 0` and `M = 1` every operation returns 0, and a last word without a partner is no operation.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) runs Algorithm L of §6.4 for every operation and Algorithm R for a deletion.  `slot` performs step L1, which takes the home slot `k % M`, and `probe` performs steps L2 and L3: it compares the key of each occupied slot with `k` and advances to the next slot until it reaches the key or an empty slot.  For code 0, `step` performs step L4: it outputs 0 when the search found the key or `M ≤ n + 1`, where `n` counts the keys, and otherwise writes the key into the empty slot where the search ended and increases `n`.  For a deletion, `step` performs step R1, which empties the key's slot, and `close` performs steps R2 to R4: it inspects the following slots up to the next empty one, and when the search for a key from its home slot passes the empty slot `j`, `move` copies the key to `j` and empties its old slot, which becomes `j`, as step R4 returns to step R1.  `hashTable` runs `step` once for each pair of the input, and the compiler translates the tail recursions of `probe` and `close` into loops, as [the verified compiler manual](../../../docs/verified-manual.md#calls-and-recursion) describes.

The table is an array of `2M` words: slot `s` is occupied when word `2s` is not 0, and then word `2s + 1` holds its key.  Every word, 0 among them, is a possible key, so the occupancy takes a word of its own, and both words of every slot lie in one array, so that a deletion, which moves keys, returns one array.  A deleted key's slot becomes empty, and the table needs no marker for deleted slots, since Algorithm R moves each later key whose search would pass the emptied slot.  The proof's invariant of the table, `Good`, states that the occupied slots hold a permutation of the specification's keys, which number either none or at most `M - 1`, and that every slot from the home slot of an occupied slot's key up to the slot before it is occupied.  The invariant of `probe`, in `probe_spec`, is that every slot it has passed is occupied and holds another key.  The invariant of `close` is `CloseInv`: every slot on the path of a key is occupied, except the empty slot `j` on the path of a key that the scan has not yet inspected.

When the table holds `n` keys, a search inspects at most `n + 1` slots, and at most `n` when it finds its key: it inspects consecutive slots and stops at the first empty one, which exists because a table of `M ≥ 1` slots holds at most `M - 1` keys, so it passes each occupied slot at most once.  The scan of Algorithm R after the deletion of one of `n` keys inspects at most `n` slots and moves at most `n - 1` keys, since each slot it passes holds a different one of the `n - 1` remaining keys.  Every operation starts with a search, an insertion into a full table included, and the keys reach these bounds when they share one home slot.  `probe` and `close` stop after a fuel of `M` slots, which gives Lean's termination check its measure, and the bounds keep both below it.  Knuth's searches move down the table, from slot `i` to slot `i - 1`, and the program's move up, so the test of step R4 appears in mirror image: a key at slot `i` with home slot `r` stays when `r` lies in the slots after `j` up to `i`, which `gap m r i < gap m j i` states, where `gap m a b` counts the steps from slot `a` to slot `b`.

## The module computes the outputs

`verified_compile compiled := [next, probe, move, gap, close, slot, hashTable]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `hashTable` is function 8.  The compiler unfolds `step` into the loop of `hashTable`, whose state owns the outputs and the table, so each operation changes the table in place.  The generated bound counts the output array, the table of `2M` words, which the module allocates before the first operation, and one word of growth for each output.  `close` allocates nothing.

| Theorem | File | Statement |
|---|---|---|
| `adv_dist`, `dist_adv`, `dist_add`, `dist_from_adv` | [The proof](Proof.lean) | Slot arithmetic: `adv m r d` is the slot `d` steps after `r`, and `dist m a b` the steps from `a` to `b`.  `adv m r (dist m r s) = s` and `dist m r (adv m r d) = d`, a slot `p` no farther before `s` than `r` splits the distance from `r` to `s`, and `dist m (adv m r d) s = dist m r s - d` for `d ≤ dist m r s`. |
| `tableKeys_fill` | [The proof](Proof.lean) | Filling an empty slot with a key adds that key to the keys of the occupied slots. |
| `Good.free` | [The proof](Proof.lean) | A table that meets `Good` with at least one slot has an empty slot. |
| `probe_spec`, `slot_spec` | [The proof](Proof.lean) | The search for `k` passes occupied slots that hold other keys and ends at an empty slot or at the slot of `k`, which is occupied exactly when `k` is a key. |
| `insert_good` | [The proof](Proof.lean) | Writing an absent key into the empty slot where its search ends keeps `Good`. |
| `close_spec` | [The proof](Proof.lean) | Algorithm R, from a state that meets `CloseInv`, returns a table that meets `Good`. |
| `delete_good` | [The proof](Proof.lean) | Deleting a key keeps `Good` with that key erased. |
| `step_agrees` | [The proof](Proof.lean) | One operation keeps `Agrees`, the invariant of the loop. |
| `hashTable_eq` | [The proof](Proof.lean) | `hashTable xs = expected xs` for every array with fewer than `2^64` words and `slots xs < 2^63`. |
| `hashTable_export` | [The compilation](Compiled.lean) | Export `hashTable` of `compiled.module` is function 8. |
| `hashTable_call` | [The compilation](Compiled.lean) | Function 8, called from a ready store with `slots xs < 2^63` and room for `compiled.hashTable.bound xs` bytes, returns `expected xs` without a trap and leaves a ready store. |
| `hashTable_file`, `hashTable_file_decode` | [The file theorems](File.lean) | `build/verified/hashTable.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`Agrees` states that the table meets `Good` for the specification's list of keys, that the count `n` is the list's length, and that the outputs so far are the specification's.  `Good.free` gives a table of at least one slot an empty slot, which makes every search end within `M` steps, at the key's slot when the key is present.  `CloseInv` places the empty slot `j` and the next slot `i` to inspect `b` and `a` slots after the slot `j0` where Algorithm R started, with the other slots from `j0` to the slot before `i` occupied.  When the scan reaches an empty slot, no key's path can cross `j`, because that path would also cross the empty slot, so the table meets `Good`.  Slot indices are numbers below `M`, and the proof writes `adv` and `dist` without `%`, so that `omega` decides the slot arithmetic after a split on their cases.  The precondition `slots xs < 2^63` keeps `2M`, `2s + 1`, and `i + M` below `2^64`.  No store could hold a table of `2^63` slots or more, and on such inputs `M + M` wraps.  The axiom report of `hashTable_call` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.HashTables.LinearProbing.Compiled
tests/verified/run.sh --cases hashTable
tests/native/verified.sh --module hashTable
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `probeInputs` in [the case inputs](../../../tests/TestSupport/Modules/LinearProbing.lean): tables of 0, 1, and 2 slots, keys that share a home slot, a cluster that wraps from the last slot to the first, a deletion that moves some keys of a cluster and leaves others, a full table, repeated and absent keys, several deletion codes, and long sequences of arbitrary operations.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each input with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 6.4](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
