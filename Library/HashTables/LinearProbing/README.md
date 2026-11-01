# LinearProbing: Algorithms L and R of TAOCP §6.4

## Request, specification, and program

[The request](request.txt) asks for a hash table of words with open addressing and linear probing, Knuth's Algorithm L, with deletion by Algorithm R.  The input is the number of slots `M` and then pairs of a code and a key: code 0 inserts, code 1 looks up, and any other code deletes.  The hash of a key is the key modulo `M`, and a table of `M` slots holds at most `M - 1` keys.  Each operation returns 1 when it adds, finds, or removes its key, and 0 otherwise.  [The specification](Spec.lean) runs the operations on a list of distinct keys: `runOps` adds an absent key while the list holds fewer than `M - 1` keys, tests membership, and erases a present key.  The specification fixes the outputs and leaves the hash function and the arrangement of the slots to the program.  A table of `M ≤ 1` slots holds no key, so for `M = 0` and `M = 1` every operation returns 0.

[The program](Program.lean) keeps the table in an array of `2M` words: slot `s` is occupied when word `2s` is not 0, and then word `2s + 1` is its key.  `probe` searches from the key's home slot `k % M` through consecutive slots, wrapping from slot `M - 1` to slot 0, until it reaches the key or an empty slot, as Algorithm L does.  An insertion writes the key into the empty slot where its search ends.  A deletion empties the key's slot and runs `close`, Algorithm R, from the next slot: it inspects the following slots up to the next empty one, and when the search for a key from its home slot passes the empty slot `j`, it moves the key to `j`, and the key's old slot becomes the empty slot `j`.  `gap m a b` counts the steps from slot `a` to slot `b`, and a key at slot `i` with home slot `r` stays when `gap m r i < gap m j i`.  Knuth's searches move down the table and these move up, so the conditions of Algorithm R appear in mirror image.  `step` performs one operation on the state of the outputs, the number of keys, and the table, and `hashTable` runs it once for each pair of the input.  The compiler translates the tail recursions of `probe` and `close` into loops, each bounded by `M` steps.

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

`Good` states the invariant of the table: the array holds `2M` words, the occupied slots hold a permutation of the specification's keys, which are distinct and number either none or at most `M - 1`, and every slot from the home slot of an occupied slot's key up to the slot before it is occupied.  The last condition makes the search for a key end at the key's slot, and the bound on the keys leaves an empty slot in a table of at least one slot, `Good.free`, which makes every search end within `M` steps.  `CloseInv` states the invariant of Algorithm R after it started at slot `j0`: the empty slot `j` and the next slot `i` to inspect lie `b` and `a` slots after `j0`, the other slots from `j0` to the slot before `i` are occupied, and every slot on the path of a key is occupied except `j` on the path of a key that lies at or after `i`.  When the scan reaches an empty slot, no key's path can cross `j`, because that path would also cross the empty slot, so the table meets `Good`.  Slot indices are numbers below `M`, and the proof writes `adv` and `dist` without `%`, so that `omega` decides the slot arithmetic after a split on their cases.  The precondition `slots xs < 2^63` keeps `2M`, `2s + 1`, and `i + M` below `2^64`.  No store could hold a table of `2^63` slots or more, and on such inputs `M + M` wraps.  The axiom report of `hashTable_call` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.HashTables.LinearProbing.Compiled
tests/verified/run.sh --cases hashTable
tests/native/verified.sh --module hashTable
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `probeInputs` in [the case inputs](../../../tests/TestSupport/Modules/LinearProbing.lean): tables of 0, 1, and 2 slots, keys that share a home slot, a cluster that wraps from the last slot to the first, a deletion that moves some keys of a cluster and leaves others, a full table, repeated and absent keys, several deletion codes, and long sequences of arbitrary operations.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each input with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, section 6.4](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [W. W. Peterson, Addressing for random-access storage, IBM Journal of Research and Development 1 (1957)](https://doi.org/10.1147/rd.12.0130)
- [Verified Compiler Manual](../../../docs/verified-manual.md)
