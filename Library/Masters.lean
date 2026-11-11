import Library.Arrays.BinarySearch.Master
import Library.Arrays.Filter.Master
import Library.Arrays.Range.Master
import Library.Arrays.Repeat.Master
import Library.Arrays.Search.Master
import Library.Arrays.Word.Master
import Library.Combinatorics.DancingLinks.Master
import Library.Combinatorics.NextPermutation.Master
import Library.Graphs.Dijkstra.Master
import Library.Graphs.TopologicalSort.Master
import Library.Graphs.UnionFind.Master
import Library.Graphs.WeightedUnionFind.Master
import Library.HashTables.LinearProbing.Master
import Library.Hashing.Crc.Bitwise.Master
import Library.Hashing.Crc.Master
import Library.Hashing.Hmac.Master
import Library.Hashing.Sha256.Master
import Library.Hashing.Sha3.Master
import Library.Hashing.Sha512.Master
import Library.Hashing.SipHash.Master
import Library.Hashing.XxHash64.Master
import Library.Lists.Word.Master
import Library.Numerics.Arithmetic.BinaryGcd.Master
import Library.Numerics.Arithmetic.CeilSqrt.Master
import Library.Numerics.Arithmetic.Fma.Master
import Library.Numerics.Arithmetic.Gcd.Master
import Library.Numerics.Arithmetic.MillerRabin.Master
import Library.Numerics.Arithmetic.ModInverse.Master
import Library.Numerics.Arithmetic.PrimeFactors.Master
import Library.Numerics.Arithmetic.Sieve.Master
import Library.Numerics.Arithmetic.Uscale.Master
import Library.Numerics.Bounds.Master
import Library.Numerics.Float64.Exp.Master
import Library.Numerics.Interval.Master
import Library.Numerics.Limiters.Minmod.Master
import Library.Numerics.MultiPrecision.Master
import Library.Queues.BinaryHeap.Master
import Library.Random.Lcg.Master
import Library.Random.ParkMiller.Master
import Library.Random.Sampling.Master
import Library.Random.SplitMix64.Master
import Library.Random.Xorshift.Master
import Library.Regex.Master
import Library.Sorting.Find.Master
import Library.Sorting.Heapsort.Master
import Library.Sorting.Insertion.Master
import Library.Sorting.MergeSort.Master
import Library.Sorting.Quicksort.Master
import Library.Sorting.RadixSort.Master
import Library.Sorting.Shellsort.Master
import Library.Sorting.StraightInsertion.Master
import Library.Strings.Kmp.Master
import Library.Trees.Avl.Master
import Library.Trees.AvlDelete.Master
import Library.Trees.Search.Master
import Library.Trees.WordTree.Master

/-! The registry of the library's master theorems: one `Verified.Master` statement for each
function of the library sections of the algorithm index.  `master_registry` checks that each name
is such a statement, and `tools/source-layout` checks that every `*_master` theorem of the library
is listed here and that the index names it. -/

master_registry [
  Library.Arrays.BinarySearch.lowerBound_master,
  Library.Arrays.Filter.removeAll_master,
  Library.Arrays.Filter.below_master,
  Library.Arrays.Filter.clearUntil_master,
  Library.Arrays.Range.evens_master,
  Library.Arrays.Repeat.repeated_master,
  Library.Arrays.Search.count_master,
  Library.Arrays.Search.firstAbove_master,
  Library.Arrays.Search.firstZero_master,
  Library.Arrays.Word.scaled_master,
  Library.Combinatorics.DancingLinks.count_master,
  Library.Combinatorics.DancingLinks.valid_master,
  Library.Combinatorics.NextPermutation.nextPerm_master,
  Library.Graphs.Dijkstra.dijkstra_master,
  Library.Graphs.TopologicalSort.topoSort_master,
  Library.Graphs.UnionFind.classes_master,
  Library.Graphs.WeightedUnionFind.classes_master,
  Library.HashTables.LinearProbing.hashTable_master,
  Library.Hashing.Crc.Bitwise.crc32Reg_master,
  Library.Hashing.Crc.Bitwise.crc32Byte_master,
  Library.Hashing.Crc.Bitwise.crc32Word_master,
  Library.Hashing.Crc.crc32_master,
  Library.Hashing.Crc.crc32c_master,
  Library.Hashing.Crc.crc32Update_master,
  Library.Hashing.Crc.crc32cUpdate_master,
  Library.Hashing.Hmac.hmacSha256_master,
  Library.Hashing.Hmac.hmacSha512_master,
  Library.Hashing.Sha256.sha256_master,
  Library.Hashing.Sha256.sha224_master,
  Library.Hashing.Sha3.sha3_224_master,
  Library.Hashing.Sha3.sha3_256_master,
  Library.Hashing.Sha3.sha3_384_master,
  Library.Hashing.Sha3.sha3_512_master,
  Library.Hashing.Sha3.shake128_master,
  Library.Hashing.Sha3.shake256_master,
  Library.Hashing.Sha512.sha512_master,
  Library.Hashing.Sha512.sha384_master,
  Library.Hashing.Sha512.sha512_256_master,
  Library.Hashing.Sha512.sha512_224_master,
  Library.Hashing.SipHash.siphash24_master,
  Library.Hashing.SipHash.siphash13_master,
  Library.Hashing.XxHash64.xxh64_master,
  Library.Lists.Word.listSum_master,
  Library.Lists.Word.range_master,
  Library.Lists.Word.sum_master,
  Library.Lists.Word.reverse_master,
  Library.Lists.Word.increment_master,
  Library.Numerics.Arithmetic.BinaryGcd.binaryGcd_master,
  Library.Numerics.Arithmetic.CeilSqrt.ceilSqrt_master,
  Library.Numerics.Arithmetic.Fma.fma_master,
  Library.Numerics.Arithmetic.Gcd.gcd_master,
  Library.Numerics.Arithmetic.MillerRabin.powMod_master,
  Library.Numerics.Arithmetic.MillerRabin.test_master,
  Library.Numerics.Arithmetic.ModInverse.modInverse_master,
  Library.Numerics.Arithmetic.PrimeFactors.compute_master,
  Library.Numerics.Arithmetic.Sieve.primes_master,
  Library.Numerics.Arithmetic.Uscale.mulSmall_master,
  Library.Numerics.Arithmetic.Uscale.shl_master,
  Library.Numerics.Arithmetic.Uscale.le_master,
  Library.Numerics.Arithmetic.Uscale.sub_master,
  Library.Numerics.Arithmetic.Uscale.wordBits_master,
  Library.Numerics.Arithmetic.Uscale.bitLen_master,
  Library.Numerics.Arithmetic.Uscale.divBits_master,
  Library.Numerics.Arithmetic.Uscale.scaledQuot_master,
  Library.Numerics.Arithmetic.Uscale.mulPow10_master,
  Library.Numerics.Arithmetic.Uscale.pow10_master,
  Library.Numerics.Bounds.absBits_master,
  Library.Numerics.Bounds.finite_master,
  Library.Numerics.Bounds.nextUpBits_master,
  Library.Numerics.Bounds.nextDownBits_master,
  Library.Numerics.Bounds.endpoint_master,
  Library.Numerics.Bounds.outAdd_master,
  Library.Numerics.Bounds.outSub_master,
  Library.Numerics.Bounds.outMul_master,
  Library.Numerics.Bounds.outDiv_master,
  Library.Numerics.Bounds.outSqrt_master,
  Library.Numerics.Float64.Exp.exp_master,
  Library.Numerics.Interval.fmin_master,
  Library.Numerics.Interval.fmax_master,
  Library.Numerics.Interval.make_master,
  Library.Numerics.Interval.point_master,
  Library.Numerics.Interval.join_master,
  Library.Numerics.Interval.add_master,
  Library.Numerics.Interval.sub_master,
  Library.Numerics.Interval.neg_master,
  Library.Numerics.Interval.extreme_master,
  Library.Numerics.Interval.mulEnd_master,
  Library.Numerics.Interval.mul_master,
  Library.Numerics.Interval.divEnd_master,
  Library.Numerics.Interval.divCore_master,
  Library.Numerics.Interval.div_master,
  Library.Numerics.Interval.sqrt_master,
  Library.Numerics.Interval.abs_master,
  Library.Numerics.Interval.clamp_master,
  Library.Numerics.Interval.outward2_master,
  Library.Numerics.Interval.increasing_master,
  Library.Numerics.Interval.decreasing_master,
  Library.Numerics.Limiters.Minmod.minmod_master,
  Library.Numerics.MultiPrecision.add_master,
  Library.Numerics.MultiPrecision.sub_master,
  Library.Numerics.MultiPrecision.mul_master,
  Library.Numerics.MultiPrecision.divide_master,
  Library.Queues.BinaryHeap.heapQueue_master,
  Library.Random.Lcg.step_master,
  Library.Random.Lcg.advance_master,
  Library.Random.Lcg.jump_master,
  Library.Random.ParkMiller.step_master,
  Library.Random.ParkMiller.advance_master,
  Library.Random.ParkMiller.seed_master,
  Library.Random.Sampling.shuffle_master,
  Library.Random.Sampling.sample_master,
  Library.Random.Sampling.reservoir_master,
  Library.Random.SplitMix64.splitMix_master,
  Library.Random.SplitMix64.unitFloat_master,
  Library.Random.Xorshift.step_master,
  Library.Random.Xorshift.advance_master,
  Library.Random.Xorshift.jump_master,
  Library.Regex.matchWith_master,
  Library.Sorting.Find.select_master,
  Library.Sorting.Heapsort.heapsort_master,
  Library.Sorting.Insertion.sortInsert_master,
  Library.Sorting.MergeSort.mergeSort_master,
  Library.Sorting.Quicksort.quicksort_master,
  Library.Sorting.RadixSort.radixSort_master,
  Library.Sorting.Shellsort.shellsort_master,
  Library.Sorting.StraightInsertion.straightInsertion_master,
  Library.Strings.Kmp.occurrences_master,
  Library.Trees.Avl.search_master,
  Library.Trees.Avl.insert_master,
  Library.Trees.AvlDelete.delete_master,
  Library.Trees.Search.search_master,
  Library.Trees.Search.insert_master,
  Library.Trees.WordTree.size_master,
  Library.Trees.WordTree.sum_master,
  Library.Trees.WordTree.height_master,
  Library.Trees.WordTree.incr_master,
  Library.Trees.WordTree.setKey_master,
  Library.Trees.WordTree.insert_master,
  Library.Trees.WordTree.leftChild_master,
  Library.Trees.WordTree.splitRoot_master]
