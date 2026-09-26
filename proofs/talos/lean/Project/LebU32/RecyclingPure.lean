import Project.LebU32.RecyclingFrame

namespace Project.LebU32.Recycling
open Spec

theorem encode_length (n : UInt64) (hn : n.toNat < 4294967296) : (lebList 10 n).length ≤ 5 := by
  apply lebList_length_of_lt 10 5 n (by decide) _ (by decide) (by decide)
  norm_num
  omega

theorem push_list (bytes : ByteArray) (byte : UInt8) :
    (bytes.push byte).data.toList = bytes.data.toList ++ [byte] := by simp

theorem split_final (target : List UInt8) (bytes : ByteArray) (fuel : Nat) (v : UInt64)
    (hFuel : 0 < fuel) (hSplit : target = bytes.data.toList ++ lebList fuel v)
    (hRest : v / 128 = 0) : target = (bytes.push (v % 128).toUInt8).data.toList := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rw [hSplit, lebList_final _ _ hRest, push_list]

theorem split_cont (target : List UInt8) (bytes : ByteArray) (fuel : Nat) (v : UInt64)
    (hFuel : 0 < fuel) (hSplit : target = bytes.data.toList ++ lebList fuel v)
    (hRest : v / 128 ≠ 0) :
    target = (bytes.push (v % 128 + 128).toUInt8).data.toList ++ lebList (fuel - 1) (v / 128) := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rw [hSplit, lebList_cont _ _ hRest, push_list]
  simp only [Nat.succ_sub_one, Nat.add_sub_cancel, List.append_assoc, List.singleton_append]

#print axioms encode_length
#print axioms split_final
#print axioms split_cont
end Project.LebU32.Recycling
