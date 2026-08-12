import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Claim 47172: splitting a label in a valid partial-sum ordering is controlled
by the new intermediate prefix; the universal ordered pair also contains the
reversed split. -/
theorem split_valid_iff_prefix_absent_claim47172
    {G : Type*} [AddCommGroup G]
    (A C : List G) (u v z : G) (hz : z = u + v)
    (hvalid :
      (List.scanl (fun s a => s + a) 0 (A ++ ([z] ++ C))).tail.Nodup) :
    (List.scanl (fun s a => s + a) 0 (A ++ ([u, v] ++ C))).tail.Nodup ↔
      A.sum + u ∉
        (List.scanl (fun s a => s + a) 0 (A ++ ([z] ++ C))).tail := by
  have hfold :
      List.foldl (fun s a : G => s + a) 0 A = A.sum :=
    List.sum_eq_foldl.symm
  have hscan_ne_nil :
      List.scanl (fun s a : G => s + a) 0 A ≠ [] :=
    List.scanl_ne_nil
  have hold :
      (List.scanl (fun s a => s + a) 0 (A ++ ([z] ++ C))).tail =
        (List.scanl (fun s a => s + a) 0 A).tail ++
          List.scanl (fun s a => s + a) (A.sum + z) C := by
    rw [List.scanl_append, List.tail_append_of_ne_nil hscan_ne_nil]
    simp [List.scanl_cons, hfold]
  have hnew :
      (List.scanl (fun s a => s + a) 0 (A ++ ([u, v] ++ C))).tail =
        (List.scanl (fun s a => s + a) 0 A).tail ++
          (A.sum + u) :: List.scanl (fun s a => s + a) (A.sum + z) C := by
    rw [List.scanl_append, List.tail_append_of_ne_nil hscan_ne_nil]
    simp [List.scanl_cons, hfold, hz, add_assoc]
  have hinsert {L R : List G} {a : G} (hold' : (L ++ R).Nodup) :
      (L ++ a :: R).Nodup ↔ a ∉ L ++ R := by
    rw [List.nodup_middle]
    simp [hold']
  rw [hold] at hvalid
  rw [hnew, hold]
  exact hinsert hvalid

end MathlibPlus.Combinatorics
