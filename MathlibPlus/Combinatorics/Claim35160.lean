import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim35160

/-- A degree-count shift by one raises the sum by the number of entries. -/
theorem shifted_list_sum
    (left right : List ℕ)
    (hzero : right.count 0 = 0)
    (hcount : ∀ d : ℕ, left.count d = right.count (d + 1)) :
    right.sum = left.sum + left.length := by
  have hcount' : ∀ d : ℕ, (left : Multiset ℕ).count d =
      (right : Multiset ℕ).count (d + 1) := by
    intro d
    simpa using hcount d
  have hzero' : (right : Multiset ℕ).count 0 = 0 := by
    simpa using hzero
  have hmult : (right : Multiset ℕ) = (left.map Nat.succ : Multiset ℕ) := by
    apply Multiset.ext.mpr
    intro d
    cases d with
    | zero =>
        simpa using hzero'
    | succ d =>
        by_cases hd : d ∈ (left : Multiset ℕ)
        · have hc := Multiset.count_map_eq_count Nat.succ (left : Multiset ℕ)
              (by intro x hx y hy hxy; exact Nat.succ.inj hxy) d hd
          exact (hcount' d).symm.trans hc.symm
        · have hleft : (left : Multiset ℕ).count d = 0 := by
            exact Multiset.count_eq_zero.mpr hd
          have hnot : Nat.succ d ∉ (left.map Nat.succ : Multiset ℕ) := by
            simpa using hd
          have hmap : (left.map Nat.succ : Multiset ℕ).count (Nat.succ d) = 0 := by
            exact Multiset.count_eq_zero.mpr hnot
          rw [hmap]
          simpa [Nat.succ_eq_add_one, hleft] using (hcount' d).symm
  have hperm : right.Perm (left.map Nat.succ) := by
    exact Multiset.coe_eq_coe.mp hmult
  have hsum := hperm.sum_eq
  have hmap_sum : ∀ l : List ℕ, (l.map Nat.succ).sum = l.sum + l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  exact hsum.trans (hmap_sum left)

end MathlibPlus.Combinatorics.Claim35160
