import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim25555

/-- The one-step cyclic rotation of a family indexed by `Fin n`. -/
def rotate (n : ℕ) {A : Type} (P : Fin n → A) : Fin n → A :=
  fun j => P (finRotate n j)

/-- The alternating boundary sum attached to a cyclic family. -/
def alternatingBoundary (n : ℕ) (P : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, (-1 : ℝ) ^ j.val * P j

lemma finRotate_alternatingSign {n : ℕ} (hn : Even n) (hn0 : 0 < n)
    (j : Fin n) :
    (-1 : ℝ) ^ j.val = -((-1 : ℝ) ^ (finRotate n j).val) := by
  cases n with
  | zero => omega
  | succ n =>
    have hn_even : Even (n + 1) := by simpa using hn
    by_cases hj : j = Fin.last n
    · subst j
      have hn_odd : Odd n := by
        rcases hn_even with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        omega
      simp [finRotate_last, hn_odd.neg_one_pow]
    · have hrot : (finRotate (n + 1) j).val = j.val + 1 :=
        coe_finRotate_of_ne_last hj
      rw [hrot]
      obtain he | ho := Nat.even_or_odd j.val
      · rw [he.neg_one_pow, (he.add_one).neg_one_pow]
        norm_num
      · rw [ho.neg_one_pow, (ho.add_one).neg_one_pow]

theorem rotation_negates_boundary {n : ℕ} (hn : Even n) (hn0 : 0 < n)
    (P : Fin n → ℝ) :
    alternatingBoundary n (rotate n P) =
      -alternatingBoundary n P := by
  have hsign (j : Fin n) := finRotate_alternatingSign hn hn0 j
  unfold alternatingBoundary rotate
  calc
    (∑ j : Fin n, (-1 : ℝ) ^ j.val * P (finRotate n j)) =
        ∑ j : Fin n, -(((-1 : ℝ) ^ (finRotate n j).val) * P (finRotate n j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hsign j]
          ring
    _ = -∑ j : Fin n, ((-1 : ℝ) ^ (finRotate n j).val) * P (finRotate n j) := by
          rw [Finset.sum_neg_distrib]
    _ = -∑ j : Fin n, (-1 : ℝ) ^ j.val * P j := by
          congr 1
          exact Equiv.sum_comp (finRotate n) (fun j : Fin n =>
            (-1 : ℝ) ^ j.val * P j)

end MathlibPlus.Combinatorics.Claim25555
