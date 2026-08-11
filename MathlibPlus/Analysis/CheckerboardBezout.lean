import Mathlib

namespace MathlibPlus.Analysis.CheckerboardBezout

open scoped BigOperators

/-- The checkerboard Bézout entry from the claim.  The displayed sum is
used on the lower triangle and the upper triangle is its symmetric extension. -/
def checkerboardBezoutEntry (t : ℕ → ℝ) (r c : ℕ) : ℝ :=
  if c ≤ r then
    ∑ l ∈ Finset.range (c + 1),
      ((r + c + 1 - 2 * l : ℕ) : ℝ) * t l * t (r + c + 1 - l)
  else
    ∑ l ∈ Finset.range (r + 1),
      ((c + r + 1 - 2 * l : ℕ) : ℝ) * t l * t (c + r + 1 - l)

theorem checkerboardBezoutEntry_sub_shift
    (t : ℕ → ℝ) {r c : ℕ} (hrc : c ≤ r) (hc : 0 < c) :
    checkerboardBezoutEntry t r c - checkerboardBezoutEntry t (r + 1) (c - 1) =
      ((r - c + 1 : ℕ) : ℝ) * t c * t (r + 1) := by
  simp only [checkerboardBezoutEntry, hrc, ↓reduceIte]
  simp only [show c - 1 ≤ r + 1 by omega, ↓reduceIte]
  rw [show c - 1 + 1 = c by omega]
  have hsum : (r + 1) + (c - 1) + 1 = r + c + 1 := by omega
  rw [hsum]
  rw [Finset.sum_range_succ]
  have hcoef : r + c + 1 - 2 * c = r - c + 1 := by omega
  have hidx : r + c + 1 - c = r + 1 := by omega
  rw [hcoef, hidx]
  ring

theorem checkerboardBezoutEntry_zero_right (t : ℕ → ℝ) (r : ℕ) :
    checkerboardBezoutEntry t r 0 =
      ((r + 1 : ℕ) : ℝ) * t 0 * t (r + 1) := by
  unfold checkerboardBezoutEntry
  simp

/-- The normalized checkerboard entry and consecutive moment ratio. -/
noncomputable def checkerboardH (t : ℕ → ℝ) (r c : ℕ) : ℝ :=
  checkerboardBezoutEntry t r c / (t c * t (r + 1))

noncomputable def momentRatio (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  t (k + 1) / t k

theorem checkerboardH_recurrence
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) {r c : ℕ}
    (hrc : c ≤ r) (hc : 0 < c) :
    checkerboardH t r c =
      (r - c + 1 : ℝ) +
        (momentRatio t (r + 1) / momentRatio t (c - 1)) *
          checkerboardH t (r + 1) (c - 1) := by
  have htc : t c ≠ 0 := ne_of_gt (ht c)
  have htr1 : t (r + 1) ≠ 0 := ne_of_gt (ht (r + 1))
  have htc1 : t (c - 1) ≠ 0 := ne_of_gt (ht (c - 1))
  have htr2 : t (r + 2) ≠ 0 := ne_of_gt (ht (r + 2))
  have hdiff := checkerboardBezoutEntry_sub_shift t hrc hc
  unfold checkerboardH momentRatio
  field_simp [htc, htr1, htc1, htr2]
  have hdiff' : checkerboardBezoutEntry t r c =
      ((r - c + 1 : ℕ) : ℝ) * t c * t (r + 1) +
        checkerboardBezoutEntry t (r + 1) (c - 1) := by
    linarith [hdiff]
  rw [show c - 1 + 1 = c by omega, hdiff']
  field_simp [htc]
  push_cast
  rw [Nat.cast_sub hrc]
  ring

/-- The factorial-anchor candidate satisfies the recurrence equation. -/
theorem factorialAnchor_recurrence_solution
    (A : ℝ) (hA : 0 < A) {r c : ℕ}
    (hrc : c ≤ r) (hc : 0 < c) :
    ((r + 1 : ℕ) : ℝ) ^ 2 / ((r + c + 1 : ℕ) : ℝ) =
      ((r - c + 1 : ℕ) : ℝ) +
        (A / ((r + 2 : ℕ) : ℝ) ^ 2) /
            (A / ((c : ℕ) : ℝ) ^ 2) *
          (((r + 2 : ℕ) : ℝ) ^ 2 / ((r + c + 1 : ℕ) : ℝ)) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hcast : ((r - c : ℕ) : ℝ) = (r : ℝ) - (c : ℝ) := by
    rw [Nat.cast_sub hrc]
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have hrc1 : (r + c + 1 : ℝ) ≠ 0 := by positivity
  have hr2 : (r + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hA0, hc0, hrc1, hr2]
  push_cast
  rw [hcast]
  ring

/-- The factorial-anchor candidate has the stated left-edge value. -/
theorem factorialAnchor_left_edge (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) ^ 2 / ((r + 0 + 1 : ℕ) : ℝ) =
      ((r + 1 : ℕ) : ℝ) := by
  have h : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [h]

/-- The factorial-anchor recurrence and its left edge determine the displayed
solution uniquely on the region `c ≤ r`. -/
theorem factorialAnchor_solution_unique
    (A : ℝ) (hA : 0 < A) (H : ℕ → ℕ → ℝ)
    (hbase : ∀ r, H r 0 = ((r + 1 : ℕ) : ℝ))
    (hrec : ∀ {r c : ℕ}, c ≤ r → 0 < c →
      H r c = ((r - c + 1 : ℕ) : ℝ) +
        (A / ((r + 2 : ℕ) : ℝ) ^ 2) /
            (A / ((c : ℕ) : ℝ) ^ 2) * H (r + 1) (c - 1))
    {r c : ℕ} (hrc : c ≤ r) :
    H r c = ((r + 1 : ℕ) : ℝ) ^ 2 / ((r + c + 1 : ℕ) : ℝ) := by
  induction c generalizing r with
  | zero =>
      calc
        H r 0 = ((r + 1 : ℕ) : ℝ) := hbase r
        _ = ((r + 1 : ℕ) : ℝ) ^ 2 / ((r + 0 + 1 : ℕ) : ℝ) :=
          (factorialAnchor_left_edge r).symm
  | succ c ih =>
      have hpos : 0 < c + 1 := by omega
      have hstep := hrec (r := r) (c := c + 1) (by omega) hpos
      have hind := ih (r := r + 1) (by omega)
      have hind' : H (r + 1) c =
          ((r + 2 : ℕ) : ℝ) ^ 2 / ((r + c + 2 : ℕ) : ℝ) := by
        simpa [add_assoc, add_left_comm, add_comm] using hind
      rw [show c + 1 - 1 = c by omega, hind'] at hstep
      have hanchor := factorialAnchor_recurrence_solution A hA hrc hpos
      calc
        H r (c + 1) = ((r - (c + 1) + 1 : ℕ) : ℝ) +
            (A / ((r + 2 : ℕ) : ℝ) ^ 2) /
              (A / ((c + 1 : ℕ) : ℝ) ^ 2) *
                (((r + 2 : ℕ) : ℝ) ^ 2 / ((r + c + 2 : ℕ) : ℝ)) := by
                  simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hstep
        _ = ((r + 1 : ℕ) : ℝ) ^ 2 /
              ((r + (c + 1) + 1 : ℕ) : ℝ) := by
                simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hanchor.symm

end MathlibPlus.Analysis.CheckerboardBezout
