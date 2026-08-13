import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Analysis.Claim49014

/-- The selector variance at block zero. -/
def selectorVariance (n : ℕ) : ℚ :=
  ((n : ℚ) + 1) / (2 * (n : ℚ))

/-- The conditional prequery variance in the block `r`, with `s = n-r`. -/
def continuationVariance (n r : ℕ) : ℚ :=
  let s := n - r
  ((s : ℚ) + 1) ^ 2 / (4 * (n : ℚ) ^ 2) +
    ((s : ℚ) - 1) / (2 * (n : ℚ) ^ 2)

/-- Its displayed simplified form. -/
theorem continuationVariance_eq (n r : ℕ) :
    continuationVariance n r =
      let s := n - r
      ((s : ℚ) ^ 2 + 4 * (s : ℚ) - 1) / (4 * (n : ℚ) ^ 2) := by
  dsimp [continuationVariance]
  ring

/-- The probability of the second query in the displayed block. -/
def secondQueryProbability (r : ℕ) : ℚ := 1 / (2 : ℚ) ^ r

/-- The closed form for the full query-level area.  The term `2^(3-n)` from
    the source is represented for natural `n` by `4 / 2^(n-1)` below. -/
def closedForm (n : ℕ) : ℚ :=
  (8 * (n : ℚ) ^ 2 - 5 * (n : ℚ) + 9) / (4 * (n : ℚ) ^ 2) -
    1 / ((2 : ℚ) ^ (n - 1) * (n : ℚ) ^ 2)

def complementClosedForm (n : ℕ) : ℚ :=
  (5 * (n : ℚ) - 9 + 4 / (2 : ℚ) ^ (n - 1)) /
    (4 * (n : ℚ) ^ 2)

/-- The exact-area interface retains the pre-selector term, every block term,
    the strict finite bound, and the limiting assertion.  The concrete
    posterior-area carrier is intentionally an explicit parameter. -/
def sharedSelectorExactArea (area preSelector : ℕ → ℚ) : Prop :=
  (∀ n, 0 < n →
    (area n = preSelector n + selectorVariance n +
      (∑ r in Finset.Icc 1 (n - 1),
        secondQueryProbability r * continuationVariance n r) ∧
      area n = closedForm n)) ∧
    area 1 = 2 ∧
    (∀ n, 2 ≤ n → area n < 2) ∧
    Filter.Tendsto area Filter.atTop (𝓝 2)

theorem two_sub_closedForm {n : ℕ} (hn : 0 < n) :
    2 - closedForm n = complementClosedForm n := by
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  simp only [closedForm, complementClosedForm]
  field_simp [hnq]
  ring

theorem closedForm_one : closedForm 1 = 2 := by
  norm_num [closedForm]

theorem closedForm_lt_two {n : ℕ} (hn : 2 ≤ n) : closedForm n < 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
  have hnlin : 0 < 5 * (n : ℚ) - 9 := by
    have hn' : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hpow : 0 < (2 : ℚ) ^ (n - 1) := by positivity
  have hterm : 0 < (4 : ℚ) / (2 : ℚ) ^ (n - 1) := by positivity
  have hnum : 0 < 5 * (n : ℚ) - 9 + 4 / (2 : ℚ) ^ (n - 1) :=
    by linarith
  have hden : 0 < 4 * (n : ℚ) ^ 2 := by positivity
  have hcomp : 0 < complementClosedForm n := by
    exact div_pos hnum hden
  have hid := two_sub_closedForm (n := n) hnpos
  linarith

end MathlibPlus.Analysis.Claim49014
