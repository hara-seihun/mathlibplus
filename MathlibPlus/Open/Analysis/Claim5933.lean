import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim5933

/-!
The source's adjacent-gap pressure series and normalized cumulative defects are
inlined below.  In particular, the supplied `E_r` bounds the actual defect;
this is not replaced by an equality.  The source's no-finite-accumulation and
absolute-convergence hypotheses are retained explicitly, while no
Riemann-specific zero-flow hypothesis is added.
-/

/-- The finite-radius Jensen pressure bound of claim 5933. -/
noncomputable def jensenPressureBound : Prop :=
  let gap : (ℤ → ℝ) → ℤ → ℝ := fun x i => x (i + 1) - x i
  let pressureSummand : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun x k j =>
    if j = k ∨ j = k + 1 then 0
    else 1 / ((x (k + 1) - x j) * (x k - x j))
  let adjacentPressure : (ℤ → ℝ) → ℤ → ℝ := fun x k =>
    2 - gap x k ^ 2 * ∑' j : ℤ, pressureSummand x k j
  let normalizedDefect :
      (ℤ → ℝ) → ℤ → ℕ → ℝ := fun x k r =>
    (gap x k)⁻¹ *
      ∑ j ∈ Finset.Icc 1 r,
        (gap x (k - (j : ℤ)) +
            gap x (k + (j : ℤ)) -
          2 * gap x k)
  ∀ (x : ℤ → ℝ) (k : ℤ) (R : ℕ) (E : ℕ → ℝ),
    (∀ i : ℤ, x i < x (i + 1)) →
    (∀ a b : ℝ, Set.Finite {i : ℤ | a ≤ x i ∧ x i ≤ b}) →
    Summable (fun j : ℤ => ‖pressureSummand x k j‖) →
    (∀ r : ℕ, 1 ≤ r → r ≤ R → normalizedDefect x k r ≤ E r) →
    (∀ r : ℕ, 1 ≤ r → r ≤ R → 0 < (r : ℝ) + E r / 2) →
    adjacentPressure x k ≤
      2 - 2 *
        ∑ r ∈ Finset.Icc 1 R,
          1 /
            (((r : ℝ) + E r / 2) *
              ((r : ℝ) + E r / 2 + 1))

end MathlibPlus.Open.Analysis.Claim5933
