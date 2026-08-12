import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.Claim9799

noncomputable section

/-- Claim 9799: the displayed generalized-Laguerre coefficient expansion and
its primitive.  The source's `L_n` in the primitive is the ordinary Laguerre
polynomial, while `L_{n-1}^1` is the parameter-one polynomial. -/
theorem generalizedLaguerreExpansionAndPrimitive_claim9799 (n : ℕ) (hn : 0 < n) :
    let L₀ : ℕ → ℝ → ℝ := fun m x =>
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) * (-x) ^ j / (j.factorial : ℝ)
    let L₁ : ℕ → ℝ → ℝ := fun m x =>
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose (m + 1) (j + 1) : ℝ) * (-x) ^ j / (j.factorial : ℝ)
    (∀ x : ℝ,
      L₁ (n - 1) x =
        ∑ j ∈ Finset.range n,
          (Nat.choose n (j + 1) : ℝ) * (-x) ^ j / (j.factorial : ℝ)) ∧
      (∀ T : ℝ,
        ∫ t in (0 : ℝ)..T, L₁ (n - 1) t = 1 - L₀ n T) := by
  let L₀ : ℕ → ℝ → ℝ := fun m x =>
    ∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℝ) * (-x) ^ j / (j.factorial : ℝ)
  let L₁ : ℕ → ℝ → ℝ := fun m x =>
    ∑ j ∈ Finset.range (m + 1),
      (Nat.choose (m + 1) (j + 1) : ℝ) * (-x) ^ j / (j.factorial : ℝ)
  change
    (∀ x : ℝ,
      L₁ (n - 1) x =
        ∑ j ∈ Finset.range n,
          (Nat.choose n (j + 1) : ℝ) * (-x) ^ j / (j.factorial : ℝ)) ∧
      (∀ T : ℝ,
        ∫ t in (0 : ℝ)..T, L₁ (n - 1) t = 1 - L₀ n T)
  have hderivL₀ : ∀ x : ℝ, HasDerivAt (L₀ n) (-L₁ (n - 1) x) x := by
    intro x
    have hsum : HasDerivAt
        (fun y : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : ℝ) * (-y) ^ j / (j.factorial : ℝ))
        (∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) *
            ((j : ℝ) * (-x) ^ (j - 1) * (-1))) / (j.factorial : ℝ)) x := by
      apply HasDerivAt.fun_sum
      intro j hj
      exact (((hasDerivAt_neg x).pow j).const_mul (Nat.choose n j : ℝ)).div_const
        (j.factorial : ℝ)
    convert hsum using 1
    simp [L₁]
    have h : n - 1 + 1 = n := by omega
    rw [h]
    rw [Finset.sum_range_succ']
    simp
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos : 0 < j + 1 := by omega
    field_simp
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hL₀zero : L₀ n 0 = 1 := by
    simp only [L₀, neg_zero]
    rw [Finset.sum_range_succ']
    simp
  constructor
  · intro x
    dsimp [L₁]
    have h : n - 1 + 1 = n := by omega
    rw [h]
  · intro T
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - L₀ n)
          (L₁ (n - 1) x) x := by
      intro x hx
      have h := (hasDerivAt_const x (1 : ℝ)).sub (hderivL₀ x)
      simpa using h
    have hcont : ContinuousOn (fun x : ℝ => L₁ (n - 1) x)
        (Set.uIcc (0 : ℝ) T) := by
      dsimp [L₁]
      fun_prop
    have hint : IntervalIntegrable (fun x : ℝ => L₁ (n - 1) x)
        MeasureTheory.volume 0 T := hcont.intervalIntegrable
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa [hL₀zero] using hmain

end

end MathlibPlus.Analysis.Claim9799
