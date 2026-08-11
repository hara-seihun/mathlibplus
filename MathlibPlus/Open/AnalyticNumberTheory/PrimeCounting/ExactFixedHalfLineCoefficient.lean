import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity formalization of claim 1170.  The Table 8 starts are the
thirty literal starts in the source table.  The claim's unrestricted real
coefficient quantifier is retained; the source context's usual denominator-
domain side condition is not silently inserted.
-/

/--
Claim 1170: at each literal Table 8 start, the strict prime-counting bound on
the complete real half-line is equivalent to the coefficient being above the
suffix maximum of `A(x) = log x - x / π(x)`.
-/
noncomputable def exactFixedHalfLineCoefficientCondition : Prop :=
  let table8Starts : Set ℝ :=
    {22078017, 18339738, 13026859, 12895928, 8832927, 7299254,
      7117256, 5465656, 4994010, 3462478, 3455648, 2279177,
      1529630, 1526671, 1525432, 1515074, 1200014, 1195296,
      624878, 618726, 618058, 445112, 359804, 356203, 355990,
      355177, 155935, 155907, 60297, 60224}
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x => Real.log x - x / primeCount x
  let alpha : ℝ → ℝ := fun x₀ => sSup (score '' Set.Ici x₀)
  let valid : ℝ → ℝ → Prop := fun x₀ c =>
    ∀ x : ℝ, x₀ ≤ x → primeCount x < x / (Real.log x - c)
  ∀ x₀ ∈ table8Starts, ∀ c : ℝ, valid x₀ c ↔ alpha x₀ < c

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
