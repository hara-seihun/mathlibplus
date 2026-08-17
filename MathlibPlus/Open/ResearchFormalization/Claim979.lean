import Mathlib.NumberTheory.PrimeCounting

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim979

/--
The exact strict-coefficient criterion for each of the 28 audited rows.  The
row starts and optimizers are the source table; the prime count is Mathlib's
real-cutoff convention, and the sharp coefficient uses the actual count at
that optimizer (so the 1.083 row uses π(1529630)=116255).
-/
def exactStrictCoefficientCriterion_claim979 : Prop :=
  let x₀ : Fin 28 → ℕ :=
    ![18339738, 13026859, 12895928, 8832927, 7299254, 7117256,
      5465656, 4994010, 3462478, 3455648, 2279177, 1529630,
      1525432, 1515074, 1200014, 1195296, 624878, 618726,
      618058, 445112, 359804, 356203, 355990, 355177,
      155935, 155907, 60297, 60224]
  let xstar : Fin 28 → ℕ :=
    ![18339738, 13026859, 12895928, 8832927, 7299254, 7117303,
      5465671, 4994010, 3462478, 3455648, 2279177, 1529630,
      1525432, 1515074, 1200014, 1195296, 624878, 618726,
      618058, 445112, 359804, 356203, 355990, 355177,
      155935, 155907, 60297, 60224]
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let aStar : Fin 28 → ℝ := fun i =>
    Real.log (xstar i) - (xstar i : ℝ) / primeCount (xstar i)
  ∀ i : Fin 28, ∀ c : ℝ, c < Real.log (x₀ i : ℝ) →
    ((∀ x : ℝ, (x₀ i : ℝ) ≤ x →
        primeCount x < x / (Real.log x - c)) ↔ aStar i < c)

end MathlibPlus.Open.ResearchFormalization.Claim979
