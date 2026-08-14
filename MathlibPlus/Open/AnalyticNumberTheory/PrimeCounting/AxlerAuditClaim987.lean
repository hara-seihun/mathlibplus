import Mathlib.NumberTheory.PrimeCounting

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-! Proof-free statement carrier for admitted C-0064 claim 987. -/

/-- Claim 987: the finite optimizer values from all 28 audit rows are separated
from every Axler-score value on the tail beginning at `H=45,399,074` by more
than `0.0019`.  The listed optimizer locations and the real prime-counting
score are kept explicit. -/
def optimizerSeparationFromTail_claim987 : Prop :=
  let H : ℝ := 45399074
  let xStar : Fin 28 → ℕ := ![
    18339738, 13026859, 12895928, 8832927, 7299254, 7117303, 5465671,
    4994010, 3462478, 3455648, 2279177, 1529630, 1525432, 1515074,
    1200014, 1195296, 624878, 618726, 618058, 445112, 359804, 356203,
    355990, 355177, 155935, 155907, 60297, 60224]
  let scoreAtNat : ℕ → ℝ := fun n =>
    Real.log n - (n : ℝ) / (Nat.primeCounting n : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let optimizer : Fin 28 → ℝ := fun r => scoreAtNat (xStar r)
  (∀ r : Fin 28, (10719996 : ℝ) / 10000000 < optimizer r) ∧
    (∀ x : ℝ, H ≤ x → score x < 107 / 100) ∧
    (∀ r : Fin 28, ∀ x : ℝ, H ≤ x →
      19 / 10000 < optimizer r - score x)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
