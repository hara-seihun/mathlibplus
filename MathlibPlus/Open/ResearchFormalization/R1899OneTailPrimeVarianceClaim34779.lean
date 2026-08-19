import MathlibPlus.Open.NumberTheory.R1899FiberVariance

namespace MathlibPlus.Open.ResearchFormalization.R1899.Claim34779

noncomputable section

open Classical
open scoped BigOperators
open MathlibPlus.Open.NumberTheory.R1899
open MathlibPlus.Open.NumberTheory.R1899FiberVariance

private def oddPrimorial (z : ℕ) : ℕ :=
  ∏ q ∈ (Finset.range (z + 1)).filter
    (fun q => Nat.Prime q ∧ 3 ≤ q), q

private def constantA (z : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    ∏ q ∈ (Finset.range (z + 1)).filter
      (fun q => Nat.Prime q ∧ 3 ≤ q),
      (1 - (2 : ℝ) / q)

private def divisorWeight (d : ℕ) : ℝ :=
  Finset.prod d.primeFactors (fun q => (1 : ℝ) / (q - 2))

private def averageVariance (Q N p : ℕ) : ℝ :=
  (Q : ℝ)⁻¹ *
    ∑ t : Fin Q,
      varianceAtPrime (N := N) (p := p) t

private def arithmeticBlockDiscrepancy (p N c : ℕ) : ℝ :=
  let M := if 0 < N then (N - 1) / c else 0
  ∑ m ∈ Finset.Icc 1 M,
    ((N - c * m : ℕ) : ℝ) *
      ((if p ∣ m then 1 else 0) - (1 : ℝ) / p)

/-- Claim 34779: for `2 ≤ z` and a prime outside the primorial, the
    one-tail-prime average variance has the exact diagonal/off-diagonal
    expansion; the block discrepancy is nonpositive, yielding the Bernoulli
    scale bound. -/
def claim34779 : Prop :=
  ∀ (N z p : ℕ), 2 ≤ z → Nat.Prime p →
    let Q := primorialUpTo z
    ¬ p ∣ Q →
    (∀ c : ℕ, 0 < N → 0 < c → ¬ p ∣ c →
      arithmeticBlockDiscrepancy p N c ≤ 0) ∧
    averageVariance Q N p =
      (N : ℝ) * roughDensity Q * (1 - (1 : ℝ) / p) +
        2 * constantA z *
          Finset.sum (oddPrimorial z).divisors
            (fun d => divisorWeight d *
              arithmeticBlockDiscrepancy p N (2 * d)) ∧
    averageVariance Q N p ≤
      (N : ℝ) * roughDensity Q * (1 - (1 : ℝ) / p)

end
end MathlibPlus.Open.ResearchFormalization.R1899.Claim34779
