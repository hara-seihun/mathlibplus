import MathlibPlus.Open.NumberTheory.R1899RoughSieveAndEntropy

namespace MathlibPlus.Open.ResearchFormalization.R1899.Claim34777

noncomputable section

open Classical
open scoped BigOperators
open MathlibPlus.Open.NumberTheory.R1899

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

private def twoPointDensity (Q h : ℕ) : ℝ :=
  (Q : ℝ)⁻¹ *
    ∑ t : Fin Q,
      if Nat.Coprime t.val Q ∧ Nat.Coprime (t.val + h) Q then 1 else 0

/-- Claim 34777: in the primorial regime `2 ≤ z`, the exact two-point
    rough density has the odd/even divisor expansion and its full divisor sum
    is the one-point rough density. -/
def claim34777 : Prop :=
  ∀ z : ℕ, 2 ≤ z →
    (∀ h : ℕ, Odd h → twoPointDensity (primorialUpTo z) h = 0) ∧
      (∀ h : ℕ, Even h →
        twoPointDensity (primorialUpTo z) h =
          constantA z *
            Finset.sum (oddPrimorial z).divisors
              (fun d => if d ∣ h / 2 then divisorWeight d else 0)) ∧
      constantA z *
          Finset.sum (oddPrimorial z).divisors
            (fun d => divisorWeight d) =
        roughDensity (primorialUpTo z)

end
end MathlibPlus.Open.ResearchFormalization.R1899.Claim34777
