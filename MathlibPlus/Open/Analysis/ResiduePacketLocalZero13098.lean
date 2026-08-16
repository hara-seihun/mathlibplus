import Mathlib

open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.Analysis.ResiduePacket13098

noncomputable section

/-- The literal prime-divisor numerator in a residue packet. -/
def residuePacketNumerator (q : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-(s - 1) * (Real.log (q : ℝ) : ℂ))

/-- The denominator accompanying a prime-divisor packet factor. -/
def residuePacketDenominator (q : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-(s - 1) * (Real.log (q : ℝ) : ℂ)) / ((q : ℂ) + 1)

/-- The local ratio in the exact packet factorization. -/
def residuePacketLocalRatio (q : ℕ) (s : ℂ) : ℂ :=
  residuePacketNumerator q s / residuePacketDenominator q s

/-- The product of the local factors in the `k`-packet of `B_N`. -/
def residuePacketLocalProduct (k : ℕ) (s : ℂ) : ℂ :=
  ∏ q ∈ k.primeFactors, residuePacketLocalRatio q s

/-- The raw Euler product `D_N` in its convergence-region form. -/
def rawResidueDensityFactor (N : ℕ) (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes,
    if ¬ (q : ℕ) ∣ N then
      1 -
          Complex.exp (-(s - 1) * (Real.log (q : ℝ) : ℂ)) /
            ((q : ℂ) + 1)
    else 1

/-- Every included nontrivial packet has a literal local zero at `s=1`; the
exceptional packet is killed by the reciprocal-zeta factor in the continued
form of `D_N`. -/
def nontrivialResiduePacketLocalZero : Prop :=
  ∀ (N : ℕ), 0 < N →
    (∀ (k : ℕ), 1 < k → Nat.Coprime k N →
      (∀ q : ℕ, q.Prime → q ∣ k →
        residuePacketNumerator q (1 : ℂ) = 0 ∧
          residuePacketDenominator q (1 : ℂ) ≠ 0 ∧
          residuePacketLocalRatio q (1 : ℂ) = 0) ∧
      residuePacketLocalProduct k (1 : ℂ) = 0) ∧
    (residuePacketLocalProduct 1 (1 : ℂ) = 1) ∧
    (∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 0 < s.re → H s ≠ 0) ∧
      (∀ s : ℂ, 1 < s.re →
        rawResidueDensityFactor N s = H s / riemannZeta s) ∧
      Tendsto
        (fun σ : ℝ => (1 : ℂ) / riemannZeta (σ : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 0) ∧
      Tendsto
        (fun σ : ℝ => H (σ : ℂ) / riemannZeta (σ : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 0))

end

end MathlibPlus.Open.Analysis.ResiduePacket13098
