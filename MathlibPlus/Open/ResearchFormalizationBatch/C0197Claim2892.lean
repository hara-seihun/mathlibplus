import Mathlib
import MathlibPlus.Open.Combinatorics.PacketMarginalGains

open scoped ComplexConjugate

namespace MathlibPlus.Open.ResearchFormalizationBatch.C0197Claim2892

noncomputable section

/-- Opposite parity makes the positive and conjugate gain grids disjoint,
leaves exactly the two one-conjugate maximizing packets, and gives the
associated Hankel determinant the stated oscillating leading term. -/
def claim2892_oppositeParityIsolation : Prop :=
  ∀ (M N : ℕ) (ω : ℂ)
    (Pzero : Polynomial ℝ) (Pplus Pminus : Polynomial ℂ) (s : ℕ → ℝ),
    0 < M →
    0 < N →
    M % 2 ≠ N % 2 →
    ω ≠ 0 →
    ω.im ≠ 0 →
    ‖ω‖ = 1 →
    Pzero.natDegree = M - 1 →
    Pzero.leadingCoeff ≠ 0 →
    Pplus.natDegree = N - 1 →
    Pplus.leadingCoeff ≠ 0 →
    Pminus.natDegree = N - 1 →
    Pminus.leadingCoeff ≠ 0 →
    (∀ n : ℕ,
      (s n : ℂ) =
        ((Pzero.eval (n : ℝ) : ℝ) : ℂ) +
          Pplus.eval (n : ℂ) * ω ^ n +
            Pminus.eval (n : ℂ) * (star ω) ^ n) →
      let aStar : ℕ := max 0 ((M + 1 - N) / 2)
      let kStar : ℕ := aStar + 1
      let d : ℕ := aStar * (M - aStar) + (N - 1)
      let determinant : ℕ → ℝ :=
        fun n =>
          Matrix.det (fun i j : Fin kStar =>
            s (n + i.1 + j.1))
      (∀ i : Fin M, ∀ j : Fin N,
        MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetGain M i.1 ≠
          MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetGain N j.1) ∧
        MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetFeasible M N kStar aStar 1 0 ∧
        MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetFeasible M N kStar aStar 0 1 ∧
        (∀ a u v : ℕ,
          MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetFeasible M N kStar a u v →
            ((∀ a' u' v' : ℕ,
                MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetFeasible M N kStar a' u' v' →
                  MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetDegree M N a' u' v' ≤
                    MathlibPlus.Open.Combinatorics.PacketMarginalGains.packetDegree M N a u v) ↔
              ((a = aStar ∧ u = 1 ∧ v = 0) ∨
                (a = aStar ∧ u = 0 ∧ v = 1)))) ∧
        ∃ C : ℂ, C ≠ 0 ∧
          ∃ R : ℕ → ℝ, ∃ C₀ : ℝ, ∃ n₀ : ℕ,
            0 ≤ C₀ ∧
              (∀ n : ℕ,
                determinant n =
                  (n : ℝ) ^ d *
                      (C * ω ^ n + star C * (star ω) ^ n).re +
                    R n) ∧
              (∀ n : ℕ, n₀ ≤ n →
                |R n| ≤ C₀ * (n : ℝ) ^ (d - 1)) ∧
              (∀ N₀ : ℕ,
                ∃ n : ℕ, N₀ ≤ n ∧ 0 < determinant n) ∧
              (∀ N₀ : ℕ,
                ∃ n : ℕ, N₀ ≤ n ∧ determinant n < 0)

end

end MathlibPlus.Open.ResearchFormalizationBatch.C0197Claim2892
