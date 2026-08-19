import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R3585.Claim50807

abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev PositiveIndex := {k : ℕ // 1 ≤ k}

/-- The literal coefficient contributed by one reflected prime-power atom. -/
def literalEulerCoefficient (p : ℕ) (r : ℝ) (k : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * (-1 : ℂ) ^ k *
    (Real.rpow (p : ℝ) ((k : ℝ) / 2) : ℂ) *
      ((r ^ k + (r ^ k)⁻¹ - 2 : ℝ) : ℂ)

/-- The coefficient at an integer, obtained from the literal prime-power
contributions of the positive-amplitude reflected family. -/
def reflectedPrimePowerCoefficient
    (r : PrimeIndex → ℝ) (n : ℕ) : ℂ :=
  ∑' p : PrimeIndex,
    ∑' k : PositiveIndex,
      if p.1 ^ k.1 = n then
        literalEulerCoefficient p.1 (r p) k.1
      else 0

/-- The ordinary Dirichlet term carried by the reflected coefficient family. -/
def reflectedDirichletTerm
    (r : PrimeIndex → ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  if 2 ≤ n then
    reflectedPrimePowerCoefficient r n * Complex.cpow (n : ℂ) (-s)
  else 0

/-- Absolute convergence of the ordinary Dirichlet series on one half-plane. -/
def ordinaryAbsoluteDirichletLog
    (r : PrimeIndex → ℝ) : Prop :=
  ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
    Summable (fun n : ℕ => ‖reflectedDirichletTerm r n s‖)

/-- Preservation of every literal Euler prime-power coefficient relative to
balanced reflected atoms. -/
def preservesLiteralEulerTower
    (r : PrimeIndex → ℝ) : Prop :=
  ∀ p : PrimeIndex, ∀ k : PositiveIndex,
    reflectedPrimePowerCoefficient r (p.1 ^ k.1) = 0

/-- Distinct prime-power rays have distinct prime and positive exponent data. -/
def primePowerRaysDisjoint : Prop :=
  ∀ (p q : PrimeIndex) (k l : PositiveIndex),
    p.1 ^ k.1 = q.1 ^ l.1 → p.1 = q.1 ∧ k.1 = l.1

/-- Positive reflected amplitudes cannot preserve the complete literal Euler
prime-power tower when their ordinary logarithmic derivative series converges. -/
def claim50807 : Prop :=
  primePowerRaysDisjoint ∧
    ∀ (r : PrimeIndex → ℝ),
      (∀ p : PrimeIndex, 0 < r p) →
        ordinaryAbsoluteDirichletLog r →
          preservesLiteralEulerTower r →
            ∀ p : PrimeIndex, r p = 1

end MathlibPlus.Open.ResearchFormalization.R3585.Claim50807

end
