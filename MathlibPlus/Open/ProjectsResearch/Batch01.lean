import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.Batch01

open scoped BigOperators

/-- The exact degree-28 integer-polynomial root configuration used in claim 44937. -/
def Degree28RootConfiguration
    (ell : Polynomial ℤ) (δ : ℝ) (β : Fin 27 → ℝ) : Prop :=
  ell.Monic ∧
    ell.natDegree = 28 ∧
    0 < δ ∧ δ < (27 : ℝ) / 1000 ∧
    (∀ i, -2 < β i ∧ β i < 2) ∧
    Polynomial.map (algebraMap ℤ ℝ) ell =
      (Polynomial.X - Polynomial.C (2 + δ)) *
        ∏ i : Fin 27, (Polynomial.X - Polynomial.C (β i))

/-- Claim 44937: the endpoint values and the congruence/product obstruction. -/
def claim44937 : Prop :=
  ∀ (ell : Polynomial ℤ) (δ : ℝ) (β : Fin 27 → ℝ),
    Degree28RootConfiguration ell δ β →
      let α : Fin 27 → ℝ := fun i => β i + 2
      let nPlus : ℤ := -ell.eval 2
      let nMinus : ℤ := ell.eval (-2)
      ((∀ i, 0 < α i ∧ α i < 4) ∧
        ((nPlus : ℝ) = δ * ∏ i : Fin 27, (4 - α i)) ∧
        ((nMinus : ℝ) = (4 + δ) * ∏ i : Fin 27, α i) ∧
        0 < nPlus ∧
        0 < nMinus ∧
        (∀ p : Polynomial ℤ,
          Int.ModEq 4 (p.eval 2) (p.eval (-2))) ∧
        Int.ModEq 4 (nPlus + nMinus) 0 ∧
        3 ≤ nPlus * nMinus)

/-- Claim 44938: the AM--GM bound and its monotone endpoint evaluation. -/
def claim44938 : Prop :=
  ∀ (ell : Polynomial ℤ) (δ : ℝ) (β : Fin 27 → ℝ),
    Degree28RootConfiguration ell δ β →
      let α : Fin 27 → ℝ := fun i => β i + 2
      let S : ℝ := (4 + δ) + ∑ i : Fin 27, α i
      let p₂ : ℝ := (4 + δ)^2 + ∑ i : Fin 27, (α i)^2
      let bound : ℝ → ℝ := fun x =>
        4 * S + 4 * x + x^2 -
          27 * Real.rpow (3 / (x * (4 + x))) ((1 : ℝ) / 27)
      (δ * (4 + δ) * ∏ i : Fin 27, (α i * (4 - α i)) ≥ 3) ∧
        (27 * Real.rpow (3 / (δ * (4 + δ))) ((1 : ℝ) / 27) ≤
            ∑ i : Fin 27, (α i * (4 - α i))) ∧
        ((∑ i : Fin 27, (α i * (4 - α i))) =
          4 * S - p₂ + 4 * δ + δ^2) ∧
        (p₂ ≤ bound δ) ∧
        StrictMonoOn bound (Set.Ioi 0) ∧
        bound δ < bound ((27 : ℝ) / 1000) ∧
        (∀ trace : ℤ, S = (trace : ℝ) →
          p₂ < bound ((27 : ℝ) / 1000))

end MathlibPlus.Open.ProjectsResearch.Batch01
