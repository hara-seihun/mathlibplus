import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.O0212

def dirichletTerm (m : ℕ) (s : ℂ) : ℂ :=
  if m = 0 then 0 else Complex.exp (-s * Complex.log (m : ℂ))

def zetaSeries (s : ℂ) : ℂ := ∑' m : ℕ, dirichletTerm m s

def derivativePower : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, f => f
  | n + 1, f => deriv (derivativePower n f)

def scaledPolynomialDerivative (Q : Polynomial ℂ) (L : ℝ)
    (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  Finset.sum Q.support (fun j =>
    Q.coeff j * ((-(L : ℂ)⁻¹) ^ j) * derivativePower j f s)

def derivativeSeriesTerm (j m : ℕ) (s : ℂ) : ℂ :=
  if m = 0 then 0 else (Complex.log (m : ℂ) ^ j) * dirichletTerm m s

def weightedDirichletTerm (Q : Polynomial ℂ) (L : ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  if m = 0 then 0 else
    Q.eval (Complex.log (m : ℂ) / (L : ℂ)) * dirichletTerm m s

def claim13808 : Prop :=
  ∀ (L : ℝ) (Q : Polynomial ℂ) (s : ℂ), 0 < L → 1 < s.re →
    (∀ j : ℕ, Summable (fun m : ℕ => ‖derivativeSeriesTerm j m s‖)) ∧
      scaledPolynomialDerivative Q L zetaSeries s =

        ∑' m : ℕ, weightedDirichletTerm Q L m s

def finiteDirichlet (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range (N + 1)) (fun n => a n * dirichletTerm n s)

def claim13810 : Prop :=
  ∀ (N M : ℕ) (a b : ℕ → ℂ) (L : ℝ) (Q : Polynomial ℂ),
    1 ≤ N → 0 < L → a 1 ≠ 0 →
    (∀ s : ℂ, 1 < s.re →
      finiteDirichlet a N s * scaledPolynomialDerivative Q L zetaSeries s =
        zetaSeries s * finiteDirichlet b M s) →
    (∃ c : ℂ, Q = Polynomial.C c ∧
      ∀ s : ℂ, 1 < s.re → finiteDirichlet b M s = c * finiteDirichlet a N s) ∧
      (∀ c : ℂ, ∀ s : ℂ, 1 < s.re →
        finiteDirichlet a N s * scaledPolynomialDerivative (Polynomial.C c) L zetaSeries s =
          zetaSeries s * (c * finiteDirichlet a N s))

end MathlibPlus.Open.Analysis.O0212
