import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch9978

open scoped BigOperators

noncomputable def paraorthogonalA : ℝ := 1 / Real.sqrt 2

noncomputable def paraorthogonalD (m : ℕ) : ℕ := 4 * m + 2

noncomputable def paraorthogonalF (m : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (m + 1))
    (fun k => Polynomial.C (paraorthogonalA ^ k) * Polynomial.X ^ k)

noncomputable def paraorthogonalH (m : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (m + 1))
    (fun k => Polynomial.C (paraorthogonalA ^ k) * Polynomial.X ^ (m - k))

noncomputable def paraorthogonalP (m : ℕ) : Polynomial ℝ :=
  paraorthogonalF m + Polynomial.X ^ (paraorthogonalD m - m) * paraorthogonalH m

noncomputable def paraorthogonalQ (m : ℕ) (τ : ℝ) : Polynomial ℝ :=
  1 + Polynomial.C τ * Polynomial.X ^ (paraorthogonalD m / 2) +
    Polynomial.X ^ paraorthogonalD m

noncomputable def paraorthogonalEval (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℝ ℂ) z p

def paraorthogonalUnitCircleRoot (p : Polynomial ℝ) (z : ℂ) : Prop :=
  paraorthogonalEval p z = 0 ∧ ‖z‖ = 1

def paraorthogonalSimpleUnitCircleRoot (p : Polynomial ℝ) (z : ℂ) : Prop :=
  paraorthogonalUnitCircleRoot p z ∧ paraorthogonalEval p.derivative z ≠ 0

def denominatorRootsAndRationalCoprimeParameter : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ τ : ℝ, |τ| < 2 →
      ∃ roots : Finset ℂ,
        roots.card = paraorthogonalD m ∧
          ∀ z : ℂ, z ∈ roots ↔ paraorthogonalUnitCircleRoot (paraorthogonalQ m τ) z) ∧
      Set.Finite {τ : ℝ |
        ∃ z : ℂ,
          paraorthogonalEval (paraorthogonalP m) z = 0 ∧
            paraorthogonalEval (paraorthogonalQ m τ) z = 0} ∧
      ∃ τm : ℚ,
        (-1 : ℚ) < τm ∧ τm < 1 ∧
          IsCoprime (paraorthogonalP m)
            (paraorthogonalQ m (τm : ℝ)) ∧
          (∀ z : ℂ,
            paraorthogonalUnitCircleRoot (paraorthogonalP m) z →
              paraorthogonalSimpleUnitCircleRoot (paraorthogonalP m) z) ∧
          (∀ z : ℂ,
            paraorthogonalUnitCircleRoot (paraorthogonalQ m (τm : ℝ)) z →
              paraorthogonalSimpleUnitCircleRoot
                (paraorthogonalQ m (τm : ℝ)) z) ∧
          (∀ z : ℂ,
            paraorthogonalUnitCircleRoot (paraorthogonalP m) z →
              ¬ paraorthogonalUnitCircleRoot (paraorthogonalQ m (τm : ℝ)) z)

end MathlibPlus.Open.ResearchFormalizationBatch9978
