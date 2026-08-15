import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open

/-- The finite Pólya-frequency criterion with all finite minors of the
bi-infinite Toeplitz matrix made explicit. -/
def finitePolyaFrequencyCriterion : Prop :=
  ∀ d : ℕ, ∀ c : Fin (d + 1) → ℝ,
    (∀ k, 0 ≤ c k) →
      let p : Polynomial ℝ :=
        ∑ k : Fin (d + 1), Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)
      let cExt : ℤ → ℝ := fun n =>
        if h : 0 ≤ n ∧ n ≤ (d : ℤ) then
          c ⟨Int.toNat n, by omega⟩
        else 0
      let allRootsNonpositive : Prop :=
        ∀ z : ℂ,
          Polynomial.IsRoot (p.map (algebraMap ℝ ℂ)) z →
            z.im = 0 ∧ z.re ≤ 0
      let allMinorsNonnegative : Prop :=
        ∀ n : ℕ, ∀ r s : Fin n → ℤ,
          StrictMono r → StrictMono s →
            0 ≤ Matrix.det (fun i j : Fin n => cExt (s j - r i))
      allRootsNonpositive ↔ allMinorsNonnegative

/-- The Newton-sum matrix specification for a real degree-d polynomial. -/
def newtonSumHermiteMatrixSpec
    (p : Polynomial ℝ) (d : ℕ)
    (H : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  p ≠ 0 ∧ p.natDegree = d ∧
    ∀ i j : Fin d,
      H i j = ((p.map (algebraMap ℝ ℂ)).roots.map
        (fun z => z ^ ((i : ℕ) + (j : ℕ)))).sum

/-- Hermite positive-semidefinite criterion for real-rootedness, with the
Newton sums and complex quadratic form written out. -/
def hermitePositiveSemidefiniteCriterion : Prop :=
  ∀ (p : Polynomial ℝ) (d : ℕ),
    p ≠ 0 → p.natDegree = d →
      (∀ z : ℂ,
          Polynomial.IsRoot (p.map (algebraMap ℝ ℂ)) z → z.im = 0) ↔
        (∀ x : Fin d → ℂ,
          0 ≤
            (∑ i : Fin d, ∑ j : Fin d,
              starRingEnd ℂ (x i) *
                (((p.map (algebraMap ℝ ℂ)).roots.map
                  (fun z => z ^ ((i : ℕ) + (j : ℕ)))).sum) * x j).re)

end MathlibPlus.Open
