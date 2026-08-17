import MathlibPlus.Open.Analysis.ResearchBatch_01a001ca_640f_77be_b198_6ef80edbd5e4

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.GeometricCauchyBinet8182

open MathlibPlus.Open.Analysis.FormalizationBatch

/-- The ordered source columns `S_ell` in the geometric expansion. -/
def sourceColumnIndex (r k ell : ℕ) (j : Fin r) : ℕ :=
  if j.1 + 1 < r then k + 1 + j.1 else k + r + ell

/-- The source minor with rows `I_m` and columns `S_ell`. -/
def sourceMinor (f : ℤ → ℝ) (r k ell : ℕ) (m : Fin (r + 1)) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    f ((sourceColumnIndex r k ell j : ℤ) -
      (deletedRowIndex r m.1 i : ℤ)))

/-- Claim 8182: the endpoint cofactor has the geometric Cauchy--Binet
expansion, and its summands are nonnegative under `PF_r`. -/
def claim8182_geometric_cauchy_binet : Prop :=
  ∀ (r k : ℕ) (α : ℝ) (f : ℤ → ℝ) (F : ℂ → ℂ) (d : ℤ → ℝ),
    0 < r →
    0 < α →
    PF r f →
    EntireWithCoefficients f F →
    ExteriorLaurentExpansion F α d →
    ∀ m : Fin (r + 1),
      (endpointCofactor d r k m.1 =
          ∑' ell : ℕ, α ^ ell * sourceMinor f r k ell m) ∧
        (∀ ell : ℕ, 0 ≤ α ^ ell * sourceMinor f r k ell m)

end MathlibPlus.Open.Analysis.GeometricCauchyBinet8182
