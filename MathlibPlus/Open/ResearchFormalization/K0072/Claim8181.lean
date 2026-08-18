import Mathlib
import MathlibPlus.Open.Analysis.ResearchBatch_01a001ca_640f_77be_b198_6ef80edbd5e4

namespace MathlibPlus.Open.ResearchFormalization.K0072.Claim8181

open MathlibPlus.Open.Analysis.FormalizationBatch

noncomputable section

/-- The positive exterior Laurent data used by the endpoint block. -/
structure ExteriorEndpointData where
  α : ℝ
  F : ℂ → ℂ
  d : ℤ → ℝ
  α_pos : 0 < α
  expansion : ExteriorLaurentExpansion F α d

/-- The `(r+1)×r` endpoint Laurent block `[d_(k+j-i)]`. -/
def endpointLaurentBlock_claim8181 (D : ExteriorEndpointData)
    (r k : ℕ) : Matrix (Fin (r + 1)) (Fin r) ℝ :=
  fun i j =>
    D.d (((k + j.1 : ℕ) : ℤ) - (i.1 : ℤ))

/-- The square block obtained by deleting row `m`. -/
def deletedEndpointBlock_claim8181 (D : ExteriorEndpointData)
    (r k : ℕ) (m : Fin (r + 1)) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => endpointLaurentBlock_claim8181 D r k (Fin.succAbove m i) j

/-- The determinant of the deleted-row endpoint block. -/
def deletedRowCofactor_claim8181 (D : ExteriorEndpointData)
    (r k : ℕ) (m : Fin (r + 1)) : ℝ :=
  Matrix.det (deletedEndpointBlock_claim8181 D r k m)

end

end MathlibPlus.Open.ResearchFormalization.K0072.Claim8181
