import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

open scoped BigOperators

abbrev PrimeVertex := {p : ℕ // p.Prime}

abbrev PrimeSubsets (S : Finset PrimeVertex) := Finset S

def incidenceKernelMatrix (S : Finset PrimeVertex) :
    Matrix (PrimeSubsets S) (PrimeSubsets S) ℝ :=
  fun A B => ((A ∩ B).card : ℝ)

def incidenceKernelPositiveSemidefinite (S : Finset PrimeVertex) : Prop :=
  ∀ v : PrimeSubsets S → ℝ,
    0 ≤ ∑ A, ∑ B, v A * incidenceKernelMatrix S A B * v B

def incidenceKernelExactRank (S : Finset PrimeVertex) : Prop :=
  Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (incidenceKernelMatrix S))) = S.card

/-- Claim 12201 for the canonical subset-incidence Gram kernel. -/
def claim12201 : Prop :=
  ∀ S : Finset PrimeVertex,
    incidenceKernelPositiveSemidefinite S ∧ incidenceKernelExactRank S

end

end MathlibPlus.Open.FormalizationBatch
