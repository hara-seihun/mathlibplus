import MathlibPlus.Open.ResearchFormalization.BatchFormalize2965And2999

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.UniqueTransferMinorFamilyClaim2998

noncomputable def transferAlpha : ℂ := 1 / 4

noncomputable def geometricTransferEntry (k s : ℕ) {r : ℕ}
    (j : Fin r) : ℂ :=
  if k + j.1 + 1 ≤ s then
    transferAlpha ^ (s - (k + j.1 + 1))
  else 0

noncomputable def geometricTransferMinor (r k : ℕ) (s : Fin r → ℕ) : ℂ :=
  Matrix.det (fun i j : Fin r => geometricTransferEntry k (s i) j)

def claim2998 : Prop :=
  ∀ r k : ℕ, 1 ≤ r →
    ∀ s : Fin r → ℕ, StrictMono s →
      (geometricTransferMinor r k s ≠ 0 ↔
        ∃ ell : ℕ,
          Set.range s = Set.range
            (MathlibPlus.Open.ResearchFormalization.BatchFormalize2965And2999.sourceColumn
              r k ell)) ∧
        (∀ ell : ℕ,
          geometricTransferMinor r k
              (MathlibPlus.Open.ResearchFormalization.BatchFormalize2965And2999.sourceColumn
                r k ell) =
            transferAlpha ^ ell)

end MathlibPlus.Open.ResearchFormalization.UniqueTransferMinorFamilyClaim2998

end
