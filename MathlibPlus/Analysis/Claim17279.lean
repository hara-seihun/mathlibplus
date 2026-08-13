import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim17279

/-!
Formalization of admitted claim 17279.  The two half-lines are represented by
`Set.Ici 0` and `Set.Iic 0`; their common endpoint is represented separately
in each subtype.  No continuity, differentiability, or operator-theoretic
hypothesis is added: the source statement is precisely the endpoint gluing
condition.
-/

/-- Even gluing of two half-line functions at their common endpoint is exactly
endpoint-value equality. -/
def evenBoundaryGluing
    (fPlus : Set.Ici (0 : ℝ) → ℝ)
    (fMinus : Set.Iic (0 : ℝ) → ℝ) : Prop :=
  fPlus ⟨0, by simp⟩ = fMinus ⟨0, by simp⟩

end MathlibPlus.Analysis.Claim17279
