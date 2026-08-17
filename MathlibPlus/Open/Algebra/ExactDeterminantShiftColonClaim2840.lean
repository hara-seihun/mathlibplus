import MathlibPlus.Open.Algebra.QuotientEmbeddingInterval

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Algebra.ExactDeterminantShiftColonClaim2840

abbrev ambientRing := MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.ambientRing
abbrev symmetricRing := MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.symmetricRing

noncomputable def truncatedVariableIdeal (j d : ℕ) : Ideal (ambientRing j) :=
  Ideal.span (Set.range (fun i : Fin j =>
    (MvPolynomial.X i : ambientRing j) ^ (d + 1)))

noncomputable def variableIdealColon (j d L : ℕ) : Ideal (ambientRing j) :=
  Submodule.colon (truncatedVariableIdeal j (L + d))
    {((∏ i : Fin j, (MvPolynomial.X i : ambientRing j)) ^ L)}

noncomputable def symmetricIdealColon (j d L : ℕ) : Ideal (symmetricRing j) :=
  Submodule.colon
    (MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j (L + d))
    {((MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.topElementary j) ^ L)}

def contraction (j : ℕ) (J : Ideal (ambientRing j)) : Ideal (symmetricRing j) :=
  Ideal.comap (symmetricRing j).val J

def claim2840 : Prop :=
  ∀ j d L : ℕ,
    variableIdealColon j d L = truncatedVariableIdeal j d ∧
      symmetricIdealColon j d L =
        MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d ∧
      contraction j (variableIdealColon j d L) = symmetricIdealColon j d L

end MathlibPlus.Open.Algebra.ExactDeterminantShiftColonClaim2840

end
