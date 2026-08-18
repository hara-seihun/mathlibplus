import MathlibPlus.Open.ResearchFormalization.R0516.Claim26073

namespace MathlibPlus.Open.ResearchFormalization.R0516

open scoped BigOperators

noncomputable section

/-- Claim 26069: the weighted connected-subtree deletion layer of a finite
tree, with the literal boundary `y` weight and literal `G^(1)` residual
polynomial. -/
noncomputable def weightedConnectedSubtreeLayer_claim26069
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (k : ℕ) :
    MvPolynomial (ColorVar 2) ℤ :=
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  ∑ S : Finset V,
    if S.Nonempty ∧ S.card = k ∧
        (T.induce (S : Set V)).Preconnected then
      letI : DecidableRel (inducedComplement T S).Adj :=
        Classical.decRel (inducedComplement T S).Adj
      (MvPolynomial.X (yVar 2) : MvPolynomial (ColorVar 2) ℤ) ^
          boundaryCount T S * GOne (inducedComplement T S)
    else 0

end
end MathlibPlus.Open.ResearchFormalization.R0516
