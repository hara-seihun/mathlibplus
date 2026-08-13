import MathlibPlus.Algebra.PositiveIntegralEdgeTensorClaim5278

namespace MathlibPlus.Algebra

/-- The displayed span realization of the positive integral edge-length space. -/
theorem positiveEdgeSpace_span_claim5278 :
    Submodule.span ℚ (Set.range positiveEdgeVector) = ⊤ := by
  change Submodule.span ℚ
      (Set.range (fun i : PositiveEdgeLength => Finsupp.single i 1)) = ⊤
  exact (Finsupp.basisSingleOne (ι := PositiveEdgeLength) (R := ℚ)).span_eq

/-- The basis vectors are exactly the ordered tensors `e_i ⊗ e_j`. -/
theorem orderedPositiveEdgeTensorBasis_apply_claim5278
    (i j : PositiveEdgeLength) :
    orderedPositiveEdgeTensorBasis (i, j) =
      positiveEdgeVector i ⊗ₜ[ℚ] positiveEdgeVector j := by
  simp [orderedPositiveEdgeTensorBasis, positiveEdgeBasis, positiveEdgeVector]

end MathlibPlus.Algebra
