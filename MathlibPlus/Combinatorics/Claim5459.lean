import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim5459

/-- The difference of edge counts is additive along two monotone successive
contractions; the displayed maps also compose to the final target. -/
theorem contractionCost_composition_claim5459
    {Obj : Type*} (edgeCount : Obj → ℕ) (T S U : Obj)
    (π ρ : Obj → Obj) (hπ : π T = S) (hρ : ρ S = U)
    (hπmono : edgeCount S ≤ edgeCount T)
    (hρmono : edgeCount U ≤ edgeCount S) :
    edgeCount T - edgeCount U =
        (edgeCount T - edgeCount S) + (edgeCount S - edgeCount U) ∧
      (ρ ∘ π) T = U := by
  constructor
  · omega
  · rw [Function.comp_apply, hπ, hρ]

end MathlibPlus.Combinatorics.Claim5459
