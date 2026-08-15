import MathlibPlus.Open.LinearAlgebra.DeletionStableBoundedAnchor

namespace MathlibPlus.Open

/-- Empty-deletion bounded-anchor recognition for a vector coloop. -/
def boundedAnchorColoopTheorem
    {ι F : Type*} [DecidableEq ι] [Field F]
    (d : ℕ) (K E : Finset ι) (v : ι → Fin d → F) (_hE : E ⊆ K) : Prop :=
  ∀ (e : ι),
    e ∈ E →
      (vectorColoop v E e ↔
        ∃ A : Finset ι,
          A ⊆ K \ {e} ∧
          A.card ≤ d - 1 ∧
          outRegister v E A = OutsideCode.one e)

end MathlibPlus.Open
