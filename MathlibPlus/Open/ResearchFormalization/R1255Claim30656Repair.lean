import MathlibPlus.Open.ResearchFormalization.R1255.Claims30659_30662

namespace MathlibPlus.Open.ResearchFormalization.R1255Claim30656Repair

open MathlibPlus.Open.ResearchFormalization.R1255

noncomputable section

/-- A normalized local kernel chart on one fixed-`b` block is induced by one
additive automorphism of the layer coordinate. -/
def normalizedLocalOrientation {N : Type*} [AddCommGroup N]
    {q : ℕ} (b : QuotientCoordinate q)
    (F : Equiv.Perm (Point N q)) : Prop :=
  ∃ φ : LayerCoordinate ≃+ LayerCoordinate,
    ∀ p : Point N q, p ∈ block (N := N) b →
      F p = (p.1, φ p.2)

/-- Claim 30656: the normalized local automorphism is exactly the identity or
`i ↦ -i` on the block, and both allowed forms restrict to the identity on the
kernel layer `i=0`. -/
def claim30656 : Prop :=
  ∀ {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) (b : QuotientCoordinate q)
    (F : Equiv.Perm (Point N q)),
    normalizedLocalOrientation b F →
      ((∀ p : Point N q, p ∈ block (N := N) b → F p = p) ∨
        (∀ p : Point N q, p ∈ block (N := N) b →
          F p = (p.1, -p.2))) ∧
      (∀ p : Point N q, p ∈ block (N := N) b → p.2 = 0 →
        ((p.1, p.2) = p ∧ (p.1, -p.2) = p))

end

end MathlibPlus.Open.ResearchFormalization.R1255Claim30656Repair
