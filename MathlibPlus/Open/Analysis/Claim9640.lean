import MathlibPlus.Analysis.Claim9639

namespace MathlibPlus.Open.Analysis

/--
The coordinate contraction onto the critical axis is an equivariant
 deformation retraction of the symmetric rectangle, relative to the axis.
-/
def equivariantContractionOntoCriticalAxis (a b : ℝ) : Prop :=
  let Q : Set (ℝ × ℝ) := {p | |p.1| ≤ a ∧ |p.2| ≤ b}
  let A : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ |p.2| ≤ b}
  let σ : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (-p.1, p.2)
  let τ : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1, -p.2)
  let I : Set ℝ := Set.Icc 0 1
  let H : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
    fun t p => ((1 - t) * p.1, p.2)
  A ⊆ Q ∧
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2) (I ×ˢ Q) ∧
    (∀ t ∈ I, Set.MapsTo (H t) Q Q) ∧
    (∀ t ∈ I, ∀ p, H t (σ p) = σ (H t p)) ∧
    (∀ t ∈ I, ∀ p, H t (τ p) = τ (H t p)) ∧
    (∀ t ∈ I, ∀ p ∈ A, H t p = p) ∧
    H 0 = id ∧
    Set.MapsTo (H 1) Q A

end MathlibPlus.Open.Analysis
