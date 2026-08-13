import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every normalized map obtained by postcomposing the displayed quadratic
binary rank-six CI-defect map with one nontrivial transposition carries only
ordinary undirected Cayley pairs that already have an additive transporter. -/
def binaryRankSixQuadraticSingleTranspositionRoutesUndirectedCIHarmless : Prop :=
  let V := Fin 6 → ZMod 2
  let q : V → V := fun x =>
    ![
      x 0 + x 1 + x 0 * x 1 + x 2 + x 0 * x 2 + x 1 * x 2 + x 3 + x 4 + x 5,
      x 0 + x 0 * x 1 + x 0 * x 2 + x 3 + x 4,
      x 1 + x 0 * x 1 + x 1 * x 2 + x 3 + x 5,
      x 0 * x 1 + x 3,
      x 2 + x 0 * x 2 + x 1 * x 2 + x 4 + x 5,
      x 0 * x 2 + x 4]
  ∀ a b : V, a ≠ b →
    let τ : V ≃ V := Equiv.swap a b
    let f : V → V := fun x => τ (q x) - τ (q 0)
    Function.Bijective f ∧ f 0 = 0 ∧
      ∀ S : Set V,
        0 ∉ S →
        (∀ x, x ∈ S ↔ -x ∈ S) →
        0 ∉ f '' S →
        (∀ x, x ∈ f '' S ↔ -x ∈ f '' S) →
        (∀ x y, y - x ∈ S ↔ f y - f x ∈ f '' S) →
        ∃ α : V ≃+ V, α '' S = f '' S

end MathlibPlus.Open.GraphTheory
