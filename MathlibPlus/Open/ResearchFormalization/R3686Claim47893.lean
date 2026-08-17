import MathlibPlus.Open.ResearchFormalization.R3686LeafDeckClaim47904

namespace MathlibPlus.Open.ResearchFormalization.R3686

open ProjectsResearch.TreeDeck

/-- The tree-indexed completion definition and the coordinatewise Jordan
parts used by the admitted leaf-deck claim. -/
def claim47893 : Prop :=
  ∀ (n : ℕ) (v : UnlabelledTree (n - 1) → ℤ)
    (z : UnlabelledTree (n - 1) → ℤ),
    (∀ H,
      v H = positivePart v H - negativePart v H ∧
        ¬ (0 < positivePart v H ∧ 0 < negativePart v H)) ∧
    (z ∈ completionSet n v ↔
      (∀ H, 0 ≤ z H) ∧
        (fun H => positivePart v H + z H) ∈ ordinaryLeafDeckVectors n ∧
        (fun H => negativePart v H + z H) ∈ ordinaryLeafDeckVectors n)

end MathlibPlus.Open.ResearchFormalization.R3686
