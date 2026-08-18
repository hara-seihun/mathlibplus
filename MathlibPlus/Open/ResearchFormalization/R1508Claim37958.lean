import MathlibPlus.Open.ResearchFormalization.R1508Claims

namespace MathlibPlus.Open.ResearchFormalization.R1508

noncomputable section

/-- The eight-block family of independently affine quinary charts and its raw
cardinality, with the source regular pair and its conjugated/generated groups
provided by the R1508 setup. -/
def claim37958 : Prop :=
  Nat.card (Fiber1508ˣ × Fiber1508) = 20 ∧
    Nat.card AffineProfile1508 = 20 ^ 8 ∧
    (20 : ℕ) ^ 8 = 25_600_000_000 ∧
    ∀ (p : AffineProfile1508) (x : Fiber1508) (j : Outer1508),
      profileChart1508 p (x, j) =
        (affineLine1508 (p.1 j) (p.2 j) x, j)

end
end MathlibPlus.Open.ResearchFormalization.R1508
