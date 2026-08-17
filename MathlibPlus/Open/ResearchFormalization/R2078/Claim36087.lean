import MathlibPlus.Open.Combinatorics.CubeSwitching

namespace MathlibPlus.Open.ResearchFormalization.R2078CharacterShear

open MathlibPlus.Open.Combinatorics.CubeSwitching

/-- A fixed-coordinate cube automorphism preserves its adjacency relation in
both directions and is bijective on the vertex carrier. -/
def fixedCubeAutomorphism {n : ℕ} (f : Vertex n → Vertex n) : Prop :=
  Function.Bijective f ∧
    ∀ a c : Vertex n,
      (cubeGraph n).Adj a c ↔ (cubeGraph n).Adj (f a) (f c)

/-- The character shear associated with an additive Boolean character. -/
def characterShear {n : ℕ} (χ : Base n →+ F2) : Vertex n → Vertex n :=
  fiberSwitch (fun x => χ x)

/-- Claim 36087: a nonzero character sends a coordinate generator to the
weight-two `e_i+z` vector, so it does not preserve the fixed cube. -/
def characterShear_not_fixed_cube_claim36087 : Prop :=
  ∀ (n : ℕ) (χ : Base n →+ F2),
    χ ≠ 0 →
      ∃ i : Fin n,
        χ (Pi.single i 1) = 1 ∧
          characterShear χ (0, 0) = (0, 0) ∧
          characterShear χ (Pi.single i 1, 0) = (Pi.single i 1, 1) ∧
          characterShear χ (Pi.single i 1, 0) -
              characterShear χ (0, 0) = (Pi.single i 1, 1) ∧
          ¬(cubeGraph n).Adj
            (characterShear χ (0, 0))
            (characterShear χ (Pi.single i 1, 0)) ∧
          ¬fixedCubeAutomorphism (characterShear χ) ∧
          ¬mapsSelectedEdgesIntoCube (cubeGraph n) (fun x => χ x) ∧
          ¬(∀ G : SimpleGraph (Vertex n),
            isSelectedSubgraph G →
              mapsSelectedEdgesIntoCube G (fun x => χ x))

end MathlibPlus.Open.ResearchFormalization.R2078CharacterShear
