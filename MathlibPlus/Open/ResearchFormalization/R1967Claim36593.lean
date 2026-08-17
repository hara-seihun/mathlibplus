import MathlibPlus.Open.ResearchFormalization.R1967

namespace MathlibPlus.Open.ResearchFormalization.R1967Claim36593

open MathlibPlus.Open.ResearchFormalization.R1967

noncomputable section

/-- The exact target-native hypercube setup: C₄-freeness is the coordinate
square condition, while H is precisely the tier whose literal translation
stabilizer quotient is F₂^r and whose selected quotient is one affine
hyperplane plus one outside point. -/
def targetNativeHypercubeSetup36593
    (n r : ℕ) (f : ∀ i : Fin n, DirectionFunction n i) : Prop :=
  2 ≤ r ∧
    coordinateSquareHasUnselected f ∧
      let q : ℕ := 2 ^ r
      let H : Set (Fin n) := hyperplanePlusOneDirections (r := r) f
      q = 2 ^ r ∧
        H = {i | losslessHyperplanePlusPoint (r := r) (f i)}

end

end MathlibPlus.Open.ResearchFormalization.R1967Claim36593
