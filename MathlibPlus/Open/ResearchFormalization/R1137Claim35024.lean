import MathlibPlus.Open.ResearchFormalization.R1137Claim30119

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim35024

open MathlibPlus.Open.ResearchFormalization.R1137Claim30119

private def displayedQ : A4Coordinates → A4Coordinates :=
  ![0, 1, 9, 3, 4, 10, 6, 7, 11, 2, 5, 8]

private def displayedAlpha : A4Coordinates → A4Coordinates :=
  ![0, 2, 1, 3, 5, 4, 9, 10, 11, 6, 7, 8]

private def a4Automorphism
    (f : A4Coordinates → A4Coordinates) : Prop :=
  Function.Bijective f ∧
    ∀ x y : A4Coordinates,
      f (a4Mul x y) = a4Mul (f x) (f y)

/-- Claim 35024: the retained one-based coordinate permutations are recorded
on the literal zero-based A₄ table, with q nonautomorphic and alpha an
A₄ automorphism. -/
def claim35024 : Prop :=
  displayedQ = q12T90 ∧
    displayedAlpha = alpha12T90 ∧
    ¬ a4Automorphism q12T90 ∧
    a4Automorphism alpha12T90

end MathlibPlus.Open.ResearchFormalization.R1137Claim35024
