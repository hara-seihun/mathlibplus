import Mathlib

namespace MathlibPlus.Open.Research.R1510

abbrev F3 := ZMod 3
abbrev RankFourPoint := Fin 4 → F3

def rankFourTransporter (X : RankFourPoint) : RankFourPoint :=
  ![ X 0 + (X 3)^2 + (X 2)^2 - X 1,
     X 1 + X 2 + X 3 + X 2 * X 3 + (X 2)^2,
     X 2,
     X 3 ]

def rankFourSection (X : RankFourPoint) : F3 :=
  -X 1 - (X 2)^2

def rankFourA (X : RankFourPoint) : F3 :=
  let x := X 0; let u := X 1; let v := X 2; let w := X 3;
  -u * w^2 - u * v * w + u * v^2 + x * v * w + x * v^2 - x * v^2 * w^2

def rankFourB (X : RankFourPoint) : F3 :=
  let x := X 0; let u := X 1; let v := X 2; let w := X 3;
  v * w^2 + v^2 * w - u + u * w^2 + u * v^2 + u * v^2 * w^2
    - x * v * w - x * v^2 + x * v^2 * w^2

/-- Claim 37985: the displayed all-pairs switching identity. -/
def explicitAllPairsSwitchingIdentity : Prop :=
  ∀ X Y : RankFourPoint,
    rankFourSection X - rankFourSection Y =
      rankFourA (X - Y) +
        rankFourB (rankFourTransporter X - rankFourTransporter Y)

def rankFourTransporterInverse (X : RankFourPoint) : RankFourPoint :=
  ![ X 0 + X 1 - X 2 - X 3 - X 2 * X 3 - X 3^2 - 2 * (X 2)^2,
     X 1 - X 2 - X 3 - X 2 * X 3 - (X 2)^2,
     X 2,
     X 3 ]

/-- Claim 37986: the quotient expression is the stated non-character. -/
def noPureQuotientSection : Prop :=
  (∀ X : RankFourPoint,
      rankFourSection (rankFourTransporterInverse X) =
        -X 1 + X 2 + X 3 + X 2 * X 3) ∧
    ¬ ∃ χ : RankFourPoint →+ F3, ∀ X : RankFourPoint,
      rankFourSection (rankFourTransporterInverse X) = χ X

end MathlibPlus.Open.Research.R1510
