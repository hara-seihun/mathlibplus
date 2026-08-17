import MathlibPlus.Open.ResearchFormalizationBatch_01a000fb67dc71b3a12d9eaf958b53bc

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_54057

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open MathlibPlus.Open.ResearchFormalizationBatch_01a000fb67dc71b3a12d9eaf958b53bc

/-- The group-ring polynomial attached to a section of the additive cyclic group
of order nine. -/
def sectionPolynomial54057 (A : Finset (ZMod 9)) : C9GroupAlgebra :=
  ∑ a ∈ A, c9Basis a

/-- A unit inverse pair is present when both of its displayed elements occur. -/
def includedUnitPair54057 (A : Finset (ZMod 9))
    (a b : ZMod 9) : Prop :=
  a ∈ A ∧ b ∈ A

/-- The number of the three displayed unit inverse pairs, reduced modulo three. -/
def beta54057 (A : Finset (ZMod 9)) : ZMod 3 :=
  ((
      (if includedUnitPair54057 A 1 8 then 1 else 0) +
      (if includedUnitPair54057 A 2 7 then 1 else 0) +
      (if includedUnitPair54057 A 4 5 then 1 else 0)
    ) % 3 : ℕ)

/-- Coordinates in the fixed algebra with respect to `1,w,w^2,w^3,w^4`. -/
def wCoordinates54057 (A : Finset (ZMod 9))
    (c : Fin 5 → ZMod 3) : Prop :=
  sectionPolynomial54057 A =
    ∑ i : Fin 5, c i • w9 ^ (i : ℕ)

/-- The nilpotent valuation is infinite when the section is scalar. -/
def valuationInfinity54057 (A : Finset (ZMod 9)) : Prop :=
  ∃ c : ZMod 3, sectionPolynomial54057 A = c • (1 : C9GroupAlgebra)

/-- The first nonzero `w`-coordinate is the coefficient of `w`. -/
def valuationOne54057 (A : Finset (ZMod 9)) : Prop :=
  ∃ c : Fin 5 → ZMod 3,
    wCoordinates54057 A c ∧ c 1 ≠ 0

/-- A zero `w`- and `w^2`-coordinate with nonzero `w^3`-coordinate. -/
def valuationThree54057 (A : Finset (ZMod 9)) : Prop :=
  ∃ c : Fin 5 → ZMod 3,
    wCoordinates54057 A c ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 ≠ 0

/-- A zero `w`, `w^2`, and `w^3` coordinate with nonzero `w^4`-coordinate. -/
def valuationFour54057 (A : Finset (ZMod 9)) : Prop :=
  ∃ c : Fin 5 → ZMod 3,
    wCoordinates54057 A c ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧ c 4 ≠ 0

/-- The excluded valuation-two case. -/
def valuationTwo54057 (A : Finset (ZMod 9)) : Prop :=
  ∃ c : Fin 5 → ZMod 3,
    wCoordinates54057 A c ∧ c 1 = 0 ∧ c 2 ≠ 0

/-- The Frobenius derivative and complete finite valuation census for inverse-
closed sections of `C₉`. -/
def claim54057 : Prop :=
  (∀ A : Finset (ZMod 9),
      inverseClosed A →
        sectionPolynomial54057 A ^ 3 - sectionPolynomial54057 A ^ 9 =
          beta54057 A • w9 ^ 3) ∧
    (w9 ^ 3 = 1 + z9 ^ 3 + z9 ^ 6) ∧
    (∀ A : Finset (ZMod 9),
      inverseClosed A →
        ∃ c : Fin 5 → ZMod 3,
          wCoordinates54057 A c ∧ c 1 = beta54057 A) ∧
    (let allInverseClosed : Finset (Finset (ZMod 9)) :=
        (Finset.univ : Finset (Finset (ZMod 9))).filter inverseClosed
     allInverseClosed.card = 32 ∧
       (allInverseClosed.filter valuationInfinity54057).card = 2 ∧
       (allInverseClosed.filter valuationOne54057).card = 24 ∧
       (allInverseClosed.filter valuationThree54057).card = 4 ∧
       (allInverseClosed.filter valuationFour54057).card = 2 ∧
       (allInverseClosed.filter valuationTwo54057).card = 0)

end

end MathlibPlus.Open.ResearchFormalizationBatch_54057
