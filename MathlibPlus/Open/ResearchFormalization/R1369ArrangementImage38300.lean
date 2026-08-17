import MathlibPlus.Open.ResearchFormalizationBatch_01a003cb_d995_7564_b82d_d782ff7e0528

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R1369ArrangementImage38300

noncomputable section

abbrev TernaryScalar :=
  MathlibPlus.Open.ResearchFormalizationBatch.TernaryScalar
abbrev TernaryDualCarrier :=
  MathlibPlus.Open.ResearchFormalizationBatch.TernaryDualCarrier
abbrev Character :=
  TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar

abbrev H1 := Fin 1 → TernaryScalar
abbrev H2 := Fin 2 → TernaryScalar

/-- The four projected characters in the fixed order. -/
def characterList : Fin 4 → Character :=
  ![
    MathlibPlus.Open.ResearchFormalizationBatch.epsilonOne,
    MathlibPlus.Open.ResearchFormalizationBatch.epsilonTwo,
    MathlibPlus.Open.ResearchFormalizationBatch.epsilonPlus,
    MathlibPlus.Open.ResearchFormalizationBatch.epsilonMinus
  ]

abbrev Arrangement (H : Type*) [AddCommGroup H] [Module TernaryScalar H] :=
  Fin 4 → Submodule TernaryScalar H

abbrev SlopeFamily (H : Type*) [AddCommGroup H] [Module TernaryScalar H]
    (A : Arrangement H) :=
  ∀ i : Fin 4, A i →ₗ[TernaryScalar] TernaryScalar

/-- Image of normalized potentials satisfying all four projected derivative
 equations. -/
def potentialImage {H : Type*} [AddCommGroup H] [Module TernaryScalar H]
    (A : Arrangement H) : Set (SlopeFamily H A) :=
  {b |
    ∃ C : H → TernaryDualCarrier,
      C 0 = 0 ∧
        (∀ i : Fin 4, ∀ h : H, h ∈ A i →
          ∀ x : H,
            characterList i (C (x + h)) - characterList i (C x) =
              characterList i (C h)) ∧
        ∀ i : Fin 4, ∀ h : A i,
          b i h = characterList i (C h)}

/-- Image of the global linear restriction map on the four subspaces. -/
def restrictionImage {H : Type*} [AddCommGroup H] [Module TernaryScalar H]
    (A : Arrangement H) : Set (SlopeFamily H A) :=
  {b |
    ∃ ell : H →ₗ[TernaryScalar] TernaryDualCarrier,
      ∀ i : Fin 4, ∀ h : A i,
        b i h = characterList i (ell h)}

/-- Claim 38300: the two finite rank slices have 16 and 1,296 arrangements,
and every arrangement has no deficiency between normalized-potential and
global-linear images. -/
def claim38300 : Prop :=
  Nat.card (Submodule TernaryScalar H1) = 2 ∧
    Nat.card (Submodule TernaryScalar H2) = 6 ∧
      Nat.card (Arrangement H1) = 2 ^ 4 ∧
        Nat.card (Arrangement H2) = 6 ^ 4 ∧
          (∀ A : Arrangement H1,
            potentialImage A = restrictionImage A) ∧
            (∀ A : Arrangement H2,
              potentialImage A = restrictionImage A)

end

end MathlibPlus.Open.ResearchFormalization.R1369ArrangementImage38300
