import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1892BalancedMediumDegreeClaim34732

noncomputable section

private abbrev ResidualCoordinate (m t : ℕ) :=
  {S : Finset (Fin m) // S.card = t}

private abbrev ConeGround (m t r : ℕ) :=
  Sum (Fin (r + 1)) (ResidualCoordinate m t)

private def allCoordinates (m t : ℕ) : Finset (ResidualCoordinate m t) :=
  Finset.univ

private def residualMember (m t : ℕ) (i : Fin m) :
    Finset (ResidualCoordinate m t) :=
  (allCoordinates m t).filter (fun S => i ∈ S.1)

private def residualDegree (m t : ℕ)
    (S : ResidualCoordinate m t) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter
    (fun i => S ∈ residualMember m t i)).card

private def threeSunflower {β : Type*} [DecidableEq β]
    (X Y Z : Finset β) : Prop :=
  X ∩ Y = X ∩ Z ∧ X ∩ Y = Y ∩ Z

private def familyPairwiseIntersecting {β : Type*} [DecidableEq β]
    (F : Finset (Finset β)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → (X ∩ Y).Nonempty

private def familyThreeSunflowerFree {β : Type*} [DecidableEq β]
    (F : Finset (Finset β)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, ∀ Z ∈ F,
    X ≠ Y → X ≠ Z → Y ≠ Z → ¬ threeSunflower X Y Z

private def conePoint (m t r : ℕ) : ConeGround m t r :=
  Sum.inl (0 : Fin (r + 1))

private def conePaddingSet (m t r : ℕ) : Finset (ConeGround m t r) :=
  (Finset.univ : Finset (Fin r)).image
    (fun j => (Sum.inl (Fin.succ j) : ConeGround m t r))

private def conePivot (m t r : ℕ) : Finset (ConeGround m t r) :=
  insert (conePoint m t r) (conePaddingSet m t r)

private def embedResidual (m t r : ℕ)
    (S : Finset (ResidualCoordinate m t)) : Finset (ConeGround m t r) :=
  S.image (fun x => (Sum.inr x : ConeGround m t r))

private def coneMember (m t r : ℕ) (H : Fin m → Finset (ResidualCoordinate m t))
    (i : Fin m) : Finset (ConeGround m t r) :=
  insert (conePoint m t r) (embedResidual m t r (H i))

private def coneFamily (m t r : ℕ)
    (H : Fin m → Finset (ResidualCoordinate m t)) :
    Finset (Finset (ConeGround m t r)) :=
  insert (conePivot m t r)
    ((Finset.univ : Finset (Fin m)).image (coneMember m t r H))

private def coneResidualDegree (m t r : ℕ)
    (F : Finset (Finset (ConeGround m t r)))
    (A : Finset (ConeGround m t r))
    (S : ResidualCoordinate m t) : ℕ :=
  ((F.erase A).filter
    (fun X => (Sum.inr S : ConeGround m t r) ∈ X)).card

private def pivotTraceValues {β : Type*} [DecidableEq β]
    (F : Finset (Finset β)) (A : Finset β) : Finset (Finset β) :=
  (F.erase A).image (fun X => A ∩ X)

private def balancedResidualFamily (m t : ℕ) :
    Fin m → Finset (ResidualCoordinate m t) :=
  residualMember m t

/-- Exact balanced medium-degree residual specialization and its actual-pivot cone. -/
def balancedMediumDegreeResidualSpecialization_claim34732 : Prop :=
  ∀ (m t : ℕ), 4 ≤ m → 2 ≤ t → t ≤ m - 1 →
    let r := Nat.choose (m - 1) (t - 1)
    let H := balancedResidualFamily m t
    let A := conePivot m t r
    let F := coneFamily m t r H
    Function.Injective H ∧
      (∀ i : Fin m, (H i).card = r) ∧
      familyPairwiseIntersecting (Finset.univ.image H) ∧
      familyThreeSunflowerFree (Finset.univ.image H) ∧
      (∀ i j k : Fin m,
        i ≠ j → i ≠ k → j ≠ k →
        H i ∩ H j ≠ H i ∩ H k) ∧
      (∀ i j k : Fin m,
        i ≠ j → i ≠ k → j ≠ k →
        ∃ S : ResidualCoordinate m t,
          i ∈ S.1 ∧ j ∈ S.1 ∧ k ∉ S.1) ∧
      (∀ S : ResidualCoordinate m t, residualDegree m t S = t) ∧
      (allCoordinates m t).card = Nat.choose m t ∧
      F.card = m + 1 ∧
      (∀ X ∈ F, X.card = r + 1) ∧
      familyPairwiseIntersecting F ∧
      familyThreeSunflowerFree F ∧
      A ∈ F ∧
      (∀ i : Fin m,
        coneMember m t r H i \ A = embedResidual m t r (H i)) ∧
      (∀ i : Fin m, ∀ S : ResidualCoordinate m t,
        ((Sum.inr S : ConeGround m t r) ∈ coneMember m t r H i ↔
          S ∈ H i)) ∧
      (∀ i j k : Fin m,
        i ≠ j → i ≠ k → j ≠ k →
        (threeSunflower (coneMember m t r H i)
          (coneMember m t r H j) (coneMember m t r H k) ↔
          threeSunflower (H i) (H j) (H k))) ∧
      (∀ i j : Fin m, i ≠ j →
        ¬ threeSunflower A (coneMember m t r H i)
          (coneMember m t r H j)) ∧
      pivotTraceValues F A =
        insert ({conePoint m t r} : Finset (ConeGround m t r))
          (∅ : Finset (Finset (ConeGround m t r))) ∧
      (∀ T : Finset (ConeGround m t r), 2 ≤ T.card →
        (F.erase A).filter (fun X => A ∩ X = T) = ∅) ∧
      (∀ S : ResidualCoordinate m t,
        coneResidualDegree m t r F A S = t)

end

end MathlibPlus.Open.ResearchFormalization.R1892BalancedMediumDegreeClaim34732
