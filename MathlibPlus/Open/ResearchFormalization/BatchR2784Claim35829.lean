import MathlibPlus.Open.ResearchFormalization.Lease01a0019fGraphOrbit

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35829

open MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

def lowerShadowsAgree35829 {n k : ℕ}
    (G H : EdgeSet n) : Prop :=
  ∀ j : ℕ, j < k → ∀ F : EdgeSet n, F.card = j →
    aX n G F = aX n H F

def firstDifference35829 {n : ℕ}
    (G H F : EdgeSet n) : ℤ :=
  (typeCountInGraph n G F : ℤ) - typeCountInGraph n H F

def normalizedDifference35829 {n : ℕ}
    (p : EdgeSet n → ℤ) (F : EdgeSet n) : ℚ :=
  (p F : ℚ) / (labelledTypeCount n F : ℚ)

def rankAtMostFamily35829 {n k : ℕ}
    (𝒜 : Finset (EdgeSet n)) : Prop :=
  (∀ A ∈ 𝒜, A.card ≤ k / 2) ∧
  (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∪ B).card ≤ k)

abbrev FamilyIndex35829 {n : ℕ} (𝒜 : Finset (EdgeSet n)) :=
  IncidenceIndex n 𝒜

def momentEntry35829 {n : ℕ} (X : EdgeSet n)
    (𝒜 : Finset (EdgeSet n))
    (A B : FamilyIndex35829 𝒜) : ℝ :=
  (aX n X (A.1 ∪ B.1) : ℝ)

def orbitIncidenceGramCone35829 {n : ℕ}
    (X : EdgeSet n) (𝒜 : Finset (EdgeSet n))
    (M : Matrix (FamilyIndex35829 𝒜) (FamilyIndex35829 𝒜) ℝ) : Prop :=
  ∃ w : EdgeSet n → ℝ,
    (∀ Y : EdgeSet n, 0 ≤ w Y) ∧
    (∀ Y : EdgeSet n, Y ∉ graphOrbit n X → w Y = 0) ∧
    M = ∑ Y : EdgeSet n,
      w Y • outerProduct (incidenceVector n 𝒜 Y)
        (incidenceVector n 𝒜 Y)

def plusMomentMatrix35829 {n k : ℕ}
    (X : EdgeSet n) (p : EdgeSet n → ℤ) (q : EdgeSet n → ℝ)
    (𝒜 : Finset (EdgeSet n)) :
    Matrix (FamilyIndex35829 𝒜) (FamilyIndex35829 𝒜) ℝ :=
  fun A B =>
    let F := A.1 ∪ B.1
    if F.card = k then
      q F + ((p F : ℚ) /
        (labelledTypeCount n F : ℚ) : ℝ) / 2
    else
      (aX n X F : ℝ)

def minusMomentMatrix35829 {n k : ℕ}
    (X : EdgeSet n) (p : EdgeSet n → ℤ) (q : EdgeSet n → ℝ)
    (𝒜 : Finset (EdgeSet n)) :
    Matrix (FamilyIndex35829 𝒜) (FamilyIndex35829 𝒜) ℝ :=
  fun A B =>
    let F := A.1 ∪ B.1
    if F.card = k then
      q F - ((p F : ℚ) /
        (labelledTypeCount n F : ℚ) : ℝ) / 2
    else
      (aX n X F : ℝ)

def commonRankKMidpoint35829 {n k : ℕ}
    (G H : EdgeSet n) (p : EdgeSet n → ℤ)
    (𝒜 : Finset (EdgeSet n)) : Prop :=
  ∃ q : EdgeSet n → ℝ,
    (∀ A B : FamilyIndex35829 𝒜,
      (A.1 ∪ B.1).card < k →
        momentEntry35829 G 𝒜 A B = momentEntry35829 H 𝒜 A B) ∧
    (∀ A B : FamilyIndex35829 𝒜,
      (A.1 ∪ B.1).card = k →
        (momentEntry35829 G 𝒜 A B =
          q (A.1 ∪ B.1) +
            ((p (A.1 ∪ B.1) : ℚ) /
              (labelledTypeCount n (A.1 ∪ B.1) : ℚ) : ℝ) / 2) ∧
        (momentEntry35829 H 𝒜 A B =
          q (A.1 ∪ B.1) -
            ((p (A.1 ∪ B.1) : ℚ) /
              (labelledTypeCount n (A.1 ∪ B.1) : ℚ) : ℝ) / 2)) ∧
    orbitIncidenceGramCone35829 G 𝒜
      (plusMomentMatrix35829 (k := k) G p q 𝒜) ∧
    orbitIncidenceGramCone35829 H 𝒜
      (minusMomentMatrix35829 (k := k) H p q 𝒜)

noncomputable def edgeSetCode35829 {n : ℕ} (F : EdgeSet n) : ℕ :=
  (Fintype.equivFin (EdgeSet n) F).val

def typeCanonical35829 {n : ℕ} (F : EdgeSet n) : Prop :=
  ∀ H : EdgeSet n, sameEdgeType n F H →
    edgeSetCode35829 F ≤ edgeSetCode35829 H

noncomputable def typeRepresentatives35829 (n r : ℕ) : Finset (EdgeSet n) :=
  @Finset.filter (EdgeSet n)
    (fun F => typeCanonical35829 F ∧ F.card = r)
    (fun F => Classical.propDecidable _) (Finset.univ : Finset (EdgeSet n))

def exactTypeMassEquations35829 {n m : ℕ} (X : EdgeSet n) : Prop :=
  (∀ F : EdgeSet n,
    (labelledTypeCount n F : ℚ) * aX n X F =
      (typeCountInGraph n X F : ℚ) ∧
    0 ≤ (typeCountInGraph n X F : ℤ)) ∧
  (∀ t : ℕ,
    ∑ F ∈ typeRepresentatives35829 n t,
      typeCountInGraph n X F = Nat.choose m t)

def properBooleanShadow35829 {n : ℕ}
    (X F B : EdgeSet n) : ℚ :=
  ∑ C ∈ B.powerset.filter (fun C => C ⊂ B),
    (-1 : ℚ) ^ C.card * aX n X ((F \ B) ∪ C)

noncomputable def rationalSup35829 (s : Finset ℚ) : ℚ :=
  if h : s.Nonempty then s.sup' h (fun x => x) else 0

noncomputable def rationalInf35829 (s : Finset ℚ) : ℚ :=
  if h : s.Nonempty then s.inf' h (fun x => x) else 1

noncomputable def evenLowerBounds35829 {n : ℕ}
    (G F : EdgeSet n) : Finset ℚ :=
  {0} ∪
    (F.powerset.filter (fun B => B.Nonempty ∧ Even B.card)).image
      (fun B => -properBooleanShadow35829 G F B)

noncomputable def oddUpperBounds35829 {n : ℕ}
    (G F : EdgeSet n) : Finset ℚ :=
  {1} ∪
    (F.powerset.filter (fun B => B.Nonempty ∧ Odd B.card)).image
      (fun B => properBooleanShadow35829 G F B)

def firstRankIntervalBounds35829 {n k : ℕ}
    (G H : EdgeSet n) (p : EdgeSet n → ℤ) (F : EdgeSet n) : Prop :=
  F.card = k →
    let lower := rationalSup35829 (evenLowerBounds35829 G F)
    let upper := rationalInf35829 (oddUpperBounds35829 G F)
    lower ≤ aX n G F ∧ lower ≤ aX n H F ∧
      aX n G F ≤ upper ∧ aX n H F ≤ upper ∧
      |normalizedDifference35829 p F| ≤ upper - lower

/-- Claim 35829: the Boolean--Möbius, first-rank, interval, literal
    orbit-incidence cone, and exact lattice/mass records hold for every
    realized pair of equal-edge hosts, without a connectedness restriction. -/
def completeFirstShadowRecord_claim35829 : Prop :=
  ∀ (n m k : ℕ) (G H : EdgeSet n),
    G.card = m → H.card = m →
      lowerShadowsAgree35829 (k := k) G H →
      (∀ A B : EdgeSet n, Disjoint A B → A.card + B.card ≤ k →
        0 ≤ bX n G A B ∧ 0 ≤ bX n H A B) ∧
      (∀ A B : EdgeSet n, Disjoint A B → A.card + B.card = k →
        bX n G A B - bX n H A B =
          (-1 : ℚ) ^ B.card *
            ((firstDifference35829 G H (A ∪ B) : ℚ) /
              (labelledTypeCount n (A ∪ B) : ℚ))) ∧
      (∀ F : EdgeSet n,
        firstRankIntervalBounds35829 (k := k) G H
          (fun F => firstDifference35829 G H F) F) ∧
      (∀ 𝒜 : Finset (EdgeSet n),
        rankAtMostFamily35829 (k := k) 𝒜 →
          commonRankKMidpoint35829 (k := k) G H
            (fun F => firstDifference35829 G H F) 𝒜) ∧
      exactTypeMassEquations35829 (m := m) G ∧
      exactTypeMassEquations35829 (m := m) H

end
end MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35829
