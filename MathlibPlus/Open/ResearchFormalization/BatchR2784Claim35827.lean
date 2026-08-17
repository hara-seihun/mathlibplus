import MathlibPlus.Open.ResearchFormalization.Lease01a0019fGraphOrbit

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35827

open MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

def lowerShadowsAgree35827 {n k : ℕ}
    (G H : EdgeSet n) : Prop :=
  ∀ j : ℕ, j < k → ∀ F : EdgeSet n, F.card = j →
    aX n G F = aX n H F

def firstDifference35827 {n : ℕ}
    (G H F : EdgeSet n) : ℤ :=
  (typeCountInGraph n G F : ℤ) - typeCountInGraph n H F

def normalizedDifference35827 {n : ℕ}
    (p : EdgeSet n → ℤ) (F : EdgeSet n) : ℝ :=
  ((p F : ℚ) / (labelledTypeCount n F : ℚ) : ℝ)

def rankAtMostFamily35827 {n k : ℕ}
    (𝒜 : Finset (EdgeSet n)) : Prop :=
  (∀ A ∈ 𝒜, A.card ≤ k / 2) ∧
  (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∪ B).card ≤ k)

abbrev FamilyIndex35827 {n : ℕ} (𝒜 : Finset (EdgeSet n)) :=
  IncidenceIndex n 𝒜

def momentEntry35827 {n : ℕ} (X : EdgeSet n)
    (𝒜 : Finset (EdgeSet n))
    (A B : FamilyIndex35827 𝒜) : ℝ :=
  (aX n X (A.1 ∪ B.1) : ℝ)

def orbitIncidenceGramCone35827 {n : ℕ}
    (X : EdgeSet n) (𝒜 : Finset (EdgeSet n))
    (M : Matrix (FamilyIndex35827 𝒜) (FamilyIndex35827 𝒜) ℝ) : Prop :=
  ∃ w : EdgeSet n → ℝ,
    (∀ Y : EdgeSet n, 0 ≤ w Y) ∧
    (∀ Y : EdgeSet n, Y ∉ graphOrbit n X → w Y = 0) ∧
    M = ∑ Y : EdgeSet n,
      w Y • outerProduct (incidenceVector n 𝒜 Y)
        (incidenceVector n 𝒜 Y)

def plusMomentMatrix35827 {n k : ℕ}
    (G : EdgeSet n) (p : EdgeSet n → ℤ) (q : EdgeSet n → ℝ)
    (𝒜 : Finset (EdgeSet n)) :
    Matrix (FamilyIndex35827 𝒜) (FamilyIndex35827 𝒜) ℝ :=
  fun A B =>
    let F := A.1 ∪ B.1
    if F.card = k then
      q F + normalizedDifference35827 p F / 2
    else
      (aX n G F : ℝ)

 def minusMomentMatrix35827 {n k : ℕ}
    (H : EdgeSet n) (p : EdgeSet n → ℤ) (q : EdgeSet n → ℝ)
    (𝒜 : Finset (EdgeSet n)) :
    Matrix (FamilyIndex35827 𝒜) (FamilyIndex35827 𝒜) ℝ :=
  fun A B =>
    let F := A.1 ∪ B.1
    if F.card = k then
      q F - normalizedDifference35827 p F / 2
    else
      (aX n H F : ℝ)

/-- The common lower-rank entries and the signed rank-`k` midpoint entries,
    together with membership in cones generated from the literal orbit
    incidence vectors. -/
def commonRankKMidpoint35827 {n k : ℕ}
    (G H : EdgeSet n) (p : EdgeSet n → ℤ)
    (𝒜 : Finset (EdgeSet n)) : Prop :=
  ∃ q : EdgeSet n → ℝ,
    (∀ A B : FamilyIndex35827 𝒜,
      (A.1 ∪ B.1).card < k →
        momentEntry35827 G 𝒜 A B = momentEntry35827 H 𝒜 A B) ∧
    (∀ A B : FamilyIndex35827 𝒜,
      (A.1 ∪ B.1).card = k →
        (momentEntry35827 G 𝒜 A B =
          q (A.1 ∪ B.1) +
            normalizedDifference35827 p (A.1 ∪ B.1) / 2) ∧
        (momentEntry35827 H 𝒜 A B =
          q (A.1 ∪ B.1) -
            normalizedDifference35827 p (A.1 ∪ B.1) / 2)) ∧
    orbitIncidenceGramCone35827 G 𝒜
      (plusMomentMatrix35827 (k := k) G p q 𝒜) ∧
    orbitIncidenceGramCone35827 H 𝒜
      (minusMomentMatrix35827 (k := k) H p q 𝒜)

/-- Claim 35827: a host-realizable integer first-difference vector admits
    the common midpoint and the two literal orbit-incidence Gram-cone
    endpoints. -/
def gramConeMidpoint_claim35827 : Prop :=
  ∀ (n k m : ℕ) (G H : EdgeSet n) (p : EdgeSet n → ℤ),
    G.card = m → H.card = m →
      lowerShadowsAgree35827 (k := k) G H →
      (∀ F : EdgeSet n, F.card = k →
        p F = firstDifference35827 G H F) →
      ∀ 𝒜 : Finset (EdgeSet n),
        rankAtMostFamily35827 (k := k) 𝒜 →
          commonRankKMidpoint35827 (k := k) G H p 𝒜

end
end MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35827
