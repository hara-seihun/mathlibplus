import MathlibPlus.Open.ResearchFormalization.Lease01a0019fGraphOrbit

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35823

open MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

def lowerShadowsAgree35823 {n k : ℕ}
    (G H : EdgeSet n) : Prop :=
  ∀ j : ℕ, j < k → ∀ F : EdgeSet n, F.card = j →
    aX n G F = aX n H F

def firstDifference35823 {n : ℕ}
    (G H F : EdgeSet n) : ℤ :=
  (typeCountInGraph n G F : ℤ) - typeCountInGraph n H F

def record3Hypotheses35823 {n k m : ℕ}
    (G H : EdgeSet n) : Prop :=
  G.card = m ∧ H.card = m ∧ lowerShadowsAgree35823 (k := k) G H

/-- Claim 35823: the first differing rank is the integer type-count
    difference over the number of labelled representatives. -/
def firstRankBooleanDifference_claim35823 : Prop :=
  ∀ (n k m : ℕ) (G H : EdgeSet n),
    record3Hypotheses35823 (k := k) (m := m) G H →
      ∀ A B : EdgeSet n, Disjoint A B → A.card + B.card = k →
        bX n G A B - bX n H A B =
          (-1 : ℚ) ^ B.card *
            (firstDifference35823 G H (A ∪ B) : ℚ) /
              (labelledTypeCount n (A ∪ B) : ℚ) ∧
        (∀ C : EdgeSet n, C ⊂ A ∪ B →
          aX n G C = aX n H C)

end
end MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35823
