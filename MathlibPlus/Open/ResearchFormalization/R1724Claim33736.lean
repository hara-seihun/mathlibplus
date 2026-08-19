import MathlibPlus.Open.ResearchFormalization.R1724Claim33727
import MathlibPlus.Open.ResearchFormalization.R1724Claim33728
import MathlibPlus.Open.ResearchFormalization.R1724Claim33738

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1724Claim33736

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1724Claim33727
open MathlibPlus.Open.ResearchFormalization.R1724Claim33738
open MathlibPlus.Open.ResearchFormalizationBatch

abbrev XPoly33736 := MvPolynomial ℕ ℚ
abbrev RootedTree33736 :=
  MathlibPlus.Open.ResearchFormalization.R1724Claim33727.RootedTree

def rowDifference33736 (k : ℕ)
    (A B : Multiset RootedTree33736) : XPoly33736 :=
  row k A - row k B

noncomputable def rationalCutTowerCombination33736
    (d : ℕ) (c : SimpleGraph (Fin d) →₀ ℚ) : XPoly33736 :=
  ∑ T ∈ c.support, c T • uPoly33738 T

def xOneFree33736 (P : XPoly33736) : Prop :=
  MvPolynomial.pderiv 1 P = 0

def supportedOnTrees33736
    {d : ℕ} (c : SimpleGraph (Fin d) →₀ ℚ) : Prop :=
  ∀ T, c T ≠ 0 → T.IsTree

def halfIntegralExample33736 : XPoly33736 :=
  (1 / 2 : ℚ) •
    (MvPolynomial.X 3 ^ 2 -
      MvPolynomial.X 2 * MvPolynomial.X 4)

/-- Claim 33736: clearing the finite rational coefficients of an `x₁`-free
    cut-tower combination yields a positive integer multiple realized by an
    actual rooted-tree pruning-row difference; the displayed half-integral
    polynomial is not itself an unscaled row difference. -/
def rationalizedCapGroup_claim33736 : Prop :=
  (∀ (d : ℕ) (c : SimpleGraph (Fin d) →₀ ℚ),
    supportedOnTrees33736 c →
      xOneFree33736 (rationalCutTowerCombination33736 d c) →
        ∃ q : ℕ, 0 < q ∧
          ∃ A B : Multiset RootedTree33736,
            totalWeight A = totalWeight B ∧
              (∀ k : ℕ, k < d → row k A = row k B) ∧
                markedRow d A = markedRow d B ∧
                  rowDifference33736 d A B =
                    (q : ℚ) • rationalCutTowerCombination33736 d c) ∧
  (∀ A B : Multiset RootedTree33736,
    rowDifference33736 6 A B ≠ halfIntegralExample33736)

end

end MathlibPlus.Open.ResearchFormalization.R1724Claim33736
