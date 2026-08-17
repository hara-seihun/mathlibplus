import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

noncomputable section

private abbrev SixEmbeddingMonomial (d : Fin 6) := Fin (d.val + 1) → Fin 3
private abbrev SixEmbeddingFamily := Σ d : Fin 6, SixEmbeddingMonomial d

private def monomialDegree {d : Fin 6} (m : SixEmbeddingMonomial d) : ℕ :=
  ∑ i : Fin (d.val + 1), (m i).val

private def monomialDivides {d : Fin 6}
    (a b : SixEmbeddingMonomial d) : Prop :=
  ∀ i, (a i).val ≤ (b i).val

private def positiveDivisorCount {d : Fin 6}
    (m : SixEmbeddingMonomial d) : ℕ :=
  (∏ i : Fin (d.val + 1), (m i).val + 1) - 1

private def degreeAtLeastFour : Finset SixEmbeddingFamily := by
  classical
  exact Finset.univ.filter (fun m => 4 ≤ monomialDegree m.2)

private abbrev shadowFamily :=
  Σ d : Fin 6, Finset (SixEmbeddingMonomial d) ×
    Finset (SixEmbeddingMonomial d)

private def embeddingDimension (s : shadowFamily) : ℕ := s.1.val + 1

private def shadowDegreeTwo (s : shadowFamily) : Finset (SixEmbeddingMonomial s.1) :=
  s.2.1

private def shadowDegreeThree (s : shadowFamily) : Finset (SixEmbeddingMonomial s.1) :=
  s.2.2

private def validShadow (s : shadowFamily) : Prop :=
  (∀ m ∈ shadowDegreeTwo s, monomialDegree m = 2) ∧
    (∀ m ∈ shadowDegreeThree s, monomialDegree m = 3) ∧
    (shadowDegreeThree s).Nonempty ∧
    embeddingDimension s + (shadowDegreeTwo s).card +
        (shadowDegreeThree s).card = 6 ∧
    (∀ c ∈ shadowDegreeThree s, ∀ q : SixEmbeddingMonomial s.1,
      monomialDegree q = 2 → monomialDivides q c → q ∈ shadowDegreeTwo s)

private def shadowCount (e w z : ℕ) : ℕ := by
  classical
  exact
    (Finset.univ.filter (fun s : shadowFamily =>
      validShadow s ∧ embeddingDimension s = e ∧
        (shadowDegreeTwo s).card = w ∧ (shadowDegreeThree s).card = z)).card

/-- The exact six-dimensional cube-free divisor-downset census: the degree-at
least-four divisor obstruction, the two nonzero-cubic Hilbert-shadow counts,
and the absence of any other nonzero-cubic tuple. -/
def sixDimensionalDivisorDownset_claim40281 : Prop := by
  classical
  exact
    (∀ m ∈ degreeAtLeastFour, 8 ≤ positiveDivisorCount m.2) ∧
      (∃ m ∈ degreeAtLeastFour, positiveDivisorCount m.2 = 8) ∧
      shadowCount 2 3 1 = 2 ∧
      shadowCount 3 2 1 = 6 ∧
      (∀ e w z : ℕ, shadowCount e w z ≠ 0 →
        (e = 2 ∧ w = 3 ∧ z = 1) ∨
          (e = 3 ∧ w = 2 ∧ z = 1)) ∧
      (∀ s : shadowFamily, validShadow s →
        (shadowDegreeThree s).card ≤ 1) ∧
      (∃ s : shadowFamily, validShadow s ∧
        (shadowDegreeThree s).card = 1)

end
end MathlibPlus.Open.Combinatorics
