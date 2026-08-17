import Mathlib
import MathlibPlus.NumberTheory.Claim44305
import MathlibPlus.GraphTheory.LabelledCopyCount
import MathlibPlus.GraphTheory.Claim44511

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R2895R2330

/-- The dyadic sequence in the exact positive-index representation carrier. -/
def dyadicWeight (n : ℕ) : ℚ :=
  (n : ℚ) / (2 : ℚ) ^ n

def consecutiveDyadicRepresentation (m : ℕ) : Prop :=
  let n := 2 ^ (m + 1) - m - 2
  3 ≤ n ∧
    dyadicWeight n =
      ∑ d ∈ Finset.Icc 1 m, dyadicWeight (n + d)

/-- Claim 44307: every m≥2 supplies the consecutive representation at the
explicit target n_m, and the resulting target set is infinite. -/
def consecutiveDyadicRepresentation_claim44307 : Prop :=
  (∀ m : ℕ, 2 ≤ m → consecutiveDyadicRepresentation m) ∧
    Set.Infinite
      {n : ℕ | ∃ m : ℕ, 2 ≤ m ∧ n = 2 ^ (m + 1) - m - 2}

/-- The Boolean adjacency interpretations used by the labelled-copy carrier. -/
def booleanGraphInterpretation
    {n : ℕ} (G : SimpleGraph (Fin n))
    (adj : Fin n → Fin n → Bool) : Prop :=
  ∀ i j, G.Adj i j ↔ adj i j = true

/-- Claim 44512: after fixing the Boolean pattern and host interpretations,
the induced deleted card and its canonical `succAbove` relabeling have equal
labelled copy counts. -/
def deletedCardLabelledCopyTransport_claim44512 : Prop := by
  classical
  exact ∀ (patternOrder hostOrder : ℕ)
    (pattern : Fin patternOrder → Fin patternOrder → Bool)
    (host : Fin (hostOrder + 1) → Fin (hostOrder + 1) → Bool)
    (P : SimpleGraph (Fin patternOrder))
    (H : SimpleGraph (Fin (hostOrder + 1)))
    (patternSymmetric : ∀ i j, pattern i j = true → pattern j i = true)
    (patternIrreflexive : ∀ i, pattern i i = false)
    (hostSymmetric : ∀ i j, host i j = true → host j i = true)
    (hostIrreflexive : ∀ i, host i i = false)
    (patternInterpreted : booleanGraphInterpretation P pattern)
    (hostInterpreted : booleanGraphInterpretation H host)
    (deleted : Fin (hostOrder + 1)),
    letI : Fintype {x : Fin (hostOrder + 1) // x ≠ deleted} :=
      Fintype.ofFinite _
    (H.induce {x : Fin (hostOrder + 1) | x ≠ deleted}).labelledCopyCount P =
      (H.comap deleted.succAbove).labelledCopyCount P

end MathlibPlus.Open.ResearchFormalization.R2895R2330
