import Mathlib

namespace MathlibPlus.Open.ResearchFormalizeBatch

abbrev SpiderVertex (r m : ℕ) := Option (Fin r ⊕ (Fin m × Fin 3))

def armAdjacent (j k : Fin 3) : Prop :=
  (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨
    (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)

def spiderEdge (r m : ℕ) : SpiderVertex r m → SpiderVertex r m → Prop
  | none, some (Sum.inl _) => True
  | some (Sum.inl _), none => True
  | none, some (Sum.inr (_, j)) => j = 0
  | some (Sum.inr (_, j)), none => j = 0
  | some (Sum.inr (i, j)), some (Sum.inr (i', k)) => i = i' ∧ armAdjacent j k
  | _, _ => False

def spiderIndependent {r m : ℕ} (s : Finset (SpiderVertex r m)) : Prop :=
  ∀ ⦃v w : SpiderVertex r m⦄, v ∈ s → w ∈ s → v ≠ w → ¬ spiderEdge r m v w

noncomputable def spiderIndependencePolynomial (r m : ℕ) : Polynomial ℤ := by
  classical
  exact ∑ s : Finset (SpiderVertex r m),
    if spiderIndependent s then (Polynomial.X : Polynomial ℤ) ^ s.card else 0

/-- Claim 48186: centre conditioning for three arms of length three. -/
def claim_48186 : Prop :=
  ∀ r : ℕ,
    spiderIndependencePolynomial r 3 =
      (1 + Polynomial.X) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
        Polynomial.X * (1 + 2 * Polynomial.X) ^ 3

/-- Claim 48219: centre conditioning for four arms of length three. -/
def claim_48219 : Prop :=
  ∀ r : ℕ,
    spiderIndependencePolynomial r 4 =
      (1 + Polynomial.X) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 4 +
        Polynomial.X * (1 + 2 * Polynomial.X) ^ 4

end MathlibPlus.Open.ResearchFormalizeBatch
