import Mathlib

noncomputable section

namespace MathlibPlus.Open

open Polynomial

private def qTrace : Polynomial ℤ :=
  X ^ 7 - 8 * X ^ 5 + 19 * X ^ 3 - 12 * X + 1

private def qComplex : Polynomial ℂ :=
  qTrace.map (algebraMap ℤ ℂ)

/-- Claim 42105: Q is irreducible over the integers (and rationals), with all
seven complex roots real. -/
def claim_42105 : Prop :=
  Irreducible qTrace ∧
    Irreducible (qTrace.map (algebraMap ℤ ℚ)) ∧
    qComplex.natDegree = 7 ∧
    ∀ z : ℂ, IsRoot qComplex z → z.im = 0

/-- Claim 42106: exactly one root of Q is outside [-2,2], and the remaining
six roots are in that interval. -/
def claim_42106 : Prop :=
  qComplex.natDegree = 7 ∧
    qComplex.roots.card = 7 ∧
    (qComplex.roots.filter
      (fun z => z.im = 0 ∧ (z.re < -2 ∨ 2 < z.re))).card = 1 ∧
    (qComplex.roots.filter
      (fun z => z.im = 0 ∧ -2 ≤ z.re ∧ z.re ≤ 2)).card = 6 ∧
    ∀ z ∈ qComplex.roots, z.im = 0

private def rootsInTraceInterval (p : Polynomial ℤ) : Prop :=
  ∀ z : ℂ, IsRoot (p.map (algebraMap ℤ ℂ)) z →
    z.im = 0 ∧ -2 ≤ z.re ∧ z.re ≤ 2

/-- Claim 42112: Q has no integer symmetric characteristic-polynomial
complement whose roots all lie in [-2,2]. -/
def claim_42112 : Prop :=
  ¬ ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (C : Polynomial ℤ),
    M.IsSymm ∧ rootsInTraceInterval C ∧ Matrix.charpoly M = qTrace * C

private noncomputable def treeAdjacencyMatrix (n : ℕ)
    (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ := by
  classical
  exact G.adjMatrix ℤ

private def treeCharpoly (n : ℕ) (G : SimpleGraph (Fin n)) : Polynomial ℚ :=
  (Matrix.charpoly (treeAdjacencyMatrix n G)).map (algebraMap ℤ ℚ)

private def totallyRealAlgebraicInteger (α : ℂ) : Prop :=
  IsIntegral ℤ α ∧ IsAlgebraic ℚ α ∧
    ∀ z : ℂ,
      IsRoot ((minpoly ℚ α).map (algebraMap ℚ ℂ)) z → z.im = 0

private def treeRoot (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℂ) : Prop :=
  IsRoot ((treeCharpoly n G).map (algebraMap ℚ ℂ)) α

/-- Claim 42110: every totally real algebraic integer is a finite-tree
adjacency eigenvalue, equivalently its minimal polynomial divides a finite-tree
characteristic polynomial. -/
def claim_42110 : Prop :=
  ∀ α : ℂ, totallyRealAlgebraicInteger α →
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.IsTree ∧ treeRoot n G α) ∧
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.IsTree ∧ minpoly ℚ α ∣ treeCharpoly n G)

/-- Claim 41266: the arithmetic consequence of the two displayed identities
in the leaf-rooted comparison. -/
def claim_41266 : Prop :=
  ∀ a b c d : ℕ,
    2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 2 ≤ d →
    a * (a - 1) * b * (b - 1) = c * (c - 1) * d * (d - 1) →
    (a : ℚ) + b - 6 / a = (c : ℚ) + d - 6 / c →
    a > c →
      ((d : ℚ) - b = ((a - c : ℕ) : ℚ) * (a * c + 6) / (a * c) ∧
        a * c ∣ 6 * (a - c) ∧
        c < 6 ∧
        a ∣ 6 * c ∧
        ((a, c) = (3, 2) ∨ (a, c) = (6, 2) ∨ (a, c) = (6, 3) ∨
          (a, c) = (12, 4) ∨ (a, c) = (30, 5)))

/-- Claim 42123: sufficiently high 3-power cyclotomic roots do not lie in a
fixed finite extension of the 3-adic field. -/
def claim_42123 : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ_[3] K]
    [FiniteDimensional ℚ_[3] K],
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ z : K,
        ¬ IsRoot ((cyclotomic (3 ^ k) ℤ).map (algebraMap ℤ K)) z

end MathlibPlus.Open
