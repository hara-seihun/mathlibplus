import Mathlib
import MathlibPlus.Open.Research.R0333PTEClaims

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Research.R0333DegreeAndCuts

open MathlibPlus.Open.Research.R0333

noncomputable section

/-- The finite degree count on the literal PTE-tree graph carrier. -/
noncomputable def pteDegree_claim19991
    {α m : ℕ} (p : Fin m → ℕ) (v : PteVertex α m) : ℕ :=
  (Finset.univ.filter (fun w => (pteGraph α m p).Adj v w)).card

/-- The degree multiset of the literal PTE-tree graph carrier. -/
def pteDegreeSequence_claim19991
    (α m : ℕ) (p : Fin m → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset (PteVertex α m)).val.map
    (pteDegree_claim19991 p)

/-- The literal degree-profile assertions for the PTE-tree construction. -/
def pteDegreeProfile_claim19991
    (α m : ℕ) (p : Fin m → ℕ) : Prop :=
  pteCompatible α m p →
    (Fintype.card (PteVertex α m) = pteOrder α m) ∧
    (∀ i : Fin m,
      pteDegree_claim19991 (α := α) (m := m) p
          (pteBranchRoot i) = α + 1) ∧
    (∀ i : Fin m, ∀ j : Fin α, ∀ k : Fin 3,
      pteDegree_claim19991 (α := α) (m := m) p
          (pteArmVertex i j k) ≤ 3) ∧
    pteDegree_claim19991 (α := α) (m := m) p
        (pteCenter (α := α) (m := m)) = m

/-- Order and the literal degree sequence determine the PTE parameters, with
all four exceptional orders retained. -/
def claim19991 : Prop :=
  (∀ (α m : ℕ) (p : Fin m → ℕ),
    pteDegreeProfile_claim19991 α m p) ∧
  (∀ (α m α' m' : ℕ)
      (p : Fin m → ℕ) (p' : Fin m' → ℕ),
    pteCompatible α m p →
    pteCompatible α' m' p' →
    pteOrder α m = pteOrder α' m' →
    pteDegreeSequence_claim19991 α m p =
      pteDegreeSequence_claim19991 α' m' p' →
    α = α' ∧ m = m') ∧
  pteOrder 1 2 = 9 ∧
  pteOrder 1 3 = 13 ∧
  pteOrder 2 2 = 15 ∧
  pteOrder 2 3 = 22

/-- The singleton-cut coefficient and edge-cut count use the same literal
PTE-tree graph and the same partition carrier. -/
def claim19993 : Prop :=
  ∀ (α m : ℕ) (p : Fin m → ℕ) (k : ℕ),
    pteCompatible α m p →
    1 ≤ k →
    k < α →
    let μ := singletonPartition α m k
    (∀ a ∈ μ, 2 ≤ a) ∧
      (-1 : ℚ) ^ (pteOrder α m - k - 3) *
          deckCoefficient (pteGraph α m p) μ =
        (edgeCutCount (pteGraph α m p) (μ + {1}) : ℚ)

end
end MathlibPlus.Open.Research.R0333DegreeAndCuts
