import MathlibPlus.Open.Combinatorics.Claim5539Formalization

namespace MathlibPlus.Open.Combinatorics.Claim5541

open MathlibPlus.Open.Combinatorics.Claim5539Formalization

/-- The data produced by a topological ordering of an acyclic selector: the
selected rows are distinct, the selected diagonal is nonzero, the minor is
triangular, and the full column family has the corresponding independence and
rank. -/
def triangularNonzeroMinorData
    {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (A : Matrix R C K) (s : C → R) : Prop :=
  ∃ order : Fin (Fintype.card C) ≃ C,
    Function.Injective (fun i => s (order i)) ∧
      (∀ i, A (s (order i)) (order i) ≠ 0) ∧
        (∀ i j, j < i → A (s (order i)) (order j) = 0) ∧
          Matrix.det (fun i j : Fin (Fintype.card C) =>
            A (s (order i)) (order j)) ≠ 0 ∧
            LinearIndependent K (fun c : C => fun r : R => A r c) ∧
              Module.finrank K
                  (Submodule.span K
                    (Set.range (fun c : C => fun r : R => A r c))) =
                Fintype.card C

/-- An acyclic incident-row selector yields a triangular nonzero minor, and
complete singleton peeling supplies such a selector and hence the same
column-independence/rank certificate. -/
def acyclicSelectorTriangularMinor_claim5541 : Prop :=
  ∀ {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (A : Matrix R C K),
    (∀ s : C → R,
      incidentRowSelector A s →
        dependencyAcyclic A s →
          triangularNonzeroMinorData A s) ∧
      (completeSingletonPeeling A →
        ∃ s : C → R,
          incidentRowSelector A s ∧
            dependencyAcyclic A s ∧
              triangularNonzeroMinorData A s)

end MathlibPlus.Open.Combinatorics.Claim5541
