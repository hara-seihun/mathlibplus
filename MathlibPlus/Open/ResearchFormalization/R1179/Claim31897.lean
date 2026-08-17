import MathlibPlus.Open.ResearchFormalization.R1179.Claim41666

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim31897

open MathlibPlus.Open.ResearchFormalization.R1179.Claim41666

/-- The exact alternating connection set in the `A × D₂m` carrier. -/
def alternatingConnectionSet {A : Type*} {m : ℕ} [Group A] :
    Set (A × DihedralGroup m) :=
  thickConnection (A := A) (m := m) ∪
    thinConnection (A := A) (m := m)

/-- Claim 31897: the displayed alternating connection set is inverse closed,
and its left Cayley relation, hence the displayed graph, is undirected. -/
def claim31897 : Prop :=
  ∀ (A : Type*) [Group A] [Fintype A] [Nontrivial A] (m : ℕ),
    3 ≤ m →
    Nat.Coprime (Fintype.card A) (2 * m) →
    let S := alternatingConnectionSet (A := A) (m := m)
    (∀ g : A × DihedralGroup m, g ∈ S ↔ g⁻¹ ∈ S) ∧
      (∀ x y : A × DihedralGroup m,
        leftStep S x y ↔ leftStep S y x) ∧
      (∀ x y : A × DihedralGroup m,
        (alternatingGraph (A := A) (m := m)).Adj x y ↔
          (alternatingGraph (A := A) (m := m)).Adj y x)

end MathlibPlus.Open.ResearchFormalization.R1179.Claim31897
