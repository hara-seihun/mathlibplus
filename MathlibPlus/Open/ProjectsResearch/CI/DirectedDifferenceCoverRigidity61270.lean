import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.CI

/-- The fixed-point set of a vertex bijection. -/
def fixedPoints61270 {G : Type*} [Group G] (q : G ≃ G) : Set G :=
  {x | q x = x}

/-- The directed right-Cayley relation for a connection set. -/
def directedRightCayleyRelation61270 {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

/-- A fixed-point set difference-covers its group. -/
def differenceCover61270 {G : Type*} [Group G] (F : Set G) : Prop :=
  {d : G | ∃ x ∈ F, ∃ y ∈ F, x⁻¹ * y = d} = Set.univ

/-- Simultaneous transport of a labelled family of directed right-Cayley relations. -/
def directedCayleyFamilyTransport61270 {G J : Type*} [Group G]
    (f : G → G) (S T : J → Set G) : Prop :=
  ∀ (j : J) (x y : G),
    directedRightCayleyRelation61270 (S j) x y ↔
      directedRightCayleyRelation61270 (T j) (f x) (f y)

/-- The directed difference-cover rigidity statement for arbitrary groups and
arbitrary labelled families. -/
def directedDifferenceCoverRigidity61270
    (G J : Type*) [Group G] : Prop :=
  ∀ (q : G ≃ G) (S T : J → Set G),
    differenceCover61270 (fixedPoints61270 q) →
      directedCayleyFamilyTransport61270 q S T →
        ∀ j : J, S j = T j

/-- The normalized form, with one previously chosen group automorphism shared
by every label. -/
def normalizedDirectedDifferenceCoverRigidity61270
    (G J : Type*) [Group G] : Prop :=
  ∀ (f q : G ≃ G) (alpha : G ≃* G) (S T : J → Set G),
    (∀ x : G, q x = alpha.symm (f x)) →
      differenceCover61270 (fixedPoints61270 q) →
        directedCayleyFamilyTransport61270 f S T →
          ∀ j : J, alpha '' S j = T j

/-- The arbitrary anchored product-fibre consequence for directed Cayley
families on a direct product of arbitrary groups. -/
def arbitraryAnchoredProductFibreConsequence61270
    (A B J : Type*) [Group A] [Group B] : Prop :=
  ∀ (gamma : A ≃* A) (beta : B ≃* B)
    (eta : A → (B ≃ B)),
    (∀ a : A, eta a 1 = 1) →
      eta 1 = beta.toEquiv →
        let f : A × B → A × B :=
          fun p => (gamma p.1, eta p.1 p.2)
        let alpha : A × B ≃* A × B := MulEquiv.prodCongr gamma beta
        (S T : J → Set (A × B)) →
          directedCayleyFamilyTransport61270 f S T →
            ∀ j : J, alpha '' S j = T j

/-- Claim 61270: directed difference-cover rigidity, its normalized common
automorphism form, and the arbitrary anchored product-fibre consequence. -/
def claim61270 : Prop :=
  (∀ (G J : Type*) [Group G],
    directedDifferenceCoverRigidity61270 G J ∧
      normalizedDirectedDifferenceCoverRigidity61270 G J) ∧
    (∀ (A B J : Type*) [Group A] [Group B],
      arbitraryAnchoredProductFibreConsequence61270 A B J)

end MathlibPlus.Open.ProjectsResearch.CI
