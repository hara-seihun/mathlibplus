import Mathlib

namespace MathlibPlus.Open.FiniteCayleyCI

/-- The ordinary undirected right-Cayley graph associated to a multiplicative connection set. -/
def rightCayleyGraph {G : Type} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

/-- The additive notation for the ordinary undirected right-Cayley graph. -/
def additiveCayleyGraph {G : Type} [AddGroup G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

/-- A presentation of the group named `Q₁₂` in the admitted claim. -/
def q12A : FreeGroup (Fin 2) := FreeGroup.of 0

def q12B : FreeGroup (Fin 2) := FreeGroup.of 1

def q12Relators : Set (FreeGroup (Fin 2)) :=
  {q12A ^ 6, q12B ^ 2 * (q12A ^ 3)⁻¹, q12B⁻¹ * q12A * q12B * q12A}

abbrev Q12 : Type := FreeGroup (Fin 2) ⧸ Subgroup.normalClosure q12Relators

/-- Claim 60258. -/
def claim60258 : Prop :=
  let G := Multiplicative (ZMod 7) × Q12
  ∀ S T : Set G,
    S ⊆ (Set.univ : Set G) \ {1} →
    T ⊆ (Set.univ : Set G) \ {1} →
    (∀ x, x ∈ S → x⁻¹ ∈ S) →
    (∀ x, x ∈ T → x⁻¹ ∈ T) →
    (S.ncard = T.ncard ∧ (S.ncard = 12 ∨ S.ncard = 71)) →
    SimpleGraph.Iso (rightCayleyGraph S) (rightCayleyGraph T) →
    ∃ α : G ≃* G, α '' S = T

/-- Claim 60259. -/
def claim60259 : Prop :=
  (∀ (P : Finset ℕ)
    (n : {p // p ∈ P} → ℕ)
    (Bp : ∀ p : {q // q ∈ P},
      Submodule (ZMod (p : ℕ)) (Fin (n p) → ZMod (p : ℕ))),
    (∀ (p : ℕ) (_hp : p ∈ P), Nat.Prime p ∧ Odd p) →
    let A := ∀ p : {q // q ∈ P}, Fin (n p) → ZMod (p : ℕ)
    let B : AddSubgroup A :=
      AddSubgroup.pi Set.univ (fun p => (Bp p).toAddSubgroup)
    B ≠ ⊤ →
    let G := ZMod 4 × A
    let H : Set G := {x | x.1 = 0 ∨ x.1 = 2}
    let L : Set G := {x | (x.1 = 0 ∨ x.1 = 2) ∧ x.2 ∈ B}
    let S : Set G := (Set.univ \ H) ∪ (L \ {(0 : G)})
    (0 : G) ∉ S ∧
    (∀ x, x ∈ S → -x ∈ S) ∧
    ∀ T : Set G,
      T ⊆ (Set.univ : Set G) \ {(0 : G)} →
      (∀ x, x ∈ T → -x ∈ T) →
      SimpleGraph.Iso (additiveCayleyGraph S) (additiveCayleyGraph T) →
      ∃ α : AddEquiv G G, α '' S = T) ∧
  (let V₃ := Fin 3 → ZMod 3
   let G₃ := ZMod 4 × V₃
   let connection : Submodule (ZMod 3) V₃ → Set G₃ := fun W =>
     (Set.univ \ {x : G₃ | x.1 = 0 ∨ x.1 = 2}) ∪
       ({x : G₃ | (x.1 = 0 ∨ x.1 = 2) ∧ x.2 ∈ W} \ {(0 : G₃)})
   (∀ W : Submodule (ZMod 3) V₃, W ≠ ⊤ →
     (0 : G₃) ∉ connection W ∧
     (∀ x, x ∈ connection W → -x ∈ connection W) ∧
     ∀ T : Set G₃,
       T ⊆ (Set.univ : Set G₃) \ {(0 : G₃)} →
       (∀ x, x ∈ T → -x ∈ T) →
       SimpleGraph.Iso (additiveCayleyGraph (connection W))
         (additiveCayleyGraph T) →
       ∃ α : AddEquiv G₃ G₃, α '' connection W = T) ∧
   Set.ncard {S : Set G₃ | ∃ W : Submodule (ZMod 3) V₃,
     W ≠ ⊤ ∧ S = connection W ∧ S.ncard = 55} = 1 ∧
   Set.ncard {S : Set G₃ | ∃ W : Submodule (ZMod 3) V₃,
     W ≠ ⊤ ∧ S = connection W ∧ S.ncard = 59} = 13 ∧
   Set.ncard {S : Set G₃ | ∃ W : Submodule (ZMod 3) V₃,
     W ≠ ⊤ ∧ S = connection W ∧ S.ncard = 71} = 13)

/-- An internal direct-sum decomposition, written with its existence and uniqueness property. -/
def isInternalDirectSum
    {R V ι : Type} [Semiring R] [AddCommMonoid V] [Module R V]
    [Fintype ι] (U : ι → Submodule R V) : Prop :=
  ∀ v : V, ∃! u : ∀ i, U i, (∑ i, (u i : V)) = v

/-- Claim 60260. -/
def claim60260 : Prop :=
  ∀ (p m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (U : Fin m → Submodule (ZMod p) V),
    Nat.Prime p →
    5 ≤ p →
    (m = p ∨ m = p + 1) →
    isInternalDirectSum U →
    (∀ i, Module.finrank (ZMod p) (U i) = 2) →
    let S : Set V := ⋃ i, ((U i : Set V) \ {(0 : V)})
    (0 : V) ∉ S ∧
    (∀ x, x ∈ S → -x ∈ S) ∧
    (∀ T : Set V,
      T ⊆ (Set.univ : Set V) \ {(0 : V)} →
      (∀ x, x ∈ T → -x ∈ T) →
      SimpleGraph.Iso (additiveCayleyGraph S) (additiveCayleyGraph T) →
      ∃ L : V ≃ₗ[ZMod p] V, L '' S = T)

end MathlibPlus.Open.FiniteCayleyCI
