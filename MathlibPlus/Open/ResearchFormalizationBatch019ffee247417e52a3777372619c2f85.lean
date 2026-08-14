import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/- The type-specific spanning-subgraph count used here counts spanning subgraphs
   once each, modulo no extra choice of an isomorphism. -/
noncomputable def spanningSubgraphCount {V : Type*} [Fintype V] (T G : SimpleGraph V) : ℕ :=
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  letI : Fintype {S : SimpleGraph V // S ≤ G ∧ Nonempty (S ≃g T)} :=
    Fintype.ofFinite _
  Fintype.card {S : SimpleGraph V // S ≤ G ∧ Nonempty (S ≃g T)}

def claim_44784 : Prop :=
  spanningSubgraphCount (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) = 1 ∧
    spanningSubgraphCount (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) = 0

/-- A permutation induces the stated isomorphism between the two deleted cards. -/
def inducesDeletedCardIso {V : Type*} [DecidableEq V]
    (A B : SimpleGraph V) (i : V) (π : Equiv.Perm V) : Prop :=
  π i = i ∧ ∀ ⦃x y : V⦄, x ≠ i → y ≠ i →
    (A.Adj x y ↔ B.Adj (π x) (π y))

def claim_44787 {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V → ∀ i : V, ∃ π : Equiv.Perm V,
    inducesDeletedCardIso A B i π

abbrev C2SquaredTimesC3 :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 3)

def preservesRelation {ι α : Type*}
    (R : ι → α → α → Prop) (p : Equiv.Perm α) : Prop :=
  ∀ j x y, R j x y ↔ R j (p x) (p y)

def isRegularPermutationSubgroup {α : Type*}
    (K : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! p : Equiv.Perm α, p ∈ K ∧ p x = y

def isRegularC2SquaredTimesC3 {α : Type*}
    (K : Subgroup (Equiv.Perm α)) : Prop :=
  isRegularPermutationSubgroup K ∧ Nonempty (K ≃* C2SquaredTimesC3)

def liesInTupleAutomorphismGroup {ι α : Type*}
    (R : ι → α → α → Prop) (K : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ p, p ∈ K → preservesRelation R p

def conjugatesSubgroup {α : Type*} (a : Equiv.Perm α)
    (K L : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ p, p ∈ L ↔ ∃ k, k ∈ K ∧ p = a * k * a⁻¹

def claim_44835 {ι : Type*} [Fintype ι]
    (R : ι → C2SquaredTimesC3 → C2SquaredTimesC3 → Prop) : Prop :=
  (∀ j x y, R j x y ↔ R j y x) →
    ∀ K L : Subgroup (Equiv.Perm C2SquaredTimesC3),
      (isRegularC2SquaredTimesC3 K ∧ liesInTupleAutomorphismGroup R K) →
      (isRegularC2SquaredTimesC3 L ∧ liesInTupleAutomorphismGroup R L) →
      ∃ a, preservesRelation R a ∧ conjugatesSubgroup a K L

end MathlibPlus.Open.ResearchFormalizationBatch
