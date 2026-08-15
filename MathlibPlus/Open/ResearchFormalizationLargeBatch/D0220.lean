import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6546_inversePairAtomIndex : Prop := by
  classical
  exact ∀ (G : Type) [AddCommGroup G] [Fintype G],
    let V := {d : G // d ≠ 0}
    let invSetoid : Setoid V :=
      { r := fun d e => e.1 = d.1 ∨ e.1 = -d.1
        iseqv :=
          { refl := fun d => Or.inl rfl
            symm := by
              intro d e h
              rcases h with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp)
            trans := by
              intro d e f hde hef
              rcases hde with hde | hde <;> rcases hef with hef | hef
              · exact Or.inl (hef.trans hde)
              · exact Or.inr (by rw [hef, hde])
              · exact Or.inr (hef.trans hde)
              · exact Or.inl (by rw [hef, hde]; simp) } }
    (∀ d e : V, Quotient.mk' d = Quotient.mk' e ↔
      e.1 = d.1 ∨ e.1 = -d.1) ∧
      (∀ d : V,
        (d.1 = -d.1 ↔
          ∀ e : V, Quotient.mk' e = Quotient.mk' d → e.1 = d.1))

def claim6549_inverseClosedConnectionSetsAreAtomSets : Prop := by
  classical
  exact ∀ (G : Type) [AddCommGroup G] [Fintype G],
    let V := {d : G // d ≠ 0}
    let invSetoid : Setoid V :=
      { r := fun d e => e.1 = d.1 ∨ e.1 = -d.1
        iseqv :=
          { refl := fun d => Or.inl rfl
            symm := by
              intro d e h
              rcases h with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp)
            trans := by
              intro d e f hde hef
              rcases hde with hde | hde <;> rcases hef with hef | hef
              · exact Or.inl (hef.trans hde)
              · exact Or.inr (by rw [hef, hde])
              · exact Or.inr (hef.trans hde)
              · exact Or.inl (by rw [hef, hde]; simp) } }
    let D := Quotient invSetoid
    let atomOf : V → D := fun d => Quotient.mk' d
    let edge : Set G → Set (G × G) := fun S =>
      {e | e.2 - e.1 ∈ S}
    let atomEdge : D → Set (G × G) := fun i =>
      {e | ∃ d : V, atomOf d = i ∧
        (e.2 - e.1 = d.1 ∨ e.2 - e.1 = -d.1)}
    let atomSet : Set G → Set D := fun S =>
      {i | ∃ d : V, d.1 ∈ S ∧ atomOf d = i}
    (∀ (S : Set G), 0 ∉ S → (∀ d ∈ S, -d ∈ S) →
      edge S = {e | ∃ i, i ∈ atomSet S ∧ e ∈ atomEdge i}) ∧
      (∀ I : Set D, ∃! S : Set G,
        0 ∉ S ∧ (∀ d ∈ S, -d ∈ S) ∧ atomSet S = I)

def claim6550_pointedPermutationSourceTargetIncidence : Prop := by
  classical
  exact ∀ (G : Type) [AddCommGroup G] [Fintype G],
    let V := {d : G // d ≠ 0}
    let invSetoid : Setoid V :=
      { r := fun d e => e.1 = d.1 ∨ e.1 = -d.1
        iseqv :=
          { refl := fun d => Or.inl rfl
            symm := by
              intro d e h
              rcases h with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp)
            trans := by
              intro d e f hde hef
              rcases hde with hde | hde <;> rcases hef with hef | hef
              · exact Or.inl (hef.trans hde)
              · exact Or.inr (by rw [hef, hde])
              · exact Or.inr (hef.trans hde)
              · exact Or.inl (by rw [hef, hde]; simp) } }
    let D := Quotient invSetoid
    let atomOf : V → D := fun d => Quotient.mk' d
    let atomEdge : D → Set (G × G) := fun i =>
      {e | ∃ d : V, atomOf d = i ∧
        (e.2 - e.1 = d.1 ∨ e.2 - e.1 = -d.1)}
    ∀ (f : G → G), Function.Bijective f → f 0 = 0 →
      let edgeMap : (G × G) → (G × G) := fun e => (f e.1, f e.2)
      let incident : D → D → Prop := fun i j =>
        (edgeMap '' atomEdge i) ∩ atomEdge j ≠ ∅
      let adjacent : D → D → Prop := fun i i' =>
        ∃ j, incident i j ∧ incident i' j
      (∀ i j, incident i j ↔
        (edgeMap '' atomEdge i) ∩ atomEdge j ≠ ∅) ∧
        (∀ i i', adjacent i i' ↔ ∃ j, incident i j ∧ incident i' j)

def claim6553_inversePairComponentCriterion : Prop := by
  classical
  exact ∀ (G : Type) [AddCommGroup G] [Fintype G],
    let V := {d : G // d ≠ 0}
    let invSetoid : Setoid V :=
      { r := fun d e => e.1 = d.1 ∨ e.1 = -d.1
        iseqv :=
          { refl := fun d => Or.inl rfl
            symm := by
              intro d e h
              rcases h with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp)
            trans := by
              intro d e f hde hef
              rcases hde with hde | hde <;> rcases hef with hef | hef
              · exact Or.inl (hef.trans hde)
              · exact Or.inr (by rw [hef, hde])
              · exact Or.inr (hef.trans hde)
              · exact Or.inl (by rw [hef, hde]; simp) } }
    let D := Quotient invSetoid
    let atomOf : V → D := fun d => Quotient.mk' d
    let atomEdge : D → Set (G × G) := fun i =>
      {e | ∃ d : V, atomOf d = i ∧
        (e.2 - e.1 = d.1 ∨ e.2 - e.1 = -d.1)}
    ∀ (f : G → G), Function.Bijective f → f 0 = 0 →
      let edgeMap : (G × G) → (G × G) := fun e => (f e.1, f e.2)
      let incident : D → D → Prop := fun i j =>
        (edgeMap '' atomEdge i) ∩ atomEdge j ≠ ∅
      let adjacent : D → D → Prop := fun i i' =>
        ∃ j, incident i j ∧ incident i' j
      let sameComponent : D → D → Prop := fun i j =>
        Relation.ReflTransGen adjacent i j
      ∀ I : Set D,
        let sourceEdges : Set (G × G) :=
          {e | ∃ i, i ∈ I ∧ e ∈ atomEdge i}
        let imageEdges : Set (G × G) := edgeMap '' sourceEdges
        ((∃ J : Set D, imageEdges =
            {e | ∃ j, j ∈ J ∧ e ∈ atomEdge j}) ↔
          ∀ i j, sameComponent i j → (i ∈ I ↔ j ∈ I))

def claim6555_eachComponentUnionGivesCayleyIsomorphism : Prop := by
  classical
  exact ∀ (G : Type) [AddCommGroup G] [Fintype G],
    let V := {d : G // d ≠ 0}
    let invSetoid : Setoid V :=
      { r := fun d e => e.1 = d.1 ∨ e.1 = -d.1
        iseqv :=
          { refl := fun d => Or.inl rfl
            symm := by
              intro d e h
              rcases h with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp)
            trans := by
              intro d e f hde hef
              rcases hde with hde | hde <;> rcases hef with hef | hef
              · exact Or.inl (hef.trans hde)
              · exact Or.inr (by rw [hef, hde])
              · exact Or.inr (hef.trans hde)
              · exact Or.inl (by rw [hef, hde]; simp) } }
    let D := Quotient invSetoid
    let atomOf : V → D := fun d => Quotient.mk' d
    let atomEdge : D → Set (G × G) := fun i =>
      {e | ∃ d : V, atomOf d = i ∧
        (e.2 - e.1 = d.1 ∨ e.2 - e.1 = -d.1)}
    let atomSet : Set G → Set D := fun S =>
      {i | ∃ d : V, d.1 ∈ S ∧ atomOf d = i}
    ∀ (f : G → G), Function.Bijective f → f 0 = 0 →
      let edgeMap : (G × G) → (G × G) := fun e => (f e.1, f e.2)
      let incident : D → D → Prop := fun i j =>
        (edgeMap '' atomEdge i) ∩ atomEdge j ≠ ∅
      let adjacent : D → D → Prop := fun i i' =>
        ∃ j, incident i j ∧ incident i' j
      let sameComponent : D → D → Prop := fun i j =>
        Relation.ReflTransGen adjacent i j
      ∀ I : Set D,
        (∀ i j, sameComponent i j → (i ∈ I ↔ j ∈ I)) →
        let J : Set D := {j | ∃ i, i ∈ I ∧ incident i j}
        let S : Set G := {d | ∃ v : V, v.1 = d ∧ atomOf v ∈ I}
        let T : Set G := {d | ∃ v : V, v.1 = d ∧ atomOf v ∈ J}
        0 ∉ S ∧ 0 ∉ T ∧
          (∀ d ∈ S, -d ∈ S) ∧ (∀ d ∈ T, -d ∈ T) ∧
          atomSet S = I ∧ atomSet T = J ∧
          (∀ v w, w - v ∈ S ↔ f w - f v ∈ T)

def claim6558_orderProfileMismatchGivesOrdinaryCIWitness : Prop := by
  classical
  exact ∀ (G : Type) [AddCommGroup G] [Fintype G],
    let V := {d : G // d ≠ 0}
    let invSetoid : Setoid V :=
      { r := fun d e => e.1 = d.1 ∨ e.1 = -d.1
        iseqv :=
          { refl := fun d => Or.inl rfl
            symm := by
              intro d e h
              rcases h with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp)
            trans := by
              intro d e f hde hef
              rcases hde with hde | hde <;> rcases hef with hef | hef
              · exact Or.inl (hef.trans hde)
              · exact Or.inr (by rw [hef, hde])
              · exact Or.inr (hef.trans hde)
              · exact Or.inl (by rw [hef, hde]; simp) } }
    let D := Quotient invSetoid
    let atomOf : V → D := fun d => Quotient.mk' d
    ∀ (f : G → G), Function.Bijective f → f 0 = 0 →
      let atomEdge : D → Set (G × G) := fun i =>
        {e | ∃ d : V, atomOf d = i ∧
          (e.2 - e.1 = d.1 ∨ e.2 - e.1 = -d.1)}
      let edgeMap : (G × G) → (G × G) := fun e => (f e.1, f e.2)
      let incident : D → D → Prop := fun i j =>
        (edgeMap '' atomEdge i) ∩ atomEdge j ≠ ∅
      let adjacent : D → D → Prop := fun i i' =>
        ∃ j, incident i j ∧ incident i' j
      let sameComponent : D → D → Prop := fun i j =>
        Relation.ReflTransGen adjacent i j
      ∀ I : Set D,
        (∀ i j, sameComponent i j → (i ∈ I ↔ j ∈ I)) →
        let J : Set D := {j | ∃ i, i ∈ I ∧ incident i j}
        let S : Set G := {d | ∃ v : V, v.1 = d ∧ atomOf v ∈ I}
        let T : Set G := {d | ∃ v : V, v.1 = d ∧ atomOf v ∈ J}
        (∃ n : ℕ,
          Set.ncard {d | d ∈ S ∧ addOrderOf d = n} ≠
            Set.ncard {d | d ∈ T ∧ addOrderOf d = n}) →
        (∀ v w, w - v ∈ S ↔ f w - f v ∈ T) ∧
          (∀ e : G ≃+ G, e '' S ≠ T)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
