import Mathlib

namespace MathlibPlus.Open.Research.Batch0225

noncomputable section

open scoped Classical

abbrev Partition (n : ℕ) := Nat.Partition n

def support (ρ : Partition n) : Finset ℕ := ρ.parts.toFinset

abbrev splitEdges (k : ℕ) := Σ ρ : Partition k, {a : ℕ // a ∈ ρ.parts}

def splitOff (ρ : Partition k) (a : {a : ℕ // a ∈ ρ.parts}) : Multiset ℕ :=
  ρ.parts.erase a.1 + {a.1 + 1}

def splitOnes (ρ : Partition k) : Multiset ℕ := ρ.parts + {1}

def splitEndpoint (ρ : Partition k) (a : {a : ℕ // a ∈ ρ.parts}) : Partition (k + 1) :=
  ⟨splitOff ρ a,
    by
      intro b hb
      rcases Multiset.mem_add.mp hb with hb | hb
      · exact ρ.parts_pos (Multiset.mem_of_mem_erase hb)
      · have hb' : b = a.1 + 1 := by simpa using hb
        subst b
        omega,
    by
      have hsum := Multiset.sum_erase a.property
      have htotal := ρ.parts_sum
      dsimp [splitOff]
      simp only [Multiset.sum_add, Multiset.sum_singleton]
      omega⟩

def unitEndpoint (ρ : Partition k) : Partition (k + 1) :=
  ⟨splitOnes ρ,
    by
      intro b hb
      rcases Multiset.mem_add.mp hb with hb | hb
      · exact ρ.parts_pos hb
      · have hb' : b = 1 := by simpa using hb
        subst b
        decide,
    by
      have htotal := ρ.parts_sum
      dsimp [splitOnes]
      simp only [Multiset.sum_add, Multiset.sum_singleton]
      omega⟩

def edgeSource (e : splitEdges k) : Partition k := e.1

def edgePart (e : splitEdges k) : {a : ℕ // a ∈ (edgeSource e).parts} := e.2

def splitEdgeEndpoints (e : splitEdges k) : Partition (k + 1) × Partition (k + 1) :=
  (splitEndpoint (edgeSource e) (edgePart e), unitEndpoint (edgeSource e))

def claim6599 : Prop :=
  ∀ (k : ℕ) (ρ : Partition k) (a : {a : ℕ // a ∈ ρ.parts}),
    splitEdgeEndpoints ⟨ρ, a⟩ =
      (⟨ρ.parts.erase a.1 + {a.1 + 1},
        by
          intro b hb
          rcases Multiset.mem_add.mp hb with hb | hb
          · exact ρ.parts_pos (Multiset.mem_of_mem_erase hb)
          · have hb' : b = a.1 + 1 := by simpa using hb
            subst b
            omega,
        by
          have hsum := Multiset.sum_erase a.property
          have htotal := ρ.parts_sum
          simp only [Multiset.sum_add, Multiset.sum_singleton]
          omega⟩,
       ⟨ρ.parts + {1},
        by
          intro b hb
          rcases Multiset.mem_add.mp hb with hb | hb
          · exact ρ.parts_pos hb
          · have hb' : b = 1 := by simpa using hb
            subst b
            decide,
        by
          have htotal := ρ.parts_sum
          simp only [Multiset.sum_add, Multiset.sum_singleton]
          omega⟩)

def graphAdj (k : ℕ) (u v : Partition (k + 1)) : Prop :=
  ∃ e : splitEdges k,
    ((splitEdgeEndpoints e).1 = u ∧ (splitEdgeEndpoints e).2 = v) ∨
      ((splitEdgeEndpoints e).1 = v ∧ (splitEdgeEndpoints e).2 = u)

def graphReachable (k : ℕ) : Partition (k + 1) → Partition (k + 1) → Prop :=
  Relation.ReflTransGen (graphAdj k)

def partitionGraphConnected (k : ℕ) : Prop :=
  ∀ u v : Partition (k + 1), graphReachable k u v

def partitionNumber (n : ℕ) : Nat := Nat.card (Partition n)
def edgeCount (k : ℕ) : Nat := Nat.card (splitEdges k)
def cycleRank (k : ℕ) : Nat := edgeCount k - partitionNumber (k + 1) + 1
def supportCount (ρ : Partition k) : Nat := (support ρ).card
noncomputable def supportSum (k : ℕ) : Nat :=
  ∑ ρ : Partition k, supportCount ρ

def claim6602 : Prop :=
  ∀ k : ℕ,
    partitionGraphConnected k ∧ edgeCount k = supportSum k ∧
      partitionNumber (k + 1) = Nat.card (Partition (k + 1)) ∧
      cycleRank k = supportSum k - partitionNumber (k + 1) + 1

def part311 : Partition 5 :=
  ⟨{3, 1, 1}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def part32 : Partition 5 :=
  ⟨{3, 2}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def part221 : Partition 5 :=
  ⟨{2, 2, 1}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def part2111 : Partition 5 :=
  ⟨{2, 1, 1, 1}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def part31 : Partition 4 :=
  ⟨{3, 1}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def part22 : Partition 4 :=
  ⟨{2, 2}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def part211 : Partition 4 :=
  ⟨{2, 1, 1}, by
      intro i hi
      simp at hi
      omega,
    by norm_num⟩

def cycleEdge31 : splitEdges 4 := ⟨part31, ⟨1, by simp [part31]⟩⟩
def cycleEdge22 : splitEdges 4 := ⟨part22, ⟨2, by simp [part22]⟩⟩
def cycleEdge211₂ : splitEdges 4 := ⟨part211, ⟨2, by simp [part211]⟩⟩
def cycleEdge211₁ : splitEdges 4 := ⟨part211, ⟨1, by simp [part211]⟩⟩

def cycleEdges : Finset (splitEdges 4) :=
  {cycleEdge31, cycleEdge22, cycleEdge211₂, cycleEdge211₁}

def edgeIncident (e : splitEdges k) (v : Partition (k + 1)) : Prop :=
  (splitEdgeEndpoints e).1 = v ∨ (splitEdgeEndpoints e).2 = v

def selectedVertices (E : Finset (splitEdges k)) : Finset (Partition (k + 1)) :=
  E.biUnion (fun e => {(splitEdgeEndpoints e).1, (splitEdgeEndpoints e).2})

def selectedAdj (E : Finset (splitEdges k)) (u v : Partition (k + 1)) : Prop :=
  ∃ e ∈ E,
    ((splitEdgeEndpoints e).1 = u ∧ (splitEdgeEndpoints e).2 = v) ∨
      ((splitEdgeEndpoints e).1 = v ∧ (splitEdgeEndpoints e).2 = u)

def selectedCycle (E : Finset (splitEdges k)) : Prop :=
  3 ≤ E.card ∧
    (∀ v ∈ selectedVertices E,
      (E.filter (fun e => edgeIncident e v)).card = 2) ∧
    (∀ u v : Partition (k + 1), u ∈ selectedVertices E → v ∈ selectedVertices E →
      Relation.ReflTransGen (selectedAdj E) u v)

def forest (E : Finset (splitEdges k)) : Prop :=
  ¬ ∃ C : Finset (splitEdges k), C ⊆ E ∧ selectedCycle C

def claim6604 : Prop :=
  partitionGraphConnected 4 ∧ cycleRank 4 = 1 ∧ selectedCycle cycleEdges ∧
    (∀ E : Finset (splitEdges 4), selectedCycle E → E = cycleEdges) ∧
    forest (Finset.univ \ cycleEdges) ∧
    (∀ v : Partition 5, ∃ c ∈ selectedVertices cycleEdges,
      Relation.ReflTransGen (selectedAdj (Finset.univ \ cycleEdges)) v c) ∧
    splitEdgeEndpoints cycleEdge31 = (part32, part311) ∧
    splitEdgeEndpoints cycleEdge22 = (part32, part221) ∧
    splitEdgeEndpoints cycleEdge211₂ = (part311, part2111) ∧
    splitEdgeEndpoints cycleEdge211₁ = (part221, part2111)

end
end MathlibPlus.Open.Research.Batch0225
