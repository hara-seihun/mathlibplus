import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.GraphClaims

/-- The homogeneous independent-part blow-up of a finite simple graph. -/
def independentPartBlowUp {V : Type} (F : SimpleGraph V) (n : ℕ) :
    SimpleGraph (V × Fin n) where
  Adj x y := F.Adj x.1 y.1
  symm := ⟨fun x y h => F.symm.symm x.1 y.1 h⟩
  loopless := ⟨fun x h => F.loopless.irrefl x.1 h⟩

/-- Replacing every base vertex by an independent part of size n and joining
parts exactly along base edges. -/
def homogeneousIndependentGraphBlowUp : Prop :=
  ∀ {V : Type} [Fintype V] (F : SimpleGraph V) (n : ℕ),
    (Fintype.card (Fin n) = n) ∧
    (∀ u v : V, ∀ i j : Fin n,
      (independentPartBlowUp F n).Adj (u, i) (v, j) ↔ F.Adj u v)

/-- Delete one vertex from a finite weighted quotient. -/
def deleteOneWeight {V : Type} [DecidableEq V]
    (w : V → ℕ) (x : V) : V → ℕ :=
  fun y => if y = x then w y - 1 else w y

/-- The one-unit transfer weights: deficit at u and surplus at v. -/
def oneUnitTransferWeights {V : Type} [DecidableEq V]
    (n : ℕ) (u v : V) : V → ℕ :=
  fun x => if x = u then n - 1 else if x = v then n + 1 else n

def regularCardWeights {V : Type} [DecidableEq V]
    (n : ℕ) (u : V) : V → ℕ :=
  fun x => if x = u then n - 1 else n

def deficitTransferCardWeights {V : Type} [DecidableEq V]
    (n : ℕ) (u v : V) : V → ℕ :=
  fun x => if x = u then n - 2 else if x = v then n + 1 else n

def ordinaryTransferCardWeights {V : Type} [DecidableEq V]
    (n : ℕ) (u v k : V) : V → ℕ :=
  fun x =>
    if x = u then n - 1 else if x = v then n + 1
    else if x = k then n - 1 else n

/-- The three card types obtained from a one-unit transfer blow-up. -/
def surplusDeficitOrdinaryTransferCards : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (n : ℕ) (u v k : V),
    u ≠ v → k ≠ u → k ≠ v →
      deleteOneWeight (oneUnitTransferWeights n u v) v =
          regularCardWeights n u ∧
      deleteOneWeight (oneUnitTransferWeights n u v) u =
          deficitTransferCardWeights n u v ∧
      deleteOneWeight (oneUnitTransferWeights n u v) k =
          ordinaryTransferCardWeights n u v k

/-- Equality of open neighborhoods is the graph-defined false-twin relation. -/
def falseTwin {V : Type} (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ z : V, G.Adj x z ↔ G.Adj y z

/-- Equality of closed neighborhoods is the graph-defined true-twin relation. -/
def trueTwin {V : Type} (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ z : V, (x = z ∨ G.Adj x z) ↔ (y = z ∨ G.Adj y z)

/-- Graph automorphisms preserve adjacency and hence the twin relations. -/
def graphAutomorphism {V : Type} (G : SimpleGraph V)
    (e : Equiv.Perm V) : Prop :=
  ∀ x y, G.Adj x y ↔ G.Adj (e x) (e y)

/-- Elements of the graph-automorphism kernel fixing every class of a
relation T. -/
def twinKernelElement {V : Type} (G : SimpleGraph V)
    (T : V → V → Prop) (k : Equiv.Perm V) : Prop :=
  graphAutomorphism G k ∧ ∀ x, T x (k x)

/-- The class-fixing kernel is a normal subgroup, expressed by its subgroup
closure and conjugation laws. -/
def twinKernelIsNormal {V : Type} (G : SimpleGraph V)
    (T : V → V → Prop) : Prop :=
  twinKernelElement G T 1 ∧
    (∀ k l, twinKernelElement G T k → twinKernelElement G T l →
      twinKernelElement G T (k * l)) ∧
    (∀ k, twinKernelElement G T k →
      twinKernelElement G T k⁻¹) ∧
    (∀ e k, graphAutomorphism G e → twinKernelElement G T k →
      twinKernelElement G T (e * k * e⁻¹))

/-- True and false twin relations are graph-defined partitions, and their
pointwise class-fixing kernels are normal in the full graph automorphism group. -/
def twinPartitionsAreGraphInvariants : Prop :=
  ∀ {V : Type} (G : SimpleGraph V),
    Equivalence (trueTwin G) ∧
    Equivalence (falseTwin G) ∧
    (∀ (e : Equiv.Perm V), graphAutomorphism G e →
      ∀ x y, trueTwin G x y ↔ trueTwin G (e x) (e y)) ∧
    (∀ (e : Equiv.Perm V), graphAutomorphism G e →
      ∀ x y, falseTwin G x y ↔ falseTwin G (e x) (e y)) ∧
    twinKernelIsNormal G (trueTwin G) ∧
    twinKernelIsNormal G (falseTwin G)

/-- A graph isomorphism written without relying on a library name for it. -/
def graphIso {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ e : α ≃ β, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- The Cayley graph with connection set the complement of an index-two subgroup. -/
def indexTwoCayley {G : Type} [Group G] (H : Subgroup G) : SimpleGraph G where
  Adj x y := x⁻¹ * y ∉ H
  symm := ⟨fun x y hxy => by
    intro hyx
    apply hxy
    simpa [mul_inv_rev] using H.inv_mem hyx⟩
  loopless := ⟨fun x h => h (by simp)⟩

def completeBipartiteOnSubgroup {G : Type} [Group G]
    (H : Subgroup G) : SimpleGraph (Sum H H) where
  Adj x y :=
    (∃ a b : H, x = Sum.inl a ∧ y = Sum.inr b) ∨
      (∃ a b : H, x = Sum.inr a ∧ y = Sum.inl b)
  symm := ⟨fun x y h => by
    rcases h with h | h
    · right
      rcases h with ⟨a, b, rfl, rfl⟩
      exact ⟨b, a, rfl, rfl⟩
    · left
      rcases h with ⟨a, b, rfl, rfl⟩
      exact ⟨b, a, rfl, rfl⟩⟩
  loopless := ⟨fun x h => by
    rcases h with h | h <;> rcases h with ⟨a, b, hx, hy⟩
    · cases hx.symm.trans hy
    · cases hx.symm.trans hy⟩

def disjointCliquesOnSubgroup {G : Type} [Group G]
    (H : Subgroup G) : SimpleGraph (Sum H H) where
  Adj x y :=
    (∃ a b : H, x = Sum.inl a ∧ y = Sum.inl b ∧ a ≠ b) ∨
      (∃ a b : H, x = Sum.inr a ∧ y = Sum.inr b ∧ a ≠ b)
  symm := ⟨fun x y h => by
    rcases h with h | h
    · left
      rcases h with ⟨a, b, rfl, rfl, hab⟩
      exact ⟨b, a, rfl, rfl, hab.symm⟩
    · right
      rcases h with ⟨a, b, rfl, rfl, hab⟩
      exact ⟨b, a, rfl, rfl, hab.symm⟩⟩
  loopless := ⟨fun x h => by
    rcases h with h | h <;> rcases h with ⟨a, b, hx, hy, hab⟩
    · exact hab (by cases hx.symm.trans hy; rfl)
    · exact hab (by cases hx.symm.trans hy; rfl)⟩

def graphComplement {V : Type} (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ¬ G.Adj x y
  symm := ⟨fun x y h => ⟨Ne.symm h.1, fun hxy => h.2 (G.symm.symm y x hxy)⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

def indexTwoSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∃ r : G, r ∉ H ∧ ∀ x : G, x ∈ H ∨ ∃ h : H, x = r * h

/-- An index-two Cayley graph is complete bipartite, its complement is two
cliques, and its false-twin classes are the two H-cosets. -/
def indexTwoCayleyGraphIsCompleteBipartite : Prop :=
  ∀ {G : Type} [Fintype G] [Group G] (H : Subgroup G),
    indexTwoSubgroup H →
      graphIso (indexTwoCayley H) (completeBipartiteOnSubgroup H) ∧
      graphIso (graphComplement (indexTwoCayley H))
        (disjointCliquesOnSubgroup H) ∧
      (∀ x y : G,
        falseTwin (indexTwoCayley H) x y ↔ x⁻¹ * y ∈ H)

/-- The right-regular intersection with the kernel fixing the two coset
blocks consists exactly of right translations by H. -/
def rightRegularIntersectionFalseTwinKernel : Prop :=
  ∀ {G : Type} [Fintype G] [Group G] (H : Subgroup G),
    indexTwoSubgroup H →
      ∀ g : G,
        (graphAutomorphism (indexTwoCayley H) (Equiv.mulRight g) ∧
          (∀ x : G, x⁻¹ * (x * g) ∈ H)) ↔ g ∈ H

/-- Two index-two subgroup presentations form a CI defect when no group
automorphism maps one connection set to the other. -/
def distinctIndexTwoOrbitsGiveCIDefect : Prop :=
  ∀ {G : Type} [Fintype G] [Group G]
    (H K : Subgroup G),
    indexTwoSubgroup H → indexTwoSubgroup K →
    (¬ ∃ α : G ≃* G, ∀ x : G, x ∈ H ↔ α x ∈ K) →
      graphIso (indexTwoCayley H) (indexTwoCayley K) ∧
      ¬ ∃ α : G ≃* G, ∀ x : G, x ∈ H ↔ α x ∈ K

end MathlibPlus.Open.ResearchFormalization.GraphClaims
