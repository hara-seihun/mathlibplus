import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchR0661

/-- A concrete labelled representative of the graph obtained from two disjoint
cliques by the matching of equal indices below `k`. -/
def L (a d k : ℕ) : SimpleGraph (Fin a ⊕ Fin d) :=
  SimpleGraph.fromRel (fun x y =>
    match x, y with
    | Sum.inl _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => True
    | Sum.inl i, Sum.inr j => i.val = j.val ∧ i.val < k
    | Sum.inr j, Sum.inl i => i.val = j.val ∧ i.val < k)

def G (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin c) := L c c b

def H (c b : ℕ) : SimpleGraph (Fin (c + 1) ⊕ Fin (c - 1)) :=
  L (c + 1) (c - 1) b

def A (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin (c - 1)) :=
  L c (c - 1) (b - 1)

def B (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin (c - 1)) :=
  L c (c - 1) b

structure NamedHosts (c b : ℕ) where
  balanced : SimpleGraph (Fin c ⊕ Fin c)
  imbalanced : SimpleGraph (Fin (c + 1) ⊕ Fin (c - 1))
  lower : SimpleGraph (Fin c ⊕ Fin (c - 1))
  upper : SimpleGraph (Fin c ⊕ Fin (c - 1))

def namedHosts (c b : ℕ) : NamedHosts c b :=
  { balanced := G c b
    imbalanced := H c b
    lower := A c b
    upper := B c b }

def GraphIso {V W : Type} (X : SimpleGraph V) (Y : SimpleGraph W) : Prop :=
  Nonempty (X ≃g Y)

def graphSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r X Y := GraphIso X Y
  iseqv :=
    { refl := fun X => ⟨SimpleGraph.Iso.refl⟩
      symm := fun {X Y} h => h.elim (fun f => ⟨f.symm⟩)
      trans := fun {X Y Z} h₁ h₂ =>
        h₁.elim (fun f₁ => h₂.elim (fun f₂ => ⟨RelIso.trans f₁ f₂⟩)) }

def GraphClass (n : ℕ) := Quotient (graphSetoid n)

noncomputable instance graphClassFintype (n : ℕ) : Fintype (GraphClass n) := by
  classical
  exact Quotient.fintype (graphSetoid n)

def deleteVertex {V : Type} (X : SimpleGraph V) (a : V) : SimpleGraph {x : V // x ≠ a} :=
  X.induce {x : V | x ≠ a}

def realizesCubicRow
    {V W Z : Type}
    (X : SimpleGraph V) (A' : SimpleGraph W) (B' : SimpleGraph Z) : Prop :=
  ∃ u v w : V,
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
    GraphIso (deleteVertex X u) A' ∧
    GraphIso (deleteVertex X v) A' ∧
    GraphIso (deleteVertex X w) B'

/-- Both named hosts realize the cubic row with two `A` cards and one `B`
card at distinct deletion vertices. -/
def claim_23725 : Prop :=
  ∀ (c b : ℕ), 3 ≤ c → 2 ≤ b → b ≤ c - 1 →
    realizesCubicRow (G c b) (A c b) (B c b) ∧
    realizesCubicRow (H c b) (A c b) (B c b)

/-- A parent graph satisfying the three deletion hypotheses has the stated
clique-number dichotomy and every displayed card has clique number `c`. -/
def claim_23726 : Prop :=
  ∀ (c b : ℕ) {V : Type} [Fintype V] (X : SimpleGraph V),
    3 ≤ c → 2 ≤ b → b ≤ c - 1 →
    (∃ u v w : V,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      GraphIso (deleteVertex X u) (A c b) ∧
      GraphIso (deleteVertex X v) (A c b) ∧
      GraphIso (deleteVertex X w) (B c b)) →
    (∀ x : V, (deleteVertex X x).cliqueNum = c) ∧
    c ≤ X.cliqueNum ∧ X.cliqueNum ≤ c + 1

/-- The row support predicate records the existence of two distinct `A`
cards and one `B` card. -/
def supportsCubicRow
    {V W Z : Type}
    (X : SimpleGraph V) (A' : SimpleGraph W) (B' : SimpleGraph Z) : Prop :=
  realizesCubicRow X A' B'

/-- Exact global support of the cubic row among finite simple graphs. -/
def claim_23730 : Prop :=
  ∀ (c b : ℕ), 3 ≤ c → 2 ≤ b → b ≤ c - 1 →
    ∀ {V : Type} [Fintype V] (X : SimpleGraph V),
      supportsCubicRow X (A c b) (B c b) ↔
        GraphIso X (G c b) ∨ GraphIso X (H c b)

/-- The six-vertex boundary is the specialization of the same exact support
statement at `(c,b)=(3,2)`. -/
def claim_23729 : Prop :=
  Fintype.card (GraphClass 6) = 156 ∧
    ∀ {V : Type} [Fintype V] (X : SimpleGraph V),
      Fintype.card V = 6 →
        supportsCubicRow X (A 3 2) (B 3 2) ↔
          GraphIso X (G 3 2) ∨ GraphIso X (H 3 2)

end MathlibPlus.Open.Research.FormalizationBatchR0661
