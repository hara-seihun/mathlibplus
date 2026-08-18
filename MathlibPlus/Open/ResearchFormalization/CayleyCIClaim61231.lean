import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CayleyCIClaim61231

noncomputable section

abbrev F3 := ZMod 3
abbrev V := Fin 6 → F3

/-- Projectivization by the full unit action.  Over F₃ this is exactly the
    quotient `(V \ {0}) / (a ~ -a)`. -/
abbrev ProjectiveQuotient :=
  Quotient (MulAction.orbitRel (F3ˣ) V)

abbrev OrdinaryDirection :=
  {p : ProjectiveQuotient // p ≠ Quotient.mk'' (0 : V)}

def directionClass (v : V) : ProjectiveQuotient :=
  Quotient.mk'' v

def triangularQ (x : V) : V :=
  ![x 0 + x 2 * x 5 ^ 2,
    x 1 + x 2 * x 3 * x 4 ^ 2,
    x 2 + 2 * x 4 + 2 * x 4 ^ 2 + x 3 * x 5 +
      x 3 ^ 2 * x 4 * x 5 + x 3 ^ 2 * x 4 ^ 2 * x 5,
    x 3 + 2 * x 4 + x 4 * x 5 + x 4 ^ 2 +
      2 * x 4 ^ 2 * x 5 + x 4 ^ 2 * x 5 ^ 2,
    x 4,
    x 5]

/-- The inverse-direction incidence relation from the displayed difference
    table, retaining representatives of both projective directions. -/
def directionIncidence
    (q : V → V) (a b : OrdinaryDirection) : Prop :=
  ∃ (x u v : V),
    u ≠ 0 ∧ v ≠ 0 ∧
      directionClass u = a.1 ∧ directionClass v = b.1 ∧
      (q (x + u) - q x = v ∨ q (x + u) - q x = -v)

def bipartiteIncidence
    (q : V → V) : (OrdinaryDirection ⊕ OrdinaryDirection) →
      (OrdinaryDirection ⊕ OrdinaryDirection) → Prop
  | Sum.inl a, Sum.inr b => directionIncidence q a b
  | Sum.inr b, Sum.inl a => directionIncidence q a b
  | _, _ => False

def componentOf
    (q : V → V) (z : OrdinaryDirection ⊕ OrdinaryDirection) :
    Set (OrdinaryDirection ⊕ OrdinaryDirection) :=
  {w | Relation.ReflTransGen (bipartiteIncidence q) z w}

def isConnectedComponent
    (q : V → V) (C : Set (OrdinaryDirection ⊕ OrdinaryDirection)) : Prop :=
  ∃ z, C = componentOf q z

def sourceSide
    (C : Set (OrdinaryDirection ⊕ OrdinaryDirection)) :
    Set OrdinaryDirection :=
  {a | Sum.inl a ∈ C}

def targetSide
    (C : Set (OrdinaryDirection ⊕ OrdinaryDirection)) :
    Set OrdinaryDirection :=
  {b | Sum.inr b ∈ C}

def componentSize
    (C : Set (OrdinaryDirection ⊕ OrdinaryDirection)) : ℕ × ℕ :=
  (Set.ncard (sourceSide C), Set.ncard (targetSide C))

def expectedComponentSize : Fin 10 → ℕ × ℕ :=
  ![(1, 1), (1, 1), (1, 1), (1, 1), (9, 9), (27, 27),
    (81, 81), (81, 81), (81, 81), (81, 81)]

def tenComponentSystem
    (q : V → V)
    (components : Fin 10 → Set (OrdinaryDirection ⊕ OrdinaryDirection)) : Prop :=
  (∀ i : Fin 10, isConnectedComponent q (components i)) ∧
    (∀ i j : Fin 10, i ≠ j → Disjoint (components i) (components j)) ∧
    (∀ z : OrdinaryDirection ⊕ OrdinaryDirection,
      ∃ i : Fin 10, z ∈ components i) ∧
    (∃ σ : Equiv.Perm (Fin 10),
      ∀ i : Fin 10,
        componentSize (components i) = expectedComponentSize (σ i))

def sourceConnection
    (components : Fin 10 → Set (OrdinaryDirection ⊕ OrdinaryDirection))
    (K : Set (Fin 10)) : Set V :=
  {v | v ≠ 0 ∧
    ∃ i : Fin 10, i ∈ K ∧
      ∃ a : OrdinaryDirection,
        Sum.inl a ∈ components i ∧ directionClass v = a.1}

def targetConnection
    (components : Fin 10 → Set (OrdinaryDirection ⊕ OrdinaryDirection))
    (K : Set (Fin 10)) : Set V :=
  {v | v ≠ 0 ∧
    ∃ i : Fin 10, i ∈ K ∧
      ∃ b : OrdinaryDirection,
        Sum.inr b ∈ components i ∧ directionClass v = b.1}

def triangularGraphIsomorphism (S T : Set V) : Prop :=
  ∃ e : (SimpleGraph.addCayley S).Iso (SimpleGraph.addCayley T),
    ∀ x : V, e.toEquiv x = triangularQ x

def linearShadow (S T : Set V) : Prop :=
  ∃ L : V ≃ₗ[F3] V, L '' S = T

/-- Claim 61231: the explicit non-linear triangular permutation has the ten
    displayed inverse-atom components, and every component fusion has both
    the graph-isomorphism and GL(6,3) shadows. -/
def claim61231 : Prop :=
  Set.ncard (Set.univ : Set OrdinaryDirection) = 364 ∧
    triangularQ 0 = 0 ∧
    (¬ ∃ L : V ≃ₗ[F3] V, ∀ x : V, L x = triangularQ x) ∧
    ∃ components : Fin 10 → Set (OrdinaryDirection ⊕ OrdinaryDirection),
      tenComponentSystem triangularQ components ∧
        ∀ K : Set (Fin 10),
          triangularGraphIsomorphism
            (sourceConnection components K)
            (targetConnection components K) ∧
          linearShadow
            (sourceConnection components K)
            (targetConnection components K)

end

end MathlibPlus.Open.ResearchFormalization.CayleyCIClaim61231
