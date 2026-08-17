import Mathlib

namespace MathlibPlus.Open.Research.PiecewiseAffineAllFusionsClaim61195

noncomputable section

abbrev F3 := ZMod 3
abbrev Fibre := Fin 5 → F3
abbrev Point := F3 × Fibre

/-- The two literal matrices in the three-layer map. -/
def B1 : Matrix (Fin 5) (Fin 5) F3 :=
  !![(1 : F3), 1, 0, 2, 0;
     0, 1, 0, 2, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 1, 0, 0, 1]

def B2 : Matrix (Fin 5) (Fin 5) F3 :=
  !![(0 : F3), 1, 0, 0, 0;
     0, 0, 0, 0, 1;
     0, 1, 1, 2, 0;
     0, 2, 0, 2, 0;
     1, 0, 2, 0, 0]

def c1 : Fibre := ![(0 : F3), 2, 2, 0, 2]

def c2 : Fibre := ![(0 : F3), 2, 2, 2, 2]

def matrixAction (M : Matrix (Fin 5) (Fin 5) F3) (h : Fibre) : Fibre :=
  Matrix.mulVec M h

/-- The displayed pointed piecewise-affine map. -/
def q : Point → Point :=
  fun x =>
    if x.1 = 0 then
      (0, x.2)
    else if x.1 = 1 then
      (1, matrixAction B1 x.2 + c1)
    else
      (2, matrixAction B2 x.2 + c2)

/-- Ordinary inverse directions as signed two-element sets. -/
def Direction : Type :=
  {D : Finset Point // ∃ a : Point, a ≠ 0 ∧ D = {a, -a}}

abbrev IncidenceNode := Direction ⊕ Direction

/-- The exact source-to-target incidence condition for two inverse directions. -/
def directionIncidence (f : Point → Point)
    (D E : Direction) : Prop :=
  ∃ x : Point, ∃ a : Point,
    a ∈ D.1 ∧ f (x + a) - f x ∈ E.1

def incidenceAdjacency (f : Point → Point)
    (u v : IncidenceNode) : Prop :=
  match u, v with
  | Sum.inl D, Sum.inr E => directionIncidence f D E
  | Sum.inr E, Sum.inl D => directionIncidence f D E
  | _, _ => False

def incidenceConnected (f : Point → Point)
    (u v : IncidenceNode) : Prop :=
  Relation.ReflTransGen (incidenceAdjacency f) u v

def incidenceComponent (f : Point → Point)
    (C : Set IncidenceNode) : Prop :=
  ∃ u : IncidenceNode, C = {v | incidenceConnected f u v}

def sourceLabels (C : Set IncidenceNode) : Set Direction :=
  {D | Sum.inl D ∈ C}

def targetLabels (C : Set IncidenceNode) : Set Direction :=
  {D | Sum.inr D ∈ C}

def sourceConnectionSet
    (C : Fin 5 → Set IncidenceNode) (K : Finset (Fin 5)) : Set Point :=
  {a | ∃ i : Fin 5, i ∈ K ∧ ∃ D : Direction,
    Sum.inl D ∈ C i ∧ a ∈ D.1}

def targetConnectionSet
    (C : Fin 5 → Set IncidenceNode) (K : Finset (Fin 5)) : Set Point :=
  {b | ∃ i : Fin 5, i ∈ K ∧ ∃ D : Direction,
    Sum.inr D ∈ C i ∧ b ∈ D.1}

/-- The ordinary undirected additive Cayley adjacency relation. -/
def cayleyAdjacency {V : Type*} [AddGroup V]
    (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

def ordinaryGraphIsomorphism {V : Type*} [AddGroup V]
    (f : V → V) (S T : Set V) : Prop :=
  Function.Bijective f ∧
    ∀ x y : V, cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def identityFree {V : Type*} [AddGroup V] (S : Set V) : Prop :=
  (0 : V) ∉ S

def inverseClosed {V : Type*} [AddGroup V] (S : Set V) : Prop :=
  ∀ ⦃x : V⦄, x ∈ S → -x ∈ S

abbrev GL6 := Point ≃ₗ[F3] Point

def linearImage {V : Type*} [AddCommGroup V] [Module F3 V]
    (L : V ≃ₗ[F3] V) (S : Set V) : Set V :=
  L '' S

def ordinaryUndirectedCayleyCIDefect
    {V : Type*} [AddCommGroup V] [Module F3 V]
    (f : V → V) (S T : Set V) : Prop :=
  identityFree S ∧
    inverseClosed S ∧
    identityFree T ∧
    inverseClosed T ∧
    ordinaryGraphIsomorphism f S T ∧
    ¬ ∃ L : V ≃ₗ[F3] V, linearImage L S = T

abbrev Extra (r : ℕ) := Fin r → F3
abbrev ExtendedPoint (r : ℕ) := Point × Extra r

def extendedQ (r : ℕ) : ExtendedPoint r → ExtendedPoint r :=
  fun x => (q x.1, x.2)

def paddedSet {r : ℕ} (S : Set Point) : Set (ExtendedPoint r) :=
  {x | x.2 = 0 ∧ x.1 ∈ S}

def extendedLinear (r : ℕ) (L : GL6) :
    ExtendedPoint r ≃ₗ[F3] ExtendedPoint r :=
  LinearEquiv.prodCongr L (LinearEquiv.refl F3 (Extra r))

/-- The exact five-component all-fusion shadow statement. -/
def claim_61195 : Prop :=
  Function.Bijective q ∧
    q (0 : Point) = 0 ∧
    Set.Finite (Set.univ : Set Direction) ∧
    Set.ncard (Set.univ : Set Direction) = 364 ∧
    Fintype.card (Finset (Fin 5)) = 32 ∧
    ∃ C : Fin 5 → Set IncidenceNode,
      (∀ i : Fin 5, incidenceComponent q (C i)) ∧
      (∀ u : IncidenceNode, ∃! i : Fin 5, u ∈ C i) ∧
      (∃ i₀ : Fin 5,
        Set.ncard (sourceLabels (C i₀)) = 40 ∧
        Set.ncard (targetLabels (C i₀)) = 40 ∧
        ∀ i : Fin 5, i ≠ i₀ →
          Set.ncard (sourceLabels (C i)) = 81 ∧
          Set.ncard (targetLabels (C i)) = 81) ∧
      ∀ K : Finset (Fin 5),
        let S := sourceConnectionSet C K
        let T := targetConnectionSet C K
        identityFree S ∧
          inverseClosed S ∧
          identityFree T ∧
          inverseClosed T ∧
          ordinaryGraphIsomorphism q S T ∧
          ∃ L : GL6,
            linearImage L S = T ∧
            ¬ ordinaryUndirectedCayleyCIDefect q S T ∧
            ∀ r : ℕ, 1 ≤ r →
              ordinaryGraphIsomorphism (extendedQ r)
                (paddedSet S) (paddedSet T) ∧
              linearImage (extendedLinear r L)
                (paddedSet S) = paddedSet T ∧
              ¬ ordinaryUndirectedCayleyCIDefect
                (extendedQ r) (paddedSet S) (paddedSet T)

end
end MathlibPlus.Open.Research.PiecewiseAffineAllFusionsClaim61195
