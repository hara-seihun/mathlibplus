import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CI61145

noncomputable section

abbrev F3 := ZMod 3
abbrev V := Fin 6 → F3

/-- The displayed three-parameter triangular permutation. -/
def qMap (alpha beta gamma : F3) (x : V) : V :=
  fun i =>
    if i = (0 : Fin 6) then
      x 0 + alpha * (x 1) ^ 2 + 2 * beta * x 1 * x 2 + gamma * (x 2) ^ 2
    else if i = (1 : Fin 6) then
      x 1
    else if i = (2 : Fin 6) then
      x 2
    else if i = (3 : Fin 6) then
      x 3 + x 1 - (x 1) ^ 2
    else if i = (4 : Fin 6) then
      x 4 + x 2 + x 1 * x 2
    else
      x 5 - (x 2) ^ 2

/-- The displayed common linear shadow. -/
def linearShadow (alpha beta : F3) (x : V) : V :=
  fun i =>
    if i = (0 : Fin 6) then
      x 0 + alpha * x 1 + beta * x 2
    else if i = (1 : Fin 6) then
      x 1
    else if i = (2 : Fin 6) then
      x 2
    else if i = (3 : Fin 6) then
      x 3
    else if i = (4 : Fin 6) then
      x 4
    else
      x 5

/-- A pointed permutation of the additive vector carrier. -/
def pointedPermutation (f : V → V) : Prop :=
  Function.Bijective f ∧ f 0 = 0

/-- The exact linearity and invertibility assertion for the displayed shadow. -/
def invertibleLinearMap (L : V → V) : Prop :=
  L 0 = 0 ∧
    (∀ x y : V, L (x + y) = L x + L y) ∧
      (∀ c : F3, ∀ x : V, L (c • x) = c • L x) ∧
        Function.Bijective L

/-- A projective direction is the two-element set `{a,-a}` for a nonzero
vector, giving the stated quotient by `a ~ -a`. -/
abbrev ProjectiveDirection :=
  {A : Set V // ∃ a : V, a ≠ 0 ∧ A = ({a, -a} : Set V)}

abbrev BipartiteVertex := Bool × ProjectiveDirection

/-- The source-to-target inverse-direction incidence relation. -/
def inverseDirectionIncidence (alpha beta gamma : F3)
    (A B : ProjectiveDirection) : Prop :=
  ∃ a : V, a ∈ A.1 ∧
    ∃ x : V,
      qMap alpha beta gamma (x + a) - qMap alpha beta gamma x ∈ B.1

/-- The incidence relation viewed as an undirected bipartite edge relation. -/
def bipartiteEdge (alpha beta gamma : F3)
    (x y : BipartiteVertex) : Prop :=
  (x.1 = false ∧ y.1 = true ∧
      inverseDirectionIncidence alpha beta gamma x.2 y.2) ∨
    (x.1 = true ∧ y.1 = false ∧
      inverseDirectionIncidence alpha beta gamma y.2 x.2)

/-- The connected component of a bipartite vertex. -/
def connectedComponent (alpha beta gamma : F3)
    (x : BipartiteVertex) : Set BipartiteVertex :=
  {y | Relation.ReflTransGen (bipartiteEdge alpha beta gamma) x y}

/-- The family of all connected components. -/
def componentFamily (alpha beta gamma : F3) :
    Set (Set BipartiteVertex) :=
  Set.range (connectedComponent alpha beta gamma)

/-- The complete source direction set of a component. -/
def sourceDirections (C : Set BipartiteVertex) :
    Set ProjectiveDirection :=
  {A | (false, A) ∈ C}

/-- The complete target direction set of a component. -/
def targetDirections (C : Set BipartiteVertex) :
    Set ProjectiveDirection :=
  {B | (true, B) ∈ C}

/-- The direction-level image induced by the displayed linear shadow. -/
def shadowImage (alpha beta : F3)
    (I : Set ProjectiveDirection) : Set ProjectiveDirection :=
  {B | ∃ A : ProjectiveDirection, A ∈ I ∧
    ∃ a : V, a ∈ A.1 ∧
      B.1 = ({linearShadow alpha beta a,
        -linearShadow alpha beta a} : Set V)}

/-- The connection set obtained from a collection of source components. -/
def sourceConnectionSet (K : Set (Set BipartiteVertex)) : Set V :=
  {a | ∃ C : Set BipartiteVertex, C ∈ K ∧
    ∃ A : ProjectiveDirection, A ∈ sourceDirections C ∧ a ∈ A.1}

/-- The connection set obtained from a collection of target components. -/
def targetConnectionSet (K : Set (Set BipartiteVertex)) : Set V :=
  {b | ∃ C : Set BipartiteVertex, C ∈ K ∧
    ∃ B : ProjectiveDirection, B ∈ targetDirections C ∧ b ∈ B.1}

/-- Every displayed connection set is inverse-closed. -/
def inverseClosed (S : Set V) : Prop :=
  ∀ ⦃a : V⦄, a ∈ S → -a ∈ S

/-- A connection set is identity-free. -/
def identityFree (S : Set V) : Prop :=
  (0 : V) ∉ S

/-- Adjacency in the ordinary Cayley graph on the additive carrier. -/
def cayleyAdjacency (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- An ordinary graph isomorphism between two Cayley graphs. -/
def cayleyIsomorphism (S T : Set V) (f : V → V) : Prop :=
  Function.Bijective f ∧
    ∀ x y : V,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

/-- The exact ordinary-undirected Cayley-CI obstruction excluded by the
common linear shadow. -/
def ordinaryUndirectedCayleyCIDefect
    (S T : Set V) (f : V → V) : Prop :=
  identityFree S ∧ identityFree T ∧
    inverseClosed S ∧ inverseClosed T ∧
      cayleyIsomorphism S T f ∧
        ¬ ∃ e : V ≃+ V,
          Set.image (fun x : V => e x) S = T

/-- A collection consists only of connected components of the displayed
bipartite relation. -/
def componentCollection (alpha beta gamma : F3)
    (K : Set (Set BipartiteVertex)) : Prop :=
  K ⊆ componentFamily alpha beta gamma

/-- Claim 61145: all 27 displayed permutations have the componentwise
linear shadow and hence no ordinary-undirected Cayley-CI defect among their
component unions. -/
def claim61145 : Prop :=
  Nat.card F3 = 3 ∧
    Nat.card ProjectiveDirection = 364 ∧
      ∀ alpha beta gamma : F3,
        pointedPermutation (qMap alpha beta gamma) ∧
          invertibleLinearMap (linearShadow alpha beta) ∧
            (∀ C : Set BipartiteVertex,
              C ∈ componentFamily alpha beta gamma →
                shadowImage alpha beta (sourceDirections C) =
                  targetDirections C) ∧
              ∀ K : Set (Set BipartiteVertex),
                componentCollection alpha beta gamma K →
                  let S := sourceConnectionSet K
                  let T := targetConnectionSet K
                  inverseClosed S ∧ identityFree S ∧
                    inverseClosed T ∧ identityFree T ∧
                      cayleyIsomorphism S T (qMap alpha beta gamma) ∧
                        Set.image (linearShadow alpha beta) S = T ∧
                          ¬ ordinaryUndirectedCayleyCIDefect
                            S T (qMap alpha beta gamma)

end

end MathlibPlus.Open.ResearchFormalization.CI61145
