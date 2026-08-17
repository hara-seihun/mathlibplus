import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61159

noncomputable section

abbrev F3 := ZMod 3
abbrev B := Fin 3 → F3
abbrev G := B × B

/-- The explicit cubic map in the admitted ternary coupled-Hénon family. -/
def henonF (z : B) : B :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

/-- The signed mixed defects used to define the direction fibre. -/
def signedMixedDefects (z : B) : Set B :=
  {w | ∃ a : B,
    w = henonF (a + z) - henonF a - henonF z ∨
    w = henonF (a - z) - henonF a - henonF (-z)}

/-- The span `W_z` of all signed mixed defects. -/
def mixedDefectSpan (z : B) : Submodule F3 B :=
  Submodule.span F3 (signedMixedDefects z)

/-- The exact set sum `A_z + W_z`, with the submodule used as a carrier. -/
def setPlusSpan (A : Set B) (Wz : Submodule F3 B) : Set B :=
  {u | ∃ a : B, a ∈ A ∧ ∃ w : Wz, u = a + w}

/-- Every slice is a union of `W_z`-cosets. -/
def sliceCosetInvariant (A : B → Set B) : Prop :=
  ∀ z : B, setPlusSpan (A z) (mixedDefectSpan z) = A z

/-- The complete coset-slice connection set. -/
def connectionSet (A : B → Set B) : Set G :=
  {p | p.1 ∈ A p.2}

/-- The coupled-Hénon permutation and its linear block-swap comparison. -/
def coupledHenon : G → G :=
  fun p => (p.2, p.1 + henonF p.2)

def blockSwap : G → G :=
  fun p => (p.2, p.1)

/-- The loopless additive Cayley adjacency relation. -/
def cayleyAdjacent {X : Type*} [AddGroup X]
    (S : Set X) (x y : X) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- A vertex-bijection isomorphism between two additive Cayley relations. -/
def cayleyGraphIso {X : Type*} [AddGroup X]
    (S T : Set X) (f : X → X) : Prop :=
  Function.Bijective f ∧
    ∀ x y : X,
      cayleyAdjacent S x y ↔ cayleyAdjacent T (f x) (f y)

/-- The identity-free and inverse-closed conditions used by ordinary
undirected Cayley graphs. -/
def identityFree {X : Type*} [Zero X] (S : Set X) : Prop :=
  (0 : X) ∉ S

def inverseClosed {X : Type*} [Neg X] (S : Set X) : Prop :=
  ∀ x : X, x ∈ S ↔ -x ∈ S

/-- An invertible `F₃`-linear image witness, written as a proof-free predicate. -/
def linearEquivalenceWitness {X : Type*} [AddCommGroup X]
    [Module F3 X] (f : X → X) : Prop :=
  Function.Bijective f ∧
    (∀ x y : X, f (x + y) = f x + f y) ∧
    (∀ c : F3, ∀ x : X, f (c • x) = c • f x)

def linearImageExists {X : Type*} [AddCommGroup X]
    [Module F3 X] (S T : Set X) : Prop :=
  ∃ f : X → X, linearEquivalenceWitness f ∧ f '' S = T

/-- A pair of ordinary undirected Cayley presentations is a CI defect when it
is graph-isomorphic but has no invertible linear connection-set image. -/
def ordinaryUndirectedCayleyCIDefect {X : Type*} [AddCommGroup X]
    [Module F3 X] (S T : Set X) : Prop :=
  identityFree S ∧
    inverseClosed S ∧
    identityFree T ∧
    inverseClosed T ∧
    (∃ f : X → X, cayleyGraphIso S T f) ∧
    ¬ linearImageExists S T

def connectedCayley {X : Type*} [AddGroup X]
    (S : Set X) : Prop :=
  ∀ x y : X,
    Relation.ReflTransGen (cayleyAdjacent S) x y

/-- The retained connected seed-21 descriptor, expressed on the exact active
carrier without introducing an unverified named data table. -/
def connectedSeed21 (S : Set G) : Prop :=
  identityFree S ∧ inverseClosed S ∧ connectedCayley S ∧ Set.ncard S = 144

/-- Fixed-coordinate padding of an active rank-six connection set. -/
abbrev Passive (r : ℕ) := Fin (r - 6) → F3
abbrev PaddedG (r : ℕ) := G × Passive r

def paddedConnectionSet (r : ℕ) (S : Set G) (C : Set (Passive r)) : Set (PaddedG r) :=
  {p | p.1 ∈ S ∧ p.2 ∈ C}

def paddedCoupledHenon (r : ℕ) : PaddedG r → PaddedG r :=
  fun p => (coupledHenon p.1, p.2)

def paddedBlockSwap (r : ℕ) : PaddedG r → PaddedG r :=
  fun p => (blockSwap p.1, p.2)

/-- Claim 61159: the signed mixed-defect coset family is transported by the
coupled-Hénon permutation, has the single block-swap shadow, and therefore
contains no ordinary undirected CI defect, including its fixed-coordinate
paddings. -/
def claim61159 : Prop :=
  (∀ z : B, henonF z ∈ mixedDefectSpan z) ∧
  (∀ A : B → Set B,
    sliceCosetInvariant A →
      let S := connectionSet A
      cayleyGraphIso S (coupledHenon '' S) coupledHenon ∧
        coupledHenon '' S = blockSwap '' S ∧
        linearEquivalenceWitness blockSwap ∧
        (identityFree S → inverseClosed S →
          ¬ ordinaryUndirectedCayleyCIDefect S (coupledHenon '' S)) ∧
        (connectedSeed21 S →
          ¬ ordinaryUndirectedCayleyCIDefect S (coupledHenon '' S)) ∧
        (∀ r : ℕ, 7 ≤ r →
          ∀ C : Set (Passive r),
            paddedCoupledHenon r '' paddedConnectionSet r S C =
              paddedBlockSwap r '' paddedConnectionSet r S C ∧
            ¬ ordinaryUndirectedCayleyCIDefect
                (paddedConnectionSet r S C)
                (paddedCoupledHenon r '' paddedConnectionSet r S C)))

end

end MathlibPlus.Open.ResearchFormalization.Claim61159
