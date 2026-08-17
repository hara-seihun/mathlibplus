import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.CI61014

noncomputable section

abbrev F3 := ZMod 3
abbrev V (d : ℕ) := Fin d → F3

private def coordinateIndex (d : ℕ) (hd : d = 6 ∨ d = 7) (i : ℕ) : Fin d :=
  ⟨i % d, Nat.mod_lt _ (by rcases hd with rfl | rfl <;> omega)⟩

private def pointedSwitch (d : ℕ) (hd : d = 6 ∨ d = 7) (v : V d) : V d :=
  let z := v (coordinateIndex d hd 0)
  let x := v (coordinateIndex d hd (d - 4))
  let u := v (coordinateIndex d hd (d - 3))
  let w := v (coordinateIndex d hd (d - 1))
  let vv := v (coordinateIndex d hd (d - 2))
  fun i =>
    if i.1 = 0 then z - u - vv ^ 2
    else if i.1 = d - 4 then x + w ^ 2 + vv ^ 2 - u
    else if i.1 = d - 3 then u + vv + w + vv * w + vv ^ 2
    else v i

private def linearShadow (d : ℕ) (hd : d = 6 ∨ d = 7) (v : V d) : V d :=
  let z := v (coordinateIndex d hd 0)
  let x := v (coordinateIndex d hd (d - 4))
  let u := v (coordinateIndex d hd (d - 3))
  let w := v (coordinateIndex d hd (d - 1))
  fun i =>
    if i.1 = 0 then z + 2 * u
    else if i.1 = d - 4 then x + 2 * u + w
    else if i.1 = d - 3 then u + w
    else v i

private def linearOverF3 {d : ℕ} (L : V d → V d) : Prop :=
  L 0 = 0 ∧
    (∀ x y : V d, L (x + y) = L x + L y) ∧
    (∀ c : F3, ∀ x : V d, L (c • x) = c • L x)

private def linearAutomorphism {d : ℕ} (L : V d → V d) : Prop :=
  linearOverF3 L ∧ Function.Bijective L

private def pointedPermutation {d : ℕ} (f : V d → V d) : Prop :=
  Function.Bijective f ∧ f 0 = 0

/-- A projective direction is represented by the exact two-element set
`{a,-a}` with `a ≠ 0`; this is a concrete representative of
`(V_d \ {0}) / (a ∼ -a)`. -/
abbrev ProjectiveDirection (d : ℕ) :=
  {A : Set (V d) // ∃ a : V d, a ≠ 0 ∧ A = ({a, -a} : Set (V d))}

abbrev BipartiteVertex (d : ℕ) := Bool × ProjectiveDirection d

private def differenceRelation (d : ℕ) (hd : d = 6 ∨ d = 7)
    (A B : ProjectiveDirection d) : Prop :=
  ∃ a : V d, a ∈ A.1 ∧
    ∃ y : V d,
      pointedSwitch d hd (y + a) - pointedSwitch d hd y ∈ B.1

private def bipartiteEdge (d : ℕ) (hd : d = 6 ∨ d = 7)
    (x y : BipartiteVertex d) : Prop :=
  (x.1 = false ∧ y.1 = true ∧ differenceRelation d hd x.2 y.2) ∨
    (x.1 = true ∧ y.1 = false ∧ differenceRelation d hd y.2 x.2)

private def connected (d : ℕ) (hd : d = 6 ∨ d = 7)
    (x y : BipartiteVertex d) : Prop :=
  Relation.ReflTransGen (bipartiteEdge d hd) x y

private def connectedComponent (d : ℕ) (hd : d = 6 ∨ d = 7)
    (x : BipartiteVertex d) : Set (BipartiteVertex d) :=
  {y | connected d hd x y}

private def componentFamily (d : ℕ) (hd : d = 6 ∨ d = 7) :
    Set (Set (BipartiteVertex d)) :=
  Set.range (connectedComponent d hd)

private def sourceDirections {d : ℕ} (C : Set (BipartiteVertex d)) :
    Set (ProjectiveDirection d) :=
  {A | (false, A) ∈ C}

private def targetDirections {d : ℕ} (C : Set (BipartiteVertex d)) :
    Set (ProjectiveDirection d) :=
  {B | (true, B) ∈ C}

private def shadowImage (d : ℕ) (hd : d = 6 ∨ d = 7)
    (I : Set (ProjectiveDirection d)) : Set (ProjectiveDirection d) :=
  {B | ∃ A : ProjectiveDirection d, A ∈ I ∧
      ∃ a : V d, a ∈ A.1 ∧ B.1 = ({linearShadow d hd a, -linearShadow d hd a} : Set (V d))}

private def componentShadowStatement (d : ℕ) (hd : d = 6 ∨ d = 7) : Prop :=
  ∀ C : Set (BipartiteVertex d), C ∈ componentFamily d hd →
    shadowImage d hd (sourceDirections C) = targetDirections C

private def sideCard {d : ℕ} (C : Set (BipartiteVertex d)) (b : Bool) : ℕ :=
  Nat.card {A : ProjectiveDirection d // (b, A) ∈ C}

private def replayCounts (d : ℕ) (hd : d = 6 ∨ d = 7) : Prop :=
  Nat.card (V d) = 3 ^ d ∧
  Nat.card (ProjectiveDirection d) = (3 ^ d - 1) / 2 ∧
  Nat.card {C : Set (BipartiteVertex d) // C ∈ componentFamily d hd} =
    (if d = 6 then 76 else 229) ∧
  Nat.card {C : Set (BipartiteVertex d) //
      C ∈ componentFamily d hd ∧ sideCard C false = 1 ∧ sideCard C true = 1} =
    (if d = 6 then 40 else 121) ∧
  Nat.card {C : Set (BipartiteVertex d) //
      C ∈ componentFamily d hd ∧ sideCard C false = 9 ∧ sideCard C true = 9} =
    if d = 6 then 36 else 108

private def sourceConnectionSet (d : ℕ) (K : Set (Set (BipartiteVertex d))) : Set (V d) :=
  {a | ∃ C : Set (BipartiteVertex d), C ∈ K ∧
      ∃ A : ProjectiveDirection d, A ∈ sourceDirections C ∧ a ∈ A.1}

private def targetConnectionSet (d : ℕ) (K : Set (Set (BipartiteVertex d))) : Set (V d) :=
  {b | ∃ C : Set (BipartiteVertex d), C ∈ K ∧
      ∃ B : ProjectiveDirection d, B ∈ targetDirections C ∧ b ∈ B.1}

private def inverseClosed {d : ℕ} (S : Set (V d)) : Prop :=
  ∀ ⦃a : V d⦄, a ∈ S → -a ∈ S

private def identityFree {d : ℕ} (S : Set (V d)) : Prop :=
  (0 : V d) ∉ S

private def cayleyAdjacency {d : ℕ} (S : Set (V d)) (x y : V d) : Prop :=
  x ≠ y ∧ y - x ∈ S

private def cayleyIsomorphism {d : ℕ} (S T : Set (V d))
    (f : V d → V d) : Prop :=
  Function.Bijective f ∧
    ∀ x y : V d,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

private def ordinaryUndirectedCayleyCIDefect {d : ℕ}
    (S T : Set (V d)) (f : V d → V d) : Prop :=
  identityFree S ∧ identityFree T ∧ inverseClosed S ∧ inverseClosed T ∧
    cayleyIsomorphism S T f ∧
    ¬ ∃ e : V d ≃+ V d, Set.image (fun x => e x) S = T

private def componentCollection {d : ℕ} (hd : d = 6 ∨ d = 7)
    (K : Set (Set (BipartiteVertex d))) : Prop :=
  K ⊆ componentFamily d hd

private def unionConclusion (d : ℕ) (hd : d = 6 ∨ d = 7) : Prop :=
  ∀ K : Set (Set (BipartiteVertex d)), componentCollection hd K →
    let S := sourceConnectionSet d K
    let T := targetConnectionSet d K
    inverseClosed S ∧ identityFree S ∧ inverseClosed T ∧ identityFree T ∧
      cayleyIsomorphism S T (pointedSwitch d hd) ∧
      Set.image (linearShadow d hd) S = T ∧
      ¬ ordinaryUndirectedCayleyCIDefect S T (pointedSwitch d hd)

/-- Claim 61014.  This retains the literal triangular switch, the literal
single linear shadow, the bipartite difference relation on projective
directions, every connected-component shadow identity, and the consequence for
all inverse-closed component unions, without replacing the finite direction
or reconstruction carriers by arbitrary predicates. -/
def claim61014 : Prop :=
  ∀ (d : ℕ) (hd : d = 6 ∨ d = 7),
    pointedPermutation (pointedSwitch d hd) ∧
    linearAutomorphism (linearShadow d hd) ∧
    replayCounts d hd ∧
    componentShadowStatement d hd ∧
    unionConclusion d hd

end
end MathlibPlus.Open.NewResearch2.CI61014
