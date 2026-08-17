import MathlibPlus.Open.GraphTheory.Claim61027

open Set
open MathlibPlus.Open.GraphTheory.Claim61027

namespace MathlibPlus.Open.GraphTheory.Claim61029

noncomputable section

/-- Right translation of a subset of a group. -/
def rightTranslateSet {G : Type} [Group G]
    (F : Set G) (g : G) : Set G :=
  {x | ∃ y, y ∈ F ∧ x = y * g}

/-- The product `F⁻¹ F`, written by its quotient-of-two-elements membership. -/
def differenceSet {G : Type} [Group G]
    (F : Set G) : Set G :=
  {g | ∃ x ∈ F, ∃ y ∈ F, x⁻¹ * y = g}

/-- The right setwise stabilizer occurring in the half-density statement. -/
def rightStabilizerSet {G : Type} [Group G]
    (F : Set G) : Set G :=
  {h | rightTranslateSet F h = F}

/-- The two orientations of a coset, kept explicit for the nonabelian claim. -/
def rightCosetSet {G : Type} [Group G]
    (H : Set G) (d : G) : Set G :=
  {x | ∃ h ∈ H, x = h * d}

def leftCosetSet {G : Type} [Group G]
    (d : G) (H : Set G) : Set G :=
  {x | ∃ h ∈ H, x = d * h}

/-- Pointwise form of the alternating-class assertion on right-multiplication
cycles. -/
def alternatesUnderRightMultiplication {G : Type} [Group G]
    (F : Set G) (d : G) : Prop :=
  ∀ x, x ∈ F ↔ x * d ∉ F

def inverseClosedSet {G : Type} [Group G]
    (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ x⁻¹ ∈ S

/-- The exact inverse atom represented by a chosen nonidentity element. -/
def inverseAtomOf {G : Type} [Group G] [DecidableEq G]
    (d : G) (hd : d ≠ 1) : InverseAtom G :=
  ⟨{d, d⁻¹}, ⟨d, hd, rfl⟩⟩

/-- The finite-group half-density difference-cover boundary, including the
subgroup, coset, inverse-closure, order-parity, and cycle assertions. -/
def claim61029SetBoundary : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (F : Set G),
    2 * Set.ncard F ≥ Fintype.card G →
    let M := Set.univ \ differenceSet F
    ∃ H : Subgroup G,
      (H : Set G) = rightStabilizerSet F ∧
      ((M = ∅ ∧ differenceSet F = Set.univ) ∨
        (M.Nonempty ∧
          2 * Set.ncard F = Fintype.card G ∧
          (∀ d ∈ M,
            rightTranslateSet F d = Set.univ \ F ∧
              d ∈ Subgroup.normalizer (H : Set G) ∧
              d ^ 2 ∈ H ∧
              M = rightCosetSet (H : Set G) d ∧
              M = leftCosetSet d (H : Set G) ∧
              M = leftCosetSet d⁻¹ (H : Set G)) ∧
          inverseClosedSet M ∧
          (∀ d ∈ M,
            Even (orderOf d) ∧
              alternatesUnderRightMultiplication F d)))

/-- The normalized permutation `q = α⁻¹ ∘ f`, as an equivalence. -/
def normalizedPermutationEquiv {G : Type} [Group G]
    (α : G ≃* G) (f : Equiv.Perm G) : Equiv.Perm G :=
  f.trans α.toEquiv.symm

/-- The target-side shadow after undoing the normalization by `α`. -/
def alphaComponentShadow {G : Type} [Group G] [DecidableEq G]
    (α : G ≃* G) (f q : Equiv.Perm G) : Prop :=
  ∀ 𝒦 : Set (Set (IncidenceVertex G)),
    isComponentCollection q 𝒦 →
      cayleyGraphIsomorphism f
        (selectedSourceSet q 𝒦)
        (Set.image (fun x => α x) (selectedTargetSet q 𝒦)) ∧
      Set.image (fun x => α x) (selectedSourceSet q 𝒦) =
        Set.image (fun x => α x) (selectedTargetSet q 𝒦)

/-- The incidence and support boundary for the normalized permutation. -/
def claim61029PermutationBoundary : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (α : G ≃* G) (f : Equiv.Perm G),
    f 1 = 1 →
    let q := normalizedPermutationEquiv α f
    let F := {x : G | q x = x}
    let M := Set.univ \ differenceSet F
    2 * q.support.card ≤ Fintype.card G →
      (∀ (d : G) (hd : d ≠ 1),
        d ∉ M →
          atomImageIntersects q (inverseAtomOf d hd) (inverseAtomOf d hd)) ∧
      (((2 * q.support.card < Fintype.card G) ∨
          Odd (Fintype.card G)) →
        M = ∅ ∧
          (∀ C : Set (IncidenceVertex G),
            isIncidenceComponent q C →
              sourceLabels q C = targetLabels q C) ∧
          identityComponentShadow q ∧
          alphaComponentShadow α f q)

/-- A pointed ordinary-undirected Cayley graph isomorphism which is not
induced by any group automorphism. -/
def normalizedCayleyCIDefect {G : Type} [Group G]
    (f : Equiv.Perm G) (S T : Set G) : Prop :=
  f 1 = 1 ∧
    cayleyGraphIsomorphism f S T ∧
    ¬ ∃ α : G ≃* G, Set.image (fun x => α x) S = T

def identityFreeInverseClosed {G : Type} [Group G]
    (S : Set G) : Prop :=
  1 ∉ S ∧ inverseClosedSet S

/-- On an odd finite group, every normalized inverse-closed Cayley CI defect
moves more than half the vertices relative to every group automorphism. -/
def claim61029OddDefectBound : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (_hodd : Odd (Fintype.card G))
    (S T : Set G) (f : Equiv.Perm G),
    identityFreeInverseClosed S →
    identityFreeInverseClosed T →
    normalizedCayleyCIDefect f S T →
    ∀ α : G ≃* G,
      2 * Set.ncard {x : G | f x ≠ α x} > Fintype.card G

/-- Claim 61029: the nonabelian half-density boundary and its normalized
inverse-atom and odd-order Cayley-CI consequences.  The final odd-order
quantifier includes every elementary-Sylow N4 scalar group `E(M,3)`, whether
or not the resulting semidirect group is abelian. -/
def claim61029 : Prop :=
  claim61029SetBoundary ∧
    claim61029PermutationBoundary ∧
    claim61029OddDefectBound

end

end MathlibPlus.Open.GraphTheory.Claim61029
