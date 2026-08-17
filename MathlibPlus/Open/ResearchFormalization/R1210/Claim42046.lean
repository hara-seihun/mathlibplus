import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1210Claim42046

open scoped BigOperators
noncomputable section

private abbrev A7 := Fin 2 → ZMod 7

private def developmentAdj (B : Finset A7) (p q : A7 × Bool) : Prop :=
  (p.2 = false ∧ q.2 = true ∧ q.1 - 2 • p.1 ∈ B) ∨
    (p.2 = true ∧ q.2 = false ∧ p.1 - 2 • q.1 ∈ B)

private def sideMap (psi0 psi1 : Equiv.Perm A7)
    (p : A7 × Bool) : A7 × Bool :=
  if p.2 then (psi1 p.1, true) else (psi0 p.1, false)

private def sidePreservingDevelopmentIso
    (B C : Finset A7) (psi0 psi1 : Equiv.Perm A7) : Prop :=
  ∀ p q,
    developmentAdj B p q ↔
      developmentAdj C (sideMap psi0 psi1 p) (sideMap psi0 psi1 q)

private def developmentEquivalent (B C : Finset A7) : Prop :=
  ∃ psi0 psi1 : Equiv.Perm A7,
    sidePreservingDevelopmentIso B C psi0 psi1

private def affineImage (L : A7 ≃ₗ[ZMod 7] A7) (c : A7)
    (B : Finset A7) : Finset A7 :=
  B.image (fun x => L x + c)

private def affineEquivalent (B C : Finset A7) : Prop :=
  ∃ L : A7 ≃ₗ[ZMod 7] A7, ∃ c : A7,
    C = affineImage L c B

private noncomputable def pointCode (x : A7) : ℕ :=
  (Fintype.equivFin A7 x).val

private noncomputable def subsetCode (B : Finset A7) : ℕ :=
  ∑ x ∈ B, 2 ^ pointCode x

private def affineCanonical (k : ℕ) (B : Finset A7) : Prop :=
  B.card = k ∧
    ∀ C : Finset A7, C.card = k → affineEquivalent B C →
      subsetCode B ≤ subsetCode C

private def developmentCanonical (k : ℕ) (B : Finset A7) : Prop :=
  B.card = k ∧
    ∀ C : Finset A7, C.card = k → developmentEquivalent B C →
      subsetCode B ≤ subsetCode C

private noncomputable def subsetCount (k : ℕ) : ℕ :=
  Nat.card {B : Finset A7 // B.card = k}

private noncomputable def affineOrbitCount (k : ℕ) : ℕ :=
  Nat.card {B : Finset A7 // affineCanonical k B}

private noncomputable def developmentTypeCount (k : ℕ) : ℕ :=
  Nat.card {B : Finset A7 // developmentCanonical k B}

private noncomputable def developmentCollisionCount (k : ℕ) : ℕ :=
  Nat.card {p : Finset A7 × Finset A7 //
    p.1.card = k ∧ p.2.card = k ∧
      developmentEquivalent p.1 p.2 ∧ ¬ affineEquivalent p.1 p.2}

private def exactAtlasRow
    (k subsets orbits development : ℕ) : Prop :=
  subsetCount k = subsets ∧
    affineOrbitCount k = orbits ∧
    developmentTypeCount k = development ∧
    developmentCollisionCount k = 0

private def expectedSubsetCount : Fin 14 → ℕ :=
  ![1, 49, 1176, 18424, 211876, 1906884, 13983816, 85900584,
    450978066, 2054455634, 8217822536, 29135916264, 92263734836,
    262596783764]

private def expectedClassCount : Fin 14 → ℕ :=
  ![1, 1, 1, 3, 8, 32, 179, 954, 4758, 21225, 84050, 296557,
    937022, 2663422]

/-- The exact subset, affine-orbit, and side-colored development atlas. -/
def exactSubsetAffineDevelopmentTable_claim42046 : Prop :=
  Fintype.card (A7 × Bool) = 98 ∧
  (∀ k : Fin 14,
    exactAtlasRow k.val (expectedSubsetCount k)
      (expectedClassCount k) (expectedClassCount k)) ∧
  (∑ k : Fin 14, subsetCount k.val = 394821713910) ∧
  (∑ k : Fin 14, affineOrbitCount k.val = 4008213) ∧
  (∑ k : Fin 14, developmentTypeCount k.val = 4008213)

end
end MathlibPlus.Open.ResearchFormalization.R1210Claim42046
