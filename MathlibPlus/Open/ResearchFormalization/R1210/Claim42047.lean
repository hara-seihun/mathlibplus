import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1210Claim42047

open scoped BigOperators
noncomputable section

private abbrev A7 := Fin 2 → ZMod 7

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

private noncomputable def affineOrbitCount (k : ℕ) : ℕ :=
  Nat.card {B : Finset A7 // affineCanonical k B}

private abbrev canonicalOnePointExtension (k : ℕ) :=
  {p : Finset A7 × A7 // affineCanonical k p.1 ∧ p.2 ∉ p.1}

/-- The exact deletion and canonical augmentation census. -/
def canonicalAugmentationCounts_claim42047 : Prop :=
  Fintype.card A7 = 49 ∧
  (∀ (k : ℕ) (C : Finset A7), C.card = k + 1 →
    ∃ x : A7, x ∈ C ∧ (C.erase x).card = k) ∧
  Nat.card (canonicalOnePointExtension 10) = 3277950 ∧
  Nat.card (canonicalOnePointExtension 11) = 11269166 ∧
  Nat.card (canonicalOnePointExtension 12) = 34669814 ∧
  affineOrbitCount 11 = 296557 ∧
  affineOrbitCount 12 = 937022 ∧
  affineOrbitCount 13 = 2663422

end
end MathlibPlus.Open.ResearchFormalization.R1210Claim42047
