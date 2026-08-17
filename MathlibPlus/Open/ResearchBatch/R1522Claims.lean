import MathlibPlus.Open.ResearchBatch.R1522

namespace MathlibPlus.Open.ResearchBatch.R1522Claims

open MathlibPlus.Open.ResearchBatch.R1522

abbrev Cycle28 := MathlibPlus.Open.ResearchBatch.R1522.Cycle28
abbrev Perm28 := Equiv.Perm Cycle28

/-- The set of products of two disjoint cross-layer transpositions. -/
def admissibleMatching : Set Perm28 :=
  {τ |
    ∃ a b c d : Cycle28,
      admissiblePosition a b c d ∧ τ = doubleTransposition a b c d}

def affineNormalizer : Subgroup (Equiv.Perm Cycle28) :=
  Subgroup.normalizer (Subgroup.zpowers cycleShift : Set (Equiv.Perm Cycle28))

def sameAffineOrbit (x y : Perm28) : Prop :=
  ∃ g : affineNormalizer,
    y = (g : Perm28) * x * (g : Perm28)⁻¹

def representativeFamily (reps : Fin 145 → Perm28) : Prop :=
  (∀ i, reps i ∈ admissibleMatching) ∧
    (∀ i j, i ≠ j → ¬ sameAffineOrbit (reps i) (reps j)) ∧
    (∀ x, x ∈ admissibleMatching → ∃ i, sameAffineOrbit x (reps i))

def targetGenerator (τ : Perm28) : Perm28 :=
  τ⁻¹ * cycleShift * τ

def generatedQuotient (τ : Perm28) : Subgroup (Equiv.Perm Cycle28) :=
  Subgroup.closure ({cycleShift, targetGenerator τ} : Set Perm28)

def quotientCopy (r : Perm28) : Subgroup (Equiv.Perm Cycle28) :=
  Subgroup.zpowers r

def conjugatesCopyBy (q : Perm28) (R T : Subgroup (Equiv.Perm Cycle28)) : Prop :=
  Set.image (fun x : Perm28 => q⁻¹ * x * q) (R : Set Perm28) = (T : Set Perm28)

def fullConjugatorCoset (τ : Perm28) : Set Perm28 :=
  {q | ∃ a : affineNormalizer, q = (a : Perm28) * τ}

def internalConjugatorSet (τ : Perm28) : Set Perm28 :=
  fullConjugatorCoset τ ∩ (generatedQuotient τ : Set Perm28)

def internalTransporter (τ : Perm28) : Prop :=
  ∃ q : Perm28,
    q ∈ internalConjugatorSet τ ∧
      conjugatesCopyBy q (quotientCopy cycleShift)
        (quotientCopy (targetGenerator τ))

def invariantBlockSystem (X : Subgroup (Equiv.Perm Cycle28)) (k : ℕ) : Prop :=
  ∃ blocks : Set (Set Cycle28),
    (∀ B : Set Cycle28, B ∈ blocks → B.Nonempty ∧ Set.ncard B = k) ∧
      (∀ x : Cycle28, ∃! B : Set Cycle28, B ∈ blocks ∧ x ∈ B) ∧
      (∀ g : X, ∀ B : Set Cycle28, B ∈ blocks →
        (fun x : Cycle28 => (g : Perm28) x) '' B ∈ blocks)

def nontrivialInvariantBlockSize
    (X : Subgroup (Equiv.Perm Cycle28)) (k : ℕ) : Prop :=
  1 < k ∧ k < 28 ∧ invariantBlockSystem X k

def exactExceptionalBlockSizes
    (X : Subgroup (Equiv.Perm Cycle28)) : Prop :=
  ∀ k : ℕ,
    nontrivialInvariantBlockSize X k ↔ k = 2 ∨ k = 14

/-- Claim 38100: the unique exceptional affine-normalizer orbit and its
exact generated-group, block, and conjugator-coset data. -/
def claim_38100 : Prop :=
  ∃ reps : Fin 145 → Perm28,
    representativeFamily reps ∧
      Nat.card {i : Fin 145 // internalTransporter (reps i)} = 144 ∧
      (∀ i : Fin 145, internalTransporter (reps i) ↔ i.val ≠ 136) ∧
      reps ⟨136, by decide⟩ = exceptionalTau ∧
      Nat.card (generatedQuotient exceptionalTau) = 208089907200 ∧
      exactExceptionalBlockSizes (generatedQuotient exceptionalTau) ∧
      Set.ncard (fullConjugatorCoset exceptionalTau) = 336 ∧
      Set.ncard (internalConjugatorSet exceptionalTau) = 0

end MathlibPlus.Open.ResearchBatch.R1522Claims
