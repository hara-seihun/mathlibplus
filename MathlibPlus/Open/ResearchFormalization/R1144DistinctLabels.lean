import Mathlib
import MathlibPlus.Combinatorics.Claim30192

namespace MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

noncomputable section

abbrev C7 := ZMod 7

def translateSet (B : Set C7) (t : C7) : Set C7 :=
  {x | ∃ b ∈ B, x = b + t}

def development (B : Set C7) : Set (Set C7) :=
  MathlibPlus.Combinatorics.Claim30192.translationDevelopment B

def affinePointPermutation (π : Equiv.Perm C7) : Prop :=
  ∃ a b : C7, ∀ x : C7, π x = a * x + b

def nonlinearDevelopmentPermutation (π : Equiv.Perm C7) : Prop :=
  ¬ affinePointPermutation π ∧
    ∃ B : Set C7,
      2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      Set.image (fun C : Set C7 => Set.image (π : C7 → C7) C)
          (development B) =
        development (Set.image (π : C7 → C7) B)

def fanoA : Set (Set C7) :=
  development ({0, 1, 3} : Set C7)

def fanoB : Set (Set C7) :=
  development ({0, 2, 3} : Set C7)

def supportedLine (π : Equiv.Perm C7)
    (F : Set (Set C7)) (B : Set C7) : Prop :=
  B ∈ F ∧
    Set.image (fun C : Set C7 => Set.image (π : C7 → C7) C)
        (development B) =
      development (Set.image (π : C7 → C7) B)

def normalizedLabel (π : Equiv.Perm C7)
    (B : Set C7) (δ : C7 → C7) : Prop :=
  δ 0 = 0 ∧
    ∀ s : C7,
      Set.image (π : C7 → C7) (translateSet B s) =
        translateSet (Set.image (π : C7 → C7) B) (δ s)

def translatedLabel (δ : C7 → C7) (t : C7) : C7 → C7 :=
  fun s => δ (t + s) - δ t

/-- The fourteen-set support system: seven cyclic lines and their seven
complements. -/
def fanoSupportSystemCarrier (F : Set (Set C7)) : Set (Set C7) :=
  F ∪ {C | ∃ B ∈ F, C = Set.univ \ B}

def fanoSupportSystem (π : Equiv.Perm C7) (F : Set (Set C7)) : Prop :=
  (F = fanoA ∨ F = fanoB) ∧
    ∀ B : Set C7, 2 ≤ B.ncard → B.ncard ≤ 5 →
      (Set.image (fun C : Set C7 => Set.image (π : C7 → C7) C)
          (development B) =
        development (Set.image (π : C7 → C7) B) ↔
        B ∈ fanoSupportSystemCarrier F)

/-- Claim 30202: every nonlinear development permutation has its unique
supported Fano system, and every normalized label on every supported line has
seven pairwise distinct translated labels. -/
def sevenTranslatedLabelsDistinct_claim30202 : Prop :=
  Nat.card {π : Equiv.Perm C7 // nonlinearDevelopmentPermutation π} = 588 ∧
    (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
      ∃! F : Set (Set C7), fanoSupportSystem π F) ∧
    (∀ (π : Equiv.Perm C7), nonlinearDevelopmentPermutation π →
      ∀ F : Set (Set C7), fanoSupportSystem π F →
        ∀ B : Set C7, B ∈ F →
          ∀ δ : C7 → C7, normalizedLabel π B δ →
            ∀ t t' : C7, t ≠ t' →
              translatedLabel δ t ≠ translatedLabel δ t')

end

end MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels
