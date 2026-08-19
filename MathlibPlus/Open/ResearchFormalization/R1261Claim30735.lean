import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1261Claim30735

noncomputable section

private abbrev CrtOdd30735 (p q r : ℕ) := ZMod p × ZMod q × ZMod r
private abbrev CrtQ4n30735 (p q r : ℕ) := CrtOdd30735 p q r × ZMod 4

private def crtQ4nMul30735 (p q r : ℕ)
    (a b : CrtQ4n30735 p q r) : CrtQ4n30735 p q r :=
  (a.1 +
      (((-1 : ZMod p) ^ a.2.val) * b.1.1,
        ((-1 : ZMod q) ^ a.2.val) * b.1.2.1,
        ((-1 : ZMod r) ^ a.2.val) * b.1.2.2),
    a.2 + b.2)

private def q4nTranslationSet30735 (p q r : ℕ) :
    Set (Equiv.Perm (CrtQ4n30735 p q r)) :=
  {e | ∃ g : CrtQ4n30735 p q r, ∀ x,
    e x = crtQ4nMul30735 p q r g x}

private def q4nStandardCopy30735 (p q r : ℕ) :
    Subgroup (Equiv.Perm (CrtQ4n30735 p q r)) :=
  Subgroup.closure (q4nTranslationSet30735 p q r)

private def standardRegularQ4n30735
    {n p q r : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n30735 p q r))) : Prop :=
  (∀ x y : CrtQ4n30735 p q r, ∃! u : R, u.1 x = y) ∧
    Nat.card R = 4 * n ∧
    R = q4nStandardCopy30735 p q r

private def triangularFormula30735 {p q r : ℕ}
    (ζ : (ZMod p)ˣ) (x : CrtQ4n30735 p q r) : CrtQ4n30735 p q r :=
  ((((ζ : ZMod p) ^ x.1.2.1.val) * x.1.1,
      x.1.2.1,
      x.1.2.2),
    x.2)

private def descendingPrimeFactors30735 (n : ℕ) : List ℕ :=
  n.primeFactorsList.reverse

private def hallPrefixProduct30735 (n j : ℕ) : ℕ :=
  (descendingPrimeFactors30735 n).take j |>.prod

private def subgroupOrbitBlock30735 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ u : P, u.1 x = y}

private def subgroupOrbitPartition30735 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, subgroupOrbitBlock30735 P x = B}

private def characteristicSubgroupOfOrder30735 {Ω : Type*}
    (R P : Subgroup (Equiv.Perm Ω)) (d : ℕ) : Prop :=
  P ≤ R ∧ Nat.card P = d ∧
    ∀ φ : R ≃* R, ∀ x : R,
      (x : Equiv.Perm Ω) ∈ P → (φ x : Equiv.Perm Ω) ∈ P

private def characteristicHallPartition30735 {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) (d : ℕ) : Set (Set Ω) :=
  {B | ∃ P : Subgroup (Equiv.Perm Ω),
    characteristicSubgroupOfOrder30735 R P d ∧
      B ∈ subgroupOrbitPartition30735 P}

private def preservesDescendingHallPrefixes30735 {p q r n : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n30735 p q r)))
    (f : Equiv.Perm (CrtQ4n30735 p q r)) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    j ≤ (descendingPrimeFactors30735 n).length →
    Set.image (fun B : Set (CrtQ4n30735 p q r) => f '' B)
        (characteristicHallPartition30735 R
          (hallPrefixProduct30735 n j)) =
      characteristicHallPartition30735 R (hallPrefixProduct30735 n j)

/-- Claim 30735: the exact CRT triangular permutation conjugates the standard
    regular quaternionic copy and preserves every characteristic descending
    Hall-prefix partition under the distinct-prime resonance hypotheses. -/
def triangularHallPrefixConjugator_claim30735 : Prop :=
  ∀ (n q p : ℕ),
    Squarefree n →
      Nat.Prime q → Nat.Prime p → q ≠ p →
        q ∣ n → p ∣ n → q ∣ p - 1 → p * q ∣ n →
          ∀ ζ : (ZMod p)ˣ, orderOf ζ = q →
            let r := n / (p * q)
            let Ω := CrtQ4n30735 p q r
            let R := q4nStandardCopy30735 p q r
            ∃ f : Equiv.Perm Ω,
              (∀ x : Ω, f x = triangularFormula30735 ζ x) ∧
                standardRegularQ4n30735 (n := n) R ∧
                  (∃ T : Subgroup (Equiv.Perm Ω),
                    (∀ g : Equiv.Perm Ω,
                      g ∈ T ↔
                        ∃ u : Equiv.Perm Ω,
                          u ∈ R ∧ g = f.symm * u * f) ∧
                    preservesDescendingHallPrefixes30735 (n := n) R f)

end

end MathlibPlus.Open.ResearchFormalization.R1261Claim30735
