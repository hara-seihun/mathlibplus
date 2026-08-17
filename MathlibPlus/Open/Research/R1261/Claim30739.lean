import Mathlib

namespace MathlibPlus.Open.Research.R1261

private abbrev CrtOdd30739 (p q r : ℕ) := ZMod p × ZMod q × ZMod r

private abbrev CrtQ4n30739 (p q r : ℕ) := CrtOdd30739 p q r × ZMod 4

private def crtQ4nMul30739 (p q r : ℕ)
    (a b : CrtQ4n30739 p q r) : CrtQ4n30739 p q r :=
  (a.1 +
      (((-1 : ZMod p) ^ a.2.val) * b.1.1,
        ((-1 : ZMod q) ^ a.2.val) * b.1.2.1,
        ((-1 : ZMod r) ^ a.2.val) * b.1.2.2),
    a.2 + b.2)

private def q4nTranslationSet30739 (p q r : ℕ) :
    Set (Equiv.Perm (CrtQ4n30739 p q r)) :=
  {e | ∃ g : CrtQ4n30739 p q r, ∀ x,
    e x = crtQ4nMul30739 p q r g x}

private def q4nStandardCopy30739 (p q r : ℕ) :
    Subgroup (Equiv.Perm (CrtQ4n30739 p q r)) :=
  Subgroup.closure (q4nTranslationSet30739 p q r)

private def standardRegularQ4n30739
    {n p q r : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n30739 p q r))) : Prop :=
  (∀ x y : CrtQ4n30739 p q r, ∃! u : R, u.1 x = y) ∧
    Nat.card R = 4 * n ∧
    R = q4nStandardCopy30739 p q r

private def triangularFormula30739 {p q r : ℕ}
    (ζ : (ZMod p)ˣ) (x : CrtQ4n30739 p q r) : CrtQ4n30739 p q r :=
  ((((ζ : ZMod p) ^ x.1.2.1.val) * x.1.1,
      x.1.2.1,
      x.1.2.2),
    x.2)

private def descendingPrimeFactors30739 (n : ℕ) : List ℕ :=
  n.primeFactorsList.reverse

private def hallPrefixProduct30739 (n j : ℕ) : ℕ :=
  (descendingPrimeFactors30739 n).take j |>.prod

private def subgroupOrbitBlock30739 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ u : P, u.1 x = y}

private def subgroupOrbitPartition30739 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, subgroupOrbitBlock30739 P x = B}

private def characteristicSubgroupOfOrder30739 {Ω : Type*}
    (R P : Subgroup (Equiv.Perm Ω)) (d : ℕ) : Prop :=
  P ≤ R ∧ Nat.card P = d ∧
    ∀ φ : R ≃* R, ∀ x : R,
      (x : Equiv.Perm Ω) ∈ P → (φ x : Equiv.Perm Ω) ∈ P

private def characteristicHallPartition30739 {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) (d : ℕ) : Set (Set Ω) :=
  {B | ∃ P : Subgroup (Equiv.Perm Ω),
    characteristicSubgroupOfOrder30739 R P d ∧
      B ∈ subgroupOrbitPartition30739 P}

private def preservesDescendingHallPrefixes30739 {p q r n : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n30739 p q r)))
    (f : Equiv.Perm (CrtQ4n30739 p q r)) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    j ≤ (descendingPrimeFactors30739 n).length →
    Set.image (fun B : Set (CrtQ4n30739 p q r) => f '' B)
        (characteristicHallPartition30739 R
          (hallPrefixProduct30739 n j)) =
      characteristicHallPartition30739 R (hallPrefixProduct30739 n j)

private def blockContainsBothAffectedCoordinates30739 {p q r : ℕ}
    (B : Set (CrtQ4n30739 p q r)) : Prop :=
  (∃ x x', x ∈ B ∧ x' ∈ B ∧ x.1.1 ≠ x'.1.1) ∧
    (∃ y y', y ∈ B ∧ y' ∈ B ∧ y.1.2.1 ≠ y'.1.2.1)

private def coordinatewiseAffineOnBlock30739 {p q r : ℕ}
    (f : Equiv.Perm (CrtQ4n30739 p q r))
    (B : Set (CrtQ4n30739 p q r)) : Prop :=
  ∃ (aₚ : (ZMod p)ˣ) (bₚ : ZMod p)
    (a_q : (ZMod q)ˣ) (b_q : ZMod q)
    (aᵣ : (ZMod r)ˣ) (bᵣ : ZMod r),
    ∀ x ∈ B,
      f x =
        ((((aₚ : ZMod p) * x.1.1 + bₚ,
            (a_q : ZMod q) * x.1.2.1 + b_q,
            (aᵣ : ZMod r) * x.1.2.2 + bᵣ),
          x.2))

private def nonBlockwiseAffineOnAffectedPrefixes30739 {p q r n : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n30739 p q r)))
    (f : Equiv.Perm (CrtQ4n30739 p q r)) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    j ≤ (descendingPrimeFactors30739 n).length →
    ∀ B : Set (CrtQ4n30739 p q r),
      B ∈ characteristicHallPartition30739 R
        (hallPrefixProduct30739 n j) →
      blockContainsBothAffectedCoordinates30739 B →
      ¬ coordinatewiseAffineOnBlock30739 f B

private def triangularWitnessAvailable30739 (n : ℕ) : Prop :=
  ∃ q p : ℕ,
    Nat.Prime q ∧ Nat.Prime p ∧ q ≠ p ∧
      q ∣ n ∧ p ∣ n ∧ q ∣ p - 1 ∧ p * q ∣ n ∧
      ∃ ζ : (ZMod p)ˣ,
        orderOf ζ = q ∧
        ∃ f : Equiv.Perm (CrtQ4n30739 p q (n / (p * q))),
          ∃ R T : Subgroup
            (Equiv.Perm (CrtQ4n30739 p q (n / (p * q)))),
            (∀ x, f x = triangularFormula30739 ζ x) ∧
            standardRegularQ4n30739 (n := n) R ∧
            (∀ g : Equiv.Perm (CrtQ4n30739 p q (n / (p * q))),
              g ∈ T ↔
                ∃ u : Equiv.Perm (CrtQ4n30739 p q (n / (p * q))),
                  u ∈ R ∧ g = f.symm * u * f) ∧
            preservesDescendingHallPrefixes30739 (n := n) R f ∧
            nonBlockwiseAffineOnAffectedPrefixes30739 (n := n) R f

private def arithmeticResonance30739 (n : ℕ) : Prop :=
  ∃ q p : ℕ,
    Nat.Prime q ∧ Nat.Prime p ∧ q ≠ p ∧
      q ∣ n ∧ p ∣ n ∧ q ∣ p - 1

/-- Claim 30739: for odd square-free `n`, the gcd/totient resonance is exactly
    the distinct-prime divisibility condition, and that resonance supplies
    the standard regular-copy, Hall-prefix-preserving, nonaffine triangular
    witness from the cited construction. -/
def claim30739 : Prop :=
  ∀ n : ℕ,
    Odd n → Squarefree n →
      (Nat.gcd n (Nat.totient n) > 1 ↔ arithmeticResonance30739 n) ∧
        (arithmeticResonance30739 n → triangularWitnessAvailable30739 n)

end MathlibPlus.Open.Research.R1261
