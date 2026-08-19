import MathlibPlus.Open.Research.R1261.Claim30739

namespace MathlibPlus.Open.ResearchFormalization.R1261Claim30736

noncomputable section

private abbrev CrtOdd (p q r : ℕ) := ZMod p × ZMod q × ZMod r
private abbrev CrtQ4n (p q r : ℕ) := CrtOdd p q r × ZMod 4

private def crtQ4nMul (p q r : ℕ)
    (a b : CrtQ4n p q r) : CrtQ4n p q r :=
  (a.1 +
      (((-1 : ZMod p) ^ a.2.val) * b.1.1,
        ((-1 : ZMod q) ^ a.2.val) * b.1.2.1,
        ((-1 : ZMod r) ^ a.2.val) * b.1.2.2),
    a.2 + b.2)

private def q4nTranslationSet (p q r : ℕ) :
    Set (Equiv.Perm (CrtQ4n p q r)) :=
  {e | ∃ g : CrtQ4n p q r, ∀ x,
    e x = crtQ4nMul p q r g x}

private def q4nStandardCopy (p q r : ℕ) :
    Subgroup (Equiv.Perm (CrtQ4n p q r)) :=
  Subgroup.closure (q4nTranslationSet p q r)

private def triangularFormula {p q r : ℕ}
    (ζ : (ZMod p)ˣ) (x : CrtQ4n p q r) : CrtQ4n p q r :=
  ((((ζ : ZMod p) ^ x.1.2.1.val) * x.1.1,
      x.1.2.1,
      x.1.2.2),
    x.2)

private def descendingPrimeFactors (n : ℕ) : List ℕ :=
  n.primeFactorsList.reverse

private def hallPrefixProduct (n j : ℕ) : ℕ :=
  (descendingPrimeFactors n).take j |>.prod

private def subgroupOrbitBlock {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ u : P, u.1 x = y}

private def subgroupOrbitPartition {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, subgroupOrbitBlock P x = B}

private def characteristicSubgroupOfOrder {Ω : Type*}
    (R P : Subgroup (Equiv.Perm Ω)) (d : ℕ) : Prop :=
  P ≤ R ∧ Nat.card P = d ∧
    ∀ φ : R ≃* R, ∀ x : R,
      (x : Equiv.Perm Ω) ∈ P → (φ x : Equiv.Perm Ω) ∈ P

private def characteristicHallPartition {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) (d : ℕ) : Set (Set Ω) :=
  {B | ∃ P : Subgroup (Equiv.Perm Ω),
    characteristicSubgroupOfOrder R P d ∧
      B ∈ subgroupOrbitPartition P}

private def conjugateCopy {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) (f : Equiv.Perm Ω) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure
    {g | ∃ u : R, g = f.symm * u.1 * f}

private def regularCopy {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! u : R, u.1 x = y

private def generatedCopies {Ω : Type*}
    (R T : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))

private def normalBlockSystem {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (P : Set (Set Ω)) : Prop :=
  ∀ g : H, ∀ B : Set Ω, B ∈ P →
    ∃ C : Set Ω, C ∈ P ∧
      (g : Equiv.Perm Ω) '' B = C

private def blockContainsBothAffectedCoordinates {p q r : ℕ}
    (B : Set (CrtQ4n p q r)) : Prop :=
  (∃ x x', x ∈ B ∧ x' ∈ B ∧ x.1.1 ≠ x'.1.1) ∧
    (∃ y y', y ∈ B ∧ y' ∈ B ∧ y.1.2.1 ≠ y'.1.2.1)

private def qCoordinateConstant {p q r : ℕ}
    (B : Set (CrtQ4n p q r)) : Prop :=
  ∀ x x', x ∈ B → x' ∈ B → x.1.2.1 = x'.1.2.1

private def pOnlyInsideBlock {p q r : ℕ}
    (f : Equiv.Perm (CrtQ4n p q r))
    (B : Set (CrtQ4n p q r)) : Prop :=
  ∀ x : CrtQ4n p q r, x ∈ B →
    f x ∈ B ∧
      (f x).1.2.1 = x.1.2.1 ∧
        (f x).1.2.2 = x.1.2.2 ∧
          (f x).2 = x.2

private def prefixPartition {p q r n : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n p q r))) (j : ℕ) :
    Set (Set (CrtQ4n p q r)) :=
  characteristicHallPartition R (hallPrefixProduct n j)

private def commonPrefixPartitions {p q r n : ℕ}
    (R T : Subgroup (Equiv.Perm (CrtQ4n p q r))) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    j ≤ (descendingPrimeFactors n).length →
      prefixPartition (n := n) R j = prefixPartition (n := n) T j

private def prefixPartitionsNormal {p q r n : ℕ}
    (R T : Subgroup (Equiv.Perm (CrtQ4n p q r))) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    j ≤ (descendingPrimeFactors n).length →
      normalBlockSystem (generatedCopies R T)
        (prefixPartition (n := n) R j)

private def prefixCoordinateCases {p q r n : ℕ}
    (R : Subgroup (Equiv.Perm (CrtQ4n p q r)))
    (f : Equiv.Perm (CrtQ4n p q r)) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    j ≤ (descendingPrimeFactors n).length →
      ∀ B : Set (CrtQ4n p q r),
        B ∈ prefixPartition (n := n) R j →
          ((¬ (∃ h : ℕ, h ∈ (descendingPrimeFactors n).take j ∧
                h = p) →
              qCoordinateConstant B) ∧
            ((p ∣ hallPrefixProduct n j ∧
                ¬ q ∣ hallPrefixProduct n j) →
              pOnlyInsideBlock f B) ∧
              (q ∣ hallPrefixProduct n j →
                blockContainsBothAffectedCoordinates B))

def descendingPrefixCollapse_claim30736 : Prop :=
  ∀ (n p q : ℕ),
    Odd n →
      Squarefree n →
        Nat.Prime p →
          Nat.Prime q →
            p ≠ q →
              q ∣ p - 1 →
                p * q ∣ n →
                  ∃ ζ : (ZMod p)ˣ,
                    orderOf ζ = q ∧
                      ∃ f : Equiv.Perm
                          (CrtQ4n p q (n / (p * q))),
                        ∃ R T : Subgroup
                            (Equiv.Perm
                              (CrtQ4n p q (n / (p * q)))),
                          (∀ x,
                            f x =
                              triangularFormula ζ x) ∧
                            R = q4nStandardCopy p q (n / (p * q)) ∧
                              regularCopy R ∧
                                regularCopy T ∧
                                  (∀ g, g ∈ T ↔
                                    ∃ u : R,
                                      g = f.symm * u.1 * f) ∧
                                    commonPrefixPartitions
                                      (n := n) R T ∧
                                      prefixPartitionsNormal
                                        (n := n) R T ∧
                                      prefixCoordinateCases
                                        (n := n) R f

end

end MathlibPlus.Open.ResearchFormalization.R1261Claim30736
