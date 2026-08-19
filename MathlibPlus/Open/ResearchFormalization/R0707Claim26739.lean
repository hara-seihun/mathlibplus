import MathlibPlus.Open.ResearchFormalization.R0707Claim26737

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0707Claim26739

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0707Claim26737

noncomputable def maximalMinorValue26739
    {A B R : Type*} [Fintype A] [Fintype B] [CommRing R]
    (M : Matrix A B R)
    (ia : Fin (min (Fintype.card A) (Fintype.card B)) ↪ A)
    (ib : Fin (min (Fintype.card A) (Fintype.card B)) ↪ B) : R :=
  Matrix.det (fun i j => M (ia i) (ib j))

def complementaryMatrixInt26739
    {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (w : P → P → ℤ) (k : ℕ) :
    Matrix (rankLevel rank k) (rankLevel rank (r - k)) ℤ :=
  complementaryPowerMatrix r rank w k

def complementaryMatrixModPrime26739
    {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (w : P → P → ℤ) (p k : ℕ) :
    Matrix (rankLevel rank k) (rankLevel rank (r - k)) (ZMod p) :=
  complementaryPowerMatrix r rank (fun x y => (w x y : ZMod p)) k

def modPrimeFullRank26739
    {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (w : P → P → ℤ) (p : ℕ) : Prop :=
  ∀ k : ℕ, 2 * k < r →
    ∃ (ia : Fin (min
        (Fintype.card (rankLevel rank k))
        (Fintype.card (rankLevel rank (r - k)))) ↪ rankLevel rank k)
      (ib : Fin (min
        (Fintype.card (rankLevel rank k))
        (Fintype.card (rankLevel rank (r - k)))) ↪
        rankLevel rank (r - k)),
      maximalMinorValue26739
          (complementaryMatrixModPrime26739 r rank w p k) ia ib ≠ 0

def integralMaximalMinorTransfer26739
    {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (w : P → P → ℤ) (p : ℕ) : Prop :=
  ∀ k : ℕ, 2 * k < r →
    ∃ (ia : Fin (min
        (Fintype.card (rankLevel rank k))
        (Fintype.card (rankLevel rank (r - k)))) ↪ rankLevel rank k)
      (ib : Fin (min
        (Fintype.card (rankLevel rank k))
        (Fintype.card (rankLevel rank (r - k)))) ↪
        rankLevel rank (r - k)),
      let mℤ := maximalMinorValue26739
        (complementaryMatrixInt26739 r rank w k) ia ib
      let mp := maximalMinorValue26739
        (complementaryMatrixModPrime26739 r rank w p k) ia ib
      mℤ ≠ 0 ∧ mp = (mℤ : ZMod p) ∧ mp ≠ 0

def positiveIntegerCoverWeight26739
    {P : Type*} [PartialOrder P] (w : P → P → ℤ) : Prop :=
  (∀ x y, coverRelation x y → 0 < w x y) ∧
    (∀ x y, ¬ coverRelation x y → w x y = 0)

/-- Claim 26739: a strictly positive integral cover weighting whose every
    complementary matrix has a nonzero maximal minor modulo one prime has
    the corresponding nonzero integral minors in characteristic zero, full
    rank over `ℚ` and `ℂ`, and the Peck/strong-Sperner conclusions. -/
def onePrimeFullRankCertificate_claim26739 : Prop :=
  ∀ (P : Type*) [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ)
    (w : P → P → ℤ) (p : ℕ),
    finiteGradedPoset r rank →
      Nat.Prime p →
        positiveIntegerCoverWeight26739 w →
          modPrimeFullRank26739 r rank w p →
            integralMaximalMinorTransfer26739 r rank w p ∧
              complementaryPowersFullRank r rank
                (fun x y => (w x y : ℚ)) ∧
                complementaryPowersFullRank r rank
                  (fun x y => (w x y : ℂ)) ∧
                peckness r rank ∧
                  strongSpernerProperty r rank

end

end MathlibPlus.Open.ResearchFormalization.R0707Claim26739
